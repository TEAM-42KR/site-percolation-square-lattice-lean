import SitePerc.Checker.CompactCertificateBytesDefs
import Init.Data.ByteArray.Lemmas
import Init.Data.String.Lemmas
import Mathlib.Data.Nat.Digits.Defs
import Lean.Elab.Tactic.Omega

/-!
# Structure-aware, exact certificate byte transport

A node token carries four fixed-width 16-byte little-endian integers.
An edge token carries four 4-byte integers and one 16-byte integer.
Raw byte tokens preserve headers, partial sampled records, and all padding.
Integers use little-endian six-bit digits (ASCII 48--111), terminated by z.
Tags p/q/r are outside the digit alphabet. Backslashes in generated literals
are escaped by the generator; decoded characters retain their exact values.
This pure codec does not inspect or trust a checker or producer verdict.
-/

namespace SitePerc.Checker.CompactCertificateBytes

def fromBytes (bytes : List UInt8) : Nat :=
  Nat.ofDigits 256 (bytes.map UInt8.toNat)

/-- Six-bit digits are chosen outside all stream tags and terminators. -/
def digitChar (d : Nat) : Char := Char.ofNat (48 + d)

def encodeNat (n : Nat) : List Char := (Nat.digits 64 n).map digitChar ++ ['z']

def tokenChars : Token → List Char
  | .node a b c d => 'p' :: (encodeNat a ++ encodeNat b ++ encodeNat c ++ encodeNat d)
  | .edge a b c d e => 'q' :: (encodeNat a ++ encodeNat b ++ encodeNat c ++ encodeNat d ++ encodeNat e)
  | .byte b => 'r' :: encodeNat b.toNat

def payload (tokens : List Token) : ByteArray := (tokens.flatMap tokenBytes).toByteArray

def encodeTokens (tokens : List Token) : String := String.ofList (tokens.flatMap tokenChars)

/-- Token fuel ensures totality even for arbitrary malformed strings. -/
theorem leBytes_fromBytes (bytes : List UInt8) :
    leBytes bytes.length (fromBytes bytes) = bytes := by
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toNat_lt
    have hdiv : (b.toNat + 256 * fromBytes bs) / 256 = fromBytes bs := by omega
    have hbyte : UInt8.ofNat (b.toNat + 256 * fromBytes bs) = b := by
      apply UInt8.toNat_inj.mp
      change (b.toNat + 256 * fromBytes bs) % 256 = b.toNat
      omega
    change UInt8.ofNat (b.toNat + 256 * fromBytes bs) ::
      leBytes bs.length ((b.toNat + 256 * fromBytes bs) / 256) = b :: bs
    rw [hbyte, hdiv, ih]

private theorem digitChar_toNat (d : Nat) (hd : d < 64) :
    (digitChar d).toNat = 48 + d := by
  have hvalid : (48 + d).isValidChar := by simp only [Nat.isValidChar]; omega
  simp only [digitChar, Char.ofNat, dite_eq_left hvalid, Char.toNat]
  rfl

private theorem readDigit_digitChar (d : Nat) (hd : d < 64) :
    readDigit (digitChar d) = some d := by
  rw [readDigit, digitChar_toNat d hd]
  split
  · congr 1
    omega
  · rename_i h
    exact False.elim (h ⟨by omega, by omega⟩)

private theorem digitChar_ne_z (d : Nat) (hd : d < 64) : digitChar d ≠ 'z' := by
  intro h
  have h' := congrArg Char.toNat h
  rw [digitChar_toNat d hd] at h'
  change 48 + d = 122 at h'
  omega

private theorem readNat_digits (digits : List Nat) (hd : ∀ d ∈ digits, d < 64)
    (rest : List Char) :
    readNat (digits.map digitChar ++ 'z' :: rest) = some (Nat.ofDigits 64 digits, rest) := by
  induction digits with
  | nil => simp [readNat, Nat.ofDigits]
  | cons d ds ih =>
    have h := hd d (by simp)
    simp only [List.map_cons, List.cons_append, readNat, digitChar_ne_z d h,
      ↓reduceIte, readDigit_digitChar d h, Option.bind_some]
    rw [ih (fun d' hd' => hd d' (by simp [hd']))]
    rfl

theorem readNat_encodeNat (n : Nat) (rest : List Char) :
    readNat (encodeNat n ++ rest) = some (n, rest) := by
  rw [encodeNat, List.append_assoc]
  change readNat ((Nat.digits 64 n).map digitChar ++ 'z' :: rest) = _
  rw [readNat_digits _ (fun d hd => Nat.digits_lt_base (by decide) hd), Nat.ofDigits_digits]

theorem readToken_tokenChars (token : Token) (rest : List Char) :
    readToken (tokenChars token ++ rest) = some (token, rest) := by
  cases token <;>
    simp [tokenChars, readToken, List.append_assoc, readNat_encodeNat, UInt8.ofNat_toNat]
  exact UInt8.toNat_lt _

private theorem tokenChars_nonempty (token : Token) : tokenChars token ≠ [] := by
  cases token <;> simp [tokenChars]

private theorem payload_cons (t : Token) (ts : List Token) :
    payload (t::ts) = (tokenBytes t).toByteArray ++ payload ts := by
  simp [payload, List.toByteArray_append]

private theorem encode_length (tokens : List Token) :
    tokens.length ≤ (tokens.flatMap tokenChars).length := by
  induction tokens with
  | nil => simp
  | cons t ts ih =>
    have ht := List.length_pos_iff.mpr (tokenChars_nonempty t)
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

private theorem decodeFuel_tokens (tokens : List Token) (out : ByteArray)
    (fuel : Nat) (hf : tokens.length ≤ fuel) :
    decodeFuel fuel (tokens.flatMap tokenChars) out = some (out ++ payload tokens) := by
  induction tokens generalizing out fuel with
  | nil => simp [decodeFuel, payload]
  | cons t ts ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hne : tokenChars t ++ ts.flatMap tokenChars ≠ [] := by
        simp [List.append_eq_nil_iff, tokenChars_nonempty]
      have hstep : decodeFuel (fuel+1) (tokenChars t ++ ts.flatMap tokenChars) out =
          decodeFuel fuel (ts.flatMap tokenChars) (out ++ (tokenBytes t).toByteArray) := by
        cases hchars : tokenChars t ++ ts.flatMap tokenChars with
        | nil => exact False.elim (hne hchars)
        | cons c cs =>
          rw [decodeFuel]
          rw [← hchars, readToken_tokenChars]
          rfl
          all_goals simp
      rw [List.flatMap_cons, hstep, ih _ fuel (by simpa using hf), payload_cons]
      simp [ByteArray.append_assoc]

theorem decodeTokens_lossless (tokens : List Token) (out : ByteArray) :
    decodeChunk (encodeTokens tokens) out = some (out ++ payload tokens) := by
  rw [decodeChunk, encodeTokens, String.toList_ofList]
  exact decodeFuel_tokens tokens out _ (encode_length tokens)

private theorem payload_append (a b : List Token) :
    payload (a ++ b) = payload a ++ payload b := by
  simp [payload, List.flatMap_append, List.toByteArray_append]

private theorem decodeChunks_fold (chunks : List (List Token)) (out : ByteArray) :
    (chunks.map encodeTokens).foldl
      (fun result encoded => result.bind (fun bytes => decodeChunk encoded bytes)) (some out) =
      some (out ++ payload chunks.flatten) := by
  induction chunks generalizing out with
  | nil => simp [payload]
  | cons ts rest ih =>
    simp only [List.map_cons, List.foldl_cons]
    change (rest.map encodeTokens).foldl
      (fun result encoded => result.bind (fun bytes => decodeChunk encoded bytes))
      (decodeChunk (encodeTokens ts) out) = _
    rw [decodeTokens_lossless, ih]
    simp [List.flatten_cons, payload_append, ByteArray.append_assoc]

theorem decodeChunks_lossless (chunks : List (List Token)) :
    decodeChunks (chunks.map encodeTokens).toArray = payload chunks.flatten := by
  rw [decodeChunks, decodeChunks?, List.foldl_toArray, decodeChunks_fold]
  simp

theorem nodeFields_exact (a b c d : List UInt8)
    (ha : a.length = 16) (hb : b.length = 16) (hc : c.length = 16) (hd : d.length = 16) :
    tokenBytes (.node (fromBytes a) (fromBytes b) (fromBytes c) (fromBytes d)) =
      a ++ b ++ c ++ d := by
  have ha' : leBytes 16 (fromBytes a) = a := by simpa only [ha] using leBytes_fromBytes a
  have hb' : leBytes 16 (fromBytes b) = b := by simpa only [hb] using leBytes_fromBytes b
  have hc' : leBytes 16 (fromBytes c) = c := by simpa only [hc] using leBytes_fromBytes c
  have hd' : leBytes 16 (fromBytes d) = d := by simpa only [hd] using leBytes_fromBytes d
  simp only [tokenBytes, ha', hb', hc', hd']

theorem edgeFields_exact (a b c d e : List UInt8)
    (ha : a.length = 4) (hb : b.length = 4) (hc : c.length = 4) (hd : d.length = 4)
    (he : e.length = 16) :
    tokenBytes (.edge (fromBytes a) (fromBytes b) (fromBytes c) (fromBytes d) (fromBytes e)) =
      a ++ b ++ c ++ d ++ e := by
  have ha' : leBytes 4 (fromBytes a) = a := by simpa only [ha] using leBytes_fromBytes a
  have hb' : leBytes 4 (fromBytes b) = b := by simpa only [hb] using leBytes_fromBytes b
  have hc' : leBytes 4 (fromBytes c) = c := by simpa only [hc] using leBytes_fromBytes c
  have hd' : leBytes 4 (fromBytes d) = d := by simpa only [hd] using leBytes_fromBytes d
  have he' : leBytes 16 (fromBytes e) = e := by simpa only [he] using leBytes_fromBytes e
  simp only [tokenBytes, ha', hb', hc', hd', he']

#print axioms nodeFields_exact
#print axioms edgeFields_exact
#print axioms leBytes_fromBytes
#print axioms readNat_encodeNat
#print axioms readToken_tokenChars
#print axioms decodeTokens_lossless
#print axioms decodeChunks_lossless

end SitePerc.Checker.CompactCertificateBytes
