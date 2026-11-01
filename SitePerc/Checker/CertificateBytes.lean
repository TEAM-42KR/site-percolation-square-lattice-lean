import Init.Data.ByteArray.Lemmas
import Init.Data.String.Lemmas
import Lean.Elab.Tactic.Omega

/-!
# Pure certificate-byte transport

Each ordinary byte is two ASCII letters A--P (high nibble, low nibble).
A run of zero bytes is Z followed by the same two-letter encoding of its
length (0--255). Encoded strings may be split only between complete tokens.
The decoder is total and rejects malformed strings. Generated constants
use no IO, producer verdict, foreign code, or custom axiom.
-/

namespace SitePerc.Checker.CertificateBytes

/-- A byte literal or a bounded zero run. Zero-length runs are harmless. -/
inductive Token where
  | literal (value : UInt8)
  | zeros (length : UInt8)
  deriving DecidableEq, Repr

/-- Encode a nibble as a safe printable ASCII letter. -/
def nibbleChar (n : Nat) : Char := Char.ofNat (65 + n)

/-- A fixed-width two-character representation of one byte. -/
def byteChars (b : UInt8) : List Char :=
  [nibbleChar (b.toNat / 16), nibbleChar (b.toNat % 16)]

/-- Logical bytes represented by a token. -/
def tokenBytes : Token → List UInt8
  | .literal b => [b]
  | .zeros n => List.replicate n.toNat 0

/-- Actual on-disk literal syntax for a token. -/
def tokenChars : Token → List Char
  | .literal b => byteChars b
  | .zeros n => 'Z' :: byteChars n

/-- Exact uncompressed semantic payload of a token sequence. -/
def payload (tokens : List Token) : ByteArray :=
  (tokens.flatMap tokenBytes).toByteArray

/-- Reference encoder used by the semantic losslessness theorem. -/
def encodeTokens (tokens : List Token) : String :=
  String.ofList (tokens.flatMap tokenChars)

/-- Decode a single hexadecimal nibble, rejecting all non-A--P characters. -/
def readNibble (c : Char) : Option Nat :=
  if 65 ≤ c.toNat ∧ c.toNat < 81 then some (c.toNat - 65) else none

/-- Decode exactly two hexadecimal letters into a byte. -/
def readByte (hi lo : Char) : Option UInt8 := do
  let h ← readNibble hi
  let l ← readNibble lo
  pure (UInt8.ofNat (16 * h + l))

/-- Append a bounded zero run without expanding any Lean literal array. -/
def appendZeros (out : ByteArray) (n : UInt8) : ByteArray :=
  out ++ (List.replicate n.toNat (0 : UInt8)).toByteArray

/-- Tail-recursive pure decoder. Its accumulator is the final byte array,
so complete tokens can be streamed across independently compiled chunks. -/
def decodeInto : List Char → ByteArray → Option ByteArray
  | [], out => some out
  | a :: b :: rest, out =>
      if a = 'Z' then
        match rest with
        | [] => none
        | c :: tail =>
            match readByte b c with
            | none => none
            | some n => decodeInto tail (appendZeros out n)
      else
        match readByte a b with
        | none => none
        | some v => decodeInto rest (out.push v)
  | _, _ => none

/-- Actual generated chunk decoder. -/
def decodeChunk (encoded : String) (out : ByteArray := ByteArray.empty) : Option ByteArray :=
  decodeInto encoded.toList out

/-- Decode independent, token-aligned string chunks into one output array. -/
def decodeChunks? (chunks : Array String) : Option ByteArray :=
  chunks.foldl (fun out encoded => out.bind (fun bytes => decodeChunk encoded bytes))
    (some ByteArray.empty)

/-- Four-array consumer wrapper. Valid generated streams never take the
fallback branch, by `decodeTokens_lossless` and the generator replay check. -/
def decodeChunks (chunks : Array String) : ByteArray :=
  (decodeChunks? chunks).getD ByteArray.empty

private theorem nibbleChar_toNat (n : Nat) (hn : n < 16) :
    (nibbleChar n).toNat = 65 + n := by
  have hvalid : (65 + n).isValidChar := by
    simp only [Nat.isValidChar]
    omega
  simp only [nibbleChar, Char.ofNat, dite_eq_left hvalid, Char.toNat]
  rfl

private theorem readNibble_nibbleChar (n : Nat) (hn : n < 16) :
    readNibble (nibbleChar n) = some n := by
  rw [readNibble, nibbleChar_toNat n hn]
  split
  · congr 1
    omega
  · rename_i h
    exact False.elim (h ⟨by omega, by omega⟩)

private theorem nibbleChar_ne_Z (n : Nat) (hn : n < 16) : nibbleChar n ≠ 'Z' := by
  intro h
  have heq := congrArg Char.toNat h
  rw [nibbleChar_toNat n hn] at heq
  change 65 + n = 90 at heq
  omega

theorem readByte_byteChars (b : UInt8) :
    readByte (nibbleChar (b.toNat / 16)) (nibbleChar (b.toNat % 16)) = some b := by
  have hb : b.toNat < 256 := b.toNat_lt
  rw [readByte, readNibble_nibbleChar _ (by omega),
    readNibble_nibbleChar _ (by omega)]
  change some (UInt8.ofNat (16 * (b.toNat / 16) + b.toNat % 16)) = some b
  have heq : 16 * (b.toNat / 16) + b.toNat % 16 = b.toNat := by omega
  rw [heq, UInt8.ofNat_toNat]

private theorem payload_nil : payload [] = ByteArray.empty := rfl

private theorem payload_cons (t : Token) (ts : List Token) :
    payload (t :: ts) = (tokenBytes t).toByteArray ++ payload ts := by
  simp [payload, List.toByteArray_append]

theorem decodeInto_tokens (tokens : List Token) (out : ByteArray) :
    decodeInto (tokens.flatMap tokenChars) out = some (out ++ payload tokens) := by
  induction tokens generalizing out with
  | nil => simp [decodeInto, payload]
  | cons t ts ih =>
    cases t with
    | literal b =>
      have hn : b.toNat / 16 < 16 := by have := b.toNat_lt; omega
      simp only [List.flatMap_cons, tokenChars, byteChars, List.cons_append,
        List.nil_append]
      have hstep (rest : List Char) :
          decodeInto (nibbleChar (b.toNat / 16) :: nibbleChar (b.toNat % 16) :: rest) out =
            decodeInto rest (out.push b) := by
        cases rest <;>
          simp only [decodeInto.eq_2, decodeInto.eq_3, nibbleChar_ne_Z _ hn,
            ↓reduceIte, readByte_byteChars]
      rw [hstep, ih, payload_cons]
      simp only [tokenBytes, ← ByteArray.append_toByteArray_singleton,
        ByteArray.append_assoc]
    | zeros n =>
      simp only [List.flatMap_cons, tokenChars, byteChars, List.cons_append,
        List.nil_append, decodeInto, ↓reduceIte, readByte_byteChars]
      rw [ih, payload_cons]
      simp only [appendZeros, tokenBytes, ByteArray.append_assoc]

theorem decodeTokens_lossless (tokens : List Token) :
    decodeChunk (encodeTokens tokens) ByteArray.empty = some (payload tokens) := by
  rw [decodeChunk, encodeTokens, String.toList_ofList, decodeInto_tokens,
    ByteArray.empty_append]

private theorem payload_append (a b : List Token) :
    payload (a ++ b) = payload a ++ payload b := by
  simp [payload, List.flatMap_append, List.toByteArray_append]

private theorem decodeChunks_fold (chunks : List (List Token)) (out : ByteArray) :
    (chunks.map encodeTokens).foldl
      (fun acc encoded => acc.bind (fun bytes => decodeChunk encoded bytes)) (some out) =
      some (out ++ payload chunks.flatten) := by
  induction chunks generalizing out with
  | nil => simp [payload]
  | cons ts rest ih =>
    have ht : decodeChunk (encodeTokens ts) out = some (out ++ payload ts) := by
      rw [decodeChunk, encodeTokens, String.toList_ofList, decodeInto_tokens]
    simp only [List.map_cons, List.foldl_cons]
    change (rest.map encodeTokens).foldl
      (fun acc encoded => acc.bind (fun bytes => decodeChunk encoded bytes))
      (decodeChunk (encodeTokens ts) out) = _
    rw [ht, ih]
    simp [List.flatten_cons, payload_append, ByteArray.append_assoc]

theorem decodeChunks_lossless (chunks : List (List Token)) :
    decodeChunks (chunks.map encodeTokens).toArray = payload chunks.flatten := by
  rw [decodeChunks, decodeChunks?, List.foldl_toArray, decodeChunks_fold]
  simp

#print axioms readByte_byteChars
#print axioms decodeInto_tokens
#print axioms decodeTokens_lossless
#print axioms decodeChunks_lossless

end SitePerc.Checker.CertificateBytes
