import Init.Data.ByteArray.Basic
import Init.Data.String.Basic

/-!
# Pure executable compact certificate-byte decoder

This module imports only Init. It retains the exact decoder definitions and
namespace consumed by generated certificate data. Proofs and mathematical
reference encoders live in CompactCertificateBytes and are not runtime inputs.
Node/edge fixed widths, reserved fields, raw fragments and headers are unchanged.
-/

namespace SitePerc.Checker.CompactCertificateBytes

inductive Token where
  | node (key supply capacity absorbed : Nat)
  | edge (src dst perm reserved flow : Nat)
  | byte (value : UInt8)
  deriving DecidableEq, Repr

/-- Fixed width is semantic: leading high zero bytes are always written back. -/
def leBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | width+1, value => UInt8.ofNat value :: leBytes width (value / 256)

/-- Exact interpretation of a little-endian source byte field. -/
def readDigit (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat < 112 then some (c.toNat - 48) else none

/-- Actual variable-length integer reader; z terminates even a zero integer. -/
def readNat : List Char → Option (Nat × List Char)
  | [] => none
  | c::cs =>
    if c = 'z' then some (0, cs)
    else do
      let d ← readDigit c
      let (n, rest) ← readNat cs
      pure (d + 64*n, rest)

/-- Every field, including reserved edge padding, has its original width. -/
def tokenBytes : Token → List UInt8
  | .node a b c d => leBytes 16 a ++ leBytes 16 b ++ leBytes 16 c ++ leBytes 16 d
  | .edge a b c d e => leBytes 4 a ++ leBytes 4 b ++ leBytes 4 c ++ leBytes 4 d ++ leBytes 16 e
  | .byte b => [b]

def readToken : List Char → Option (Token × List Char)
  | [] => none
  | tag::cs =>
    if tag = 'p' then do
      let (a, cs) ← readNat cs
      let (b, cs) ← readNat cs
      let (c, cs) ← readNat cs
      let (d, cs) ← readNat cs
      pure (.node a b c d, cs)
    else if tag = 'q' then do
      let (a, cs) ← readNat cs
      let (b, cs) ← readNat cs
      let (c, cs) ← readNat cs
      let (d, cs) ← readNat cs
      let (e, cs) ← readNat cs
      pure (.edge a b c d e, cs)
    else if tag = 'r' then do
      let (b, cs) ← readNat cs
      if b < 256 then pure (.byte (UInt8.ofNat b), cs) else none
    else none

def decodeFuel : Nat → List Char → ByteArray → Option ByteArray
  | _, [], out => some out
  | 0, _, _ => none
  | fuel+1, cs, out => do
      let (token, rest) ← readToken cs
      decodeFuel fuel rest (out ++ (tokenBytes token).toByteArray)

/-- Actual decoder used by the generated four-array consumer. -/
def decodeChunk (encoded : String) (out : ByteArray := ByteArray.empty) : Option ByteArray :=
  decodeFuel encoded.toList.length encoded.toList out

def decodeChunks? (chunks : Array String) : Option ByteArray :=
  chunks.foldl (fun result encoded => result.bind (fun bytes => decodeChunk encoded bytes))
    (some ByteArray.empty)

def decodeChunks (chunks : Array String) : ByteArray :=
  (decodeChunks? chunks).getD ByteArray.empty

end SitePerc.Checker.CompactCertificateBytes
