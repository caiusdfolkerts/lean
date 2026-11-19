module

public meta import Lean.Elab.Term

/-!
# Large certificate numerals

This is an untrusted term elaborator for data, not a proof tactic. It returns
only a natural-number literal. Every mathematical property of the resulting
certificate is checked separately by the ordinary Lean kernel. Splitting the
digit string avoids the quadratic cost of the standard one-digit-at-a-time
parser on certificate numerals containing hundreds of thousands of digits.
-/

public meta section
namespace CertificateData

open Lean Elab Term

private def digit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def decode (digits : Array Nat) (start len : Nat) : Nat → Nat
  | 0 => (List.range len).foldl (fun n i => 16 * n + digits[start + i]!) 0
  | fuel + 1 =>
    if len ≤ 512 then
      (List.range len).foldl (fun n i => 16 * n + digits[start + i]!) 0
    else
      let left := len / 2
      Nat.shiftLeft (decode digits start left fuel) (4 * (len - left)) +
        decode digits (start + left) (len - left) fuel

syntax (name := hexadecimalData) "hexnat% " str : term

@[term_elab hexadecimalData] meta def elaborateHexadecimalData : TermElab := fun stx _ => do
  let some text := stx[1].isStrLit? |
    throwErrorAt stx "expected a hexadecimal certificate string"
  let mut digits : Array Nat := #[]
  for c in text.toList do
    match digit c with
    | some n => digits := digits.push n
    | none => throwErrorAt stx "invalid hexadecimal certificate digit"
  if digits.isEmpty then throwErrorAt stx "empty hexadecimal certificate numeral"
  return Lean.mkNatLit (decode digits 0 digits.size digits.size)

end CertificateData
