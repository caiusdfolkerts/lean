module

public meta import Lean.Elab.Term

/-!
# Sparse hexadecimal certificate numerals

`sparse_nat%` is an untrusted data elaborator. It emits an ordinary `Nat`
literal; it proves nothing, and every certificate property is still checked
by Lean's kernel. Hexadecimal digits have their usual meaning. A token
`z<count>;` inserts `count` zero hexadecimal digits, with the count itself
written in hexadecimal. For example, `sparse_nat% "az3;b"` is `0xa000b`.

The generated incidence matrices are sparse but have very large bit indices.
Encoding their zero runs avoids parsing thousands of explicit zero digits per
matrix. The decoder joins bounded digit blocks in a balanced tree, so dense
parts also avoid the quadratic cost of digit-by-digit big-number parsing.
-/

public meta section
namespace CertificateData.Sparse

open Lean Elab Term

private def digit (c : UInt8) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c ∧ c ≤ 102 then some (c.toNat - 87)
  else if 65 ≤ c ∧ c ≤ 70 then some (c.toNat - 55)
  else none

private def join (a b : Nat × Nat) : Nat × Nat :=
  (Nat.lor (Nat.shiftLeft a.1 (4 * b.2)) b.1, a.2 + b.2)

private def combine (blocks : Array (Nat × Nat)) (start len : Nat) : Nat → Nat × Nat
  | 0 => (List.range len).foldl (fun acc i => join acc blocks[start + i]!) (0, 0)
  | fuel + 1 =>
      if len = 0 then (0, 0)
      else if len = 1 then blocks[start]!
      else
        let left := len / 2
        join (combine blocks start left fuel)
          (combine blocks (start + left) (len - left) fuel)

private def maxDigits : Nat := 16 * 1024 * 1024

/-- The parser accepts only hexadecimal digits and explicit zero-run tokens.
The size bound catches accidental enormous shifts in generated input. -/
def decode (text : String) : Except String Nat := do
  let bytes := text.toUTF8
  if bytes.isEmpty then throw "empty sparse certificate numeral"
  let mut blocks : Array (Nat × Nat) := #[]
  let mut word := 0
  let mut width := 0
  let mut total := 0
  let mut run : Option Nat := none
  let mut runDigits := 0
  for c in bytes do
    match run with
    | some count =>
        if c = 59 then
          if runDigits = 0 ∨ count = 0 then
            throw "a zero-run token needs a positive hexadecimal count"
          if total + count > maxDigits then
            throw "sparse certificate numeral exceeds the size limit"
          blocks := blocks.push (0, count)
          total := total + count
          run := none
          runDigits := 0
        else
          let some d := digit c | throw "invalid hexadecimal zero-run count"
          let next := 16 * count + d
          if next > maxDigits then
            throw "sparse certificate zero run exceeds the size limit"
          run := some next
          runDigits := runDigits + 1
    | none =>
        if c = 122 then
          if width > 0 then blocks := blocks.push (word, width)
          word := 0
          width := 0
          run := some 0
          runDigits := 0
        else
          let some d := digit c | throw "invalid sparse hexadecimal certificate digit"
          if total = maxDigits then
            throw "sparse certificate numeral exceeds the size limit"
          word := 16 * word + d
          width := width + 1
          total := total + 1
          if width = 256 then
            blocks := blocks.push (word, width)
            word := 0
            width := 0
  if run.isSome then throw "unterminated hexadecimal zero-run token"
  if width > 0 then blocks := blocks.push (word, width)
  return (combine blocks 0 blocks.size blocks.size).1

syntax (name := sparseNaturalData) "sparse_nat% " str : term

@[term_elab sparseNaturalData] meta def elaborateSparseNaturalData : TermElab := fun stx _ => do
  let some text := stx[1].isStrLit? |
    throwErrorAt stx "expected a sparse hexadecimal certificate string"
  match decode text with
  | .error message => throwErrorAt stx message
  | .ok value => return Lean.mkNatLit value

end CertificateData.Sparse
