module
public meta import GraphNumerals

/-! Numerical certificate files have no Lean terms. Each file is an LZ4
block of byte lengths followed by little-endian binary natural numbers.
Its immutable name appears beside the source module in the packaged tree. -/

public meta section
open Lean Elab Term
register_option palomar.groupedCertificateSource : String := {
  defValue := ""
  descr := "Original source basename for grouped certificate numerals"
}

namespace CertificateNumbers

initialize cachedNumbers : IO.Ref (Std.HashMap String (Array Nat)) ← IO.mkRef {}

def load (p : System.FilePath) : TermElabM (Array Nat) := do
  if let some values := (← cachedNumbers.get)[p.toString]? then return values
  let packed ← IO.FS.readBinFile p
  let some values := GraphNumerals.decodeNumericBlock packed | throwError "invalid numerical file {p}"
  cachedNumbers.modify (·.insert p.toString values)
  return values

def sibling (extension : String) : TermElabM System.FilePath := do
  let current := System.FilePath.mk (← getFileName)
  let original := palomar.groupedCertificateSource.get (← getOptions)
  let source := if original.isEmpty then current else current.withFileName original
  return source.withExtension extension

elab "certNat% " n:num : term => do
  let values ← load (← sibling "natpack")
  let some val := values[n.getNat]? | throwError "certificate literal index out of bounds"
  return mkNatLit val

end CertificateNumbers
