module
public meta import GraphNumerals

/-! Numerical certificate files have no Lean terms. Each file is an LZ4
block of byte lengths followed by little-endian binary natural numbers.
Its immutable name appears beside the source module in the packaged tree. -/

public meta section
open Lean Elab Term
namespace CertificateNumbers

initialize cachedNumbers : IO.Ref (Std.HashMap String (Array Nat)) ← IO.mkRef {}

def load (p : System.FilePath) : TermElabM (Array Nat) := do
  if let some values := (← cachedNumbers.get)[p.toString]? then return values
  let packed ← IO.FS.readBinFile p
  let some values := GraphNumerals.decodeNumericBlock packed | throwError "invalid numerical file {p}"
  cachedNumbers.modify (·.insert p.toString values)
  return values

def sibling (extension : String) : TermElabM System.FilePath := do
  return (System.FilePath.mk (← getFileName)).withExtension extension

elab "certNat% " n:num : term => do
  let values ← load (← sibling "natpack")
  let some val := values[n.getNat]? | throwError "certificate literal index out of bounds"
  return mkNatLit val

end CertificateNumbers
