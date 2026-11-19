module
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

section
namespace PalomarHomologicalBoundary
universe uLiteralV uLiteralK
/-- The literal signed augmented simplicial differential: exterior contraction
by the sum of the coordinate functionals, on the actual exterior algebra. -/
abbrev differential {V : Type uLiteralV} {k : Type uLiteralK} [Fintype V] [CommRing k] :
    ExteriorAlgebra k (V → k) →ₗ[k] ExteriorAlgebra k (V → k) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k (V → k)))
    (Fintype.linearCombination k (fun _ : V => (1 : k)))
end PalomarHomologicalBoundary
end
