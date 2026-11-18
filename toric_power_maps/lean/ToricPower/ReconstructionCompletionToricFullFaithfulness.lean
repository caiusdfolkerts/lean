module

public import ToricPower.ReconstructionCompletionFullFaithfulnessTransport
public import ToricPower.ReconstructionCompletionNormalizedDerivedInterface

/-! # The original normalized right adjoint from genuine reconstruction

The categorical conclusion is identified with the paper's named right
adjoint before the actual geometric reconstruction is substituted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones]
  (regular : fan.IsRegular) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

/-- Genuine normalized reconstruction proves full faithfulness of the
paper's exact named right adjoint, in its original chosen category. -/
def arrangementNormalizedDerivedHom_fullyFaithful_of_reconstruction
    (comparison : arrangementToricDerivedHom fan nonempty regular basis rays ⋙
      reconstructionNormalizedDerivedInterface fan regular basis rays ≅
      (arrangementNormalizationEquivalence fan regular (n := n)).functor) :
    (arrangementNormalizedDerivedHom fan regular basis rays).FullyFaithful :=
  normalizedReconstructionFullyFaithfulOfInterface
    (arrangementToricDerivedRealization fan nonempty regular basis rays)
    (arrangementToricDerivedHom fan nonempty regular basis rays)
    (arrangementToricDerivedAdjunction fan nonempty regular basis rays)
    (arrangementNormalizationEquivalence fan regular (n := n))
    (reconstructionNormalizedDerivedInterface fan regular basis rays)
    (reconstructionNormalizedDerivedInterfaceIso fan regular basis rays)
    comparison

end ToricPower

end
