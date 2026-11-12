module

public import ToricPower.ArrangementCoherentInverseSerre

/-! # Actual generation from detection of target shifts -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (complete : fan.IsComplete)

local instance targetDetectionNoetherian : IsNoetherian fan.algebraicRealization := toricScheme_isNoetherian fan
local instance targetDetectionDerivedCoh : HasDerivedCategory.{1} (Coh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance targetDetectionDerivedQCoh : HasDerivedCategory.{1} (QCoh fan.algebraicRealization) := HasDerivedCategory.standard _

include complete in
/-- Shift equivalence turns the actual target-shift detection theorem
into the precise left-orthogonality condition of inverse-Serre generation. -/
theorem arrangementDbCoh_generator_of_targetDetection
    (fullyFaithful : (arrangementNormalizedDerivedHom fan regular basis rays).FullyFaithful)
    (G : DbCoh fan.algebraicRealization)
    (detect : ∀ Y : DerivedQCoh fan.algebraicRealization, ¬ IsZero Y →
      ∃ q : ℤ, ∃ f : Y ⟶
        ((boundedCoherentToQuasicoherent fan.algebraicRealization).obj G)⟦q⟧, f ≠ 0) :
    generatesDbCoh G := by
  apply arrangementDbCoh_generator_of_unbounded_leftDetection
    fan regular basis rays complete fullyFaithful G
  intro Y vanished
  by_contra nonzero
  obtain ⟨q,f,hf⟩ := detect Y nonzero
  let e := shiftShiftNeg ((boundedCoherentToQuasicoherent fan.algebraicRealization).obj G) q
  have shifted : f⟦(-q)⟧' = 0 := by
    apply (cancel_mono e.hom).mp
    simpa only [zero_comp] using vanished (-q) (f⟦(-q)⟧' ≫ e.hom)
  apply hf
  apply (shiftFunctor (DerivedQCoh fan.algebraicRealization) (-q)).map_injective
  simpa only [CategoryTheory.Functor.map_zero] using shifted

end ToricPower

end
