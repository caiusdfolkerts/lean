module

public import PaperVerification.FermionGradedHilbert

/-! # Hilbert series under transport of an actual internal grading -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.GradedHilbert

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]

theorem series_map (G : TauCeti.InternalGrading K M ℕ) (e : M ≃ₗ[K] N) :
    series (G.map e) = series G := by
  ext d
  rw [coeff_series, coeff_series, TauCeti.InternalGrading.map_piece]
  exact congrArg (fun t : ℕ => (t : ℤ)) (e.submoduleMap (G.piece d)).finrank_eq.symm

end PaperVerification.GradedHilbert
