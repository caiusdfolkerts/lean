module

public import PaperVerification.HomogeneousBasisProfile

/-!
# Intrinsic Hilbert series from every actual homogeneous augmented basis

The coefficient comparison uses genuine homogeneous pieces of the given
internal grading. It therefore makes no basis choice part of the Hilbert
series, and it includes degree zero through the actual augmentation.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical PowerSeries

namespace PaperVerification.HomogeneousBasisHilbert

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (G : TauCeti.InternalGrading K A ℕ) (ε : A →ₐ[K] K)
  (B : Module.Basis (Option I) K A) (δ : I → ℕ)
  (hzero : G.piece 0=(1 : Submodule K A)) (hunit : B none=1)
  (hhom : ∀ i,B (some i)∈G.piece (δ i)) (hpos : ∀ i,0<δ i)

def series : PowerSeries ℤ := PowerSeries.mk (fun d => (Module.finrank K (G.piece d) : ℤ))

include ε hzero in
theorem degree_zero_finrank : Module.finrank K (G.piece 0)=1 := by
  have he := (DimensionFiveGradedBasis.scalarPieceEquiv G ε hzero).finrank_eq
  simpa only [Module.finrank_self] using he.symm

include ε hzero hunit hhom hpos in
theorem one_add_positiveSeries_eq : 1+WeightedBar.positiveSeries δ=series G := by
  apply PowerSeries.ext
  intro d
  rw [map_add,PowerSeries.coeff_one,HomogeneousBasisProfile.coeff_positiveSeries,
    series,PowerSeries.coeff_mk]
  by_cases hd : d=0
  · subst d
    have hn : ∀ i,δ i≠0 := fun i => Nat.ne_of_gt (hpos i)
    simp [hn,degree_zero_finrank G ε hzero]
  · rw [HomogeneousBasisProfile.card_degree G B δ hzero hunit hhom d (Nat.pos_of_ne_zero hd)]
    simp [hd]

end PaperVerification.HomogeneousBasisHilbert
