module

public import PaperVerification.AffineSpaceTotalChowRank
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-!
# The rank bound supplied by an actual finite affine paving

Each localization sequence is the genuine sequence on the displayed schemes.
An empty last stage and the proved affine-cell calculation bound the full Chow
rank by the number of nonempty strata.  The original common-isotropic paving
is substituted into this theorem in the geometric application.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TotalChow

open AlgebraicGeometry CategoryTheory
open OAI.AlgebraicGeometry
open scoped BigOperators

/-- The affine-space calculation on the literal polynomial spectrum. -/
theorem polynomialSpectrum_total_rank (ι : Type) [Finite ι] :
    Module.Finite ℚ (TotalChowQ
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial ι ℂ))))) ∧
    Module.finrank ℚ (TotalChowQ
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial ι ℂ))))) ≤ 1 := by
  let q := Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial ι ℂ)))
  letI : LocallyOfFiniteType q := HasRingHomProperty.Spec_iff.mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  let e := (AlgebraicGeometry.AffineSpace.SpecIso ι (CommRingCat.of ℂ)).symm
  have he : e.hom ≫ ((AlgebraicGeometry.AffineSpace ι complexBase ↘ complexBase) ≫
      𝟙 complexBase) = q := by
    rw [Category.comp_id]
    exact AlgebraicGeometry.AffineSpace.SpecIso_inv_over (n := ι) (CommRingCat.of ℂ)
  let E := totalChowEquiv e q _ he
  have h := finrank_complexAffineSpace_total_le_one ι
  letI := h.1
  exact ⟨Module.Finite.equiv E.symm, E.finrank_eq.trans_le h.2⟩

/-- An affine chart isomorphism over the original base gives the same
all-grading Chow bound on the actual stratum. -/
theorem finite_and_finrank_le_one_of_polynomialIso
    {U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian U]
    (f : U ⟶ complexBase) [LocallyOfFiniteType f]
    (ι : Type) [Finite ι] (e : U ≅ Spec (CommRingCat.of (MvPolynomial ι ℂ)))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial ι ℂ))) = f) :
    Module.Finite ℚ (TotalChowQ f) ∧ Module.finrank ℚ (TotalChowQ f) ≤ 1 := by
  let q := Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial ι ℂ)))
  letI : LocallyOfFiniteType q := HasRingHomProperty.Spec_iff.mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  let E := totalChowEquiv e f q he
  have h := polynomialSpectrum_total_rank ι
  letI := h.1
  exact ⟨Module.Finite.equiv E.symm, E.finrank_eq.trans_le h.2⟩

theorem finite_and_finrank_eq_zero_of_empty
    {U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian U] [IsEmpty U]
    (f : U ⟶ complexBase) :
    Module.Finite ℚ (TotalChowQ f) ∧ Module.finrank ℚ (TotalChowQ f) = 0 := by
  refine ⟨finite_of_finite_points f,?_⟩
  have h : Module.finrank ℚ (TotalChowQ f) ≤ 0 := by
    simpa only [Nat.card_of_isEmpty] using (finrank_le_card_points f)
  exact Nat.eq_zero_of_le_zero h

section Filtration

variable (stage : ℕ → Scheme.{0}) [∀ m, AlgebraicGeometry.IsNoetherian (stage m)]
  (base : ∀ m, stage m ⟶ complexBase) [∀ m, LocallyOfFiniteType (base m)]
  (closed : ∀ m, stage (m+1) ⟶ stage m) [∀ m, IsClosedImmersion (closed m)]
  (over_base : ∀ m, closed m ≫ base m = base (m+1))
  (cell : ∀ m, (stage m).Opens)
  (N : ℕ)
  (complement : ∀ m < N, Set.range (closed m) = (Set.range (cell m).ι)ᶜ)
  (last_empty : IsEmpty (stage N))
  (budget : ℕ → ℕ)
  (cell_rank : ∀ m < N,
    Module.Finite ℚ (TotalChowQ ((cell m).ι ≫ base m)) ∧
      Module.finrank ℚ (TotalChowQ ((cell m).ι ≫ base m)) ≤ budget m)

include over_base complement last_empty cell_rank

/-- The inductive bound uses every stratum and reaches the original stage. -/
theorem finitePaving_total_rank :
    Module.Finite ℚ (TotalChowQ (base 0)) ∧
      Module.finrank ℚ (TotalChowQ (base 0)) ≤ ∑ m ∈ Finset.range N, budget m := by
  have h : ∀ m ≤ N, Module.Finite ℚ (TotalChowQ (base m)) ∧
      Module.finrank ℚ (TotalChowQ (base m)) ≤ ∑ j ∈ Finset.Ico m N, budget j := by
    intro m hm
    induction hm using Nat.decreasingInduction with
    | self =>
      letI := last_empty
      have he := finite_and_finrank_eq_zero_of_empty (base N)
      exact ⟨he.1,by simp only [he.2,Finset.Ico_self,Finset.sum_empty,le_refl]⟩
    | @of_succ m hm ih =>
      have hc := cell_rank m hm
      letI := hc.1
      letI : Module.Finite ℚ (TotalChowQ (closed m ≫ base m)) := by
        rw [over_base m]
        exact ih.1
      have hf := finite_of_closed_open (cell m).ι (closed m) (base m) (complement m hm)
      refine ⟨hf,?_⟩
      have hr := finrank_le_closed_add_open (cell m).ι (closed m) (base m) (complement m hm)
      rw [over_base m] at hr
      rw [Finset.sum_eq_sum_Ico_succ_bot hm]
      exact hr.trans ((Nat.add_le_add ih.2 hc.2).trans_eq (Nat.add_comm _ _))
  simpa only [Nat.Ico_zero_eq_range] using h 0 (Nat.zero_le N)

end Filtration
end PaperVerification.TotalChow
