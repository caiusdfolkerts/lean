module

public import PaperVerification.AlternatingFormsLiteralSectionFourRationality
public import PaperVerification.AlternatingFormsOnePlaneRationality
public import PaperVerification.AlternatingFormsCanonicalOddSmoothness

/-!
# The geometric clauses of Section 4 in the paper's coordinates

The Section 4 pair is literally `(G, -F)` in path coordinates. Equality of
the homogeneous defining ideals transports smoothness and nonemptiness,
as it already transports the finite-dimensional rationality witness.

`sectionFourPositiveRankOver k r` is the original scheme of `(r+1)`-planes.
Its two branches are the actual one-plane restriction ideal and the actual
rank-`t+2` restriction ideal. The branch equalities below make this indexing
explicit. The final theorem covers every `1 ≤ s ≤ k+1`, including `k = 0`.
It concerns the geometric clauses; it does not assert a cohomology or Chow
presentation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [CharZero K]

/-- The smoothness statement uses exactly the two forms printed in Section 4. -/
theorem sectionFour_isotropicStructureMap_smooth (k t : ℕ) :
    Smooth (isotropicStructureMap (t := t) (sectionFourPluckerForms (K := K) k)) :=
  (isotropicStructureMap_smooth_of_ideal_eq _ _
    (sectionFour_isotropicPluckerIdeal k t)).mpr
      (canonicalOdd_isotropicStructureMap_smooth k t)

/-- Equality of homogeneous ideals preserves the actual Proj and its points. -/
theorem sectionFour_isotropicProj_nonempty (k t : ℕ) (h : t+2 ≤ k+1) :
    Nonempty (Proj
      (isotropicProjectiveGrading (t := t) (sectionFourPluckerForms (K := K) k))) := by
  let H := {Q : Ideal (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K) //
    Q.IsHomogeneous (homogeneousSubmodule (PluckerIndex (t+2) (2*k+1)) K)}
  let P : H → Prop := fun Q =>
    Nonempty (Proj (HomogeneousQuotientProjective.grading Q.val Q.property))
  let Q₁ : H := ⟨isotropicPluckerIdeal (t := t) (sectionFourPluckerForms (K := K) k),
    isotropicPluckerIdeal_isHomogeneous (sectionFourPluckerForms k)⟩
  let Q₂ : H := ⟨isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k),
    isotropicPluckerIdeal_isHomogeneous (oddPluckerForms k)⟩
  have hQ : Q₁ = Q₂ := Subtype.ext (sectionFour_isotropicPluckerIdeal k t)
  change P Q₁
  rw [hQ]
  exact canonicalOdd_isotropicProj_nonempty k t h

/-- The actual Section 4 common-isotropic scheme of `(r+1)`-planes over `K`. -/
def sectionFourPositiveRankOver (k : ℕ) : ℕ → Over (Spec (CommRingCat.of K))
  | 0 => onePlaneIsotropicOver (sectionFourPluckerForms k)
  | t+1 => Over.mk (isotropicStructureMap (t := t) (sectionFourPluckerForms k))

@[simp] theorem sectionFourPositiveRankOver_zero (k : ℕ) :
    sectionFourPositiveRankOver (K := K) k 0 =
      onePlaneIsotropicOver (sectionFourPluckerForms k) := rfl

@[simp] theorem sectionFourPositiveRankOver_succ (k t : ℕ) :
    sectionFourPositiveRankOver (K := K) k (t+1) =
      Over.mk (isotropicStructureMap (t := t) (sectionFourPluckerForms k)) := rfl

/-- Nonemptiness, smoothness, and a finite affine birational witness in every
positive plane rank allowed in Section 4. All maps are over the original field. -/
theorem sectionFour_positive_rank_geometry (k r : ℕ) (hr : r ≤ k) :
    Nonempty (sectionFourPositiveRankOver (K := K) k r).left ∧
      Smooth (sectionFourPositiveRankOver (K := K) k r).hom ∧
      ∃ N : Type, Finite N ∧ Scheme.BirationalOver
        (sectionFourPositiveRankOver (K := K) k r).hom
        (𝔸(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
  cases r with
  | zero =>
      have hg := onePlaneIsotropic_geometry (sectionFourPluckerForms (K := K) k)
        (by omega : 0 < 2*k+1)
      exact ⟨hg.1, hg.2.1,
        onePlaneIsotropic_finite_rationality k (sectionFourPluckerForms k)⟩
  | succ t =>
      obtain ⟨N, hN, _, hbir⟩ :=
        paper_theorem_4_1_section_four_finite_rationality (K := K) k t hr
      exact ⟨sectionFour_isotropicProj_nonempty k t (by omega),
        sectionFour_isotropicStructureMap_smooth k t, N, hN, hbir⟩

/-- The shift in the uniform positive-rank indexing recovers the paper's rank. -/
theorem sectionFour_paper_rank (s : ℕ) (hs : 1 ≤ s) : s-1+1 = s := by omega

/-- The complete range of the smoothness and rationality clauses, stated with
the paper's parameters `k` and `s`. The represented plane rank is exactly `s`
by `sectionFour_paper_rank`; the case `s = 1` uses the proved line equations. -/
theorem paper_theorem_4_1_geometric_clauses
    (k s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ k+1) :
    Nonempty (sectionFourPositiveRankOver (K := K) k (s-1)).left ∧
      Smooth (sectionFourPositiveRankOver (K := K) k (s-1)).hom ∧
      ∃ N : Type, Finite N ∧ Scheme.BirationalOver
        (sectionFourPositiveRankOver (K := K) k (s-1)).hom
        (𝔸(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) :=
  sectionFour_positive_rank_geometry k (s-1) (by omega)

end PaperVerification.AlternatingForms
