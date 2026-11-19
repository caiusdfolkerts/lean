module

public import PaperVerification.CommonIsotropicProjectiveNonempty
public import PaperVerification.HomogeneousQuotientAffineChartOver

/-!
# The one-plane boundary in every ambient dimension

Alternating forms vanish on lines. The original one-plane Plücker scheme has
normalized affine-space charts of dimension `n-1`; these prove its native
smooth relative dimension and nonemptiness for every positive `n`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] [CharZero K]

/-- The structure morphism of the original one-plane Plücker scheme. -/
def onePlaneOriginalStructureMap (n : ℕ) :
    Proj (onePlaneOriginalGrading (K := K) n) ⟶ Spec (CommRingCat.of K) :=
  HomogeneousQuotientCharts.structureMap _ _

/-- The normalized original Plücker chart is an actual affine space. -/
def onePlaneOriginalAffineIso {n : ℕ} (p : PluckerIndex 1 n) :
    (Proj.basicOpen (onePlaneOriginalGrading (K := K) n)
      (Ideal.Quotient.mk (matrixPluckerIdeal (K := K)) (X p))).toScheme ≅
      𝔸(PluckerChartVariable p; Spec (CommRingCat.of K)) :=
  HomogeneousQuotientCharts.polynomialChartIso matrixPluckerIdeal
    (matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1)) p
    (pluckerBigCellEquiv (K := K) p)

theorem onePlaneOriginalAffineIso_over {n : ℕ} (p : PluckerIndex 1 n) :
    (onePlaneOriginalAffineIso (K := K) p).hom ≫
      (𝔸(PluckerChartVariable p; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) =
      (Proj.basicOpen (onePlaneOriginalGrading (K := K) n)
        (Ideal.Quotient.mk (matrixPluckerIdeal (K := K)) (X p))).ι ≫
          onePlaneOriginalStructureMap n :=
  HomogeneousQuotientCharts.polynomialChartIso_hom_over matrixPluckerIdeal
    (matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1)) p
    (pluckerBigCellEquiv (K := K) p)

/-- The original one-row normalized charts cover the whole projective scheme. -/
theorem onePlaneOriginal_basicOpen_cover (n : ℕ) :
    (⨆ p : PluckerIndex 1 n,
      Proj.basicOpen (onePlaneOriginalGrading (K := K) n)
        (Ideal.Quotient.mk (matrixPluckerIdeal (K := K)) (X p))) = ⊤ :=
  HomogeneousQuotientProjective.presentation_basicOpen_cover
    (matrixPluckerIdeal (K := K) (s := 1) (n := n))
    (matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1))
    (Ideal.Quotient.mkₐ K _) Ideal.Quotient.mk_surjective
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _)

/-- Smoothness with the expected relative dimension includes the complete
one-plane boundary; it is not restricted to odd-dimensional pencils. -/
theorem onePlaneOriginalStructureMap_smoothOfRelativeDimension (n : ℕ) :
    SmoothOfRelativeDimension (n - 1) (onePlaneOriginalStructureMap (K := K) n) := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @AlgebraicGeometry.SmoothOfRelativeDimension.{0} (n - 1))
    (fun p : PluckerIndex 1 n ↦ Proj.basicOpen (onePlaneOriginalGrading (K := K) n)
      (Ideal.Quotient.mk (matrixPluckerIdeal (K := K)) (X p)))
    (onePlaneOriginal_basicOpen_cover n)
  intro p
  rw [← onePlaneOriginalAffineIso_over]
  have hcard : Nat.card (PluckerChartVariable p) = n - 1 := by
    classical
    have hrange : Fintype.card (Set.range p.val) = 1 := by
      simpa only [Fintype.card_fin] using
        (Fintype.card_congr (Equiv.ofInjective p.val p.property.injective)).symm
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_subtype_compl, Fintype.card_fin, hrange, one_mul]
  letI : SmoothOfRelativeDimension (n - 1)
      (𝔸(PluckerChartVariable p; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) :=
    AffineSpace.smoothOfRelativeDimension_of_card_eq _ hcard
  have h : SmoothOfRelativeDimension (0 + (n - 1))
      ((onePlaneOriginalAffineIso (K := K) p).hom ≫
        (𝔸(PluckerChartVariable p; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))) :=
    inferInstance
  simpa only [Nat.zero_add] using h

/-- The nonempty smooth projective one-plane scheme, for every `1 ≤ n`. -/
theorem onePlaneOriginal_nonempty_smooth (n : ℕ) (hn : 0 < n) :
    Nonempty (Proj (onePlaneOriginalGrading (K := K) n)) ∧
      SmoothOfRelativeDimension (n - 1) (onePlaneOriginalStructureMap (K := K) n) :=
  ⟨onePlaneOriginalProj_nonempty n hn,
    onePlaneOriginalStructureMap_smoothOfRelativeDimension n⟩

/-- The zero-dimensional ambient vector space has no one-dimensional planes. -/
theorem onePlaneOriginalProj_zero_empty :
    IsEmpty (Proj (onePlaneOriginalGrading (K := K) 0)) := by
  constructor
  intro x
  have hx : x ∈ (⨆ p : PluckerIndex 1 0,
      Proj.basicOpen (onePlaneOriginalGrading (K := K) 0)
        (Ideal.Quotient.mk (matrixPluckerIdeal (K := K)) (X p))) := by
    rw [onePlaneOriginal_basicOpen_cover]
    trivial
  obtain ⟨p, _⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact Fin.elim0 (p.val 0)

end PaperVerification.AlternatingForms
