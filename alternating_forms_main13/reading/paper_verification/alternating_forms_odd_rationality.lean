module

public import PaperVerification.AlternatingFormsOddAffineChart
public import PaperVerification.AlternatingFormsProjRationality
public import PaperVerification.AlternatingFormsProjOver
public import PaperVerification.HomogeneousQuotientAffineChartOver
public import PaperVerification.AlternatingFormsOddPrime

/-!
# Rationality of the actual odd common-isotropic schemes

The displayed basic open of the genuine Proj is isomorphic over `Spec K`
to affine space.  The coordinate-ring primality theorem proves that this
nonempty open is dense.  The conclusion is Mathlib's
`Scheme.IsRationalOver`, with the canonical ground-field structure map.
The one-plane boundary is handled by its ordinary Plucker big cell.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [CharZero K]

def oddIsotropicBigCellPolynomialIso (k t : ℕ) (h : t+1 ≤ k) :
    (Proj.basicOpen (isotropicProjectiveGrading (t := t) (oddPluckerForms (K := K) k))
      (Ideal.Quotient.mk (isotropicPluckerIdeal (oddPluckerForms k))
        (X (oddAffinePivot k (t+1) h)))).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial (OddAffineFreeVariable k (t+1) h) K)) :=
  isotropicProjBasicOpenIso (oddAffinePivot k (t+1) h) (oddPluckerForms k) ≪≫
    Scheme.Spec.mapIso (oddAffineChartEquiv k t h).symm.toRingEquiv.toCommRingCatIso.op

/-- The actual common-isotropic open chart is affine space over the
original coefficient field, through explicitly constructed polynomials. -/
def oddIsotropicBigCellAffineIso (k t : ℕ) (h : t+1 ≤ k) :
    (Proj.basicOpen (isotropicProjectiveGrading (t := t) (oddPluckerForms (K := K) k))
      (Ideal.Quotient.mk (isotropicPluckerIdeal (oddPluckerForms k))
        (X (oddAffinePivot k (t+1) h)))).toScheme ≅
      𝔸(OddAffineFreeVariable k (t+1) h; Spec (CommRingCat.of K)) :=
  oddIsotropicBigCellPolynomialIso k t h ≪≫
    (AffineSpace.SpecIso (OddAffineFreeVariable k (t+1) h) (CommRingCat.of K)).symm

theorem oddIsotropicBigCellAffineIso_over (k t : ℕ) (h : t+1 ≤ k) :
    (oddIsotropicBigCellAffineIso (K := K) k t h).hom ≫
      (𝔸(OddAffineFreeVariable k (t+1) h; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) =
      (Proj.basicOpen (isotropicProjectiveGrading (t := t) (oddPluckerForms (K := K) k))
        (Ideal.Quotient.mk (isotropicPluckerIdeal (oddPluckerForms k))
          (X (oddAffinePivot k (t+1) h)))).ι ≫ isotropicStructureMap (oddPluckerForms k) := by
  simp only [oddIsotropicBigCellAffineIso, oddIsotropicBigCellPolynomialIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, AffineSpace.SpecIso_inv_over]
  exact (congrArg (fun f ↦
      (isotropicProjBasicOpenIso (oddAffinePivot k (t+1) h) (oddPluckerForms k)).hom ≫ f)
      (specAlgEquiv_hom_over (oddAffineChartEquiv k t h))).trans
    (isotropicProjBasicOpenIso_hom_over (oddAffinePivot k (t+1) h) (oddPluckerForms k))

theorem oddIsotropicBigCell_nonempty (k t : ℕ) (h : t+1 ≤ k) :
    (Proj.basicOpen (isotropicProjectiveGrading (t := t) (oddPluckerForms (K := K) k))
      (Ideal.Quotient.mk (isotropicPluckerIdeal (oddPluckerForms k))
        (X (oddAffinePivot k (t+1) h)))).carrier.Nonempty := by
  let x : Spec (CommRingCat.of (MvPolynomial (OddAffineFreeVariable k (t+1) h) K)) :=
    Classical.arbitrary _
  let y := (oddIsotropicBigCellPolynomialIso (K := K) k t h).inv x
  exact ⟨y.val,y.property⟩

theorem oddIsotropicBigCell_dense (k t : ℕ) (h : t+1 ≤ k) :
    Dense (Proj.basicOpen
      (isotropicProjectiveGrading (t := t) (oddPluckerForms (K := K) k))
      (Ideal.Quotient.mk (isotropicPluckerIdeal (oddPluckerForms k))
        (X (oddAffinePivot k (t+1) h)))).carrier := by
  letI : (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k)).IsPrime :=
    odd_isotropicPluckerIdeal_isPrime k t (by omega)
  exact projective_basicOpen_dense_of_nonempty _ _ (oddIsotropicBigCell_nonempty k t h)

/-- The rationality clause of Theorem 4.1 in every odd ambient dimension
and every common-isotropic plane dimension at least two in its full range. -/
theorem paper_theorem_4_1_rationality_at_least_two (k t : ℕ) (h : t+1 ≤ k) :
    Scheme.IsRationalOver
      (isotropicStructureMap (t := t) (oddPluckerForms (K := K) k)) :=
  scheme_isRationalOver_of_dense_affine_chart _ _
    (oddIsotropicBigCell_dense k t h) (OddAffineFreeVariable k (t+1) h)
    (oddIsotropicBigCellAffineIso k t h) (oddIsotropicBigCellAffineIso_over k t h)

/-- Classical rationality with an explicitly finite affine-space witness.
Mathlib's `IsRationalOver` alone does not require its index to be finite. -/
theorem paper_theorem_4_1_finite_rationality_at_least_two
    (k t : ℕ) (h : t+1 ≤ k) :
    ∃ N : Type, Finite N ∧ Scheme.BirationalOver
      (isotropicStructureMap (t := t) (oddPluckerForms (K := K) k))
      (𝔸(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
  refine ⟨OddAffineFreeVariable k (t+1) h, inferInstance, ?_⟩
  exact scheme_birationalOver_affine_of_dense_chart _ _
    (oddIsotropicBigCell_dense k t h) (OddAffineFreeVariable k (t+1) h)
    (oddIsotropicBigCellAffineIso k t h) (oddIsotropicBigCellAffineIso_over k t h)

/-- The same canonical structure map for the one-plane boundary. -/
def onePlaneStructureMap (k : ℕ) :
    Proj (HomogeneousQuotientProjective.grading
      (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
      (matrixPluckerIdeal_isHomogeneous (by decide : 0<1))) ⟶ Spec (CommRingCat.of K) :=
  HomogeneousQuotientCharts.structureMap _ _

def onePlaneAffineIso (k : ℕ) (p : PluckerIndex 1 (2*k+1)) :
    (Proj.basicOpen
      (HomogeneousQuotientProjective.grading (matrixPluckerIdeal (K := K))
        (matrixPluckerIdeal_isHomogeneous (by decide : 0<1)))
      (Ideal.Quotient.mk matrixPluckerIdeal (X p))).toScheme ≅
      𝔸(PluckerChartVariable p; Spec (CommRingCat.of K)) :=
  HomogeneousQuotientCharts.polynomialChartIso
    matrixPluckerIdeal (matrixPluckerIdeal_isHomogeneous (by decide : 0<1)) p
    (pluckerBigCellEquiv (K := K) p)

theorem onePlaneAffineIso_over (k : ℕ) (p : PluckerIndex 1 (2*k+1)) :
    (onePlaneAffineIso (K := K) k p).hom ≫
      (𝔸(PluckerChartVariable p; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) =
      (Proj.basicOpen
        (HomogeneousQuotientProjective.grading (matrixPluckerIdeal (K := K))
          (matrixPluckerIdeal_isHomogeneous (by decide : 0<1)))
        (Ideal.Quotient.mk matrixPluckerIdeal (X p))).ι ≫ onePlaneStructureMap k :=
  HomogeneousQuotientCharts.polynomialChartIso_hom_over
    matrixPluckerIdeal (matrixPluckerIdeal_isHomogeneous (by decide : 0<1)) p
    (pluckerBigCellEquiv (K := K) p)

/-- The one-plane case, including ambient dimension one, completes the
boundary of the rationality clause. -/
theorem paper_theorem_4_1_finite_rationality_one_plane (k : ℕ) :
    ∃ N : Type, Finite N ∧ Scheme.BirationalOver
      (onePlaneStructureMap (K := K) k)
      (𝔸(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
  let p := onePlaneIndex (0 : Fin (2*k+1))
  let U := Proj.basicOpen
    (HomogeneousQuotientProjective.grading (matrixPluckerIdeal (K := K))
      (matrixPluckerIdeal_isHomogeneous (by decide : 0<1)))
    (Ideal.Quotient.mk matrixPluckerIdeal (X p))
  letI : (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1)).IsPrime :=
    onePlane_ideal_isPrime _
  have hU : U.carrier.Nonempty := by
    let x : Spec (CommRingCat.of (MvPolynomial (PluckerChartVariable p) K)) :=
      Classical.arbitrary _
    let a := (AffineSpace.SpecIso (PluckerChartVariable p) (CommRingCat.of K)).inv x
    let y := (onePlaneAffineIso (K := K) k p).inv a
    exact ⟨y.val,y.property⟩
  refine ⟨PluckerChartVariable p, inferInstance, ?_⟩
  exact scheme_birationalOver_affine_of_dense_chart _ U
    (projective_basicOpen_dense_of_nonempty _ _ hU) (PluckerChartVariable p)
    (onePlaneAffineIso k p) (onePlaneAffineIso_over k p)

/-- The standard library rationality class follows from the stronger
finite-dimensional statement. -/
theorem paper_theorem_4_1_rationality_one_plane (k : ℕ) :
    Scheme.IsRationalOver (onePlaneStructureMap (K := K) k) := by
  obtain ⟨N, _, hN⟩ := paper_theorem_4_1_finite_rationality_one_plane (K := K) k
  exact ⟨N, hN⟩

end PaperVerification.AlternatingForms
