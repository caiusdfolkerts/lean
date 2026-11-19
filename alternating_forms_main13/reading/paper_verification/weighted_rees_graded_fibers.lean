module

public import PaperVerification.WeightedReesCoordinateGrading
public import PaperVerification.GradedAlgebraQuotient

/-!
# The actual weighted Rees fiber isomorphisms preserve coordinate degree

Each fiber receives its grading from the image of the ordinary-coordinate
pieces of the literal family. The existing special and nonzero fiber
algebra isomorphisms preserve this grading in both directions. In
particular, the fiber gradings are not defined by transporting an
unrelated grading through those isomorphisms.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MvPolynomial Polynomial

namespace PaperVerification.WeightedInitialFiber

variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K
attribute [local instance] MvPolynomial.gradedAlgebra

theorem reesParameterIdeal_coordinate_homogeneous (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) :
    (Ideal.span ({reesParameter Q w} : Set (reesAlgebra Q w))).IsHomogeneous
      (reesCoordinateGrading Q hQ w).piece := by
  apply Ideal.homogeneous_span
  rintro a rfl
  exact ⟨0, reesParameter_coordinate_degree_zero Q hQ w⟩

def zeroFiberCoordinateGrading (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) :
    TauCeti.InternalGrading K (ZeroFiber Q w) ℕ :=
  GradedAlgebraQuotient.grading (reesCoordinateGrading Q hQ w)
    (Ideal.span {reesParameter Q w}) (reesParameterIdeal_coordinate_homogeneous Q hQ w)

instance zeroFiberCoordinateGradedAlgebra (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) :
    GradedAlgebra (zeroFiberCoordinateGrading Q hQ w).piece :=
  GradedAlgebraQuotient.gradedAlgebra _ _ _

theorem zeroFiberCoordinateGrading_piece (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) (d : ℕ) :
    (zeroFiberCoordinateGrading Q hQ w).piece d =
      ((reesCoordinateGrading Q hQ w).piece d).map (fiberMap Q w).toLinearMap :=
  GradedAlgebraQuotient.grading_piece _ _ _ _

theorem specialMap_coordinate_homogeneous (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) :
    TauCeti.LinearMap.IsHomogeneous (specialMap Q w).toLinearMap
      (ordinaryPolynomialGrading (K := K) (σ := σ)).piece
      (zeroFiberCoordinateGrading Q hQ w).piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro d p hp
  rw [add_zero, zeroFiberCoordinateGrading_piece]
  refine ⟨reesCover Q w (Polynomial.C p), ?_, rfl⟩
  change reesCover Q w (Polynomial.C p) ∈ (reesCoordinateGrading Q hQ w).piece d
  simpa only [add_zero, AlgHom.toLinearMap_apply] using (reesCover_coordinate_homogeneous Q hQ w).map_mem
    (PolynomialCoefficientGrading.C_mem (ordinaryPolynomialGrading (K := K) (σ := σ)) hp)

/-- Homogeneity of the actual initial ideal follows from the graded special-fiber map. -/
theorem initialIdeal_coordinate_homogeneous (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) :
    (initialIdeal Q w).IsHomogeneous (homogeneousSubmodule σ K) := by
  rw [← specialMap_ker Q w]
  have h := (specialMap_coordinate_homogeneous Q hQ w).isHomogeneous_ker
  change DirectSum.SetLike.IsHomogeneous
    (TauCeti.InternalGrading.ofDecomposition (homogeneousSubmodule σ K)).piece
    ((RingHom.ker (specialMap Q w).toRingHom).restrictScalars K) at h
  rwa [TauCeti.InternalGrading.isHomogeneous_ofDecomposition_piece_iff] at h

@[simp] theorem initialQuotientEquiv_mk (Q : Ideal P) (w : σ → ℕ) (p : P) :
    initialQuotientEquiv Q w (Ideal.Quotient.mk (initialIdeal Q w) p) = specialMap Q w p := by
  simp only [initialQuotientEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk (f := specialMap Q w)
    (specialMap_surjective Q w) p

/-- The original special-fiber isomorphism is homogeneous for the original coordinate degrees. -/
theorem initialQuotientEquiv_coordinate_homogeneous (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) :
    TauCeti.LinearMap.IsHomogeneous (initialQuotientEquiv Q w).toLinearEquiv.toLinearMap
      (HomogeneousIdealPieces.grading (initialIdeal Q w)
        (initialIdeal_coordinate_homogeneous Q hQ w)).piece
      (zeroFiberCoordinateGrading Q hQ w).piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro d a ha
  rw [HomogeneousIdealPieces.grading_piece] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  change initialQuotientEquiv Q w (Ideal.Quotient.mk (initialIdeal Q w) p) ∈ _
  rw [initialQuotientEquiv_mk]
  have hp' : p ∈ (ordinaryPolynomialGrading (K := K) (σ := σ)).piece d := by
    rwa [ordinaryPolynomialGrading_piece]
  exact (specialMap_coordinate_homogeneous Q hQ w).map_mem hp'

theorem initialQuotientEquiv_coordinate_piece (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) (d : ℕ) :
    (HomogeneousIdealPieces.piece (initialIdeal Q w) d).map
      (initialQuotientEquiv Q w).toLinearEquiv.toLinearMap =
        (zeroFiberCoordinateGrading Q hQ w).piece d := by
  have hf := initialQuotientEquiv_coordinate_homogeneous Q hQ w
  have hg := hf.linearEquiv_symm
  apply le_antisymm
  · rintro a ⟨p, hp, rfl⟩
    have hp' : p ∈ (HomogeneousIdealPieces.grading (initialIdeal Q w)
        (initialIdeal_coordinate_homogeneous Q hQ w)).piece d := by
      rwa [HomogeneousIdealPieces.grading_piece]
    have h := hf.map_mem hp'
    simpa only [add_zero] using h
  · intro a ha
    refine ⟨(initialQuotientEquiv Q w).symm a, ?_, (initialQuotientEquiv Q w).apply_symm_apply a⟩
    change (initialQuotientEquiv Q w).symm a ∈
      HomogeneousIdealPieces.piece (initialIdeal Q w) d
    have h := hg.map_mem ha
    simpa only [add_zero, HomogeneousIdealPieces.grading_piece, LinearEquiv.coe_toLinearMap,
      AlgEquiv.coe_symm_toLinearEquiv] using h

theorem reesFiberIdeal_coordinate_homogeneous (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) (c : K) :
    (Ideal.span ({reesParameter Q w - algebraMap K (reesAlgebra Q w) c} :
      Set (reesAlgebra Q w))).IsHomogeneous (reesCoordinateGrading Q hQ w).piece := by
  apply Ideal.homogeneous_span
  rintro a rfl
  refine ⟨0, ((reesCoordinateGrading Q hQ w).piece 0).sub_mem
    (reesParameter_coordinate_degree_zero Q hQ w) ?_⟩
  simpa only [Algebra.smul_def, mul_one] using
    ((reesCoordinateGrading Q hQ w).piece 0).smul_mem c
      (SetLike.GradedOne.one_mem : (1 : reesAlgebra Q w) ∈
        (reesCoordinateGrading Q hQ w).piece 0)

def parameterFiberCoordinateGrading (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) (c : K) :
    TauCeti.InternalGrading K (ParameterFiber Q w c) ℕ :=
  GradedAlgebraQuotient.grading (reesCoordinateGrading Q hQ w)
    (Ideal.span {reesParameter Q w - algebraMap K (reesAlgebra Q w) c})
    (reesFiberIdeal_coordinate_homogeneous Q hQ w c)

instance parameterFiberCoordinateGradedAlgebra (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) (c : K) :
    GradedAlgebra (parameterFiberCoordinateGrading Q hQ w c).piece :=
  GradedAlgebraQuotient.gradedAlgebra _ _ _

theorem parameterFiberCoordinateGrading_piece (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) (c : K) (d : ℕ) :
    (parameterFiberCoordinateGrading Q hQ w c).piece d =
      ((reesCoordinateGrading Q hQ w).piece d).map
        (Ideal.Quotient.mkₐ K (Ideal.span
          {reesParameter Q w - algebraMap K (reesAlgebra Q w) c})).toLinearMap :=
  GradedAlgebraQuotient.grading_piece _ _ _ _

theorem scalarEval_coordinate_mem {A : Type*} [CommRing A] [Algebra K A]
    (G : TauCeti.InternalGrading K A ℕ) (c : K) {d : ℕ} {p : Polynomial A}
    (hp : p ∈ (PolynomialCoefficientGrading.grading G).piece d) :
    scalarEval c p ∈ G.piece d := by
  classical
  rw [← Polynomial.sum_monomial_eq p, Polynomial.sum_def, map_sum]
  apply (G.piece d).sum_mem
  intro j _
  rw [scalarEval_monomial]
  exact (G.piece d).smul_mem _ (hp j)

theorem reesEvaluation_coordinate_homogeneous (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) (c : K) :
    TauCeti.LinearMap.IsHomogeneous (reesEvaluation Q w c).toLinearMap
      (reesCoordinateGrading Q hQ w).piece (HomogeneousIdealPieces.grading Q hQ).piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro d a ha
  rw [AlgHom.toLinearMap_apply, add_zero]
  change scalarEval c a.val ∈ (HomogeneousIdealPieces.grading Q hQ).piece d
  have ha' : a.val ∈
      (PolynomialCoefficientGrading.grading (HomogeneousIdealPieces.grading Q hQ)).piece d := by
    intro j
    rw [HomogeneousIdealPieces.grading_piece]
    exact (mem_reesCoordinateGrading_iff Q hQ w d a).mp ha j
  exact scalarEval_coordinate_mem (HomogeneousIdealPieces.grading Q hQ) c ha'

@[simp] theorem nonzeroFiberEquiv_mk (Q : Ideal P) (w : σ → ℕ)
    (c : K) (hc : c ≠ 0) (a : reesAlgebra Q w) :
    nonzeroFiberEquiv Q w c hc (Ideal.Quotient.mk _ a) = reesEvaluation Q w c a := by
  simp only [nonzeroFiberEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk (f := reesEvaluation Q w c)
    (reesEvaluation_surjective Q w c hc) a

/-- Every existing nonzero-fiber algebra isomorphism preserves ordinary degree. -/
theorem nonzeroFiberEquiv_coordinate_homogeneous (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ)
    (c : K) (hc : c ≠ 0) :
    TauCeti.LinearMap.IsHomogeneous (nonzeroFiberEquiv Q w c hc).toLinearEquiv.toLinearMap
      (parameterFiberCoordinateGrading Q hQ w c).piece
      (HomogeneousIdealPieces.grading Q hQ).piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro d a ha
  rw [parameterFiberCoordinateGrading_piece] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  change nonzeroFiberEquiv Q w c hc (Ideal.Quotient.mk _ b) ∈ _
  rw [nonzeroFiberEquiv_mk]
  exact (reesEvaluation_coordinate_homogeneous Q hQ w c).map_mem hb

theorem nonzeroFiberEquiv_coordinate_piece (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ)
    (c : K) (hc : c ≠ 0) (d : ℕ) :
    ((parameterFiberCoordinateGrading Q hQ w c).piece d).map
      (nonzeroFiberEquiv Q w c hc).toLinearEquiv.toLinearMap =
        HomogeneousIdealPieces.piece Q d := by
  have hf := nonzeroFiberEquiv_coordinate_homogeneous Q hQ w c hc
  have hg := hf.linearEquiv_symm
  apply le_antisymm
  · rintro a ⟨p, hp, rfl⟩
    have h := hf.map_mem hp
    simpa only [add_zero, HomogeneousIdealPieces.grading_piece] using h
  · intro a ha
    refine ⟨(nonzeroFiberEquiv Q w c hc).symm a, ?_,
      (nonzeroFiberEquiv Q w c hc).apply_symm_apply a⟩
    have ha' : a ∈ (HomogeneousIdealPieces.grading Q hQ).piece d := by
      rwa [HomogeneousIdealPieces.grading_piece]
    change (nonzeroFiberEquiv Q w c hc).symm a ∈
      (parameterFiberCoordinateGrading Q hQ w c).piece d
    have h := hg.map_mem ha'
    simpa only [add_zero, LinearEquiv.coe_toLinearMap, AlgEquiv.coe_symm_toLinearEquiv] using h

end PaperVerification.WeightedInitialFiber
