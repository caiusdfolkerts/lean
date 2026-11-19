module

public import PaperVerification.PolynomialCoefficientGrading
public import PaperVerification.HomogeneousQuotientProjective
public import PaperVerification.WeightedInitialGeneralFiber

/-!
# Ordinary coordinate grading on the literal weighted Rees image

The ambient ring is the actual polynomial extension `(K[x]/Q)[t]` and the
family is the existing range of the substitution `xᵢ ↦ t^(wᵢ) xᵢ`.
Ordinary coordinate degree is taken coefficientwise; the parameter has
degree zero. Homogeneity of the original ideal is the only extra input
needed for this grading, and is discharged for the paper's ideals.
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

def ordinaryPolynomialGrading : TauCeti.InternalGrading K P ℕ :=
  .ofDecomposition (MvPolynomial.homogeneousSubmodule σ K)

@[simp] theorem ordinaryPolynomialGrading_piece (d : ℕ) :
    (ordinaryPolynomialGrading (K := K) (σ := σ)).piece d = homogeneousSubmodule σ K d := by
  simp only [ordinaryPolynomialGrading, TauCeti.InternalGrading.ofDecomposition_piece]

instance ordinaryPolynomialGradedMonoid :
    SetLike.GradedMonoid (ordinaryPolynomialGrading (K := K) (σ := σ)).piece := by
  dsimp only [ordinaryPolynomialGrading]
  rw [TauCeti.InternalGrading.ofDecomposition_piece]
  infer_instance

/-- Selecting a weight component does not change ordinary coordinate degree. -/
theorem weightedComponent_isHomogeneous (w : σ → ℕ) {p : P} {d : ℕ}
    (hp : p.IsHomogeneous d) (j : ℕ) :
    (weightedHomogeneousComponent w j p).IsHomogeneous d := by
  classical
  intro a ha
  apply hp
  intro hz
  apply ha
  simp only [coeff_weightedHomogeneousComponent, hz, ite_self]

theorem coefficientLift_isHomogeneous (w : σ → ℕ) {g : Polynomial P} {d : ℕ}
    (hg : ∀ j, (g.coeff j).IsHomogeneous d) (l : ℕ) :
    (coefficientLift w g l).IsHomogeneous d := by
  unfold coefficientLift
  exact (homogeneousSubmodule σ K d).sum_mem fun j _ ↦
    weightedComponent_isHomogeneous w (hg j) (l - j)

/-- The existing Rees substitution preserves the actual ordinary coefficient degree. -/
theorem reesMap_coordinate_homogeneous (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) :
    TauCeti.LinearMap.IsHomogeneous (reesMap Q w).toLinearMap
      (PolynomialCoefficientGrading.grading (ordinaryPolynomialGrading (K := K) (σ := σ))).piece
      (PolynomialCoefficientGrading.grading (HomogeneousIdealPieces.grading Q hQ)).piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro d g hg l
  rw [AlgHom.toLinearMap_apply, add_zero, reesMap_coeff, HomogeneousIdealPieces.grading_piece]
  have hg' : ∀ j, (g.coeff j).IsHomogeneous d := by
    intro j
    have h : g.coeff j ∈ (ordinaryPolynomialGrading (K := K) (σ := σ)).piece d := hg j
    rw [ordinaryPolynomialGrading_piece] at h
    exact h
  exact ⟨coefficientLift w g l, coefficientLift_isHomogeneous w hg' l, rfl⟩

theorem reesAlgebra_coordinate_homogeneous (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) :
    DirectSum.SetLike.IsHomogeneous
      (PolynomialCoefficientGrading.grading (HomogeneousIdealPieces.grading Q hQ)).piece
      (reesAlgebra Q w).toSubmodule := by
  exact (reesMap_coordinate_homogeneous Q hQ w).isHomogeneous_range

/-- Genuine internal grading on the literal Rees image, inherited from its coefficients. -/
def reesCoordinateGrading (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) :
    TauCeti.InternalGrading K (reesAlgebra Q w) ℕ :=
  (PolynomialCoefficientGrading.grading (HomogeneousIdealPieces.grading Q hQ)).submodule
    (reesAlgebra Q w).toSubmodule (reesAlgebra_coordinate_homogeneous Q hQ w)

/-- Degree means ordinary degree of every original quotient coefficient. -/
theorem mem_reesCoordinateGrading_iff (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ)
    (d : ℕ) (a : reesAlgebra Q w) :
    a ∈ (reesCoordinateGrading Q hQ w).piece d ↔
      ∀ j, a.val.coeff j ∈ HomogeneousIdealPieces.piece Q d := by
  change (∀ j, a.val.coeff j ∈ (HomogeneousIdealPieces.grading Q hQ).piece d) ↔ _
  simp only [HomogeneousIdealPieces.grading_piece]

instance reesCoordinateGradedMonoid (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) :
    SetLike.GradedMonoid (reesCoordinateGrading Q hQ w).piece where
  one_mem := by
    rw [mem_reesCoordinateGrading_iff]
    intro j
    change (1 : Polynomial (P ⧸ Q)).coeff j ∈ HomogeneousIdealPieces.piece Q 0
    by_cases hj : j = 0
    · subst j
      rw [Polynomial.coeff_one_zero]
      exact ⟨1, isHomogeneous_one σ K, (Ideal.Quotient.mkₐ K Q).map_one⟩
    · rw [Polynomial.coeff_one, if_neg hj]
      exact (HomogeneousIdealPieces.piece Q 0).zero_mem
  mul_mem := by
    intro a b x y hx hy
    rw [mem_reesCoordinateGrading_iff] at hx hy ⊢
    intro j
    change (x.val * y.val).coeff j ∈ HomogeneousIdealPieces.piece Q (a + b)
    rw [Polynomial.coeff_mul]
    exact (HomogeneousIdealPieces.piece Q (a + b)).sum_mem fun uv _ ↦
      AlternatingForms.homogeneousQuotient_mul_mem Q a b _ _ (hx uv.1) (hy uv.2)

instance reesCoordinateGradedAlgebra (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) :
    GradedAlgebra (reesCoordinateGrading Q hQ w).piece :=
  (reesCoordinateGrading Q hQ w).isInternal.gradedAlgebra

theorem reesCover_coordinate_homogeneous (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) :
    TauCeti.LinearMap.IsHomogeneous (reesCover Q w).toLinearMap
      (PolynomialCoefficientGrading.grading (ordinaryPolynomialGrading (K := K) (σ := σ))).piece
      (reesCoordinateGrading Q hQ w).piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro d g hg
  exact (reesMap_coordinate_homogeneous Q hQ w).map_mem hg

theorem reesParameter_coordinate_degree_zero (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) :
    reesParameter Q w ∈ (reesCoordinateGrading Q hQ w).piece 0 := by
  exact (reesCover_coordinate_homogeneous Q hQ w).map_mem
    (PolynomialCoefficientGrading.X_mem_zero (ordinaryPolynomialGrading (K := K) (σ := σ)))

/-- Every original Plücker coordinate, with its specified Rees weight,
still has ordinary coordinate degree one. -/
theorem reesCoordinateGenerator_degree_one (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) (i : σ) :
    reesCover Q w (Polynomial.C (MvPolynomial.X i)) ∈
      (reesCoordinateGrading Q hQ w).piece 1 := by
  have hx : MvPolynomial.X i ∈ (ordinaryPolynomialGrading (K := K) (σ := σ)).piece 1 := by
    rw [ordinaryPolynomialGrading_piece]
    exact isHomogeneous_X K i
  simpa only [add_zero, AlgHom.toLinearMap_apply] using
    (reesCover_coordinate_homogeneous Q hQ w).map_mem
      (PolynomialCoefficientGrading.C_mem (ordinaryPolynomialGrading (K := K) (σ := σ)) hx)

theorem reesParameterMap_coordinate_degree_zero (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ)
    (f : Polynomial K) :
    reesParameterMap Q w f ∈ (reesCoordinateGrading Q hQ w).piece 0 := by
  rw [mem_reesCoordinateGrading_iff]
  intro j
  rw [reesParameterMap_val, Polynomial.coeff_map]
  refine ⟨MvPolynomial.C (f.coeff j), isHomogeneous_C σ _, ?_⟩
  exact (Ideal.Quotient.mkₐ K Q).commutes _

/-- The original `K[t]` scalar action preserves every ordinary-coordinate piece. -/
theorem reesPolynomial_smul_coordinate_mem (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ)
    (f : Polynomial K) {d : ℕ} {a : reesAlgebra Q w}
    (ha : a ∈ (reesCoordinateGrading Q hQ w).piece d) :
    f • a ∈ (reesCoordinateGrading Q hQ w).piece d := by
  change reesParameterMap Q w f * a ∈ _
  simpa only [zero_add] using SetLike.GradedMul.mul_mem
    (reesParameterMap_coordinate_degree_zero Q hQ w f) ha

/-- The same actual pieces as modules over the original parameter ring `K[t]`. -/
def reesParameterPiece (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) (d : ℕ) :
    Submodule (Polynomial K) (reesAlgebra Q w) where
  carrier := (reesCoordinateGrading Q hQ w).piece d
  zero_mem' := ((reesCoordinateGrading Q hQ w).piece d).zero_mem
  add_mem' := ((reesCoordinateGrading Q hQ w).piece d).add_mem
  smul_mem' := fun f _ ha ↦ reesPolynomial_smul_coordinate_mem Q hQ w f ha

@[simp] theorem mem_reesParameterPiece (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ)
    (d : ℕ) (a : reesAlgebra Q w) :
    a ∈ reesParameterPiece Q hQ w d ↔ a ∈ (reesCoordinateGrading Q hQ w).piece d := Iff.rfl

/-- The direct sum is genuine also as a module over the polynomial parameter ring. -/
def reesParameterInternalGrading (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) :
    TauCeti.InternalGrading (Polynomial K) (reesAlgebra Q w) ℕ where
  piece := reesParameterPiece Q hQ w
  isInternal := (reesCoordinateGrading Q hQ w).isInternal

instance reesParameterGradedMonoid (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) :
    SetLike.GradedMonoid (reesParameterPiece Q hQ w) where
  one_mem := (SetLike.GradedOne.one_mem : (1 : reesAlgebra Q w) ∈
    (reesCoordinateGrading Q hQ w).piece 0)
  mul_mem := by
    intro a b x y hx hy
    change x * y ∈ (reesCoordinateGrading Q hQ w).piece (a + b)
    exact SetLike.GradedMul.mul_mem hx hy

/-- The literal flat family is an ordinary-coordinate graded `K[t]`-algebra. -/
instance reesParameterGradedAlgebra (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) :
    GradedAlgebra (reesParameterPiece Q hQ w) := by
  have h : DirectSum.IsInternal (reesParameterPiece Q hQ w) :=
    (reesParameterInternalGrading Q hQ w).isInternal
  exact h.gradedAlgebra

end PaperVerification.WeightedInitialFiber
