module

public import paper_verification.coefficient_grading3
import all paper_verification.coefficient_grading3
public import paper_verification.literal005
import all paper_verification.literal005
public import paper_verification.literal004
import all paper_verification.literal004
public import paper_verification.literal001
import all paper_verification.literal001
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Isomorphisms
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.WeightedReesCoordinateGrading -/


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
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.WeightedReesCoordinateGrading"

section ComponentSource_1
/- Original module: PaperVerification.GradedAlgebraQuotient -/


/-!
# The actual quotient algebra by a homogeneous ideal

The homogeneous pieces are the images of the original pieces under the
literal ideal quotient map. This construction allows a general graded
coefficient algebra, including the weighted Rees image with a degree-zero
parameter.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace PaperVerification.GradedAlgebraQuotient

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

theorem quotientMap_ker (Q : Ideal A) :
    (Ideal.Quotient.mkₐ K Q).toLinearMap.ker = Q.restrictScalars K := by
  ext a
  exact Ideal.Quotient.eq_zero_iff_mem

def quotientToRingEquiv (Q : Ideal A) : (A ⧸ Q.restrictScalars K) ≃ₗ[K] (A ⧸ Q) :=
  (Submodule.quotEquivOfEq _ _ (quotientMap_ker Q).symm).trans
    ((Ideal.Quotient.mkₐ K Q).toLinearMap.quotKerEquivOfSurjective
      (Ideal.Quotient.mkₐ_surjective K Q))

@[simp] theorem quotientToRingEquiv_mk (Q : Ideal A) (a : A) :
    quotientToRingEquiv (K := K) Q (Submodule.Quotient.mk a) = Ideal.Quotient.mk Q a := by
  simp only [quotientToRingEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

def grading (G : TauCeti.InternalGrading K A ℕ) (Q : Ideal A)
    (hQ : DirectSum.SetLike.IsHomogeneous G.piece Q) :
    TauCeti.InternalGrading K (A ⧸ Q) ℕ :=
  (G.quotient (Q.restrictScalars K) hQ).map (quotientToRingEquiv Q)

theorem grading_piece (G : TauCeti.InternalGrading K A ℕ) (Q : Ideal A)
    (hQ : DirectSum.SetLike.IsHomogeneous G.piece Q) (d : ℕ) :
    (grading G Q hQ).piece d = (G.piece d).map (Ideal.Quotient.mkₐ K Q).toLinearMap := by
  simp only [grading, TauCeti.InternalGrading.map_piece,
    TauCeti.InternalGrading.quotient_piece, LinearMap.restrictScalars_self,
    ← Submodule.map_comp]
  have he : (quotientToRingEquiv (K := K) Q).toLinearMap.comp
      (Q.restrictScalars K).mkQ = (Ideal.Quotient.mkₐ K Q).toLinearMap := by
    apply LinearMap.ext
    intro a
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Submodule.mkQ_apply,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk] using quotientToRingEquiv_mk (K := K) Q a
  rw [he]

theorem mk_mem (G : TauCeti.InternalGrading K A ℕ) (Q : Ideal A)
    (hQ : DirectSum.SetLike.IsHomogeneous G.piece Q) {d : ℕ} {a : A}
    (ha : a ∈ G.piece d) : Ideal.Quotient.mk Q a ∈ (grading G Q hQ).piece d := by
  rw [grading_piece]
  exact ⟨a, ha, rfl⟩

theorem quotientMap_homogeneous (G : TauCeti.InternalGrading K A ℕ) (Q : Ideal A)
    (hQ : DirectSum.SetLike.IsHomogeneous G.piece Q) :
    TauCeti.LinearMap.IsHomogeneous (Ideal.Quotient.mkₐ K Q).toLinearMap
      G.piece (grading G Q hQ).piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro d a ha
  simpa only [add_zero, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk] using mk_mem G Q hQ ha

instance gradedMonoid (G : TauCeti.InternalGrading K A ℕ)
    [SetLike.GradedMonoid G.piece] (Q : Ideal A)
    (hQ : DirectSum.SetLike.IsHomogeneous G.piece Q) :
    SetLike.GradedMonoid (grading G Q hQ).piece where
  one_mem := by
    simpa only [map_one] using mk_mem G Q hQ
      (SetLike.GradedOne.one_mem : (1 : A) ∈ G.piece 0)
  mul_mem := by
    intro a b x y hx hy
    rw [grading_piece] at hx hy ⊢
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hy
    exact ⟨p * q, SetLike.GradedMul.mul_mem hp hq,
      (Ideal.Quotient.mkₐ K Q).map_mul p q⟩

instance gradedAlgebra (G : TauCeti.InternalGrading K A ℕ)
    [SetLike.GradedMonoid G.piece] (Q : Ideal A)
    (hQ : DirectSum.SetLike.IsHomogeneous G.piece Q) :
    GradedAlgebra (grading G Q hQ).piece :=
  (grading G Q hQ).isInternal.gradedAlgebra

section Equivalence

variable {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- A bijective homogeneous linear map identifies entire homogeneous pieces. -/
theorem homogeneousEquiv_map_piece
    (G : TauCeti.InternalGrading K M ℕ) (H : TauCeti.InternalGrading K N ℕ)
    (e : M ≃ₗ[K] N)
    (he : TauCeti.LinearMap.IsHomogeneous e.toLinearMap G.piece H.piece 0) (d : ℕ) :
    (G.piece d).map e.toLinearMap = H.piece d := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    simpa only [add_zero] using he.map_mem hx
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change e.symm y ∈ G.piece d
    simpa only [add_zero, LinearEquiv.coe_toLinearMap] using he.linearEquiv_symm.map_mem hy

end Equivalence

end PaperVerification.GradedAlgebraQuotient
end
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.GradedAlgebraQuotient"

section ComponentSource_2
/- Original module: PaperVerification.WeightedReesGradedFibers -/


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
end
end
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.WeightedReesGradedFibers"

section ComponentSource_3
/- Original module: PaperVerification.WeightedReesGradedSpecialization -/


/-!
# Graded special-fiber comparison under a proved initial-ideal equality

An equality of the literal initial ideal with a displayed target ideal
preserves the original polynomial grading. This records the precise map
used in both degenerations of the paper.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MvPolynomial

namespace PaperVerification.WeightedInitialFiber

variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K
attribute [local instance] MvPolynomial.gradedAlgebra

theorem quotientEquivAlgOfEq_coordinate_piece {Q J : Ideal P} (h : Q = J) (d : ℕ) :
    (HomogeneousIdealPieces.piece Q d).map
      (Ideal.quotientEquivAlgOfEq K h).toLinearEquiv.toLinearMap =
        HomogeneousIdealPieces.piece J d := by
  apply le_antisymm
  · rintro a ⟨x, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨p, hp, ?_⟩
    exact (Ideal.quotientEquivAlgOfEq_mk K h p).symm
  · rintro a ⟨p, hp, rfl⟩
    refine ⟨Ideal.Quotient.mk Q p, ⟨p, hp, rfl⟩, ?_⟩
    exact Ideal.quotientEquivAlgOfEq_mk K h p

def specialFiberEquivOfInitial (Q : Ideal P) (w : σ → ℕ) (J : Ideal P)
    (h : initialIdeal Q w = J) : ZeroFiber Q w ≃ₐ[K] (P ⧸ J) :=
  (initialQuotientEquiv Q w).symm.trans (Ideal.quotientEquivAlgOfEq K h)

theorem initialQuotientEquiv_symm_coordinate_piece (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) (d : ℕ) :
    ((zeroFiberCoordinateGrading Q hQ w).piece d).map
      (initialQuotientEquiv Q w).symm.toLinearEquiv.toLinearMap =
        HomogeneousIdealPieces.piece (initialIdeal Q w) d := by
  have h := GradedAlgebraQuotient.homogeneousEquiv_map_piece
    (zeroFiberCoordinateGrading Q hQ w)
    (HomogeneousIdealPieces.grading (initialIdeal Q w)
      (initialIdeal_coordinate_homogeneous Q hQ w))
    (initialQuotientEquiv Q w).toLinearEquiv.symm
    (initialQuotientEquiv_coordinate_homogeneous Q hQ w).linearEquiv_symm d
  simpa only [HomogeneousIdealPieces.grading_piece, AlgEquiv.toLinearEquiv_symm] using h

/-- The given special-fiber map identifies whole ordinary-coordinate pieces. -/
theorem specialFiberEquivOfInitial_coordinate_piece (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) (J : Ideal P)
    (h : initialIdeal Q w = J) (d : ℕ) :
    ((zeroFiberCoordinateGrading Q hQ w).piece d).map
      (specialFiberEquivOfInitial Q w J h).toLinearEquiv.toLinearMap =
        HomogeneousIdealPieces.piece J d := by
  change ((zeroFiberCoordinateGrading Q hQ w).piece d).map
    ((Ideal.quotientEquivAlgOfEq K h).toLinearEquiv.toLinearMap.comp
      (initialQuotientEquiv Q w).symm.toLinearEquiv.toLinearMap) = _
  rw [Submodule.map_comp, initialQuotientEquiv_symm_coordinate_piece,
    quotientEquivAlgOfEq_coordinate_piece]

end PaperVerification.WeightedInitialFiber
end
end
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.WeightedReesGradedSpecialization"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`PaperVerification.WeightedInitialFiber.reesCoordinateGrading, "definition"),
    (`PaperVerification.WeightedInitialFiber.mem_reesCoordinateGrading_iff, "theorem"),
    (`PaperVerification.WeightedInitialFiber.reesParameterPiece, "definition"),
    (`PaperVerification.WeightedInitialFiber.reesParameterInternalGrading, "definition"),
    (`PaperVerification.WeightedInitialFiber.reesParameter_coordinate_degree_zero, "theorem"),
    (`PaperVerification.WeightedInitialFiber.reesCoordinateGenerator_degree_one, "theorem"),
    (`PaperVerification.WeightedInitialFiber.reesPolynomial_smul_coordinate_mem, "theorem"),
    (`PaperVerification.WeightedInitialFiber.zeroFiberCoordinateGrading, "definition"),
    (`PaperVerification.WeightedInitialFiber.zeroFiberCoordinateGrading_piece, "theorem"),
    (`PaperVerification.WeightedInitialFiber.parameterFiberCoordinateGrading, "definition"),
    (`PaperVerification.WeightedInitialFiber.parameterFiberCoordinateGrading_piece, "theorem"),
    (`PaperVerification.WeightedInitialFiber.initialIdeal_coordinate_homogeneous, "theorem"),
    (`PaperVerification.WeightedInitialFiber.initialQuotientEquiv_coordinate_piece, "theorem"),
    (`PaperVerification.WeightedInitialFiber.nonzeroFiberEquiv_coordinate_piece, "theorem"),
    (`PaperVerification.WeightedInitialFiber.specialFiberEquivOfInitial_coordinate_piece, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "658a0423bee272578c56ca047cb4a473"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:658a0423bee272578c56ca047cb4a473"
