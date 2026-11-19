module
public import graph_foundation.part012
public import shared_results.part024

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.IdealTransferredGrading -/
section

/-!
# Homological grading of the actual transferred polynomial resolution

Exterior removal has degree minus one. Scalar extension carries the actual
contraction identities to the free polynomial module, and its negative
homotopy has the same homological degrees. The transferred differential,
its actual augmentation, and the basis degree projections are compared here.
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial DirectSum
open HomologicalPerturbation PolynomialModuleResolution
open scoped TensorProduct

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]
  (P : QuotientGroebnerData V k)
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
  (hfree : ∀ q p, Module.Free k (actualIdealOrdinaryHomology P hJ q p))

local notation "S" => MvPolynomial V k
local notation "C" => actualIdealTensorContraction P hJ hfree

theorem ideal_removeExterior_basis (v : V) (a : IdealTensorIndex P) :
    removeExterior P.ideal v (idealTensorBasis P a) =
      if v ∈ a.2 then TauCeti.ExteriorAlgebra.basisEraseSign v a.2 •
        idealTensorBasis P (a.1,a.2.erase v) else 0 := by
  simp only [removeExterior, idealTensorBasis, Module.Basis.tensorProduct_apply',
    TensorProduct.map_tmul, LinearMap.id_apply, Simplicial.contraction_basis]
  split_ifs <;> simp only [TensorProduct.tmul_smul, TensorProduct.tmul_zero]

theorem ideal_removeExterior_homogeneous (v : V) (a : IdealTensorIndex P) :
    removeExterior P.ideal v (idealTensorBasis P a) ∈
      Grading.Piece (idealTensorBasis P) (fun a => a.2.card) (a.2.card-1) := by
  rw [ideal_removeExterior_basis]
  by_cases hv : v ∈ a.2
  · rw [if_pos hv]
    have hb : idealTensorBasis P (a.1,a.2.erase v) ∈
        Grading.Piece (idealTensorBasis P) (fun a => a.2.card) (a.2.card-1) := by
      simpa only [Finset.card_erase_of_mem hv] using
        Grading.basis_mem_piece (idealTensorBasis P) (fun a => a.2.card) (a.1,a.2.erase v)
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul k]
    exact (Grading.Piece (idealTensorBasis P) (fun a => a.2.card) (a.2.card-1)).smul_mem _ hb
  · rw [if_neg hv]
    exact Submodule.zero_mem _

theorem ideal_removeExterior_zero (v : V) (a : IdealTensorIndex P) (ha : a.2.card=0) :
    removeExterior P.ideal v (idealTensorBasis P a) = 0 := by
  rw [ideal_removeExterior_basis, Finset.card_eq_zero.mp ha]
  simp only [Finset.notMem_empty, if_false]

set_option backward.isDefEq.respectTransparency true in
theorem ideal_removeExterior_projection (v : V) (p : ℕ) :
    removeExterior P.ideal v * idealTensorHomologicalProjection P (p+1) =
      idealTensorHomologicalProjection P p * removeExterior P.ideal v := by
  apply (idealTensorBasis P).ext
  intro a
  change removeExterior P.ideal v
      (Grading.projection (idealTensorBasis P)
        (fun i : IdealTensorIndex P => i.2.card) (p+1) (idealTensorBasis P a)) =
    Grading.projection (idealTensorBasis P)
      (fun i : IdealTensorIndex P => i.2.card) p
      (removeExterior P.ideal v (idealTensorBasis P a))
  rw [Grading.projection_basis]
  by_cases ha : a.2.card = p+1
  · rw [if_pos ha]
    exact (Grading.projection_eq_self (by
      simpa only [ha, Nat.add_sub_cancel] using
        ideal_removeExterior_homogeneous P v a)).symm
  · rw [if_neg ha, map_zero]
    by_cases h0 : a.2.card = 0
    · rw [ideal_removeExterior_zero P v a h0, map_zero]
    · exact (Grading.projection_eq_zero
        (show p ≠ a.2.card - 1 from by omega)
        (ideal_removeExterior_homogeneous P v a)).symm

theorem ideal_removeExterior_projection_zero (v : V) :
    removeExterior P.ideal v * idealTensorHomologicalProjection P 0 = 0 := by
  apply (idealTensorBasis P).ext
  intro a
  change removeExterior P.ideal v
    (Grading.projection (idealTensorBasis P) (fun a => a.2.card) 0 (idealTensorBasis P a)) = 0
  rw [Grading.projection_basis]
  split_ifs with h
  · exact ideal_removeExterior_zero P v a h
  · exact map_zero _

def idealBarHomologicalProjection (p : ℕ) : Module.End S (Bar (R := k) (V := V) P.ideal) :=
  (idealTensorHomologicalProjection P p).baseChange S

def idealFreeHomologicalProjection (p : ℕ) : Module.End S (S ⊗[k] IdealGradedHomology P hJ) :=
  (idealHomologyProjection P hJ p).baseChange S

theorem ideal_externalDifferential_projection (p : ℕ) :
    externalDifferential P.ideal * idealBarHomologicalProjection P (p+1) =
      idealBarHomologicalProjection P p * externalDifferential P.ideal := by
  rw [externalDifferential, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  change (removeExterior P.ideal v).baseChange S *
      (idealTensorHomologicalProjection P (p+1)).baseChange S =
    (idealTensorHomologicalProjection P p).baseChange S *
      (removeExterior P.ideal v).baseChange S
  rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul,
    ideal_removeExterior_projection]

theorem ideal_externalDifferential_projection_zero :
    externalDifferential P.ideal * idealBarHomologicalProjection P 0 = 0 := by
  rw [externalDifferential, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro v _
  rw [smul_mul_assoc]
  change (X v : S) • ((removeExterior P.ideal v).baseChange S *
    (idealTensorHomologicalProjection P 0).baseChange S) = 0
  rw [← LinearMap.baseChange_mul, ideal_removeExterior_projection_zero,
    LinearMap.baseChange_zero, smul_zero]

set_option backward.isDefEq.respectTransparency true in
abbrev idealExtendedContraction :
    LinearContraction (R := S)
      (M := Bar (R := k) (V := V) P.ideal)
      (H := S ⊗[k] IdealGradedHomology P hJ) :=
  PolynomialPerturbation.extendedContraction (R := k) (V := V)
    (H := IdealGradedHomology P hJ) P.ideal (C)

set_option backward.isDefEq.respectTransparency true in
theorem idealExtended_h_projection (p : ℕ) :
    (idealExtendedContraction P hJ hfree).h * idealBarHomologicalProjection P p =
      idealBarHomologicalProjection P (p+1) * (idealExtendedContraction P hJ hfree).h := by
  change (-((C).h.baseChange S)).comp
    ((idealTensorHomologicalProjection P p).baseChange S) =
    ((idealTensorHomologicalProjection P (p+1)).baseChange S).comp
      (-((C).h.baseChange S))
  rw [LinearMap.neg_comp, LinearMap.comp_neg]
  exact congrArg Neg.neg
    ((LinearMap.baseChange_comp (A := S)
      (f := idealTensorHomologicalProjection P p) (g := (C).h)).symm.trans
      ((congrArg (fun f : Module.End k
          (TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal)) => f.baseChange S)
        (actualIdealTensorContraction_h_projection P hJ hfree p)).trans
        (LinearMap.baseChange_comp (A := S)
          (f := (C).h) (g := idealTensorHomologicalProjection P (p+1)))))

set_option backward.isDefEq.respectTransparency true in
theorem idealExtended_h_projection_zero :
    idealBarHomologicalProjection P 0 * (idealExtendedContraction P hJ hfree).h = 0 := by
  change ((idealTensorHomologicalProjection P 0).baseChange S).comp
    (-((C).h.baseChange S)) = 0
  rw [LinearMap.comp_neg]
  have hz : ((idealTensorHomologicalProjection P 0).baseChange S).comp
      ((C).h.baseChange S) = 0 :=
    (LinearMap.baseChange_comp (A := S)
      (f := (C).h) (g := idealTensorHomologicalProjection P 0)).symm.trans
      ((congrArg (fun f : Module.End k
          (TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal)) => f.baseChange S)
        (actualIdealTensorContraction_h_projection_zero P hJ hfree)).trans
        (LinearMap.baseChange_zero (R := k) (A := S)
          (M := TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal))
          (N := TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal))))
  exact (congrArg Neg.neg hz).trans (by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.neg_apply, LinearMap.zero_apply, neg_zero])

set_option backward.isDefEq.respectTransparency true in
theorem idealExtended_inclusion_projection (p : ℕ) :
    (idealExtendedContraction P hJ hfree).inclusion.comp (idealFreeHomologicalProjection P hJ p) =
      (idealBarHomologicalProjection P p).comp (idealExtendedContraction P hJ hfree).inclusion := by
  change ((C).inclusion.baseChange S).comp ((idealHomologyProjection P hJ p).baseChange S) =
    ((idealTensorHomologicalProjection P p).baseChange S).comp ((C).inclusion.baseChange S)
  exact (LinearMap.baseChange_comp (A := S)
    (f := idealHomologyProjection P hJ p) (g := (C).inclusion)).symm.trans
    ((congrArg (fun f : IdealGradedHomology P hJ →ₗ[k]
        TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal) => f.baseChange S)
      (actualIdealTensorContraction_inclusion_projection P hJ hfree p)).trans
      (LinearMap.baseChange_comp (A := S)
        (f := (C).inclusion) (g := idealTensorHomologicalProjection P p)))

set_option backward.isDefEq.respectTransparency true in
theorem idealExtended_projection_projection (p : ℕ) :
    (idealExtendedContraction P hJ hfree).projection.comp (idealBarHomologicalProjection P p) =
      (idealFreeHomologicalProjection P hJ p).comp (idealExtendedContraction P hJ hfree).projection := by
  change ((C).projection.baseChange S).comp ((idealTensorHomologicalProjection P p).baseChange S) =
    ((idealHomologyProjection P hJ p).baseChange S).comp ((C).projection.baseChange S)
  exact (LinearMap.baseChange_comp (A := S)
    (f := idealTensorHomologicalProjection P p) (g := (C).projection)).symm.trans
    ((congrArg (fun f : TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal) →ₗ[k]
        IdealGradedHomology P hJ => f.baseChange S)
      (actualIdealTensorContraction_projection_projection P hJ hfree p)).trans
      (LinearMap.baseChange_comp (A := S)
        (f := (C).projection) (g := idealHomologyProjection P hJ p)))

abbrev actualIdealCoefficientDegree
    (a : NonstandardIndex P.order P.ideal) : ℕ := a.val.degree

set_option backward.isDefEq.respectTransparency true in
theorem idealTensorBasis_eq_polynomial :
    idealTensorBasis P =
      PolynomialPerturbation.tensorBasis (R := k) (V := V) P.ideal
        (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading) := by
  unfold idealTensorBasis PolynomialPerturbation.tensorBasis
  rfl

theorem idealTensorOrdinaryDegree_eq_polynomial :
    idealTensorOrdinaryDegree P =
      PolynomialPerturbation.internalDegree (V := V) (actualIdealCoefficientDegree P) := by
  funext a
  rfl

set_option backward.isDefEq.respectTransparency true in
/-- The ideal tensor basis and its ordinary degree agree with the generic
polynomial-perturbation presentation. Keep the actual contraction opaque. -/
theorem actualIdealTensorContraction_h_nonincreasing_polynomial :
    DegreeNonincreasing (R := k)
      (M := CoefficientKoszul (R := k) (V := V) P.ideal)
      (PolynomialPerturbation.tensorBasis (R := k) (V := V) P.ideal
        (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading))
      (PolynomialPerturbation.internalDegree (V := V) (actualIdealCoefficientDegree P))
      (C).h := by
  rw [← idealTensorBasis_eq_polynomial P, ← idealTensorOrdinaryDegree_eq_polynomial P]
  exact actualIdealTensorContraction_h_nonincreasing P hJ hfree

set_option backward.isDefEq.respectTransparency true in
abbrev actualIdealFreeModel :
    LinearDeformationRetract (R := S)
      (M := Bar (R := k) (V := V) P.ideal)
      (H := S ⊗[k] IdealGradedHomology P hJ) :=
  PolynomialPerturbation.transferred (R := k) (V := V)
    (H := IdealGradedHomology P hJ) P.ideal C
    (actualIdealTensorContraction_d P hJ hfree)
    (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading)
    (actualIdealCoefficientDegree P)
    (actualIdealTensorContraction_h_nonincreasing_polynomial P hJ hfree)

set_option backward.isDefEq.respectTransparency true in
abbrev actualIdealPerturbationUnit :
    (Module.End S (Bar (R := k) (V := V) P.ideal))ˣ := by
  have hd : DegreeDecreasing (R := S)
      (M := Bar (R := k) (V := V) P.ideal)
      ((idealTensorBasis P).baseChange S) (idealTensorOrdinaryDegree P)
      (externalDifferential (R := k) (V := V) P.ideal) := by
    rw [idealTensorBasis_eq_polynomial P, idealTensorOrdinaryDegree_eq_polynomial P]
    exact PolynomialPerturbation.externalDifferential_decreases (R := k) (V := V) P.ideal
      (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading)
      (actualIdealCoefficientDegree P)
  refine (idealExtendedContraction P hJ hfree).leftPerturbationUnit
    (R := S) (M := Bar (R := k) (V := V) P.ideal)
    (H := S ⊗[k] IdealGradedHomology P hJ)
    ((idealTensorBasis P).baseChange S) (idealTensorOrdinaryDegree P)
    (externalDifferential (R := k) (V := V) P.ideal) hd ?_
  change DegreeNonincreasing (R := S)
    (M := Bar (R := k) (V := V) P.ideal)
    ((idealTensorBasis P).baseChange S) (idealTensorOrdinaryDegree P)
    (-((C).h.baseChange S))
  exact (((actualIdealTensorContraction_h_nonincreasing P hJ hfree).baseChange S).neg)

set_option backward.isDefEq.respectTransparency true in
private abbrev actualIdealPolynomialPerturbationUnit :
    (Module.End S (Bar (R := k) (V := V) P.ideal))ˣ :=
  (idealExtendedContraction P hJ hfree).leftPerturbationUnit
    ((PolynomialPerturbation.tensorBasis (R := k) (V := V) P.ideal
      (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading)).baseChange S)
    (PolynomialPerturbation.internalDegree (V := V) (actualIdealCoefficientDegree P))
    (externalDifferential (R := k) (V := V) P.ideal)
    (PolynomialPerturbation.externalDifferential_decreases (R := k) (V := V) P.ideal
      (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading)
      (actualIdealCoefficientDegree P))
    (((actualIdealTensorContraction_h_nonincreasing_polynomial P hJ hfree).baseChange S).neg)

set_option backward.isDefEq.respectTransparency true in
private theorem actualIdealPolynomialPerturbationUnit_eq :
    actualIdealPolynomialPerturbationUnit P hJ hfree =
      actualIdealPerturbationUnit P hJ hfree := by
  apply Units.ext
  calc
    (actualIdealPolynomialPerturbationUnit P hJ hfree :
        Module.End S (Bar (R := k) (V := V) P.ideal)) =
        1 + externalDifferential (R := k) (V := V) P.ideal *
          (idealExtendedContraction P hJ hfree).h := by
      unfold actualIdealPolynomialPerturbationUnit
      exact LinearContraction.leftPerturbationUnit_val
        (R := S) (M := Bar (R := k) (V := V) P.ideal)
        (H := S ⊗[k] IdealGradedHomology P hJ) (I := IdealTensorIndex P)
        (idealExtendedContraction P hJ hfree)
        ((PolynomialPerturbation.tensorBasis (R := k) (V := V) P.ideal
          (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading)).baseChange S)
        (PolynomialPerturbation.internalDegree (V := V) (actualIdealCoefficientDegree P))
        (externalDifferential (R := k) (V := V) P.ideal) _ _
    _ = (actualIdealPerturbationUnit P hJ hfree :
        Module.End S (Bar (R := k) (V := V) P.ideal)) := by
      symm
      unfold actualIdealPerturbationUnit
      exact LinearContraction.leftPerturbationUnit_val
        (R := S) (M := Bar (R := k) (V := V) P.ideal)
        (H := S ⊗[k] IdealGradedHomology P hJ) (I := IdealTensorIndex P)
        (idealExtendedContraction P hJ hfree)
        ((idealTensorBasis P).baseChange S) (idealTensorOrdinaryDegree P)
        (externalDifferential (R := k) (V := V) P.ideal) _ _

set_option backward.isDefEq.respectTransparency true in
private theorem actualIdealFreeModel_targetD_eq :
    (actualIdealFreeModel P hJ hfree).targetD =
      (idealExtendedContraction P hJ hfree).transferredDifferential
        (externalDifferential (R := k) (V := V) P.ideal)
        (actualIdealPerturbationUnit P hJ hfree) := by
  change (idealExtendedContraction P hJ hfree).transferredDifferential
      (externalDifferential (R := k) (V := V) P.ideal)
      (actualIdealPolynomialPerturbationUnit P hJ hfree) = _
  exact congrArg ((idealExtendedContraction P hJ hfree).transferredDifferential
    (externalDifferential (R := k) (V := V) P.ideal))
    (actualIdealPolynomialPerturbationUnit_eq P hJ hfree)

set_option backward.isDefEq.respectTransparency true in
private theorem actualIdealFreeModel_inclusion_eq :
    (actualIdealFreeModel P hJ hfree).inclusion =
      (idealExtendedContraction P hJ hfree).transferredInclusion
        (externalDifferential (R := k) (V := V) P.ideal)
        (actualIdealPerturbationUnit P hJ hfree) := by
  change (idealExtendedContraction P hJ hfree).transferredInclusion
      (externalDifferential (R := k) (V := V) P.ideal)
      (actualIdealPolynomialPerturbationUnit P hJ hfree) = _
  exact congrArg ((idealExtendedContraction P hJ hfree).transferredInclusion
    (externalDifferential (R := k) (V := V) P.ideal))
    (actualIdealPolynomialPerturbationUnit_eq P hJ hfree)

set_option backward.isDefEq.respectTransparency true in
theorem actualIdealFreeModel_d_projection (p : ℕ) :
    (actualIdealFreeModel P hJ hfree).targetD.comp (idealFreeHomologicalProjection P hJ (p+1)) =
      (idealFreeHomologicalProjection P hJ p).comp (actualIdealFreeModel P hJ hfree).targetD := by
  rw [actualIdealFreeModel_targetD_eq]
  exact (idealExtendedContraction P hJ hfree).transferredDifferential_lowers_degree
    (idealBarHomologicalProjection P) (idealFreeHomologicalProjection P hJ)
    (externalDifferential P.ideal) (actualIdealPerturbationUnit P hJ hfree)
    (LinearContraction.leftPerturbationUnit_val ..)
    (idealExtended_h_projection P hJ hfree) (ideal_externalDifferential_projection P)
    (idealExtended_inclusion_projection P hJ hfree)
    (idealExtended_projection_projection P hJ hfree) p

set_option backward.isDefEq.respectTransparency true in
theorem actualIdealFreeModel_d_projection_zero :
    (actualIdealFreeModel P hJ hfree).targetD.comp (idealFreeHomologicalProjection P hJ 0) = 0 := by
  rw [actualIdealFreeModel_targetD_eq]
  exact (idealExtendedContraction P hJ hfree).transferredDifferential_zero_degree
    (idealBarHomologicalProjection P) (idealFreeHomologicalProjection P hJ)
    (externalDifferential P.ideal) (actualIdealPerturbationUnit P hJ hfree)
    (ideal_externalDifferential_projection_zero P)
    (idealExtended_inclusion_projection P hJ hfree)

set_option backward.isDefEq.respectTransparency true in
theorem actualIdealFreeModel_inclusion_projection (p : ℕ) :
    (actualIdealFreeModel P hJ hfree).inclusion.comp (idealFreeHomologicalProjection P hJ p) =
      (idealBarHomologicalProjection P p).comp (actualIdealFreeModel P hJ hfree).inclusion := by
  rw [actualIdealFreeModel_inclusion_eq]
  exact (idealExtendedContraction P hJ hfree).transferredInclusion_preserves_degree
    (idealBarHomologicalProjection P) (idealFreeHomologicalProjection P hJ)
    (externalDifferential P.ideal) (actualIdealPerturbationUnit P hJ hfree)
    (LinearContraction.leftPerturbationUnit_val ..)
    (idealExtended_h_projection P hJ hfree) (idealExtended_h_projection_zero P hJ hfree)
    (ideal_externalDifferential_projection P) (ideal_externalDifferential_projection_zero P)
    (idealExtended_inclusion_projection P hJ hfree) p

section ActualIdealHomologyBasis

-- Prefer the existing literal quotient instances when the summand indices
-- are projections from the chosen basis index. No new structure is introduced.
attribute [local instance 2000] actualIdealOrdinaryHomologyAddCommGroup
  actualIdealOrdinaryHomologyModule
set_option backward.isDefEq.respectTransparency true

/-- Choose bases only after installing the proved freeness of every actual
homology summand. The assumption remains the explicit argument `hfree`. -/
abbrev ActualIdealHomologyBasisIndex :=
  letI : ∀ q p, Module.Free k (actualIdealOrdinaryHomology P hJ q p) := hfree
  GradedFreeIndex (R := k) (fun q p => actualIdealOrdinaryHomology P hJ q p)

def actualIdealHomologyBasis : Module.Basis (ActualIdealHomologyBasisIndex P hJ hfree) k
    (IdealGradedHomology P hJ) := by
  letI : ∀ q p, Module.Free k (actualIdealOrdinaryHomology P hJ q p) := hfree
  exact gradedFreeBasis (R := k) (fun q p => actualIdealOrdinaryHomology P hJ q p)

@[simp] theorem actualIdealHomologyBasis_lof (a : ActualIdealHomologyBasisIndex P hJ hfree) :
    letI : Module.Free k (actualIdealOrdinaryHomology P hJ a.1 a.2.1) := hfree a.1 a.2.1
    actualIdealHomologyBasis P hJ hfree a = idealHomologyLof P hJ a.1 a.2.1
      (Module.Free.chooseBasis k (actualIdealOrdinaryHomology P hJ a.1 a.2.1) a.2.2) := by
  letI : ∀ q p, Module.Free k (actualIdealOrdinaryHomology P hJ q p) := hfree
  rw [actualIdealHomologyBasis, gradedFreeBasis, directSum_basis_apply, directSum_basis_apply]
  rfl

@[simp] theorem idealHomologyProjection_basis (p : ℕ)
    (a : ActualIdealHomologyBasisIndex P hJ hfree) :
    idealHomologyProjection P hJ p (actualIdealHomologyBasis P hJ hfree a) =
      if a.2.1=p then actualIdealHomologyBasis P hJ hfree a else 0 := by
  rw [actualIdealHomologyBasis_lof, idealHomologyProjection_lof]

def actualIdealFreeBasis : Module.Basis (ActualIdealHomologyBasisIndex P hJ hfree) S
    (S ⊗[k] IdealGradedHomology P hJ) := (actualIdealHomologyBasis P hJ hfree).baseChange S

/-- The canonical direct-sum degree is exactly the degree in the actual
polynomial free basis used for the finite chain-resolution packaging. -/
theorem actualIdealFreeBasis_projection (p : ℕ) :
    Grading.projection (actualIdealFreeBasis P hJ hfree) (fun a => a.2.1) p =
      idealFreeHomologicalProjection P hJ p := by
  apply (actualIdealFreeBasis P hJ hfree).ext
  intro a
  rw [Grading.projection_basis]
  simp only [actualIdealFreeBasis, idealFreeHomologicalProjection,
    Module.Basis.baseChange_apply, LinearMap.baseChange_tmul, idealHomologyProjection_basis]
  split_ifs <;> simp only [TensorProduct.tmul_zero]

end ActualIdealHomologyBasis

theorem idealBarHomologicalProjection_basis (p : ℕ) (a : IdealTensorIndex P) :
    idealBarHomologicalProjection P p ((idealTensorBasis P).baseChange S a) =
      if a.2.card=p then (idealTensorBasis P).baseChange S a else 0 := by
  rw [Module.Basis.baseChange_apply]
  change (idealTensorHomologicalProjection P p).baseChange S
    (1 ⊗ₜ[k] idealTensorBasis P a) = _
  rw [LinearMap.baseChange_tmul]
  change (1 : S) ⊗ₜ[k]
    Grading.projection (idealTensorBasis P) (fun a => a.2.card) p (idealTensorBasis P a) = _
  rw [Grading.projection_basis]
  split_ifs <;> simp only [TensorProduct.tmul_zero]

/-- The literal diagonal augmentation is supported in exterior degree zero. -/
theorem idealBarAugmentation_projection_zero :
    (PolynomialModuleResolution.augmentation P.ideal).comp
      (idealBarHomologicalProjection P 0) = PolynomialModuleResolution.augmentation P.ideal := by
  apply ((idealTensorBasis P).baseChange S).ext
  rintro ⟨a,F⟩
  simp only [LinearMap.comp_apply, idealBarHomologicalProjection_basis]
  by_cases h : F.card=0
  · rw [if_pos h]
  · rw [if_neg h, map_zero]
    have hF : F ≠ ∅ := by
      intro he
      apply h
      rw [he, Finset.card_empty]
    rw [Module.Basis.baseChange_apply, idealTensorBasis, Module.Basis.tensorProduct_apply,
      PolynomialModuleResolution.augmentation_tmul_basis, if_neg hF]

set_option backward.isDefEq.respectTransparency true in
abbrev actualIdealFreeAugmentation :
    (S ⊗[k] IdealGradedHomology P hJ) →ₗ[S] P.ideal :=
  PolynomialPerturbation.augmentation (R := k) (V := V)
    (H := IdealGradedHomology P hJ) P.ideal C
    (actualIdealTensorContraction_d P hJ hfree)
    (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading)
    (actualIdealCoefficientDegree P)
    (actualIdealTensorContraction_h_nonincreasing_polynomial P hJ hfree)

set_option backward.isDefEq.respectTransparency true in
/-- The transferred augmentation has the same genuine degree-zero support. -/
theorem actualIdealFreeAugmentation_projection_zero :
    (actualIdealFreeAugmentation P hJ hfree).comp (idealFreeHomologicalProjection P hJ 0) =
      actualIdealFreeAugmentation P hJ hfree := by
  change ((PolynomialModuleResolution.augmentation P.ideal).comp
    (actualIdealFreeModel P hJ hfree).inclusion).comp (idealFreeHomologicalProjection P hJ 0) =
      (PolynomialModuleResolution.augmentation P.ideal).comp
        (actualIdealFreeModel P hJ hfree).inclusion
  rw [LinearMap.comp_assoc, actualIdealFreeModel_inclusion_projection,
    ← LinearMap.comp_assoc, idealBarAugmentation_projection_zero]

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.actualIdealFreeModel_d_projection

#print axioms FourPapers.Sublattice.actualIdealFreeModel_d_projection_zero

#print axioms FourPapers.Sublattice.actualIdealFreeModel_inclusion_projection

#print axioms FourPapers.Sublattice.actualIdealFreeBasis_projection

#print axioms FourPapers.Sublattice.actualIdealFreeAugmentation_projection_zero

end
end
end


end
