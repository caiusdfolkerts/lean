module
public import graph_results.closed_graph_transferred_grading
public import graph_results.grading_foundations

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphInternalGrading -/
section

/-!
# Ordinary internal grading of the actual transferred resolution

The total degree is external polynomial degree plus the original Koszul
ordinary degree. The actual contraction preserves the latter, whereas each
external-variable Koszul term transfers one unit from exterior degree to
polynomial degree. The inverse perturbation operators therefore preserve
total degree, and the resulting polynomial matrix entries have exactly the
difference of the source and target shifts.
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule
attribute [local instance 2000] LinearMap.IsScalarTower.compatibleSMul
attribute [local instance 2000] actualIdealOrdinaryHomologyAddCommGroup
  actualIdealOrdinaryHomologyModule

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial DirectSum
open HomologicalPerturbation PolynomialModuleResolution
open scoped TensorProduct

/-- Basis projections commute using only the additive structure of the bases. -/
theorem internalShiftedProjection_commutes
    {k X Y I J A B : Type*} [CommRing k]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    (b : Module.Basis I k X) (c : Module.Basis J k Y)
    (deg : I → A) (degree : J → B) (shift : A → B)
    (hshift : Function.Injective shift) (f : X →ₗ[k] Y)
    (hf : ∀ i, f (b i) ∈ Grading.Piece c degree (shift (deg i))) (a : A) :
    f.comp (Grading.projection b deg a) =
      (Grading.projection c degree (shift a)).comp f := by
  apply b.ext
  intro i
  simp only [LinearMap.comp_apply, Grading.projection_basis]
  by_cases hi : deg i = a
  · rw [if_pos hi]
    exact (Grading.projection_eq_self (hi ▸ hf i)).symm
  · rw [if_neg hi, map_zero]
    exact (Grading.projection_eq_zero
      (show shift a ≠ shift (deg i) from fun h => hi (hshift h).symm) (hf i)).symm

section OrdinaryPolynomialExtension
variable {k₀ W M₀ H₀ I₀ J₀ : Type*} [CommRing k₀]
  [AddCommGroup M₀] [Module k₀ M₀] [AddCommGroup H₀] [Module k₀ H₀]
  (C₀ : LinearContraction (R := k₀) (M := M₀) (H := H₀))
  (b : Module.Basis I₀ k₀ M₀) (c : Module.Basis J₀ k₀ H₀)
  (degree : I₀ → ℕ) (degree' : J₀ → ℕ)

private theorem internalPolynomialExtended_h
    (hh : ∀ i, C₀.h (b i) ∈ Grading.Piece b degree (degree i))
    (a : (W →₀ ℕ) × I₀) :
    ((C₀.baseChange (MvPolynomial W k₀)).negDifferential).h.restrictScalars k₀
        (polynomialTensorBasis b a) ∈
      Grading.Piece (polynomialTensorBasis b) (polynomialTensorDegree degree)
        (polynomialTensorDegree degree a) := by
  change -((C₀.h.baseChange (MvPolynomial W k₀)).restrictScalars k₀
    (polynomialTensorBasis b a)) ∈ _
  exact Submodule.neg_mem _
    (polynomialTensor_baseChange_piece b b degree degree C₀.h hh a)

private theorem internalPolynomialExtended_inclusion
    (hi : ∀ j, C₀.inclusion (c j) ∈ Grading.Piece b degree (degree' j))
    (a : (W →₀ ℕ) × J₀) :
    ((C₀.baseChange (MvPolynomial W k₀)).negDifferential).inclusion.restrictScalars k₀
        (polynomialTensorBasis c a) ∈
      Grading.Piece (polynomialTensorBasis b) (polynomialTensorDegree degree)
        (polynomialTensorDegree degree' a) :=
  polynomialTensor_baseChange_piece c b degree' degree C₀.inclusion hi a

theorem internalPolynomialExtended_projection
    (hp : ∀ i, C₀.projection (b i) ∈ Grading.Piece c degree' (degree i))
    (a : (W →₀ ℕ) × I₀) :
    ((C₀.baseChange (MvPolynomial W k₀)).negDifferential).projection.restrictScalars k₀
        (polynomialTensorBasis b a) ∈
      Grading.Piece (polynomialTensorBasis c) (polynomialTensorDegree degree')
        (polynomialTensorDegree degree a) :=
  polynomialTensor_baseChange_piece b c degree degree' C₀.projection hp a

private theorem internalPolynomialExtended_inclusion_commutes
    (hi : ∀ j, C₀.inclusion (c j) ∈ Grading.Piece b degree (degree' j)) (q : ℕ) :
    (((C₀.baseChange (MvPolynomial W k₀)).negDifferential).inclusion.restrictScalars k₀).comp
        (Grading.projection (polynomialTensorBasis (V := W) c) (polynomialTensorDegree degree') q) =
      (Grading.projection (polynomialTensorBasis (V := W) b) (polynomialTensorDegree degree) q).comp
        (((C₀.baseChange (MvPolynomial W k₀)).negDifferential).inclusion.restrictScalars k₀) := by
  exact internalShiftedProjection_commutes
    (polynomialTensorBasis (V := W) c) (polynomialTensorBasis (V := W) b)
    (polynomialTensorDegree degree') (polynomialTensorDegree degree) id Function.injective_id
    (((C₀.baseChange (MvPolynomial W k₀)).negDifferential).inclusion.restrictScalars k₀)
    (internalPolynomialExtended_inclusion C₀ b c degree degree' hi) q

theorem internalPolynomialExtended_projection_commutes
    (hp : ∀ i, C₀.projection (b i) ∈ Grading.Piece c degree' (degree i)) (q : ℕ) :
    (((C₀.baseChange (MvPolynomial W k₀)).negDifferential).projection.restrictScalars k₀).comp
        (Grading.projection (polynomialTensorBasis (V := W) b) (polynomialTensorDegree degree) q) =
      (Grading.projection (polynomialTensorBasis (V := W) c) (polynomialTensorDegree degree') q).comp
        (((C₀.baseChange (MvPolynomial W k₀)).negDifferential).projection.restrictScalars k₀) := by
  exact internalShiftedProjection_commutes
    (polynomialTensorBasis (V := W) b) (polynomialTensorBasis (V := W) c)
    (polynomialTensorDegree degree) (polynomialTensorDegree degree') id Function.injective_id
    (((C₀.baseChange (MvPolynomial W k₀)).negDifferential).projection.restrictScalars k₀)
    (internalPolynomialExtended_projection C₀ b c degree degree' hp) q

end OrdinaryPolynomialExtension

section InternalScalarRestriction
variable {K R M H : Type*} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module R M] [Module K M] [IsScalarTower K R M]
  [AddCommGroup H] [Module R H] [Module K H] [IsScalarTower K R H]
  (D : LinearContraction (R := R) (M := M) (H := H))
  (δ : Module.End R M) (u : (Module.End R M)ˣ)

private theorem internalTransferredDifferential_restrictScalars :
    (D.transferredDifferential δ u).restrictScalars K =
      (D.restrictScalars K).transferredDifferential (δ.restrictScalars K)
        (restrictScalarsUnit (K := K) u) := by
  apply LinearMap.ext
  intro x
  rfl

private theorem internalTransferredInclusion_restrictScalars :
    (D.transferredInclusion δ u).restrictScalars K =
      (D.restrictScalars K).transferredInclusion (δ.restrictScalars K)
        (restrictScalarsUnit (K := K) u) := by
  apply LinearMap.ext
  intro x
  rfl

end InternalScalarRestriction

section InternalRestrictionPreservation
variable {K R M H : Type*} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module R M] [Module K M] [IsScalarTower K R M]
  [AddCommGroup H] [Module R H] [Module K H] [IsScalarTower K R H]
  (D : LinearContraction (R := R) (M := M) (H := H))
  (F : LinearDeformationRetract (R := R) (M := M) (H := H))
  (P₀ : Module.End K M) (Q₀ : Module.End K H)
  (δ : Module.End R M) (u : (Module.End R M)ˣ)
  (hu : (restrictScalarsUnit (K := K) u : Module.End K M) =
    1 + δ.restrictScalars K * D.h.restrictScalars K)
  (hh : D.h.restrictScalars K * P₀ = P₀ * D.h.restrictScalars K)
  (hδ : δ.restrictScalars K * P₀ = P₀ * δ.restrictScalars K)
  (hi : (D.inclusion.restrictScalars K).comp Q₀ = P₀.comp (D.inclusion.restrictScalars K))
  (hp : (D.projection.restrictScalars K).comp P₀ = Q₀.comp (D.projection.restrictScalars K))

include P₀ hu hh hδ hi hp in
theorem internalRestrictedTarget_preserves
    (hF : F.targetD = D.transferredDifferential δ u) :
    (F.targetD.restrictScalars K).comp Q₀ = Q₀.comp (F.targetD.restrictScalars K) := by
  rw [hF, internalTransferredDifferential_restrictScalars]
  exact (D.restrictScalars K).transferredDifferential_preserves_internal P₀ Q₀
    (δ.restrictScalars K) (restrictScalarsUnit (K := K) u) hu hh hδ hi hp


end InternalRestrictionPreservation

/-- Retain the coefficient action already present in a typed linear map. -/
abbrev internalGradingMapTargetModule {R X Y : Type*} [Semiring R]
    [AddCommMonoid X] [AddCommMonoid Y] [Module R X] [h : Module R Y]
    (_f : X →ₗ[R] Y) : Module R Y := h

abbrev internalGradingInclusion {R M H : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
    (D : LinearContraction (R := R) (M := M) (H := H)) : H → M := D.inclusion

abbrev internalGradingProjection {R M H : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
    (D : LinearContraction (R := R) (M := M) (H := H)) : M → H := D.projection

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]
  (P : QuotientGroebnerData V k)
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
  (hfree : ∀ q p, Module.Free k (actualIdealOrdinaryHomology P hJ q p))

local notation "S" => MvPolynomial V k
local notation "C" => actualIdealTensorContraction P hJ hfree

abbrev internalGradingHomologyModule :=
  @internalGradingMapTargetModule _ _ _ _ _ _ _ _ (idealHomologyLof P hJ 0 0)
attribute [local instance 2000] internalGradingHomologyModule
attribute [local irreducible] actualIdealHomologyBasis
local instance : DecidableEq V := LinearOrder.toDecidableEq

abbrev actualIdealHomologyOrdinaryDegree (a : ActualIdealHomologyBasisIndex P hJ hfree) : ℕ := a.1

/-- Every element of an actual homology summand has its original ordinary
degree, independently of the choice of a basis in that summand. -/
theorem idealHomologyLof_ordinary (q p : ℕ) (x : actualIdealOrdinaryHomology P hJ q p) :
    idealHomologyLof P hJ q p x ∈
      Grading.Piece (actualIdealHomologyBasis P hJ hfree) (actualIdealHomologyOrdinaryDegree P hJ hfree) q := by
  letI : ∀ q p, Module.Free k (actualIdealOrdinaryHomology P hJ q p) := hfree
  let L := Grading.Piece (actualIdealHomologyBasis P hJ hfree)
    (actualIdealHomologyOrdinaryDegree P hJ hfree) q
  have hle : (⊤ : Submodule k (actualIdealOrdinaryHomology P hJ q p)) ≤
      L.comap (idealHomologyLof P hJ q p) := by
    rw [← (Module.Free.chooseBasis k (actualIdealOrdinaryHomology P hJ q p)).span_eq]
    apply Submodule.span_le.mpr
    rintro y ⟨i,rfl⟩
    change idealHomologyLof P hJ q p
      (Module.Free.chooseBasis k (actualIdealOrdinaryHomology P hJ q p) i) ∈ L
    rw [← actualIdealHomologyBasis_lof P hJ hfree ⟨q,p,i⟩]
    exact Grading.basis_mem_piece (actualIdealHomologyBasis P hJ hfree)
      (actualIdealHomologyOrdinaryDegree P hJ hfree) ⟨q,p,i⟩
  exact hle (Submodule.mem_top : x ∈ (⊤ : Submodule k _))

theorem actualIdealTensorContraction_inclusion_ordinary
    (a : ActualIdealHomologyBasisIndex P hJ hfree) :
    (@internalGradingInclusion _ _ _ _ _ _ _ _ (C))
      (actualIdealHomologyBasis P hJ hfree a) ∈
      Grading.Piece (idealTensorBasis P) (idealTensorOrdinaryDegree P) a.1 := by
  rw [internalGradingInclusion, actualIdealHomologyBasis_lof,
    actualIdealTensorContraction_inclusion_lof]
  exact idealTensor_lift_ordinary P a.1 a.2.1 _

theorem actualIdealTensorContraction_projection_ordinary (a : IdealTensorIndex P) :
    (@internalGradingProjection _ _ _ _ _ _ _ _ (C)) (idealTensorBasis P a) ∈
      Grading.Piece (actualIdealHomologyBasis P hJ hfree)
        (actualIdealHomologyOrdinaryDegree P hJ hfree) (idealTensorOrdinaryDegree P a) := by
  let q := idealTensorOrdinaryDegree P a
  let p := a.2.card
  let i : ActualIdealIndex P p := ⟨⟨a.2,rfl⟩,a.1⟩
  have hi : (actualIdealDegree i).degree=q := by
    simp only [i,q,actualIdealDegree,map_add,degree_faceExponent,idealTensorOrdinaryDegree]
  let x : actualIdealOrdinaryPiece P q p := actualIdealOrdinaryBasis P q p ⟨i,hi⟩
  have hx : TensorExteriorKoszul.lift (K := k) (M := P.ideal) p x.val = idealTensorBasis P a := by
    have hxval : x.val = actualIdealCoefficientBasis P p i :=
      actualIdealOrdinaryBasis_val P q p ⟨i, hi⟩
    rw [hxval, actualIdealCoefficientBasis_apply, TensorExteriorKoszul.lift_single]
    simpa only [idealTensorBasis, i, groebnerIdealBasis_apply] using
      (Module.Basis.tensorProduct_apply
        (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading)
        Simplicial.basis a.1 a.2).symm
  let y : actualIdealOrdinaryHomology P hJ q p :=
    actualIdealSplittingHomologyEquiv P hJ q p
      (ProjectiveComplexSplitting.homologyProjection
        (fun r => ↥(actualIdealOrdinaryPiece P q r))
        (actualIdealOrdinaryDifferential P hJ q) (actualIdealOrdinarySquare P hJ q)
        (actualIdealOrdinaryTerm_projective P q)
        (actualIdealSplittingHomology_projective P hJ hfree q) p x)
  let π : TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal) →
      IdealGradedHomology P hJ := @internalGradingProjection _ _ _ _ _ _ _ _ (C)
  have hπ : π (TensorExteriorKoszul.lift (K := k) (M := P.ideal) p x.val) =
      idealHomologyLof P hJ q p y :=
    actualIdealTensorContraction_projection_lift P hJ hfree q p x
  have hpoint := (congrArg π hx).symm.trans hπ
  let L := Grading.Piece (actualIdealHomologyBasis P hJ hfree)
    (actualIdealHomologyOrdinaryDegree P hJ hfree) q
  exact (congrArg (fun z : IdealGradedHomology P hJ => z ∈ L) hpoint).mpr
    (idealHomologyLof_ordinary P hJ hfree q p y)

def idealBarInternalBasis := polynomialTensorBasis (k := k) (V := V)
  (M := TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal))
  (I := IdealTensorIndex P) (idealTensorBasis P)
def idealBarInternalDegree := polynomialTensorDegree (V := V) (idealTensorOrdinaryDegree P)
def idealModelInternalBasis := polynomialTensorBasis (k := k) (V := V)
  (M := IdealGradedHomology P hJ) (I := ActualIdealHomologyBasisIndex P hJ hfree)
  (actualIdealHomologyBasis P hJ hfree)
def idealModelInternalDegree := polynomialTensorDegree (V := V) (actualIdealHomologyOrdinaryDegree P hJ hfree)

def idealBarInternalProjection (q : ℕ) : Module.End k (Bar (R := k) (V := V) P.ideal) :=
  Grading.projection (idealBarInternalBasis P) (idealBarInternalDegree P) q

def idealModelInternalProjection (q : ℕ) : Module.End k (S ⊗[k] IdealGradedHomology P hJ) :=
  Grading.projection (idealModelInternalBasis P hJ hfree) (idealModelInternalDegree P hJ hfree) q

theorem idealExtended_h_internal_basis (a : (V →₀ ℕ) × IdealTensorIndex P) :
    (idealExtendedContraction P hJ hfree).h.restrictScalars k (idealBarInternalBasis P a) ∈
      Grading.Piece (idealBarInternalBasis P) (idealBarInternalDegree P) (idealBarInternalDegree P a) :=
  internalPolynomialExtended_h (k₀ := k) (W := V)
    (M₀ := TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal))
    (H₀ := IdealGradedHomology P hJ) (I₀ := IdealTensorIndex P)
    (C) (idealTensorBasis P) (idealTensorOrdinaryDegree P)
    (actualIdealTensorContraction_h_ordinary P hJ hfree) a

theorem idealExtended_inclusion_internal_basis
    (a : (V →₀ ℕ) × ActualIdealHomologyBasisIndex P hJ hfree) :
    (@internalGradingInclusion _ _ _ _ _ _ _ _ (idealExtendedContraction P hJ hfree))
      (idealModelInternalBasis P hJ hfree a) ∈
    Grading.Piece (idealBarInternalBasis P) (idealBarInternalDegree P) (idealModelInternalDegree P hJ hfree a) :=
  internalPolynomialExtended_inclusion (k₀ := k) (W := V)
    (M₀ := TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal))
    (H₀ := IdealGradedHomology P hJ) (I₀ := IdealTensorIndex P)
    (J₀ := ActualIdealHomologyBasisIndex P hJ hfree)
    (C) (idealTensorBasis P) (actualIdealHomologyBasis P hJ hfree)
    (idealTensorOrdinaryDegree P) (actualIdealHomologyOrdinaryDegree P hJ hfree)
    (actualIdealTensorContraction_inclusion_ordinary P hJ hfree) a

set_option maxHeartbeats 1000000 in
/-- The exact scalar-extended projection membership proof. Its proposition is
inferred from the generic map-field lemma, preserving the chosen module dictionaries. -/
def idealExtended_projection_internal_basis (a : (V →₀ ℕ) × IdealTensorIndex P) :=
  @internalPolynomialExtended_projection k V
    (TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal))
    (IdealGradedHomology P hJ) (IdealTensorIndex P)
    (ActualIdealHomologyBasisIndex P hJ hfree) _ _ _ _ _ (C) (idealTensorBasis P) (actualIdealHomologyBasis P hJ hfree)
    (idealTensorOrdinaryDegree P) (actualIdealHomologyOrdinaryDegree P hJ hfree)
    (actualIdealTensorContraction_projection_ordinary P hJ hfree) a

/-- External multiplication adds one polynomial degree while exterior
contraction removes exactly one coefficient Koszul degree. -/
theorem ideal_external_internal_basis (a : (V →₀ ℕ) × IdealTensorIndex P) :
    (externalDifferential P.ideal).restrictScalars k (idealBarInternalBasis P a) ∈
      Grading.Piece (idealBarInternalBasis P) (idealBarInternalDegree P) (idealBarInternalDegree P a) := by
  rcases a with ⟨α,u,F⟩
  let L := Grading.Piece (idealBarInternalBasis P) (idealBarInternalDegree P)
    (idealBarInternalDegree P (α,u,F))
  change externalDifferential P.ideal (idealBarInternalBasis P (α,u,F)) ∈ L
  rw [idealBarInternalBasis, polynomialTensorBasis_apply, idealTensorBasis,
    Module.Basis.tensorProduct_apply, externalDifferential_tmul]
  apply Submodule.sum_mem
  intro v _
  rw [Simplicial.contraction_basis]
  by_cases hv : v ∈ F
  · rw [if_pos hv, Units.smul_def, ← Int.cast_smul_eq_zsmul k,
      TensorProduct.tmul_smul, TensorProduct.tmul_smul]
    have hX : X v * monomial α (1:k) = monomial (α + Finsupp.single v 1) 1 := by
      simp only [X,monomial_mul_monomial,one_mul,add_comm]
    rw [hX]
    have hd : idealBarInternalDegree P (α+Finsupp.single v 1,u,F.erase v) =
        idealBarInternalDegree P (α,u,F) := by
      simp only [idealBarInternalDegree,polynomialTensorDegree,idealTensorOrdinaryDegree,
        map_add,Finsupp.degree_single,Finset.card_erase_of_mem hv]
      have hp := Finset.card_pos.mpr ⟨v,hv⟩
      omega
    have hb := Grading.basis_mem_piece (idealBarInternalBasis P)
      (idealBarInternalDegree P) (α+Finsupp.single v 1,u,F.erase v)
    rw [hd] at hb
    have hb' : monomial (α+Finsupp.single v 1) 1 ⊗ₜ[k]
        ((groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading) u ⊗ₜ[k]
          Simplicial.basis (F.erase v)) ∈ L := by
      simpa only [L,idealBarInternalBasis,polynomialTensorBasis_apply,idealTensorBasis,
        Module.Basis.tensorProduct_apply] using hb
    exact Submodule.smul_mem L _ hb'
  · rw [if_neg hv, TensorProduct.tmul_zero, TensorProduct.tmul_zero]
    exact L.zero_mem

set_option backward.isDefEq.respectTransparency true in
theorem idealExtended_h_internal_projection (q : ℕ) :
    (idealExtendedContraction P hJ hfree).h.restrictScalars k * idealBarInternalProjection P q =
      idealBarInternalProjection P q * (idealExtendedContraction P hJ hfree).h.restrictScalars k := by
  simp only [idealBarInternalProjection, Module.End.mul_eq_comp]
  exact internalShiftedProjection_commutes (k := k)
    (X := Bar (R := k) (V := V) P.ideal) (Y := Bar (R := k) (V := V) P.ideal)
    (I := (V →₀ ℕ) × IdealTensorIndex P) (J := (V →₀ ℕ) × IdealTensorIndex P)
    (A := ℕ) (B := ℕ)
    (idealBarInternalBasis P) (idealBarInternalBasis P)
    (idealBarInternalDegree P) (idealBarInternalDegree P) id Function.injective_id
    ((idealExtendedContraction P hJ hfree).h.restrictScalars k)
    (idealExtended_h_internal_basis P hJ hfree) q

set_option backward.isDefEq.respectTransparency true in
theorem ideal_external_internal_projection (q : ℕ) :
    (externalDifferential P.ideal).restrictScalars k * idealBarInternalProjection P q =
      idealBarInternalProjection P q * (externalDifferential P.ideal).restrictScalars k := by
  simp only [idealBarInternalProjection, Module.End.mul_eq_comp]
  exact internalShiftedProjection_commutes (k := k)
    (X := Bar (R := k) (V := V) P.ideal) (Y := Bar (R := k) (V := V) P.ideal)
    (I := (V →₀ ℕ) × IdealTensorIndex P) (J := (V →₀ ℕ) × IdealTensorIndex P)
    (A := ℕ) (B := ℕ)
    (idealBarInternalBasis P) (idealBarInternalBasis P)
    (idealBarInternalDegree P) (idealBarInternalDegree P) id Function.injective_id
    ((externalDifferential P.ideal).restrictScalars k) (ideal_external_internal_basis P) q

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency true in
theorem idealExtended_inclusion_internal_projection (q : ℕ) :
    ((idealExtendedContraction P hJ hfree).inclusion.restrictScalars k).comp
      (idealModelInternalProjection P hJ hfree q) =
    (idealBarInternalProjection P q).comp
      ((idealExtendedContraction P hJ hfree).inclusion.restrictScalars k) := by
  simp only [idealModelInternalProjection, idealBarInternalProjection,
    idealModelInternalBasis, idealBarInternalBasis, idealModelInternalDegree, idealBarInternalDegree]
  exact @internalPolynomialExtended_inclusion_commutes k V
    (TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal))
    (IdealGradedHomology P hJ) (IdealTensorIndex P)
    (ActualIdealHomologyBasisIndex P hJ hfree) _ _ _ _ _ (C) (idealTensorBasis P) (actualIdealHomologyBasis P hJ hfree)
    (idealTensorOrdinaryDegree P) (actualIdealHomologyOrdinaryDegree P hJ hfree)
    (actualIdealTensorContraction_inclusion_ordinary P hJ hfree) q

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency true in
/-- The actual extended projection commutes with the two ordinary-degree
projections. Infer this same equality directly from the checked map and bases,
so the coefficient-module dictionaries are retained. -/
def idealExtended_projection_internal_projection (q : ℕ) :=
  @internalPolynomialExtended_projection_commutes k V
    (TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal))
    (IdealGradedHomology P hJ) (IdealTensorIndex P)
    (ActualIdealHomologyBasisIndex P hJ hfree) _ _ _ _ _ (C)
    (idealTensorBasis P) (actualIdealHomologyBasis P hJ hfree)
    (idealTensorOrdinaryDegree P) (actualIdealHomologyOrdinaryDegree P hJ hfree)
    (actualIdealTensorContraction_projection_ordinary P hJ hfree) q

set_option backward.isDefEq.respectTransparency true in
/-- The accepted projection-commutation identity in the literal named
contraction and ordinary-degree projections used by the transfer theorem. -/
theorem idealExtended_projection_internal_projection_literal (q : ℕ) :
    ((idealExtendedContraction P hJ hfree).projection.restrictScalars k).comp
      (idealBarInternalProjection P q) =
    (idealModelInternalProjection P hJ hfree q).comp
      ((idealExtendedContraction P hJ hfree).projection.restrictScalars k) := by
  have hp := idealExtended_projection_internal_projection (V := V) (k := k) P hJ hfree q
  -- Expand only the thin aliases connecting the literal projections to the
  -- generic result. Keep the actual contraction and homology basis sealed.
  simpa only [idealExtendedContraction, PolynomialPerturbation.extendedContraction,
    idealBarInternalProjection, idealModelInternalProjection,
    idealBarInternalBasis, idealModelInternalBasis,
    idealBarInternalDegree, idealModelInternalDegree] using hp

#check idealExtended_projection_internal_projection
#print axioms idealExtended_projection_internal_projection

abbrev idealInternalUnit := restrictScalarsUnit (K := k) (actualIdealPerturbationUnit P hJ hfree)

theorem idealInternalUnit_val :
    (idealInternalUnit P hJ hfree : Module.End k (Bar (R := k) (V := V) P.ideal)) =
      1 + (externalDifferential P.ideal).restrictScalars k *
        (idealExtendedContraction P hJ hfree).h.restrictScalars k := by
  have hval : (actualIdealPerturbationUnit P hJ hfree :
        Module.End S (Bar (R := k) (V := V) P.ideal)) =
      1 + externalDifferential (R := k) (V := V) P.ideal *
        (idealExtendedContraction P hJ hfree).h := by
    unfold actualIdealPerturbationUnit
    exact LinearContraction.leftPerturbationUnit_val
      (R := S) (M := Bar (R := k) (V := V) P.ideal)
      (H := S ⊗[k] IdealGradedHomology P hJ) (I := IdealTensorIndex P)
      (idealExtendedContraction P hJ hfree)
      ((idealTensorBasis P).baseChange S) (idealTensorOrdinaryDegree P)
      (externalDifferential (R := k) (V := V) P.ideal) _ _
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun hval x

/-- The very same inverse operators used to define the resolution commute
with each actual ordinary-degree projection. -/
theorem idealInternalUnit_commutes (q : ℕ) :
    Commute (idealInternalUnit P hJ hfree : Module.End k (Bar (R := k) (V := V) P.ideal))
      (idealBarInternalProjection P q) :=
  ((idealExtendedContraction P hJ hfree).restrictScalars k).internalPerturbationUnit_commutes
    (idealBarInternalProjection P q) ((externalDifferential P.ideal).restrictScalars k)
    (idealInternalUnit P hJ hfree) (idealInternalUnit_val P hJ hfree)
    (idealExtended_h_internal_projection P hJ hfree q) (ideal_external_internal_projection P q)

theorem idealInternalUnit_inverse_commutes (q : ℕ) :
    Commute (↑((idealInternalUnit P hJ hfree)⁻¹) : Module.End k (Bar (R := k) (V := V) P.ideal))
      (idealBarInternalProjection P q) :=
  (idealInternalUnit_commutes P hJ hfree q).units_inv_left

set_option backward.isDefEq.respectTransparency true in
private abbrev internalActualPolynomialPerturbationUnit :
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
private theorem internalActualPolynomialPerturbationUnit_eq :
    internalActualPolynomialPerturbationUnit P hJ hfree =
      actualIdealPerturbationUnit P hJ hfree := by
  apply Units.ext
  calc
    (internalActualPolynomialPerturbationUnit P hJ hfree :
        Module.End S (Bar (R := k) (V := V) P.ideal)) =
        1 + externalDifferential (R := k) (V := V) P.ideal *
          (idealExtendedContraction P hJ hfree).h := by
      unfold internalActualPolynomialPerturbationUnit
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
theorem internalActualFreeModel_targetD_eq :
    (actualIdealFreeModel P hJ hfree).targetD =
      (idealExtendedContraction P hJ hfree).transferredDifferential
        (externalDifferential (R := k) (V := V) P.ideal)
        (actualIdealPerturbationUnit P hJ hfree) := by
  change (idealExtendedContraction P hJ hfree).transferredDifferential
      (externalDifferential (R := k) (V := V) P.ideal)
      (internalActualPolynomialPerturbationUnit P hJ hfree) = _
  exact congrArg ((idealExtendedContraction P hJ hfree).transferredDifferential
    (externalDifferential (R := k) (V := V) P.ideal))
    (internalActualPolynomialPerturbationUnit_eq P hJ hfree)

set_option backward.isDefEq.respectTransparency true in
theorem internalActualFreeModel_inclusion_eq :
    (actualIdealFreeModel P hJ hfree).inclusion =
      (idealExtendedContraction P hJ hfree).transferredInclusion
        (externalDifferential (R := k) (V := V) P.ideal)
        (actualIdealPerturbationUnit P hJ hfree) := by
  change (idealExtendedContraction P hJ hfree).transferredInclusion
      (externalDifferential (R := k) (V := V) P.ideal)
      (internalActualPolynomialPerturbationUnit P hJ hfree) = _
  exact congrArg ((idealExtendedContraction P hJ hfree).transferredInclusion
    (externalDifferential (R := k) (V := V) P.ideal))
    (internalActualPolynomialPerturbationUnit_eq P hJ hfree)

/-- The literal transferred differential preserves total ordinary degree. -/
def actualIdealFreeModel_d_internal_projection (q : ℕ) :=
  @internalRestrictedTarget_preserves k S
    (Bar (R := k) (V := V) P.ideal)
    (S ⊗[k] IdealGradedHomology P hJ)
    _ _ _ _ _ _ _ _ _ _ _
    (idealExtendedContraction P hJ hfree)
    (actualIdealFreeModel P hJ hfree)
    (idealBarInternalProjection P q) (idealModelInternalProjection P hJ hfree q)
    (externalDifferential (R := k) (V := V) P.ideal)
    (actualIdealPerturbationUnit P hJ hfree)
    (idealInternalUnit_val P hJ hfree)
    (idealExtended_h_internal_projection P hJ hfree q)
    (ideal_external_internal_projection P q)
    (idealExtended_inclusion_internal_projection P hJ hfree q)
    (idealExtended_projection_internal_projection_literal (V := V) (k := k) P hJ hfree q)
    (internalActualFreeModel_targetD_eq P hJ hfree)

theorem actualIdealFreeModel_inclusion_internal_projection (q : ℕ) :
    ((actualIdealFreeModel P hJ hfree).inclusion.restrictScalars k).comp
      (idealModelInternalProjection P hJ hfree q) =
    (idealBarInternalProjection P q).comp
      ((actualIdealFreeModel P hJ hfree).inclusion.restrictScalars k) := by
  rw [internalActualFreeModel_inclusion_eq, internalTransferredInclusion_restrictScalars]
  exact ((idealExtendedContraction P hJ hfree).restrictScalars k).transferredInclusion_preserves_internal
    (idealBarInternalProjection P q) (idealModelInternalProjection P hJ hfree q)
    ((externalDifferential P.ideal).restrictScalars k) (idealInternalUnit P hJ hfree)
    (idealInternalUnit_val P hJ hfree) (idealExtended_h_internal_projection P hJ hfree q)
    (ideal_external_internal_projection P q)
    (idealExtended_inclusion_internal_projection P hJ hfree q)

@[simp] theorem actualIdealFreeBasis_internal (a : ActualIdealHomologyBasisIndex P hJ hfree) :
    actualIdealFreeBasis P hJ hfree a = idealModelInternalBasis P hJ hfree (0,a) := by
  simp only [actualIdealFreeBasis, Module.Basis.baseChange_apply, idealModelInternalBasis,
    polynomialTensorBasis_apply, MvPolynomial.monomial_zero', MvPolynomial.C_1]

theorem actualIdealFreeModel_d_internal_basis (a : ActualIdealHomologyBasisIndex P hJ hfree) :
    (actualIdealFreeModel P hJ hfree).targetD (actualIdealFreeBasis P hJ hfree a) ∈
      Grading.Piece (idealModelInternalBasis P hJ hfree) (idealModelInternalDegree P hJ hfree) a.1 := by
  have he := LinearMap.congr_fun (actualIdealFreeModel_d_internal_projection P hJ hfree a.1)
    (actualIdealFreeBasis P hJ hfree a)
  change (actualIdealFreeModel P hJ hfree).targetD
      (idealModelInternalProjection P hJ hfree a.1 (actualIdealFreeBasis P hJ hfree a)) =
    idealModelInternalProjection P hJ hfree a.1
      ((actualIdealFreeModel P hJ hfree).targetD (actualIdealFreeBasis P hJ hfree a)) at he
  have hx : actualIdealFreeBasis P hJ hfree a ∈
      Grading.Piece (idealModelInternalBasis P hJ hfree) (idealModelInternalDegree P hJ hfree) a.1 := by
    rw [actualIdealFreeBasis_internal]
    simpa only [idealModelInternalDegree,polynomialTensorDegree,map_zero,zero_add,
      actualIdealHomologyOrdinaryDegree] using Grading.basis_mem_piece
        (idealModelInternalBasis P hJ hfree) (idealModelInternalDegree P hJ hfree) (0,a)
  rw [show idealModelInternalProjection P hJ hfree a.1 (actualIdealFreeBasis P hJ hfree a) =
    actualIdealFreeBasis P hJ hfree a from Grading.projection_eq_self hx] at he
  rw [he]
  exact Grading.projection_mem _ _ _ _

/-- Every nonzero monomial coefficient has precisely the difference of the
actual source and target shifts. This is stronger than a total-degree bound. -/
theorem actualIdealFreeModel_matrix_degree (i j : ActualIdealHomologyBasisIndex P hJ hfree)
    (a : V →₀ ℕ)
    (ha : ((actualIdealFreeBasis P hJ hfree).repr
      ((actualIdealFreeModel P hJ hfree).targetD (actualIdealFreeBasis P hJ hfree i)) j).coeff a ≠ 0) :
    a.degree + j.1 = i.1 := by
  -- Infer the coordinate identity independently of the membership proof.
  -- In particular, do not match a generic tensor-piece premise against the
  -- already typed actual model's homogeneous-piece proposition.
  have hrepr := polynomialTensorBasis_repr
    (k := k) (V := V) (M := IdealGradedHomology P hJ)
    (I := ActualIdealHomologyBasisIndex P hJ hfree)
    (actualIdealHomologyBasis P hJ hfree)
    ((actualIdealFreeModel P hJ hfree).targetD (actualIdealFreeBasis P hJ hfree i)) a j
  have hdegree := (Grading.mem_piece (R := k)
    (idealModelInternalBasis P hJ hfree) (idealModelInternalDegree P hJ hfree) i.1
    ((actualIdealFreeModel P hJ hfree).targetD (actualIdealFreeBasis P hJ hfree i))).mp
      (actualIdealFreeModel_d_internal_basis P hJ hfree i) (a,j) (by
        intro hz
        apply ha
        exact hrepr.symm.trans hz)
  simpa only [idealModelInternalDegree, polynomialTensorDegree,
    actualIdealHomologyOrdinaryDegree] using hdegree

theorem actualIdealFreeModel_matrix_homogeneous (i j : ActualIdealHomologyBasisIndex P hJ hfree) :
    IsWeightedHomogeneous (fun _ : V => (1 : ℕ))
      ((actualIdealFreeBasis P hJ hfree).repr
        ((actualIdealFreeModel P hJ hfree).targetD (actualIdealFreeBasis P hJ hfree i)) j)
      (i.1-j.1) := by
  intro a ha
  have hdegree := actualIdealFreeModel_matrix_degree P hJ hfree i j a ha
  rw [← Finsupp.degree_eq_weight_one]
  omega

theorem actualIdealFreeModel_matrix_zero_of_shift_gt (i j : ActualIdealHomologyBasisIndex P hJ hfree)
    (hij : i.1 < j.1) :
    (actualIdealFreeBasis P hJ hfree).repr
      ((actualIdealFreeModel P hJ hfree).targetD (actualIdealFreeBasis P hJ hfree i)) j = 0 := by
  ext a
  by_contra ha
  have hne : ((actualIdealFreeBasis P hJ hfree).repr
      ((actualIdealFreeModel P hJ hfree).targetD (actualIdealFreeBasis P hJ hfree i)) j).coeff a ≠ 0 := by
    simpa only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using ha
  have hdegree := actualIdealFreeModel_matrix_degree P hJ hfree i j a hne
  omega

include hJ in
theorem actualIdealOrdinaryBasis_piece_eq (q : ℕ) :
    Grading.Piece (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading)
      (actualIdealCoefficientDegree P) q =
    idealWeightedComponent P.ideal (fun _ : V => (1 : ℕ)) q := by
  -- The degree occurs as a function argument, so identify that entire
  -- function before applying the weighted-component theorem.
  have hdegree : actualIdealCoefficientDegree P =
      (fun a : NonstandardIndex P.order P.ideal =>
        Finsupp.weight (fun _ : V => (1 : ℕ)) a.val) := by
    funext a
    change a.val.degree = Finsupp.weight (fun _ : V => (1 : ℕ)) a.val
    rw [Finsupp.degree_eq_weight_one]
  rw [hdegree]
  exact groebnerIdealBasis_piece_eq P.order P.ideal P.generators P.groebner P.unitLeading
    (fun _ : V => (1 : ℕ)) hJ q

include hJ in
theorem idealBarAugmentation_internal_basis (a : (V →₀ ℕ) × IdealTensorIndex P) :
    (PolynomialModuleResolution.augmentation P.ideal).restrictScalars k
      (idealBarInternalBasis P a) ∈
    Grading.Piece (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading)
      (actualIdealCoefficientDegree P) (idealBarInternalDegree P a) := by
  rcases a with ⟨α,u,F⟩
  rw [LinearMap.restrictScalars_apply, idealBarInternalBasis,
    polynomialTensorBasis_apply, idealTensorBasis, Module.Basis.tensorProduct_apply,
    PolynomialModuleResolution.augmentation_tmul_basis]
  by_cases hF : F = ∅
  · rw [if_pos hF, actualIdealOrdinaryBasis_piece_eq P hJ,
      mem_idealWeightedComponent]
    simp only [Submodule.coe_smul, smul_eq_mul]
    have hm := isWeightedHomogeneous_monomial (fun _ : V => (1 : ℕ)) α (1:k) rfl
    have hi := idealLift_isWeightedHomogeneous P.order P.ideal P.generators P.groebner P.unitLeading
      (fun _ : V => (1 : ℕ)) hJ u
    simpa only [groebnerIdealBasis_apply, idealBarInternalDegree, polynomialTensorDegree,
      idealTensorOrdinaryDegree, hF, Finset.card_empty, add_zero, ← Finsupp.degree_eq_weight_one]
      using hm.mul hi
  · rw [if_neg hF]
    exact Submodule.zero_mem _

theorem actualIdealFreeModel_inclusion_internal_basis (a : ActualIdealHomologyBasisIndex P hJ hfree) :
    (actualIdealFreeModel P hJ hfree).inclusion (actualIdealFreeBasis P hJ hfree a) ∈
      Grading.Piece (idealBarInternalBasis P) (idealBarInternalDegree P) a.1 := by
  have he := LinearMap.congr_fun (actualIdealFreeModel_inclusion_internal_projection P hJ hfree a.1)
    (actualIdealFreeBasis P hJ hfree a)
  change (actualIdealFreeModel P hJ hfree).inclusion
      (idealModelInternalProjection P hJ hfree a.1 (actualIdealFreeBasis P hJ hfree a)) =
    idealBarInternalProjection P a.1
      ((actualIdealFreeModel P hJ hfree).inclusion (actualIdealFreeBasis P hJ hfree a)) at he
  have hx : actualIdealFreeBasis P hJ hfree a ∈
      Grading.Piece (idealModelInternalBasis P hJ hfree) (idealModelInternalDegree P hJ hfree) a.1 := by
    rw [actualIdealFreeBasis_internal]
    simpa only [idealModelInternalDegree,polynomialTensorDegree,map_zero,zero_add,
      actualIdealHomologyOrdinaryDegree] using Grading.basis_mem_piece
        (idealModelInternalBasis P hJ hfree) (idealModelInternalDegree P hJ hfree) (0,a)
  rw [show idealModelInternalProjection P hJ hfree a.1 (actualIdealFreeBasis P hJ hfree a) =
    actualIdealFreeBasis P hJ hfree a from Grading.projection_eq_self hx] at he
  rw [he]
  exact Grading.projection_mem _ _ _ _

/-- The actual module-action augmentation is homogeneous with the original
ordinary polynomial grading on the ideal. -/
theorem actualIdealFreeAugmentation_internal_basis (a : ActualIdealHomologyBasisIndex P hJ hfree) :
    IsWeightedHomogeneous (fun _ : V => (1 : ℕ))
      (actualIdealFreeAugmentation P hJ hfree (actualIdealFreeBasis P hJ hfree a)).val a.1 := by
  have hx := map_mem_piece_of_basis (idealBarInternalBasis P)
    (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading)
    (idealBarInternalDegree P) (actualIdealCoefficientDegree P)
    ((PolynomialModuleResolution.augmentation P.ideal).restrictScalars k)
    (idealBarAugmentation_internal_basis P hJ) a.1
    (actualIdealFreeModel_inclusion_internal_basis P hJ hfree a)
  rw [actualIdealOrdinaryBasis_piece_eq P hJ] at hx
  exact hx

section IntegralGraph

variable {N : ℕ} {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G)
  (s : ℕ) (hs : 0 < s)

/-- The shift is the original ordinary Koszul degree of the actual
homology summand that indexes this free generator. -/
def integralGraphResolutionShift (a : IntegralGraphResolutionIndex hG s hs) : ℕ := a.1

/-- Each polynomial matrix entry has the degree required for a graded
resolution of the actual power of the integral parameter ideal. -/
theorem integralGraphResolution_matrix_homogeneous (i j : IntegralGraphResolutionIndex hG s hs) :
    IsWeightedHomogeneous (fun _ : GraphIntegralVariables N => (1 : ℕ))
      ((integralGraphResolutionBasis hG s hs).repr
        ((integralGraphTransferredModel hG s hs).targetD (integralGraphResolutionBasis hG s hs i)) j)
      (integralGraphResolutionShift hG s hs i-integralGraphResolutionShift hG s hs j) :=
  actualIdealFreeModel_matrix_homogeneous (integralGraphParameterData hG s)
    (integralGraphParameterHomogeneous hG s) (integralGraphHomologyPiece_free hG s hs) i j

theorem integralGraphResolution_matrix_degree (i j : IntegralGraphResolutionIndex hG s hs)
    (a : GraphIntegralVariables N →₀ ℕ)
    (ha : ((integralGraphResolutionBasis hG s hs).repr
      ((integralGraphTransferredModel hG s hs).targetD (integralGraphResolutionBasis hG s hs i)) j).coeff a ≠ 0) :
    a.degree + integralGraphResolutionShift hG s hs j = integralGraphResolutionShift hG s hs i :=
  actualIdealFreeModel_matrix_degree (integralGraphParameterData hG s)
    (integralGraphParameterHomogeneous hG s) (integralGraphHomologyPiece_free hG s hs) i j a ha

theorem integralGraphResolution_matrix_zero_of_shift_gt
    (i j : IntegralGraphResolutionIndex hG s hs)
    (hij : integralGraphResolutionShift hG s hs i < integralGraphResolutionShift hG s hs j) :
    (integralGraphResolutionBasis hG s hs).repr
      ((integralGraphTransferredModel hG s hs).targetD (integralGraphResolutionBasis hG s hs i)) j = 0 :=
  actualIdealFreeModel_matrix_zero_of_shift_gt (integralGraphParameterData hG s)
    (integralGraphParameterHomogeneous hG s) (integralGraphHomologyPiece_free hG s hs) i j hij

theorem integralGraphAugmentation_internal_basis (i : IntegralGraphResolutionIndex hG s hs) :
    IsWeightedHomogeneous (fun _ : GraphIntegralVariables N => (1 : ℕ))
      (integralGraphAugmentation hG s hs (integralGraphResolutionBasis hG s hs i)).val
      (integralGraphResolutionShift hG s hs i) :=
  actualIdealFreeAugmentation_internal_basis (integralGraphParameterData hG s)
    (integralGraphParameterHomogeneous hG s) (integralGraphHomologyPiece_free hG s hs) i

end IntegralGraph
end FourPapers.Sublattice

end
end
end


end
