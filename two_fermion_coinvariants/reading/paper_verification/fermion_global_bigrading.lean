module

public import PaperVerification.FermionGlobalOddPresentation
public import PaperVerification.FermionIndependentClusterBigraded

/-!
# Literal exterior bigrading of the original separated quotient

The pieces are images of original exterior word spans under ambient scalar
base change and actual quotienting. The two generator formulas identify
them with the original separate theta and xi degrees.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical TensorProduct

namespace PaperVerification.Fermion
namespace SeparatedPairedData

variable {F : Type*} [Field F] {n : ℕ} (d : SeparatedPairedData F n)
local instance FermionGlobalBigrading_oddOrder : LinearOrder (Fin n⊕Fin n) := finiteIndexLinearOrder _

@[simp] theorem globalSuperPolynomialBaseEquiv_apply (x : d.SuperQuotient) :
    d.globalSuperPolynomialBaseEquiv x=
      (1 : d.O.Ordinary) ⊗ₜ[PolynomialRing F n] x := rfl

def globalSuperExteriorLift :
    ClusterExterior (d.O.Ordinary) (Fin n) →ₐ[d.O.Ordinary]
      d.SuperQuotient :=
  (d.globalSuperPolynomialBaseEquiv).symm.toAlgHom.comp
    ((tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
      (S := d.O.Ordinary) d.superIdeal).symm.toAlgHom.comp
      (((d.ordinaryTensorIdeal).ringCon.mkₐ (d.O.Ordinary)).comp
        (d.ordinaryAmbientEquiv).symm.toAlgHom))

theorem globalSuperExteriorLift_theta (i : Fin n) :
    d.globalSuperExteriorLift (clusterTheta i)=
      d.superMk (theta F n i) := by
  have ha : (d.ordinaryAmbientEquiv).symm (clusterTheta i)=
      1 ⊗ₜ[PolynomialRing F n] theta F n i := by
    apply (d.ordinaryAmbientEquiv).injective
    rw [AlgEquiv.apply_symm_apply,d.ordinaryAmbientEquiv_theta]
  have hq :
      (tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
        (S := d.O.Ordinary) d.superIdeal).symm
        ((d.ordinaryTensorIdeal).ringCon.mkₐ (d.O.Ordinary)
          (1 ⊗ₜ[PolynomialRing F n] theta F n i))=
        1 ⊗ₜ[PolynomialRing F n] d.superMk (theta F n i) := by
    apply (tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
      (S := d.O.Ordinary) d.superIdeal).injective
    rw [AlgEquiv.apply_symm_apply]
    convert (tensorTwoSidedQuotientEquiv_tmul_mk (R := PolynomialRing F n)
      (S := d.O.Ordinary) (A := SuperRing F n)
      d.superIdeal 1 (theta F n i)).symm using 1 <;> rfl
  change (d.globalSuperPolynomialBaseEquiv).symm
    ((tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
      (S := d.O.Ordinary) d.superIdeal).symm
      ((d.ordinaryTensorIdeal).ringCon.mkₐ (d.O.Ordinary)
        ((d.ordinaryAmbientEquiv).symm (clusterTheta i))))=_
  rw [ha,hq]
  apply (d.globalSuperPolynomialBaseEquiv).injective
  rw [AlgEquiv.apply_symm_apply,d.globalSuperPolynomialBaseEquiv_apply]

theorem globalSuperExteriorLift_xi (i : Fin n) :
    d.globalSuperExteriorLift (clusterXi i)=
      d.superMk (xi F n i) := by
  have ha : (d.ordinaryAmbientEquiv).symm (clusterXi i)=
      1 ⊗ₜ[PolynomialRing F n] xi F n i := by
    apply (d.ordinaryAmbientEquiv).injective
    rw [AlgEquiv.apply_symm_apply,d.ordinaryAmbientEquiv_xi]
  have hq :
      (tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
        (S := d.O.Ordinary) d.superIdeal).symm
        ((d.ordinaryTensorIdeal).ringCon.mkₐ (d.O.Ordinary)
          (1 ⊗ₜ[PolynomialRing F n] xi F n i))=
        1 ⊗ₜ[PolynomialRing F n] d.superMk (xi F n i) := by
    apply (tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
      (S := d.O.Ordinary) d.superIdeal).injective
    rw [AlgEquiv.apply_symm_apply]
    convert (tensorTwoSidedQuotientEquiv_tmul_mk (R := PolynomialRing F n)
      (S := d.O.Ordinary) (A := SuperRing F n)
      d.superIdeal 1 (xi F n i)).symm using 1 <;> rfl
  change (d.globalSuperPolynomialBaseEquiv).symm
    ((tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
      (S := d.O.Ordinary) d.superIdeal).symm
      ((d.ordinaryTensorIdeal).ringCon.mkₐ (d.O.Ordinary)
        ((d.ordinaryAmbientEquiv).symm (clusterXi i))))=_
  rw [ha,hq]
  apply (d.globalSuperPolynomialBaseEquiv).injective
  rw [AlgEquiv.apply_symm_apply,d.globalSuperPolynomialBaseEquiv_apply]

def globalSuperBigradedPart (g : ℕ×ℕ) : Submodule (d.O.Ordinary) (d.SuperQuotient) :=
  (exteriorBigradedPart g).map (d.globalSuperExteriorLift).toLinearMap

set_option maxHeartbeats 1000000 in
theorem globalSuperOddPresentation_lift
    (x : ClusterExterior (d.O.Ordinary) (Fin n)) :
    d.globalSuperEquivOddPresentation (d.globalSuperExteriorLift x)=
      (d.ordinaryOddIdeal).ringCon.mkₐ (d.O.Ordinary) x := by
  letI := polynomialAmbientTensorRing (F := F) (n := n) (d.O.Ordinary)
  let E1 := d.globalSuperPolynomialBaseEquiv
  let E := tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
    (S := d.O.Ordinary) (A := SuperRing F n) d.superIdeal
  let a := d.ordinaryAmbientEquiv
  let q := (d.ordinaryTensorIdeal).ringCon.mkₐ (d.O.Ordinary)
  let f := twoSidedQuotientEquiv (R := d.O.Ordinary)
    (A := d.O.Ordinary ⊗[PolynomialRing F n] SuperRing F n)
    (B := ClusterExterior (d.O.Ordinary) (Fin n))
    a (d.ordinaryTensorIdeal) (d.ordinaryOddIdeal) (d.ordinaryAmbientEquiv_ideal) (d.ordinaryAmbientEquiv_symm_ideal)
  change f (E (E1 (E1.symm (E.symm (q (a.symm x))))))=_
  rw [AlgEquiv.apply_symm_apply,AlgEquiv.apply_symm_apply]
  exact (twoSidedQuotientEquiv_mk a (d.ordinaryTensorIdeal) (d.ordinaryOddIdeal)
    (d.ordinaryAmbientEquiv_ideal) (d.ordinaryAmbientEquiv_symm_ideal) (a.symm x)).trans
      (congrArg ((d.ordinaryOddIdeal).ringCon.mkₐ (d.O.Ordinary)) (a.apply_symm_apply x))

theorem globalSuperExteriorLift_eq_zero_iff
    (x : ClusterExterior (d.O.Ordinary) (Fin n)) :
    d.globalSuperExteriorLift x=0 ↔ x∈d.ordinaryOddIdeal := by
  have hq :
      (d.ordinaryOddIdeal).ringCon.mkₐ (d.O.Ordinary) x=0 ↔
        x∈d.ordinaryOddIdeal := by
    constructor
    · intro hx
      change ((x : ClusterExterior (d.O.Ordinary) (Fin n)) :
        (d.ordinaryOddIdeal).ringCon.Quotient)=
        ((0 : ClusterExterior (d.O.Ordinary) (Fin n)) :
          (d.ordinaryOddIdeal).ringCon.Quotient) at hx
      exact Quotient.exact hx
    · exact quotientMk_eq_zero_of_mem (R := d.O.Ordinary) d.ordinaryOddIdeal x
  rw [←d.globalSuperOddPresentation_lift x] at hq
  exact ((d.globalSuperEquivOddPresentation).map_eq_zero_iff).symm.trans hq

theorem globalSuperExteriorLift_surjective :
    Function.Surjective (d.globalSuperExteriorLift) := by
  intro x
  obtain ⟨y,hy⟩ := (d.ordinaryOddIdeal).ringCon.mk'_surjective
    (d.globalSuperEquivOddPresentation x)
  refine ⟨y,(d.globalSuperEquivOddPresentation).injective ?_⟩
  rw [d.globalSuperOddPresentation_lift]
  exact hy

/-- Directness and multiplication of the literal localized image pieces
are proved from the homogeneous actual relation ideal. -/
def globalSuperBigrading :
    GradedAlgebra (R := d.O.Ordinary) (A := d.SuperQuotient) d.globalSuperBigradedPart := by
  letI := exteriorWeightedGrading (A := d.O.Ordinary) (oddBidegree (ι := Fin n))
  exact gradedImageAlgebra (R := d.O.Ordinary)
    (A := ClusterExterior d.O.Ordinary (Fin n)) (B := d.SuperQuotient)
    (Γ := ℕ×ℕ) (exteriorBigradedPart (A := d.O.Ordinary) (ι := Fin n))
    (d.globalSuperExteriorLift)
    (d.globalSuperExteriorLift_surjective) (by
      intro g a ha
      apply (d.globalSuperExteriorLift_eq_zero_iff _).mpr
      exact twoSided_span_multihomogeneous exteriorBigradedPart
        (Set.range fun p : LocalOddFamily×ℕ ↦
          separatedOddCurrent (d.O.ordinaryNode)
            (fun i ↦ algebraMap F (d.O.Ordinary) (d.beta i))
            (d.ordinaryA) (d.ordinaryB) p.1 p.2)
        (by
          rintro z ⟨⟨family,k⟩,rfl⟩
          exact ⟨oddFamilyBidegree family,separatedOddCurrent_bidegree _ _ _ _ family k⟩)
        a ((d.globalSuperExteriorLift_eq_zero_iff a).mp ha) g)

theorem globalSuperOddPresentation_bigraded_iff (g : ℕ×ℕ) (x : d.SuperQuotient) :
    d.globalSuperEquivOddPresentation x∈
      separatedOddBigradedPart (d.O.ordinaryNode)
        (fun i ↦ algebraMap F (d.O.Ordinary) (d.beta i))
        (d.ordinaryA) (d.ordinaryB) g ↔
      x∈d.globalSuperBigradedPart g := by
  constructor
  · rintro ⟨y,hy,hey⟩
    refine ⟨y,hy,?_⟩
    apply (d.globalSuperEquivOddPresentation).injective
    rw [AlgHom.toLinearMap_apply,d.globalSuperOddPresentation_lift]
    simpa only [ordinaryOddIdeal,AlgHom.toLinearMap_apply,RingCon.mkₐ_apply] using hey
  · rintro ⟨y,hy,rfl⟩
    refine ⟨y,hy,?_⟩
    simpa only [ordinaryOddIdeal,AlgHom.toLinearMap_apply,RingCon.mkₐ_apply] using
      (d.globalSuperOddPresentation_lift y).symm


end SeparatedPairedData
end PaperVerification.Fermion

