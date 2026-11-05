module

public import PaperVerification.FermionLocalTensorBigraded
public import PaperVerification.FermionLocalFactorBigraded

/-!
# Actual nonzero local factors and Theorem 7.2 assembly

The augmentation is constructed from the literal moment presentation.
It proves that every enumerated support point contributes a nonzero factor.
The theorem then assembles the exterior-bigraded local equivalences,
the finite Artinian product, and the faithful original paired-factor bridge.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion

section Augmentation

variable {F ι κ : Type*} [Field F] [CharZero F] [Fintype ι] [Fintype κ]
  [LinearOrder (ι⊕ι)]
  (beta : ι → F) (cluster : ι → κ) (r : ι → ℕ) (s : κ → ℕ) (u v : ι → ℕ)
  (hr : ∀ i,0<r i) (hs : ∀ i,0<s (cluster i))

def homogeneousClusterAugmentationRepresentation :
    ClusterRepresentation (NGradedAlgebra.scalar F).part beta cluster r s u v where
  z _ := 0
  theta _ := 0
  xi _ := 0
  z_degree _ := Submodule.zero_mem _
  theta_degree _ := Submodule.zero_mem _
  xi_degree _ := Submodule.zero_mem _
  ordinary c k := by
    apply Finset.sum_eq_zero
    intro i hi
    have hpos : 0<r i.1*(s c+k) := by
      apply Nat.mul_pos (hr i.1)
      have hh := hs i.1
      rw [i.property] at hh
      omega
    simp only [zero_pow (Nat.ne_of_gt hpos),mul_zero]
  theta_moment _ _ := by simp only [mul_zero,Finset.sum_const_zero]
  xi_moment _ _ := by simp only [mul_zero,Finset.sum_const_zero]
  mixed_moment _ _ := by simp only [mul_zero,Finset.sum_const_zero]

def homogeneousClusterAugmentation :
    HomogeneousClusterAlgebra beta cluster r s u v →ₐ[F] F :=
  (homogeneousClusterAugmentationRepresentation beta cluster r s u v hr hs).lift
    NGradedAlgebra.scalar_supercommutative

include hr hs in
theorem homogeneousCluster_nontrivial :
    Nontrivial (HomogeneousClusterAlgebra beta cluster r s u v) :=
  (homogeneousClusterAugmentation beta cluster r s u v hr hs).toRingHom.domain_nontrivial

end Augmentation

namespace SeparatedPairedData

variable {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
  (d : SeparatedPairedData F n)

local instance FermionTheoremSevenTwo_oddOrder : LinearOrder (Fin n⊕Fin n) := finiteIndexLinearOrder _

theorem localSuper_nontrivial (rho : d.O.SupportPoint) :
    Nontrivial (d.LocalSuper rho) :=
  ((homogeneousClusterAugmentation d.beta (d.O.pointCluster rho)
      (d.O.ramificationOrder rho) (d.O.clusterMultiplicity rho)
      (d.thetaOrder rho) (d.xiOrder rho) (d.O.ramificationOrder_pos rho)
      (fun i ↦ d.O.clusterMultiplicity_pos rho (d.O.pointCluster rho i))).comp
    (d.localSuperEquivHomogeneousCluster rho).toAlgHom).toRingHom.domain_nontrivial

end SeparatedPairedData

/-- The full roots-and-ramification decomposition: each actual local quotient
has its natural exterior bigrading, each tensor factor is an actual original
homogeneous paired quotient with inherited root data, and the original
global algebra is the finite product over exactly the actual support points. -/
theorem theorem_7_2 {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
    (d : SeparatedPairedData F n) :
    Finite d.O.SupportPoint ∧
    (∀ rho : d.O.SupportPoint,∃ e :
        d.LocalSuper rho ≃ₐ[F] (d.localClusterFamily rho).tensor.Carrier,
      ∀ g x,e x∈(d.localClusterFamily rho).tensorBigrading.part g ↔
        x∈d.localSuperBigradedPart rho g) ∧
    Nonempty (d.SuperQuotient ≃ₐ[F]
      ∀ rho : d.O.SupportPoint,(d.localClusterFamily rho).tensor.Carrier) ∧
    (∀ rho : d.O.SupportPoint,Nontrivial (d.LocalSuper rho)) ∧
    (∀ (rho : d.O.SupportPoint) (c : Fin (Fintype.card (d.O.PointCluster rho))),
      ∃ e : ((d.localClusterFamily rho).factor c).Carrier ≃ₐ[F]
        PairedQuotient (d.localFactorPairedData rho c).beta
          (d.localFactorPairedData rho c).phi
          (d.localFactorPairedData rho c).a
          (d.localFactorPairedData rho c).b,
        ∀ g x,e x∈d.localFactorPairedBigradedPart rho c g ↔
          x∈((d.localClusterFamily rho).factorBigrading c).part g) := by
  refine ⟨inferInstance,fun rho ↦ ⟨d.localSuperTensorEquiv rho,
    d.localSuperTensorEquiv_bigraded_iff rho⟩,
    ⟨d.globalSuperTensorProductEquiv⟩,d.localSuper_nontrivial,?_⟩
  intro rho c
  exact d.localFactorBigradedEquivPaired rho c

end PaperVerification.Fermion

