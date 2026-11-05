module

public import PaperVerification.FermionLocalTensorAssembly
public import PaperVerification.FermionSingleClusterPresentation
public import PaperVerification.FermionHighestPowerMonomial

/-!
# The local tensor factors are the paper's original paired quotients

The finite cluster index is reindexed by an explicit equivalence with Fin.
Every exponent and weight is pulled back along that equivalence. Positivity,
the paired exponent balance, and every subset-weight unit condition are
proved from the actual support-point data. Thus these are instances of the
original homogeneous paired theorem, with no assumed dimension or basis.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion

section Reindex

variable {F ι : Type*} [Field F] [CharZero F] [Fintype ι]
  [LinearOrder (ι⊕ι)]
  (beta : ι → F) (r : ι → ℕ) (s : ℕ) (u v : ι → ℕ)

def singleClusterFinParameterEquiv :
    ClusterParameterEquiv beta (fun _ : ι ↦ ()) r (fun _ ↦ s) u v
      (fun j ↦ beta ((Fintype.equivFin ι).symm j))
      (fun _ : Fin (Fintype.card ι) ↦ ())
      (fun j ↦ r ((Fintype.equivFin ι).symm j)) (fun _ ↦ s)
      (fun j ↦ u ((Fintype.equivFin ι).symm j))
      (fun j ↦ v ((Fintype.equivFin ι).symm j)) where
  index := Fintype.equivFin ι
  label := Equiv.refl Unit
  beta_eq i := by simp only [Equiv.symm_apply_apply]
  cluster_eq i := rfl
  r_eq i := by simp only [Equiv.symm_apply_apply]
  s_eq c := rfl
  u_eq i := by simp only [Equiv.symm_apply_apply]
  v_eq i := by simp only [Equiv.symm_apply_apply]

end Reindex

namespace SeparatedPairedData

variable {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
  (d : SeparatedPairedData F n) (rho : d.O.SupportPoint)
  (c : Fin (Fintype.card (d.O.PointCluster rho)))

abbrev LocalFactorIndex := (d.localClusterFamily rho).Index c

def localFactorIndex : Fin (Fintype.card (d.LocalFactorIndex rho c)) → Fin n :=
  fun j ↦ ((Fintype.equivFin (d.LocalFactorIndex rho c)).symm j).1

theorem localFactorIndex_injective : Function.Injective (d.localFactorIndex rho c) := by
  intro i j h
  apply (Fintype.equivFin (d.LocalFactorIndex rho c)).symm.injective
  exact Subtype.ext h

theorem localFactorIndex_cluster (j : Fin (Fintype.card (d.LocalFactorIndex rho c))) :
    d.O.pointCluster rho (d.localFactorIndex rho c j)=(d.localClusterLabels rho).symm c :=
  ((Fintype.equivFin (d.LocalFactorIndex rho c)).symm j).property

theorem localFactor_nonempty : Nonempty (d.LocalFactorIndex rho c) := by
  obtain ⟨i,hi⟩ := ((d.localClusterLabels rho).symm c).property
  refine ⟨⟨i,?_⟩⟩
  exact Subtype.ext hi

theorem localFactor_card_pos : 0<Fintype.card (d.LocalFactorIndex rho c) := by
  letI := d.localFactor_nonempty rho c
  exact Fintype.card_pos

theorem localFactor_subset_units
    (U : Finset (Fin (Fintype.card (d.LocalFactorIndex rho c)))) (hU : U.Nonempty) :
    IsUnit (∑ j∈U,d.beta (d.localFactorIndex rho c j)) := by
  let e : Fin (Fintype.card (d.LocalFactorIndex rho c)) ↪ Fin n :=
    ⟨d.localFactorIndex rho c,d.localFactorIndex_injective rho c⟩
  have h := d.beta_units (U.map e) hU.map
  simpa only [Finset.sum_map,e,Function.Embedding.coeFn_mk] using h

def localFactorPairedData :
    PairedData (K := F) (n := Fintype.card (d.LocalFactorIndex rho c)) where
  positive_n := d.localFactor_card_pos rho c
  s := (d.localClusterFamily rho).s c
  positive_s := d.O.clusterMultiplicity_pos rho ((d.localClusterLabels rho).symm c)
  r j := d.O.ramificationOrder rho (d.localFactorIndex rho c j)
  u j := d.thetaOrder rho (d.localFactorIndex rho c j)
  v j := d.xiOrder rho (d.localFactorIndex rho c j)
  positive_r j := d.O.ramificationOrder_pos rho (d.localFactorIndex rho c j)
  degree_split j := by
    change d.thetaOrder rho (d.localFactorIndex rho c j)+
        d.xiOrder rho (d.localFactorIndex rho c j)=
      d.O.ramificationOrder rho (d.localFactorIndex rho c j)*
        d.O.clusterMultiplicity rho ((d.localClusterLabels rho).symm c)
    rw [←d.localFactorIndex_cluster rho c j]
    exact d.local_exponent_balance rho (d.localFactorIndex rho c j)
  beta j := d.beta (d.localFactorIndex rho c j)
  allowed_weights := ⟨isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
    d.localFactor_subset_units rho c⟩
  phi j := MvPolynomial.X j^d.O.ramificationOrder rho (d.localFactorIndex rho c j)
  a j := MvPolynomial.X j^d.thetaOrder rho (d.localFactorIndex rho c j)
  b j := MvPolynomial.X j^d.xiOrder rho (d.localFactorIndex rho c j)
  highest_phi j := highestPower_X_pow _ j _
  highest_a j := highestPower_X_pow _ j _
  highest_b j := highestPower_X_pow _ j _

local instance FermionLocalPairedFactors_factorOddOrder :
    LinearOrder (d.LocalFactorIndex rho c⊕d.LocalFactorIndex rho c) := finiteIndexLinearOrder _

local instance FermionLocalPairedFactors_originalOddOrder :
    LinearOrder (Fin (Fintype.card (d.LocalFactorIndex rho c))⊕
      Fin (Fintype.card (d.LocalFactorIndex rho c))) := finiteIndexLinearOrder _

/-- Each genuine tensor factor is an original homogeneous paired quotient,
with the exact inherited weights and root multiplicities. -/
def localFactorEquivPaired :
    ((d.localClusterFamily rho).factor c).Carrier ≃ₐ[F]
      PairedQuotient (d.localFactorPairedData rho c).beta
        (d.localFactorPairedData rho c).phi
        (d.localFactorPairedData rho c).a
        (d.localFactorPairedData rho c).b := by
  let p := d.localFactorPairedData rho c
  let e := singleClusterFinParameterEquiv
    ((d.localClusterFamily rho).beta c) ((d.localClusterFamily rho).r c)
    ((d.localClusterFamily rho).s c) ((d.localClusterFamily rho).u c)
    ((d.localClusterFamily rho).v c)
  exact e.algEquiv.trans
    (pairedPowerEquivSingleCluster p.beta p.allowed_weights.2 p.r p.positive_r
      p.s p.positive_s p.u p.v p.degree_split).symm

end SeparatedPairedData
end PaperVerification.Fermion

