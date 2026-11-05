module

public import PaperVerification.FermionOddPresentation

/-!
# The actual local odd normalization isomorphism

Both maps are induced on genuine two-sided quotient rings by inverse diagonal
exterior automorphisms. All three relation families, including the mixed
family, are checked using the full nilpotent-jet current equivalence.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.Fermion

variable {F A B ι κ : Type*} [Field F] [CommRing A] [Algebra F A]
  [Ring B] [Algebra A B] [Fintype ι] [Fintype κ]

variable (G : Polynomial F) (hG : G≠0)
  (center : κ → F) (hc : Function.Injective center)
  (cluster : ι → κ) (node z beta a b : ι → A) (r u v : ι → ℕ)
  (hz : ∀ i,z i^r i=node i-algebraMap F A (center (cluster i)))
  (N : κ → ℕ)
  (hN : ∀ i,(node i-algebraMap F A (center (cluster i)))^(N (cluster i))=0)
  (unitA unitB : ι → Aˣ)
  (ha : ∀ i,a i=z i^u i*(unitA i : A))
  (hb : ∀ i,b i=z i^v i*(unitB i : A))
  (hAB : ∀ i,(unitA i : A)*(unitB i : A)=
    Polynomial.aeval (node i) (rootCofactor G (center (cluster i))))

include hG hc hz hN ha hb hAB in
theorem odd_normalization_kills_iff (q : ClusterExterior A ι →ₐ[A] B) :
    (∀ x∈separatedOddIdeal node beta a b,q x=0) ↔
      ∀ x∈clusterOddIdeal cluster z beta r u v,
        (q.comp (pairedOddUnitEquiv unitA unitB).toAlgHom) x=0 := by
  rw [separatedOddIdeal_killed_iff,clusterOddIdeal_killed_iff]
  simpa only [AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,
    pairedOddUnitEquiv_theta,pairedOddUnitEquiv_xi,map_smul,
    smul_mul_smul_comm,mul_comm] using
    separated_odd_cluster_equivalence G hG center hc cluster node z beta a b r u v
      hz N hN unitA unitB ha hb hAB
      (fun i ↦ q (clusterTheta i)) (fun i ↦ q (clusterXi i))
      (fun i ↦ q (clusterTheta i)*q (clusterXi i))

/-- The isomorphism sends the old odd generators to the inversely rescaled
normalized generators and fixes the entire actual coefficient algebra. -/
def oddNormalizationEquiv :
    SeparatedOddQuotient node beta a b ≃ₐ[A]
      ClusterOddQuotient cluster z beta r u v := by
  let I := separatedOddIdeal node beta a b
  let J := clusterOddIdeal cluster z beta r u v
  let qI := I.ringCon.mkₐ A
  let qJ := J.ringCon.mkₐ A
  let e := pairedOddUnitEquiv unitA unitB
  let f : ClusterExterior A ι →ₐ[A] J.ringCon.Quotient := qJ.comp e.symm.toAlgHom
  have hf : ∀ x∈I,f x=0 := by
    apply (odd_normalization_kills_iff G hG center hc cluster node z beta a b r u v
      hz N hN unitA unitB ha hb hAB f).mpr
    intro x hx
    change qJ (e.symm (e x))=0
    rw [AlgEquiv.symm_apply_apply]
    exact quotientMk_eq_zero_of_mem J x hx
  let g : ClusterExterior A ι →ₐ[A] I.ringCon.Quotient := qI.comp e.toAlgHom
  have hg : ∀ x∈J,g x=0 :=
    (odd_normalization_kills_iff G hG center hc cluster node z beta a b r u v
      hz N hN unitA unitB ha hb hAB qI).mp
        (fun x hx ↦ quotientMk_eq_zero_of_mem I x hx)
  let fbar : I.ringCon.Quotient →ₐ[A] J.ringCon.Quotient :=
    I.ringCon.liftₐ f (ringCon_le_ker_of_kills I f hf)
  let gbar : J.ringCon.Quotient →ₐ[A] I.ringCon.Quotient :=
    J.ringCon.liftₐ g (ringCon_le_ker_of_kills J g hg)
  exact AlgEquiv.ofAlgHom fbar gbar
    (by
      apply RingCon.Quotient.hom_extₐ
      apply AlgHom.ext
      intro x
      change qJ (e.symm (e x))=qJ x
      rw [AlgEquiv.symm_apply_apply])
    (by
      apply RingCon.Quotient.hom_extₐ
      apply AlgHom.ext
      intro x
      change qI (e (e.symm x))=qI x
      rw [AlgEquiv.apply_symm_apply])

@[simp] theorem oddNormalizationEquiv_mk (x : ClusterExterior A ι) :
    oddNormalizationEquiv G hG center hc cluster node z beta a b r u v
      hz N hN unitA unitB ha hb hAB
      ((separatedOddIdeal node beta a b).ringCon.mkₐ A x)=
    (clusterOddIdeal cluster z beta r u v).ringCon.mkₐ A
      ((pairedOddUnitEquiv unitA unitB).symm x) := rfl

@[simp] theorem oddNormalizationEquiv_theta (i : ι) :
    oddNormalizationEquiv G hG center hc cluster node z beta a b r u v
      hz N hN unitA unitB ha hb hAB
      ((separatedOddIdeal node beta a b).ringCon.mkₐ A (clusterTheta i))=
    (↑((unitB i)⁻¹) : A) •
      (clusterOddIdeal cluster z beta r u v).ringCon.mkₐ A (clusterTheta i) := by
  rw [oddNormalizationEquiv_mk,pairedOddUnitEquiv_symm_theta,map_smul]

@[simp] theorem oddNormalizationEquiv_xi (i : ι) :
    oddNormalizationEquiv G hG center hc cluster node z beta a b r u v
      hz N hN unitA unitB ha hb hAB
      ((separatedOddIdeal node beta a b).ringCon.mkₐ A (clusterXi i))=
    (↑((unitA i)⁻¹) : A) •
      (clusterOddIdeal cluster z beta r u v).ringCon.mkₐ A (clusterXi i) := by
  rw [oddNormalizationEquiv_mk,pairedOddUnitEquiv_symm_xi,map_smul]

end PaperVerification.Fermion
