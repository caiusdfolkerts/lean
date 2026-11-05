module

public import PaperVerification.FermionOrdinaryCurrentNormalization

/-!
# Exact normalization of all three odd current families

This module proves the simultaneous theta, xi, and mixed-current equivalence
in an arbitrary module over the actual coefficient algebra. Applying it to
genuine exterior quotients proves ideal descent of the diagonal odd change
of variables, including the mixed relation.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open scoped Classical BigOperators

variable {F A ι κ M : Type*} [Field F] [CommRing A] [Algebra F A]
  [Fintype ι] [Fintype κ] [AddCommGroup M] [Module A M]

theorem cluster_power_current_equivalence
    (center : κ → F) (hc : Function.Injective center)
    (cluster : ι → κ) (node z : ι → A) (r : ι → ℕ)
    (hz : ∀ i,z i^r i=node i-algebraMap F A (center (cluster i)))
    (N : κ → ℕ)
    (hN : ∀ i,(node i-algebraMap F A (center (cluster i)))^(N (cluster i))=0)
    (v : ι → M) :
    (∀ k : ℕ,∑ i,node i^k • v i=0) ↔
      ∀ c k,∑ i : {i : ι // cluster i=c},z i.1^(r i.1*k) • v i.1=0 := by
  have he := nilpotent_cluster_current_equivalence center hc cluster node N hN v
  have hs : ∀ c k,
      (∑ i,if cluster i=c then
        (node i-algebraMap F A (center c))^k • v i else 0)=
      ∑ i : {i : ι // cluster i=c},z i.1^(r i.1*k) • v i.1 := by
    intro c k
    rw [sum_cluster_subtype cluster c (fun i : ι ↦ z i^(r i*k) • v i)]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hic : cluster i=c
    · simp only [hic,if_true]
      have hzi := hz i
      rw [hic] at hzi
      rw [←hzi,pow_mul]
    · simp only [hic,if_false]
  simpa only [hs] using he

def HasSeparatedOddCurrents (node beta a b : ι → A)
    (theta xi mixed : ι → M) : Prop :=
  (∀ k : ℕ,∑ i,node i^k • (b i • theta i)=0) ∧
  (∀ k : ℕ,∑ i,node i^k • ((beta i*a i) • xi i)=0) ∧
  (∀ k : ℕ,∑ i,node i^k • mixed i=0)

def HasClusterOddCurrents (cluster : ι → κ) (z beta : ι → A)
    (r u v : ι → ℕ) (theta xi mixed : ι → M) : Prop :=
  (∀ c k,∑ i : {i : ι // cluster i=c},
    z i.1^(r i.1*k) • (z i.1^v i.1 • theta i.1)=0) ∧
  (∀ c k,∑ i : {i : ι // cluster i=c},
    z i.1^(r i.1*k) • ((beta i.1*z i.1^u i.1) • xi i.1)=0) ∧
  (∀ c k,∑ i : {i : ι // cluster i=c},
    z i.1^(r i.1*k) • mixed i.1=0)

/-- All three odd relation families transform simultaneously. The mixed
relation uses the exact product of the two residual units; it is not dropped
or replaced by a consequence valid only on reduced points. -/
theorem separated_odd_cluster_equivalence
    (G : Polynomial F) (hG : G≠0)
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
    (theta xi mixed : ι → M) :
    HasSeparatedOddCurrents node beta a b theta xi mixed ↔
      HasClusterOddCurrents cluster z beta r u v
        (fun i ↦ (unitB i : A) • theta i)
        (fun i ↦ (unitA i : A) • xi i)
        (fun i ↦ ((unitA i : A)*(unitB i : A)) • mixed i) := by
  have htheta := cluster_power_current_equivalence center hc cluster node z r hz N hN
    (fun i ↦ b i • theta i)
  have hxi := cluster_power_current_equivalence center hc cluster node z r hz N hN
    (fun i ↦ (beta i*a i) • xi i)
  have hu : ∀ c,(rootCofactor G (center c)).eval (center c)≠0 :=
    fun c ↦ rootCofactor_eval_ne_zero G hG (center c)
  have hmixed :=
    (nilpotent_moments_unit_cluster_equivalence center hc cluster node N hN
      (fun c ↦ rootCofactor G (center c)) hu mixed).trans
    (cluster_power_current_equivalence center hc cluster node z r hz N hN
      (fun i ↦ Polynomial.aeval (node i) (rootCofactor G (center (cluster i))) •
        mixed i))
  have hs : ∀ i,Polynomial.aeval (node i) (rootCofactor G (center (cluster i))) •
      mixed i=((unitA i : A)*(unitB i : A)) • mixed i := by
    intro i
    rw [←hAB i]
  change _ ∧ _ ∧ _ ↔ _ ∧ _ ∧ _
  apply and_congr
  · simpa only [hb,mul_smul] using htheta
  · apply and_congr
    · simpa only [ha,mul_assoc,mul_smul] using hxi
    · simpa only [hs] using hmixed

end PaperVerification.Fermion
