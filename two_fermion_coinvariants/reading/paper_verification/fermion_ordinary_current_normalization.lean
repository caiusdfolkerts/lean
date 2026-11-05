module

public import PaperVerification.FermionNilpotentCurrents
public import PaperVerification.FermionRamification

/-!
# Exact normalization of the ordinary separated moment equations

The equivalence is an equality of all current relations inside the actual
coefficient algebra. It retains the nilpotent structure and removes the
root cofactor only by a polynomial inverse on all finite jets.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open Polynomial
open scoped Classical BigOperators

variable {F A ι κ M : Type*} [Field F] [CommRing A] [Algebra F A]
  [Fintype ι] [Fintype κ] [AddCommMonoid M]

theorem sum_cluster_subtype (cluster : ι → κ) (c : κ) (f : ι → M) :
    (∑ i : {i : ι // cluster i=c},f i.1)=
      ∑ i,if cluster i=c then f i else 0 := by
  simpa only [Finset.sum_filter] using
    (Finset.sum_subtype (Finset.univ.filter (fun i ↦ cluster i=c))
      (by intro i; simp) f).symm

theorem separated_ordinary_cluster_equivalence
    (G : Polynomial F) (hG : G≠0)
    (beta : ι → F) (center : κ → F) (hc : Function.Injective center)
    (cluster : ι → κ) (node z : ι → A) (r : ι → ℕ)
    (hz : ∀ i,z i^r i=node i-algebraMap F A (center (cluster i)))
    (N : κ → ℕ)
    (hN : ∀ i,(node i-algebraMap F A (center (cluster i)))^(N (cluster i))=0) :
    (∀ k : ℕ,∑ i,algebraMap F A (beta i)*node i^k*Polynomial.aeval (node i) G=0) ↔
      ∀ c k,∑ i : {i : ι // cluster i=c},
        algebraMap F A (beta i.1)*
          z i.1^(r i.1*(G.rootMultiplicity (center c)+k))=0 := by
  let s : κ → ℕ := fun c ↦ G.rootMultiplicity (center c)
  let u : κ → Polynomial F := fun c ↦ rootCofactor G (center c)
  let v : ι → A := fun i ↦ algebraMap F A (beta i)*z i^(r i*s (cluster i))
  have hu : ∀ c,(u c).eval (center c)≠0 :=
    fun c ↦ rootCofactor_eval_ne_zero G hG (center c)
  have hvalue : ∀ i,Polynomial.aeval (node i) G=
      z i^(r i*s (cluster i))*Polynomial.aeval (node i) (u (cluster i)) := by
    intro i
    have he := congrArg (Polynomial.aeval (node i))
      (rootCofactor_factorization G (center (cluster i)))
    have he' := he.symm
    simpa only [map_mul,map_pow,map_sub,Polynomial.aeval_X,Polynomial.aeval_C,
      ←hz i,←pow_mul,s,u] using he'
  have hsum : ∀ k,
      (∑ i,node i^k • (Polynomial.aeval (node i) (u (cluster i)) • v i)) =
      ∑ i,algebraMap F A (beta i)*node i^k*Polynomial.aeval (node i) G := by
    intro k
    apply Finset.sum_congr rfl
    intro i hi
    rw [hvalue i]
    simp only [v,smul_eq_mul]
    ring
  have hcluster : ∀ c k,
      (∑ i,if cluster i=c then
        (node i-algebraMap F A (center c))^k • v i else 0) =
      ∑ i : {i : ι // cluster i=c},
        algebraMap F A (beta i.1)*z i.1^(r i.1*(s c+k)) := by
    intro c k
    rw [sum_cluster_subtype cluster c
      (fun i : ι ↦ algebraMap F A (beta i)*z i^(r i*(s c+k)))]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hic : cluster i=c
    · simp only [hic,if_true,v,smul_eq_mul]
      have hzi := hz i
      rw [hic] at hzi
      rw [←hzi]
      calc
        (z i^r i)^k*(algebraMap F A (beta i)*z i^(r i*s c)) =
            algebraMap F A (beta i)*(z i^(r i*k)*z i^(r i*s c)) := by
          rw [←pow_mul]
          ring
        _=algebraMap F A (beta i)*z i^(r i*(s c+k)) := by
          rw [←pow_add,←Nat.mul_add,Nat.add_comm k (s c)]
    · simp only [hic,if_false]
  have he :=
    (nilpotent_moments_unit_cluster_equivalence center hc cluster node N hN u hu v).symm.trans
      (nilpotent_cluster_current_equivalence center hc cluster node N hN v)
  simpa only [hsum,hcluster,s] using he

end PaperVerification.Fermion
