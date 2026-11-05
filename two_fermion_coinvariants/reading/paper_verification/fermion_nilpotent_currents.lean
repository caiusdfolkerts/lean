module

public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.Ring

/-!
# Exact current equations at nilpotent separated nodes

Chinese remainder interpolation acts on the full nilpotent jets. It therefore
separates clusters and removes the clusterwise invertible prefactors in every
Artinian coefficient algebra, including nonreduced algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open Polynomial
open scoped Classical BigOperators
variable {F A ι κ M : Type*} [Field F] [CommRing A] [Algebra F A]
  [Fintype ι] [Fintype κ]
  [AddCommGroup M] [Module A M]

theorem finite_jet_interpolation (center : κ → F) (hc : Function.Injective center)
    (N : κ → ℕ) (u : κ → Polynomial F) :
    ∃ p : Polynomial F,∀ c,(X-C (center c))^(N c)∣p-u c := by
  let J : κ → Ideal (Polynomial F) := fun c ↦ Ideal.span {(X-C (center c))^(N c)}
  have hJ : Pairwise (fun c d ↦ IsCoprime (J c) (J d)) := by
    intro c d hcd
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (hc.ne hcd)))).pow
  obtain ⟨p,hp⟩ := Ideal.exists_forall_sub_mem_ideal hJ u
  exact ⟨p,fun c ↦ Ideal.mem_span_singleton.mp (hp c)⟩

theorem jet_divisibility_evaluation {c : F} {N : ℕ} {p q : Polynomial F}
    (hp : (X-C c)^N∣p-q) (x : A) (hx : (x-algebraMap F A c)^N=0) :
    Polynomial.aeval x p=Polynomial.aeval x q := by
  obtain ⟨g,hg⟩ := hp
  have he := congrArg (Polynomial.aeval x) hg
  apply sub_eq_zero.mp
  simpa only [map_sub,map_mul,map_pow,Polynomial.aeval_X,Polynomial.aeval_C,
    hx,zero_mul] using he

theorem piecewise_polynomial_on_nodes (center : κ → F) (hc : Function.Injective center)
    (cluster : ι → κ) (node : ι → A) (N : κ → ℕ)
    (hN : ∀ i,(node i-algebraMap F A (center (cluster i)))^(N (cluster i))=0)
    (u : κ → Polynomial F) :
    ∃ p : Polynomial F,∀ i,Polynomial.aeval (node i) p=
      Polynomial.aeval (node i) (u (cluster i)) := by
  obtain ⟨p,hp⟩ := finite_jet_interpolation center hc N u
  exact ⟨p,fun i ↦ jet_divisibility_evaluation (hp (cluster i)) (node i) (hN i)⟩

theorem polynomial_current_of_moments (node : ι → A) (v : ι → M)
    (hm : ∀ k : ℕ,∑ i,node i^k • v i=0) (p : Polynomial F) :
    ∑ i,Polynomial.aeval (node i) p • v i=0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add,add_smul,Finset.sum_add_distrib,hp,hq,add_zero]
  | monomial k c =>
      simp only [Polynomial.aeval_monomial,mul_smul,←Finset.smul_sum,hm,smul_zero]

theorem moments_polynomial_multiplier (node : ι → A) (v : ι → M)
    (hm : ∀ k : ℕ,∑ i,node i^k • v i=0) (p : Polynomial F) :
    ∀ k : ℕ,∑ i,node i^k • (Polynomial.aeval (node i) p • v i)=0 := by
  intro k
  calc
    (∑ i,node i^k • (Polynomial.aeval (node i) p • v i))=
        ∑ i,Polynomial.aeval (node i) (X^k*p) • v i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Polynomial.aeval_mul,Polynomial.aeval_X_pow,mul_smul]
    _=0 := polynomial_current_of_moments node v hm (X^k*p)

theorem nilpotent_cluster_current_equivalence
    (center : κ → F) (hc : Function.Injective center)
    (cluster : ι → κ) (node : ι → A) (N : κ → ℕ)
    (hN : ∀ i,(node i-algebraMap F A (center (cluster i)))^(N (cluster i))=0)
    (v : ι → M) :
    (∀ k : ℕ,∑ i,node i^k • v i=0) ↔
      ∀ c k,(∑ i,if cluster i=c then
        (node i-algebraMap F A (center c))^k • v i else 0)=0 := by
  constructor
  · intro hm c k
    obtain ⟨p,hp⟩ := piecewise_polynomial_on_nodes center hc cluster node N hN
      (fun d ↦ if d=c then (X-C (center c))^k else 0)
    have he := polynomial_current_of_moments node v hm p
    have hterm : ∀ i,Polynomial.aeval (node i) p • v i=
        if cluster i=c then (node i-algebraMap F A (center c))^k • v i else 0 := by
      intro i
      rw [hp i]
      by_cases hi : cluster i=c
      · simp only [hi,if_true,map_pow,map_sub,Polynomial.aeval_X,Polynomial.aeval_C]
      · simp only [hi,if_false,map_zero,zero_smul]
    simpa only [hterm] using he
  · intro hm k
    have hc0 : ∀ c,∑ i,node i^k • (if cluster i=c then v i else 0)=0 := by
      intro c
      have hm' : ∀ j : ℕ,∑ i,(node i-algebraMap F A (center c))^j •
          (if cluster i=c then v i else 0)=0 := by
        intro j
        simpa only [smul_ite,smul_zero] using hm c j
      have he := polynomial_current_of_moments
        (fun i ↦ node i-algebraMap F A (center c))
        (fun i ↦ if cluster i=c then v i else 0) hm' ((X+C (center c))^k)
      simpa only [map_pow,map_add,Polynomial.aeval_X,Polynomial.aeval_C,
        sub_add_cancel] using he
    have he : ∑ c : κ,∑ i,node i^k • (if cluster i=c then v i else 0)=0 :=
      Finset.sum_eq_zero fun c hc ↦ hc0 c
    simpa only [Finset.sum_comm,smul_ite,smul_zero,Finset.sum_ite_eq,
      Finset.mem_univ,if_true] using he

/-- An explicit Bezout identity supplies the inverse of a polynomial on
every nilpotent jet at a point where its constant value is nonzero. -/
theorem inverse_polynomial_jet (p : Polynomial F) (c : F) (hp : p.eval c≠0)
    (N : ℕ) :
    ∃ u v : Polynomial F,u*p+v*(X-C c)^N=1 := by
  have hd : X-C c∣p-C (p.eval c) :=
    Polynomial.dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot])
  obtain ⟨g,hg⟩ := hd
  have hcop : IsCoprime p (X-C c) := by
    refine ⟨C ((p.eval c)⁻¹),-C ((p.eval c)⁻¹)*g,?_⟩
    calc
      C ((p.eval c)⁻¹)*p+(-C ((p.eval c)⁻¹)*g)*(X-C c) =
          C ((p.eval c)⁻¹)*(p-(X-C c)*g) := by ring
      _=C ((p.eval c)⁻¹)*C (p.eval c) := by rw [←hg]; ring
      _=1 := by rw [←C_mul,inv_mul_cancel₀ hp,C_1]
  exact hcop.pow_right

theorem piecewise_inverse_polynomial_on_nodes
    (center : κ → F) (hc : Function.Injective center)
    (cluster : ι → κ) (node : ι → A) (N : κ → ℕ)
    (hN : ∀ i,(node i-algebraMap F A (center (cluster i)))^(N (cluster i))=0)
    (u : κ → Polynomial F) (hu : ∀ c,(u c).eval (center c)≠0) :
    ∃ p : Polynomial F,∀ i,Polynomial.aeval (node i) p*
      Polynomial.aeval (node i) (u (cluster i))=1 := by
  choose inv rest hrest using fun c ↦ inverse_polynomial_jet (u c) (center c) (hu c) (N c)
  obtain ⟨p,hp⟩ := piecewise_polynomial_on_nodes center hc cluster node N hN inv
  refine ⟨p,fun i ↦ ?_⟩
  rw [hp i]
  have he := congrArg (Polynomial.aeval (node i)) (hrest (cluster i))
  simpa only [map_add,map_mul,map_pow,map_sub,map_one,Polynomial.aeval_X,
    Polynomial.aeval_C,hN i,mul_zero,add_zero] using he

/-- Clusterwise invertible prefactors do not change the full moment
relations. Both implications use actual polynomial current combinations. -/
theorem nilpotent_moments_unit_cluster_equivalence
    (center : κ → F) (hc : Function.Injective center)
    (cluster : ι → κ) (node : ι → A) (N : κ → ℕ)
    (hN : ∀ i,(node i-algebraMap F A (center (cluster i)))^(N (cluster i))=0)
    (u : κ → Polynomial F) (hu : ∀ c,(u c).eval (center c)≠0) (v : ι → M) :
    (∀ k : ℕ,∑ i,node i^k • v i=0) ↔
      ∀ k : ℕ,∑ i,node i^k • (Polynomial.aeval (node i) (u (cluster i)) • v i)=0 := by
  obtain ⟨p,hp⟩ := piecewise_polynomial_on_nodes center hc cluster node N hN u
  obtain ⟨q,hq⟩ := piecewise_inverse_polynomial_on_nodes center hc cluster node N hN u hu
  constructor
  · intro hm
    simpa only [hp] using moments_polynomial_multiplier node v hm p
  · intro hm
    have he := moments_polynomial_multiplier node
      (fun i ↦ Polynomial.aeval (node i) (u (cluster i)) • v i) hm q
    simpa only [←mul_smul,hq,one_smul] using he

end PaperVerification.Fermion
