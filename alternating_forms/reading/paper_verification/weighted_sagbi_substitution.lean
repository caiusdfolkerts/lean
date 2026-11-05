module

public import PaperVerification.WeightedSagbiCore

/-!
# Weighted top parts of the actual polynomial substitution

Products of the specified greatest monomials give the greatest monomial of
each substituted source monomial. Finite coefficient expansion then proves
the bounded top-component and graded monomial-substitution identities used
by the exact initial-kernel criterion.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.WeightedSagbi

open MvPolynomial
open scoped BigOperators
open AlternatingForms WeightedInitialFiber

variable {K σ τ : Type*} [Field K]

def exponentMap (a : σ → τ →₀ ℕ) : (σ →₀ ℕ) →ₗ[ℕ] (τ →₀ ℕ) :=
  Finsupp.linearCombination ℕ a

def inducedWeight (u : τ → ℕ) (a : σ → τ →₀ ℕ) : σ → ℕ :=
  fun i => Finsupp.weight u (a i)

theorem exponentMap_weight (u : τ → ℕ) (a : σ → τ →₀ ℕ) (m : σ →₀ ℕ) :
    Finsupp.weight u (exponentMap a m)=Finsupp.weight (inducedWeight u a) m := by
  change Finsupp.linearCombination ℕ u (Finsupp.linearCombination ℕ a m)=
    Finsupp.linearCombination ℕ (fun i => Finsupp.linearCombination ℕ u (a i)) m
  exact Finsupp.linearCombination_linearCombination ℕ u a m

def monomialSubstitution (a : σ → τ →₀ ℕ) :
    MvPolynomial σ K →ₐ[K] MvPolynomial τ K :=
  aeval (fun i => monomial (a i) 1)

theorem monomialSubstitution_monomial (a : σ → τ →₀ ℕ) (m : σ →₀ ℕ) (c : K) :
    monomialSubstitution a (monomial m c)=monomial (exponentMap a m) c := by
  classical
  simp only [monomialSubstitution,aeval_monomial,exponentMap,Finsupp.linearCombination_apply,
    Finsupp.prod,Finsupp.sum,monomial_pow,one_pow]
  rw [show (∏ i ∈ m.support,monomial (m i • a i) (1 : K))=
      monomial (∑ i ∈ m.support,m i • a i) 1 from by
    induction m.support using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
        rw [Finset.prod_insert hi,Finset.sum_insert hi,ih,monomial_mul,one_mul]]
  simp only [algebraMap_eq,C_mul_monomial,mul_one]

theorem substitution_monomial_weightMonic (u : τ → ℕ)
    (p : σ → MvPolynomial τ K) (a : σ → τ →₀ ℕ)
    (hp : ∀ i,IsWeightMonic (fun j => (u j : ℤ)) (p i) (a i)) (m : σ →₀ ℕ) :
    IsWeightMonic (fun j => (u j : ℤ)) (aeval (R := K) p (monomial m 1)) (exponentMap a m) := by
  classical
  rw [aeval_monomial,map_one,one_mul]
  exact isWeightMonic_prod m.support (fun i => p i ^ m i) (fun i => m i • a i)
    (fun i hi => (hp i).pow (m i))

theorem map_eq_coefficient_sum
    (f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K) (q : MvPolynomial σ K) :
    f q=∑ m ∈ q.support,q.coeff m • f (monomial m 1) := by
  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have he : monomial m (q.coeff m)=q.coeff m • (monomial m 1 : MvPolynomial σ K) := by
    simp only [smul_monomial,smul_eq_mul,mul_one]
  rw [he,map_smul]

theorem substitution_bound (u : τ → ℕ) (p : σ → MvPolynomial τ K)
    (a : σ → τ →₀ ℕ)
    (hp : ∀ i,IsWeightMonic (fun j => (u j : ℤ)) (p i) (a i))
    (q : MvPolynomial σ K) (d : ℕ) (hq : WeightBound (inducedWeight u a) d q) :
    WeightBound u d (aeval (R := K) p q) := by
  classical
  rw [map_eq_coefficient_sum]
  apply weightBound_sum
  intro m hm
  apply weightBound_smul
  have h := weightBound_of_weightMonic u _ _ (substitution_monomial_weightMonic u p a hp m)
  intro b hb
  exact (h b hb).trans (by
    rw [exponentMap_weight]
    exact hq m (mem_support_iff.mp hm))

theorem substitution_top (u : τ → ℕ) (p : σ → MvPolynomial τ K)
    (a : σ → τ →₀ ℕ)
    (hp : ∀ i,IsWeightMonic (fun j => (u j : ℤ)) (p i) (a i))
    (q : MvPolynomial σ K) (d : ℕ) (hq : WeightBound (inducedWeight u a) d q) :
    weightedHomogeneousComponent u d (aeval (R := K) p q)=
      monomialSubstitution a (weightedHomogeneousComponent (inducedWeight u a) d q) := by
  classical
  rw [map_eq_coefficient_sum (aeval (R := K) p) q]
  conv_rhs => rw [q.as_sum]
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro m hm
  have hmono := substitution_monomial_weightMonic u p a hp m
  have hw := hq m (mem_support_iff.mp hm)
  have hsource := isWeightedHomogeneous_monomial (inducedWeight u a) m (q.coeff m) rfl
  rw [weightedHomogeneousComponent_of_mem hsource]
  by_cases hd : d=Finsupp.weight (inducedWeight u a) m
  · rw [if_pos hd,monomialSubstitution_monomial,hd,←exponentMap_weight,
      component_of_weightMonic u _ _ hmono,smul_monomial,smul_eq_mul,mul_one]
  · rw [if_neg hd,map_zero]
    have hlt : weightedTotalDegree u (aeval (R := K) p (monomial m 1))<d := by
      exact (total_le_of_weightBound u _ _ (weightBound_of_weightMonic u _ _ hmono)).trans_lt
        (by rw [exponentMap_weight]; omega)
    rw [weightedHomogeneousComponent_eq_zero d _ hlt,smul_zero]

theorem monomialSubstitution_graded (u : τ → ℕ) (a : σ → τ →₀ ℕ)
    (q : MvPolynomial σ K) (d : ℕ) :
    weightedHomogeneousComponent u d (monomialSubstitution a q)=
      monomialSubstitution a (weightedHomogeneousComponent (inducedWeight u a) d q) := by
  classical
  induction q using MvPolynomial.induction_on' with
  | add q r hq hr => simp only [map_add,hq,hr]
  | monomial m c =>
      rw [monomialSubstitution_monomial,
        weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial u _ c rfl),
        weightedHomogeneousComponent_of_mem
          (isWeightedHomogeneous_monomial (inducedWeight u a) m c rfl),exponentMap_weight]
      split_ifs <;> simp only [monomialSubstitution_monomial,map_zero]

end PaperVerification.WeightedSagbi
