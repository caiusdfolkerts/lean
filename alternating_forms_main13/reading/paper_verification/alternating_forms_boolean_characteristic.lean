module

public import PaperVerification.AlternatingFormsBoolean
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Data.Finset.Image
import Lean.Elab.Tactic.Omega

/-!
# Boolean inclusion in the exact characteristic range

The same literal inverse remains valid whenever its factorial denominator
is nonzero. Restriction to central subuniverses then proves injectivity on
every lower Boolean rank, which is the injectivity needed in Theorem 7.2.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K : Type*} [Field K]

theorem inverseCoefficient_last_of_factorial (n : ℕ)
    (hfac : ((n + 1).factorial : K) ≠ 0) :
    (n + 1 : K) * inverseCoefficient n n = 1 := by
  have hprod : (n + 1 : K) * (n.factorial : K) ≠ 0 := by
    simpa only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hfac
  have hn := left_ne_zero_of_mul hprod
  have hf := right_ne_zero_of_mul hprod
  simp only [inverseCoefficient, Nat.sub_self, pow_zero, one_mul,
    Nat.factorial_zero, Nat.cast_one, mul_one, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp

theorem inverseCoefficient_recurrence_any_characteristic (n j : ℕ) (hj : j < n) :
    (j + 1 : K) * inverseCoefficient n j +
      (n - j : ℕ) * inverseCoefficient n (j + 1) = 0 := by
  have hsub : n - j = n - (j + 1) + 1 := by omega
  have hpow : (-1 : K) ^ (n - j) = -((-1 : K) ^ (n - (j + 1))) := by
    rw [hsub, pow_succ]
    ring
  have hfact : ((n - j).factorial : K) =
      (n - j : ℕ) * ((n - (j + 1)).factorial : K) := by
    conv_lhs => rw [hsub, Nat.factorial_succ]
    rw [Nat.cast_mul, ← hsub]
  have hjfact : ((j + 1).factorial : K) = (j + 1 : K) * (j.factorial : K) := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [inverseCoefficient, hpow, hfact, hjfact]
  ring

section CentralRank

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

theorem inclusion_inverse_row_of_factorial (n : ℕ)
    (hfac : ((n + 1).factorial : K) ≠ 0) (hι : Fintype.card ι = 2 * n + 1)
    (U P : Finset ι) (hU : U.card = n + 1) (hP : P.card = n + 1) :
    (∑ a ∈ U, inverseCoefficient (K := K) n ((U.erase a ∩ P).card)) =
      if U = P then 1 else 0 := by
  classical
  by_cases hUP : U = P
  · subst P
    rw [if_pos rfl]
    have he (a : ι) (ha : a ∈ U) : (U.erase a ∩ U).card = n := by
      rw [Finset.inter_eq_left.mpr (Finset.erase_subset a U), Finset.card_erase_of_mem ha,
        hU]
      omega
    rw [Finset.sum_congr rfl (fun a ha => congrArg (inverseCoefficient (K := K) n)
      (he a ha))]
    simpa [hU, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using
      (inverseCoefficient_last_of_factorial (K := K) n hfac)
  · rw [if_neg hUP]
    let q := (U ∩ P).card
    have hqpos : 0 < q := by
      have hc := Finset.card_union_add_card_inter U P
      have hu : (U ∪ P).card ≤ Fintype.card ι := Finset.card_le_univ _
      dsimp [q]
      omega
    have hqle : q ≤ n + 1 := by
      dsimp [q]
      calc
        (U ∩ P).card ≤ U.card := Finset.card_le_card Finset.inter_subset_left
        _ = n + 1 := hU
    have hqlt : q < n + 1 := by
      by_contra hn
      have hq : q = n + 1 := by omega
      have hu : U ∩ P = U := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_left (by simpa [q, hU] using hq.ge)
      have hp : U ∩ P = P := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_right (by simpa [q, hP] using hq.ge)
      exact hUP (hu.symm.trans hp)
    have hinter (a : ι) (ha : a ∈ U ∩ P) : (U.erase a ∩ P).card = q - 1 := by
      rw [Finset.erase_inter, Finset.card_erase_of_mem ha]
    have hdiff (a : ι) (ha : a ∈ U \ P) : (U.erase a ∩ P).card = q := by
      rw [Finset.erase_inter, Finset.erase_eq_of_notMem]
      exact fun h => (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp h).2
    rw [← Finset.sum_inter_add_sum_sdiff U P
      (fun a => inverseCoefficient (K := K) n ((U.erase a ∩ P).card))]
    have hc : (U \ P).card = n + 1 - q := by
      rw [Finset.card_sdiff, Finset.inter_comm, hU]
    have hs₁ : (∑ a ∈ U ∩ P, inverseCoefficient (K := K) n ((U.erase a ∩ P).card)) =
        (q : K) * inverseCoefficient n (q - 1) := by
      rw [Finset.sum_congr rfl (fun a ha => congrArg (inverseCoefficient (K := K) n)
        (hinter a ha)), Finset.sum_const, nsmul_eq_mul]
    have hs₂ : (∑ a ∈ U \ P, inverseCoefficient (K := K) n ((U.erase a ∩ P).card)) =
        (n + 1 - q : ℕ) * inverseCoefficient n q := by
      rw [Finset.sum_congr rfl (fun a ha => congrArg (inverseCoefficient (K := K) n)
        (hdiff a ha)), Finset.sum_const, nsmul_eq_mul, hc]
    rw [hs₁, hs₂]
    have hpred : q - 1 + 1 = q := by omega
    have hsub : n - (q - 1) = n + 1 - q := by omega
    have hcast : (q - 1 : ℕ) + (1 : K) = (q : K) := by
      simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun m : ℕ => (m : K)) hpred
    simpa only [hpred, hsub, hcast] using
      (inverseCoefficient_recurrence_any_characteristic (K := K) n (q - 1) (by omega))


theorem inclusionOperator_inclusionInverse_of_factorial (n : ℕ)
    (hfac : ((n + 1).factorial : K) ≠ 0)
    (hι : Fintype.card ι = 2 * n + 1) (v : FixedSubsets ι (n + 1) → K) :
    inclusionOperator n (inclusionInverse n v) = v := by
  classical
  ext U
  change (∑ a : U.1, ∑ P : FixedSubsets ι (n + 1),
    v P * inverseCoefficient n ((U.1.erase a) ∩ P.1).card) = v U
  have hrow (P : FixedSubsets ι (n + 1)) :
      (∑ a : U.1, inverseCoefficient (K := K) n ((U.1.erase a) ∩ P.1).card) =
        if U = P then 1 else 0 := by
    rw [Finset.sum_coe_sort U.1
      (fun a : ι => inverseCoefficient (K := K) n ((U.1.erase a) ∩ P.1).card)]
    simpa only [Subtype.ext_iff] using
      (inclusion_inverse_row_of_factorial (K := K) n hfac hι U.1 P.1 U.2 P.2)
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hrow]
  simp [mul_ite]


theorem inclusionOperator_bijective_of_factorial (n : ℕ)
    (hfac : ((n + 1).factorial : K) ≠ 0)
    (hι : Fintype.card ι = 2 * n + 1) :
    Function.Bijective (inclusionOperator (K := K) (ι := ι) n) := by
  have hs : Function.Surjective (inclusionOperator (K := K) (ι := ι) n) :=
    fun v => ⟨inclusionInverse n v,
      inclusionOperator_inclusionInverse_of_factorial n hfac hι v⟩
  have hc : Fintype.card (FixedSubsets ι n) =
      Fintype.card (FixedSubsets ι (n + 1)) := by
    simp only [FixedSubsets, Fintype.card_finset_len]
    have hsub : Fintype.card ι - n = n + 1 := by omega
    rw [← hsub, Nat.choose_symm (by omega : n ≤ Fintype.card ι)]
  have hd : Module.finrank K (FixedSubsets ι n → K) =
      Module.finrank K (FixedSubsets ι (n + 1) → K) := by
    simpa only [Module.finrank_fintype_fun_eq_card] using hc
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hs, hs⟩

end CentralRank

section Restriction

variable {ι κ : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq κ] [Fintype κ]

def fixedSubsetMap (e : ι ↪ κ) {n : ℕ} (T : FixedSubsets ι n) : FixedSubsets κ n :=
  ⟨T.1.map e, by rw [Finset.card_map, T.2]⟩

/-- Restricting coefficients to a smaller universe commutes with upward
inclusion: an output subset receives contributions only from its own faces. -/
theorem inclusionOperator_restrict (e : ι ↪ κ) (n : ℕ)
    (v : FixedSubsets κ n → K) (U : FixedSubsets ι (n + 1)) :
    inclusionOperator n (fun T => v (fixedSubsetMap e T)) U =
      inclusionOperator n v (fixedSubsetMap e U) := by
  classical
  change (∑ a : U.1, v (fixedSubsetMap e (eraseSubset U a))) =
    ∑ a : U.1.map e, v (eraseSubset (fixedSubsetMap e U) a)
  apply Fintype.sum_equiv (U.1.equivMap e)
  intro a
  congr 1
  apply Subtype.ext
  change (U.1.erase a.1).map e = (U.1.map e).erase (e a.1)
  exact Finset.map_erase e U.1 a.1

/-- The full lower-rank Boolean injectivity theorem.  No bound on the
ambient universe above `2n+1` is imposed. -/
theorem inclusionOperator_injective_of_card_le (n : ℕ)
    (hfac : ((n + 1).factorial : K) ≠ 0)
    (hι : 2 * n + 1 ≤ Fintype.card ι) :
    Function.Injective (inclusionOperator (K := K) (ι := ι) n) := by
  classical
  intro v w hvw
  funext T
  obtain ⟨S, hTS, _, hS⟩ := Finset.exists_subsuperset_card_eq
    (T.1.subset_univ) (by rw [T.2]; omega : T.1.card ≤ 2 * n + 1)
    (by simpa only [Finset.card_univ] using hι)
  let e : S ↪ ι := Function.Embedding.subtype _
  have hrestrict :
      inclusionOperator n (fun U : FixedSubsets S n => v (fixedSubsetMap e U)) =
        inclusionOperator n (fun U : FixedSubsets S n => w (fixedSubsetMap e U)) := by
    ext U
    rw [inclusionOperator_restrict, inclusionOperator_restrict, hvw]
  have heq := (inclusionOperator_bijective_of_factorial (K := K) (ι := S) n hfac
    (by simpa only [Fintype.card_coe] using hS)).injective hrestrict
  let T' : FixedSubsets S n :=
    ⟨T.1.subtype (fun i => i ∈ S), by
      rw [Finset.card_subtype, Finset.filter_eq_self.mpr hTS, T.2]⟩
  have hmap : fixedSubsetMap e T' = T := by
    apply Subtype.ext
    exact Finset.subtype_map_of_mem hTS
  have hx := congrFun heq T'
  simpa only [hmap] using hx

end Restriction

/-- The exact factorial nonvanishing required above follows from `n+1<p`;
there is no unnecessary invertibility condition on the ambient cardinality. -/
theorem inclusionOperator_injective_charP {ι : Type*} [DecidableEq ι] [Fintype ι]
    (p n : ℕ) [Fact p.Prime] [CharP K p] (hn : n + 1 < p)
    (hι : 2 * n + 1 ≤ Fintype.card ι) :
    Function.Injective (inclusionOperator (K := K) (ι := ι) n) := by
  apply inclusionOperator_injective_of_card_le n _ hι
  intro hz
  exact (not_le_of_gt hn) ((Fact.out : p.Prime).dvd_factorial.mp
    ((CharP.cast_eq_zero_iff K p (n+1).factorial).mp hz))

end PaperVerification.AlternatingForms
