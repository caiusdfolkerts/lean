module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The Boolean inclusion inverse used in the odd-pencil straightening argument

This file proves the coefficient calculation in Lemma 3.1 of
`03_two_alternating_forms(6).pdf`.  The universe has cardinality `2r - 1`;
multiplication by the sum of the square-zero pair variables is the inclusion
operator from `(r - 1)`-subsets to `r`-subsets.  No cohomological assertions or
Hilbert-series assertions are assumed here.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-- The inverse coefficient, with `n = r - 1`.  This is the factorial form of
`(-1)^(r - 1 - j) / (r * choose (r - 1) j)`. -/
def inverseCoefficient (n j : ℕ) : K :=
  (-1 : K) ^ (n - j) * (j.factorial : K) * ((n - j).factorial : K) /
    ((n + 1).factorial : K)

/-- The factorial expression agrees with the binomial expression printed in
Lemma 3.1 throughout its full index range. -/
theorem inverseCoefficient_eq_binomial (n j : ℕ) (hj : j ≤ n) :
    inverseCoefficient (K := K) n j =
      (-1 : K) ^ (n - j) / ((n + 1 : K) * (n.choose j : K)) := by
  have hc : (n.choose j : K) * (j.factorial : K) * ((n - j).factorial : K) =
      (n.factorial : K) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  have hn : (n + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hb : (n.choose j : K) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hj
  have hjf : (j.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hnf : ((n - j).factorial : K) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - j)
  simp only [inverseCoefficient, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, ← hc]
  field_simp

theorem inverseCoefficient_last (n : ℕ) :
    (n + 1 : K) * inverseCoefficient n n = 1 := by
  simp only [inverseCoefficient, Nat.sub_self, pow_zero, one_mul,
    Nat.factorial_zero, Nat.cast_one, mul_one, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hn : (n + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

theorem inverseCoefficient_recurrence (n j : ℕ) (hj : j < n) :
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

section FiniteSets

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- Every row of the Boolean inclusion matrix has the claimed inverse
coefficient.  This is the identity `q b_(q-1) + (r-q) b_q = δ_(U,P)`,
with the intersection count and its nonvanishing proved from cardinalities. -/
theorem inclusion_inverse_row (n : ℕ) (hι : Fintype.card ι = 2 * n + 1)
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
      (inverseCoefficient_last (K := K) n)
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
    have hcast : (q - 1 : ℕ) + (1 : K) = (q : K) := by exact_mod_cast hpred
    simpa only [hpred, hsub, hcast] using
      (inverseCoefficient_recurrence (K := K) n (q - 1) (by omega))

end FiniteSets

section InclusionOperator

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- Subsets of a specified cardinality. -/
abbrev FixedSubsets (ι : Type*) (r : ℕ) := {U : Finset ι // U.card = r}

/-- Removing an element from an `(n+1)`-subset gives an `n`-subset. -/
def eraseSubset {n : ℕ} (U : FixedSubsets ι (n + 1)) (a : U.1) : FixedSubsets ι n :=
  ⟨U.1.erase a, by rw [Finset.card_erase_of_mem a.2, U.2]; omega⟩

/-- The upward Boolean inclusion operator.  Its coefficient at `U` is the sum
of the coefficients at its codimension-one faces. -/
noncomputable def inclusionOperator (n : ℕ) :
    (FixedSubsets ι n → K) →ₗ[K] (FixedSubsets ι (n + 1) → K) where
  toFun v U := ∑ a : U.1, v (eraseSubset U a)
  map_add' v w := by ext U; simp [Finset.sum_add_distrib]
  map_smul' c v := by ext U; simp [Finset.mul_sum]

/-- The explicit candidate inverse to the central Boolean inclusion operator. -/
noncomputable def inclusionInverse (n : ℕ) :
    (FixedSubsets ι (n + 1) → K) →ₗ[K] (FixedSubsets ι n → K) where
  toFun v T := ∑ P : FixedSubsets ι (n + 1),
    v P * inverseCoefficient n (T.1 ∩ P.1).card
  map_add' v w := by ext T; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c v := by ext T; simp [mul_assoc, Finset.mul_sum]

/-- The local inverse works for all vectors, not just a finite list of examples. -/
theorem inclusionOperator_inclusionInverse (n : ℕ)
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
      (inclusion_inverse_row (K := K) n hι U.1 P.1 U.2 P.2)
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hrow]
  simp [mul_ite]

theorem inclusionOperator_surjective (n : ℕ)
    (hι : Fintype.card ι = 2 * n + 1) :
    Function.Surjective (inclusionOperator (K := K) (ι := ι) n) :=
  fun v => ⟨inclusionInverse n v, inclusionOperator_inclusionInverse n hι v⟩

theorem inclusionOperator_injective (n : ℕ)
    (hι : Fintype.card ι = 2 * n + 1) :
    Function.Injective (inclusionOperator (K := K) (ι := ι) n) := by
  have hc : Fintype.card (FixedSubsets ι n) =
      Fintype.card (FixedSubsets ι (n + 1)) := by
    simp only [FixedSubsets, Fintype.card_finset_len]
    have hsub : Fintype.card ι - n = n + 1 := by omega
    rw [← hsub, Nat.choose_symm (by omega : n ≤ Fintype.card ι)]
  have hd : Module.finrank K (FixedSubsets ι n → K) =
      Module.finrank K (FixedSubsets ι (n + 1) → K) := by
    simpa only [Module.finrank_fintype_fun_eq_card] using hc
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr
    (inclusionOperator_surjective n hι)

/-- Both composite identities for the explicit inverse are kernel-checked;
the second uses the equality of the complementary Boolean ranks. -/
theorem inclusionInverse_inclusionOperator (n : ℕ)
    (hι : Fintype.card ι = 2 * n + 1) (v : FixedSubsets ι n → K) :
    inclusionInverse n (inclusionOperator n v) = v := by
  apply inclusionOperator_injective n hι
  exact inclusionOperator_inclusionInverse n hι (inclusionOperator n v)

end InclusionOperator

end PaperVerification.AlternatingForms
