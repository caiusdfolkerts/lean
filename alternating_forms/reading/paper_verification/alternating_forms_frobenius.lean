module

public import PaperVerification.AlternatingFormsCharacteristicDivision
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.Data.List.FinRange

/-!
# Frobenius relations for actual exterior matching forms

The factorial expansion is proved from Boolean incidence, over an arbitrary
field. In characteristic `p` it proves that the actual matching form has
`p`th power zero. It also retains the exact factorial coefficient used by the
sparse-coordinate certificates in Theorem 7.2.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K : Type*} [Field K]

section SquareZero

variable {A ι : Type*} [CommRing A] [Algebra K A] [Fintype ι] [DecidableEq ι]

theorem squarefreeEvaluation_one_zero (y : ι → A) :
    squarefreeEvaluation (K := K) y 0 (fun _ => 1) = 1 := by
  classical
  let T₀ : FixedSubsets ι 0 := ⟨∅, rfl⟩
  have hT (T : FixedSubsets ι 0) : T = T₀ := by
    apply Subtype.ext
    exact Finset.card_eq_zero.mp T.property
  letI : Unique (FixedSubsets ι 0) := ⟨⟨T₀⟩, hT⟩
  have hd : (default : FixedSubsets ι 0) = T₀ := hT _
  simp [squarefreeEvaluation, hd, T₀]

theorem inclusionOperator_one (n : ℕ) :
    inclusionOperator (K := K) (ι := ι) n (fun _ => 1) =
      fun _ => (n + 1 : K) := by
  funext U
  change (∑ _a : U.val, (1 : K)) = n + 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, U.property,
    nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]

/-- The full squarefree factorial expansion, before imposing a
characteristic. In particular, no Frobenius relation is assumed. -/
theorem squareZero_sum_pow_factorial (y : ι → A)
    (hy : ∀ i, y i * y i = 0) (n : ℕ) :
    (∑ i, y i) ^ n =
      (n.factorial : K) • squarefreeEvaluation (K := K) y n (fun _ => 1) := by
  induction n with
  | zero => simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_smul,
      squarefreeEvaluation_one_zero (K := K) y]
  | succ n ih =>
    rw [pow_succ', ih, mul_smul_comm, squarefreeEvaluation_inclusion (K := K) y hy,
      inclusionOperator_one (K := K) (ι := ι)]
    have hconst : squarefreeEvaluation (K := K) y (n + 1)
        (fun _ => (n + 1 : K)) =
        (n + 1 : K) • squarefreeEvaluation (K := K) y (n + 1) (fun _ => 1) := by
      have hc : (fun _ : FixedSubsets ι (n + 1) => (n + 1 : K)) =
          (n + 1 : K) • (fun _ : FixedSubsets ι (n + 1) => (1 : K)) := by
        funext T
        simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      rw [hc]
      exact (squarefreeEvaluation (K := K) y (n + 1)).map_smul
        (n + 1 : K) (fun _ => 1)
    rw [hconst, smul_smul, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    congr 1
    exact mul_comm _ _

/-- At the top squarefree degree the expansion has a single retained
product, with the coefficient `card(ι)!`. -/
theorem squareZero_sum_pow_card (y : ι → A)
    (hy : ∀ i, y i * y i = 0) :
    (∑ i, y i) ^ Fintype.card ι =
      ((Fintype.card ι).factorial : K) • ∏ i, y i := by
  classical
  let T₀ : FixedSubsets ι (Fintype.card ι) := ⟨Finset.univ, Finset.card_univ⟩
  have hT (T : FixedSubsets ι (Fintype.card ι)) : T = T₀ := by
    apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le T.val.subset_univ
      (by rw [Finset.card_univ, T.property])
  letI : Unique (FixedSubsets ι (Fintype.card ι)) := ⟨⟨T₀⟩, hT⟩
  rw [squareZero_sum_pow_factorial (K := K) y hy]
  have hd : (default : FixedSubsets ι (Fintype.card ι)) = T₀ := hT _
  simp [squarefreeEvaluation, hd, T₀]

/-- Frobenius vanishing follows from the zero factorial coefficient. -/
theorem squareZero_sum_pow_char (y : ι → A)
    (hy : ∀ i, y i * y i = 0) (p : ℕ) [Fact p.Prime] [CharP K p] :
    (∑ i, y i) ^ p = 0 := by
  rw [squareZero_sum_pow_factorial (K := K) y hy]
  have hfac : (p.factorial : K) = 0 := by
    exact (CharP.cast_eq_zero_iff K p p.factorial).mpr
      ((Fact.out : p.Prime).dvd_factorial.mpr le_rfl)
  rw [hfac, zero_smul]

end SquareZero

section Exterior

variable {M ι : Type*} [AddCommGroup M] [Module K M] [Fintype ι] [DecidableEq ι]

/-- The central sum is the actual sum of exterior pair monomials. -/
theorem exterior_matching_pow_char (u v : ι → M)
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (∑ i, ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i)) ^ p = 0 := by
  have h := squareZero_sum_pow_char (K := K)
    (fun i => exteriorPairCentral (K := K) (u i) (v i))
    (fun i => exteriorPairCentral_square_zero (u i) (v i)) p
  have hc := congrArg
    (fun a : Subalgebra.center K (ExteriorAlgebra K M) =>
      (a : ExteriorAlgebra K M)) h
  simpa only [Subalgebra.coe_pow, AddSubmonoidClass.coe_finsetSum,
    exteriorPairCentral_coe, ZeroMemClass.coe_zero] using hc

/-- The exact sparse projection coefficient in the genuine exterior
algebra. Nonvanishing is supplied separately by the retained exterior word. -/
theorem exterior_matching_pow_card (u v : ι → M) :
    (∑ i, ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i)) ^ Fintype.card ι =
      ((Fintype.card ι).factorial : K) • pairedMonomial u v Finset.univ := by
  have h := squareZero_sum_pow_card (K := K)
    (fun i => exteriorPairCentral (K := K) (u i) (v i))
    (fun i => exteriorPairCentral_square_zero (u i) (v i))
  have hc := congrArg
    (fun a : Subalgebra.center K (ExteriorAlgebra K M) =>
      (a : ExteriorAlgebra K M)) h
  simpa only [Subalgebra.coe_pow, AddSubmonoidClass.coe_finsetSum,
    exteriorPairCentral_coe, Subalgebra.coe_smul, pairedMonomial] using hc

end Exterior

section BasisWords

variable {M I : Type*} [AddCommGroup M] [Module K M] [LinearOrder I]

/-- Any repetition-free word in basis generators is a nonzero scalar
multiple of the canonical exterior basis vector with exactly its support. -/
theorem exterior_basis_word_unit (b : Module.Basis I K M)
    (L : List I) (hL : L.Nodup) :
    ∃ ε : K, ε ≠ 0 ∧
      ((L.map b).map (ExteriorAlgebra.ι K)).prod =
        ε • b.ExteriorAlgebra L.toFinset := by
  classical
  let S : Finset I := L.toFinset
  let c : Fin S.card ↪o I := S.orderEmbOfFin rfl
  have hc : (List.ofFn c).Nodup := List.nodup_ofFn_ofInjective c.injective
  have hperm : L.Perm (List.ofFn c) := by
    apply (List.perm_ext_iff_of_nodup hL hc).mpr
    intro i
    rw [List.mem_ofFn]
    change i ∈ L ↔ i ∈ Set.range c
    rw [show Set.range c = (S : Set I) from Finset.range_orderEmbOfFin S rfl]
    simp only [S, Finset.mem_coe, List.mem_toFinset]
  obtain ⟨ε, hε, heq⟩ := exterior_word_permutation (K := K) (hperm.map b)
  refine ⟨ε, hε, ?_⟩
  rw [heq]
  congr 1
  rw [ExteriorAlgebra.basis_apply_ofCard b (s_card := rfl)]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, List.map_ofFn, Function.comp_def,
    Set.powersetCard.ofCard, S, c]

/-- A word with distinct basis generators is genuinely nonzero. -/
theorem exterior_basis_word_ne_zero (b : Module.Basis I K M)
    (L : List I) (hL : L.Nodup) :
    ((L.map b).map (ExteriorAlgebra.ι K)).prod ≠ 0 := by
  obtain ⟨ε, hε, heq⟩ := exterior_basis_word_unit b L hL
  rw [heq]
  exact smul_ne_zero hε (b.ExteriorAlgebra.ne_zero L.toFinset)

end BasisWords

end PaperVerification.AlternatingForms
