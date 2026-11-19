module

public import PaperVerification.AlternatingFormsBooleanCharacteristic
public import PaperVerification.AlternatingFormsSingletonStates

/-!
# Exterior division with its exact factorial denominator

These statements generalize the literal local inverse to arbitrary fields.
Every use of characteristic zero is replaced by the nonvanishing of the one
factorial that occurs in that inverse. The identities remain identities in
the genuine exterior algebra, with their homogeneous degrees retained.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K : Type*} [Field K]

section SquareZero

variable {A ι : Type*} [CommRing A] [Algebra K A] [Fintype ι] [DecidableEq ι]

/-- The exact local inverse needs only `(n+1)!` to be invertible. -/
theorem local_pair_division_of_factorial
    (y : ι → A) (hy : ∀ i, y i * y i = 0)
    (n : ℕ) (hfac : ((n + 1).factorial : K) ≠ 0)
    (hι : Fintype.card ι = 2 * n + 1)
    (P : FixedSubsets ι (n + 1)) :
    (∑ i, y i) *
        (∑ T : FixedSubsets ι n,
          inverseCoefficient (K := K) n (T.1 ∩ P.1).card • ∏ i ∈ T.1, y i) =
      ∏ i ∈ P.1, y i := by
  have h := squarefreeEvaluation_inclusion y hy n
    (inclusionInverse n (Pi.single P (1 : K)))
  rw [inclusionOperator_inclusionInverse_of_factorial n hfac hι] at h
  simpa [squarefreeEvaluation, inclusionInverse, Pi.single_apply] using h

end SquareZero

section Exterior

variable {M ι : Type*} [AddCommGroup M] [Module K M] [Fintype ι] [DecidableEq ι]

/-- The complete local inverse identity for actual exterior pair variables,
with arbitrary universe size and arbitrary vectors in an arbitrary module. -/
theorem local_exterior_pair_division_of_factorial
    (u v : ι → M) (n : ℕ) (hfac : ((n + 1).factorial : K) ≠ 0) (hι : Fintype.card ι = 2 * n + 1)
    (P : FixedSubsets ι (n + 1)) :
    (∑ i, ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i)) *
        (∑ T : FixedSubsets ι n,
          inverseCoefficient (K := K) n (T.1 ∩ P.1).card • pairedMonomial u v T.1) =
      pairedMonomial u v P.1 := by
  have h := local_pair_division_of_factorial (K := K)
    (fun i => exteriorPairCentral (K := K) (u i) (v i))
    (fun i => exteriorPairCentral_square_zero (u i) (v i)) n hfac hι P
  have hcoe := congrArg
    (fun x : Subalgebra.center K (ExteriorAlgebra K M) =>
      (x : ExteriorAlgebra K M)) h
  simpa only [Subalgebra.coe_mul, Subalgebra.coe_smul, map_sum,
    AddSubmonoidClass.coe_finsetSum,
    exteriorPairCentral_coe, pairedMonomial] using hcoe

/-- The local inverse preserves an arbitrary prescribed singleton word.
Pairs occupied by that word annihilate it; every term in the inverse changes
only unoccupied pairs.  This is the support information used in the paper's
straightening weights, beyond mere existence of a prefix inverse. -/
theorem local_exterior_pair_division_with_singletons_of_factorial
    (u v : ι → M) (S : Finset ι) (L : List M)
    (hL : ∀ i ∈ S, u i ∈ L ∨ v i ∈ L)
    (n : ℕ) (hfac : ((n + 1).factorial : K) ≠ 0) (hι : Fintype.card {i : ι // i ∉ S} = 2 * n + 1)
    (P : FixedSubsets {i : ι // i ∉ S} (n + 1)) :
    let z := (L.map (ExteriorAlgebra.ι K)).prod
    (∑ i, ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i)) *
        (z * ∑ T : FixedSubsets {i : ι // i ∉ S} n,
          inverseCoefficient (K := K) n (T.1 ∩ P.1).card •
            pairedMonomial (fun i : {i : ι // i ∉ S} => u i.val)
              (fun i : {i : ι // i ∉ S} => v i.val) T.1) =
      z * pairedMonomial (fun i : {i : ι // i ∉ S} => u i.val)
        (fun i : {i : ι // i ∉ S} => v i.val) P.1 := by
  classical
  dsimp only
  let z := (L.map (ExteriorAlgebra.ι K)).prod
  let y : ι → ExteriorAlgebra K M :=
    fun i => ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i)
  have hkill (i : ι) (hi : i ∈ S) : y i * z = 0 := by
    rcases hL i hi with hu | hv
    · simpa only [y, z, exteriorPair_coe] using
        twoForm_mul_word_eq_zero_of_mem (exteriorPair (u i) (v i)) (u i)
          (exteriorPair_mul_left_generator (u i) (v i)) L hu
    · simpa only [y, z, exteriorPair_coe] using
        twoForm_mul_word_eq_zero_of_mem (exteriorPair (u i) (v i)) (v i)
          (exteriorPair_mul_right_generator (u i) (v i)) L hv
  have hsum : (∑ i, y i) * z = (∑ i : {i : ι // i ∉ S}, y i.val) * z := by
    letI : Fintype {i : ι // i ∈ S} := Subtype.fintype (fun i => i ∈ S)
    rw [Finset.sum_mul, Finset.sum_mul]
    have hz : (∑ i : {i : ι // i ∈ S}, y i.val * z) = 0 :=
      Finset.sum_eq_zero fun i _ => hkill i.val i.property
    calc
      _ = (∑ i : {i : ι // i ∈ S}, y i.val * z) +
          (∑ i : {i : ι // i ∉ S}, y i.val * z) :=
        (Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ S) (fun i => y i * z)).symm
      _ = _ := by rw [hz, zero_add]
  have hcomm : (∑ i : {i : ι // i ∉ S}, y i.val) * z =
      z * (∑ i : {i : ι // i ∉ S}, y i.val) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [y, exteriorPair_coe] using
      (twoForm_commute (exteriorPair (u i.val) (v i.val)) z).eq
  have hdiv := local_exterior_pair_division_of_factorial (K := K)
    (fun i : {i : ι // i ∉ S} => u i.val)
    (fun i : {i : ι // i ∉ S} => v i.val) n hfac hι P
  change (∑ i, y i) * (z * _) = z * _
  rw [← mul_assoc, hsum, hcomm, mul_assoc]
  exact congrArg (fun a : ExteriorAlgebra K M => z * a) hdiv

/-- The singleton-preserving inverse has precisely the required homogeneous
degree.  Its formula uses the same singleton word and only unoccupied pairs. -/
theorem singleton_state_division_exists_of_factorial
    (u v : ι → M) (S : Finset ι) (L : List M)
    (hL : ∀ i ∈ S, u i ∈ L ∨ v i ∈ L)
    (n : ℕ) (hfac : ((n + 1).factorial : K) ≠ 0) (hι : Fintype.card {i : ι // i ∉ S} = 2 * n + 1)
    (P : FixedSubsets {i : ι // i ∉ S} (n + 1)) :
    ∃ η : ⋀[K]^(L.length + 2 * n) M,
      (∑ i, ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i)) *
          (η : ExteriorAlgebra K M) =
        (L.map (ExteriorAlgebra.ι K)).prod *
          pairedMonomial (fun i : {i : ι // i ∉ S} => u i.val)
            (fun i : {i : ι // i ∉ S} => v i.val) P.1 := by
  classical
  let ηpairs : ExteriorAlgebra K M :=
    ∑ T : FixedSubsets {i : ι // i ∉ S} n,
      inverseCoefficient (K := K) n (T.1 ∩ P.1).card •
        pairedMonomial (fun i : {i : ι // i ∉ S} => u i.val)
          (fun i : {i : ι // i ∉ S} => v i.val) T.1
  have hηpairs : ηpairs ∈ ⋀[K]^(2 * n) M := by
    apply Submodule.sum_mem
    intro T _
    apply Submodule.smul_mem
    simpa only [T.2] using pairedMonomial_mem
      (fun i : {i : ι // i ∉ S} => u i.val)
      (fun i : {i : ι // i ∉ S} => v i.val) T.1
  refine ⟨⟨(L.map (ExteriorAlgebra.ι K)).prod * ηpairs,
    SetLike.mul_mem_graded (exteriorWord_mem L) hηpairs⟩, ?_⟩
  exact local_exterior_pair_division_with_singletons_of_factorial u v S L hL n hfac hι P


/-- In prime characteristic the exact denominator is nonzero below `p`. -/
theorem factorial_cast_ne_zero_of_lt_char (p n : ℕ) [Fact p.Prime] [CharP K p]
    (hn : n < p) : (n.factorial : K) ≠ 0 := by
  intro hz
  exact (not_le_of_gt hn) ((Fact.out : p.Prime).dvd_factorial.mp
    ((CharP.cast_eq_zero_iff K p n.factorial).mp hz))

end Exterior

end PaperVerification.AlternatingForms
