module

public import PaperVerification.AlternatingFormsExteriorCentrality
public import PaperVerification.AlternatingFormsStraightening
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The local division identity inside the exterior algebra

Here the commuting square-zero variables are the genuine products of pairs
of degree-one exterior generators.  Their commutativity and square-zero
relations are proved from the exterior algebra, not assumed.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- The decomposable exterior two-form associated to two vectors. -/
def exteriorPair (u v : M) : ⋀[K]^2 M :=
  exteriorPower.ιMulti K 2 ![u, v]

@[simp] theorem exteriorPair_coe (u v : M) :
    (exteriorPair (K := K) u v : ExteriorAlgebra K M) =
      ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v := by
  simp [exteriorPair, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]

/-- Pair variables belong to the center of the exterior algebra. -/
def exteriorPairCentral (u v : M) : Subalgebra.center K (ExteriorAlgebra K M) :=
  ⟨(exteriorPair (K := K) u v : ExteriorAlgebra K M),
    Subalgebra.mem_center_iff.mpr fun x =>
      (twoForm_commute (exteriorPair (K := K) u v) x).eq.symm⟩

@[simp] theorem exteriorPairCentral_coe (u v : M) :
    (exteriorPairCentral (K := K) u v : ExteriorAlgebra K M) =
      ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v := exteriorPair_coe (K := K) u v

theorem exteriorPairCentral_square_zero (u v : M) :
    exteriorPairCentral (K := K) u v * exteriorPairCentral u v = 0 := by
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, exteriorPairCentral_coe, ZeroMemClass.coe_zero]
  have hvu : ExteriorAlgebra.ι K v * ExteriorAlgebra.ι K u =
      -(ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap v u)
  calc
    (ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v) *
        (ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v) =
      ExteriorAlgebra.ι K u *
        ((ExteriorAlgebra.ι K v * ExteriorAlgebra.ι K u) * ExteriorAlgebra.ι K v) := by
          simp only [mul_assoc]
    _ = 0 := by
      rw [hvu]
      simp [neg_mul, mul_neg, ← mul_assoc, ExteriorAlgebra.ι_sq_zero]

theorem exteriorPair_mul_left_generator (u v : M) :
    (exteriorPair (K := K) u v : ExteriorAlgebra K M) * ExteriorAlgebra.ι K u = 0 := by
  rw [exteriorPair_coe, mul_assoc,
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap v u)]
  simp [mul_neg, ← mul_assoc, ExteriorAlgebra.ι_sq_zero]

theorem exteriorPair_mul_right_generator (u v : M) :
    (exteriorPair (K := K) u v : ExteriorAlgebra K M) * ExteriorAlgebra.ι K v = 0 := by
  rw [exteriorPair_coe, mul_assoc, ExteriorAlgebra.ι_sq_zero, mul_zero]

/-- A central two-form that annihilates one generator annihilates every word
containing that generator.  The position of the generator is unrestricted. -/
theorem twoForm_mul_word_eq_zero_of_mem (f : ⋀[K]^2 M) (a : M)
    (hfa : (f : ExteriorAlgebra K M) * ExteriorAlgebra.ι K a = 0)
    (L : List M) (ha : a ∈ L) :
    (f : ExteriorAlgebra K M) * (L.map (ExteriorAlgebra.ι K)).prod = 0 := by
  induction L with
  | nil => simp at ha
  | cons b L ih =>
    rw [List.map_cons, List.prod_cons]
    rcases List.mem_cons.mp ha with hab | ha
    · subst b
      rw [← mul_assoc, hfa, zero_mul]
    · rw [← mul_assoc, (twoForm_commute f (ExteriorAlgebra.ι K b)).eq,
        mul_assoc, ih ha, mul_zero]

/-- A word of length `q` belongs to the genuine `q`th exterior power. -/
theorem exteriorWord_mem (L : List M) :
    (L.map (ExteriorAlgebra.ι K)).prod ∈ ⋀[K]^L.length M := by
  have hgen (a : M) : ExteriorAlgebra.ι K a ∈ ⋀[K]^1 M := by
    change ExteriorAlgebra.ι K a ∈ (LinearMap.range (ExteriorAlgebra.ι K)) ^ 1
    rw [pow_one]
    exact LinearMap.mem_range_self _ a
  simpa using SetLike.list_prod_map_mem_graded
    (A := fun d : ℕ => ⋀[K]^d M) L (fun _ => 1) (ExteriorAlgebra.ι K)
    (fun a _ => hgen a)

section FinitePairs

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- A product of pair variables, formed in the center and then included in
the exterior algebra.  This makes the absence of pair-order signs explicit. -/
def pairedMonomial (u v : ι → M) (T : Finset ι) : ExteriorAlgebra K M :=
  ((∏ i ∈ T, exteriorPairCentral (K := K) (u i) (v i)) :
    Subalgebra.center K (ExteriorAlgebra K M))

@[simp] theorem pairedMonomial_empty (u v : ι → M) :
    pairedMonomial (K := K) u v ∅ = 1 := by
  simp [pairedMonomial]

theorem pairedMonomial_insert (u v : ι → M) (T : Finset ι) (a : ι) (ha : a ∉ T) :
    pairedMonomial (K := K) u v (insert a T) =
      (exteriorPair (K := K) (u a) (v a) : ExteriorAlgebra K M) * pairedMonomial u v T := by
  simp only [pairedMonomial, Finset.prod_insert ha, Subalgebra.coe_mul,
    exteriorPairCentral]

/-- Pair products have degree twice their actual number of pairs. -/
theorem pairedMonomial_mem (u v : ι → M) (T : Finset ι) :
    pairedMonomial (K := K) u v T ∈ ⋀[K]^(2 * T.card) M := by
  induction T using Finset.induction_on with
  | empty => simpa using SetLike.one_mem_graded (fun d : ℕ => ⋀[K]^d M)
  | @insert a T ha ih =>
    rw [pairedMonomial_insert u v T a ha, Finset.card_insert_of_notMem ha]
    simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm] using
      SetLike.mul_mem_graded (exteriorPair (K := K) (u a) (v a)).property ih

/-- The complete local inverse identity for actual exterior pair variables,
with arbitrary universe size and arbitrary vectors in an arbitrary module. -/
theorem local_exterior_pair_division [CharZero K]
    (u v : ι → M) (n : ℕ) (hι : Fintype.card ι = 2 * n + 1)
    (P : FixedSubsets ι (n + 1)) :
    (∑ i, ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i)) *
        (∑ T : FixedSubsets ι n,
          inverseCoefficient (K := K) n (T.1 ∩ P.1).card • pairedMonomial u v T.1) =
      pairedMonomial u v P.1 := by
  have h := local_pair_division (K := K)
    (fun i => exteriorPairCentral (K := K) (u i) (v i))
    (fun i => exteriorPairCentral_square_zero (u i) (v i)) n hι P
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
theorem local_exterior_pair_division_with_singletons [CharZero K]
    (u v : ι → M) (S : Finset ι) (L : List M)
    (hL : ∀ i ∈ S, u i ∈ L ∨ v i ∈ L)
    (n : ℕ) (hι : Fintype.card {i : ι // i ∉ S} = 2 * n + 1)
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
  have hdiv := local_exterior_pair_division (K := K)
    (fun i : {i : ι // i ∉ S} => u i.val)
    (fun i : {i : ι // i ∉ S} => v i.val) n hι P
  change (∑ i, y i) * (z * _) = z * _
  rw [← mul_assoc, hsum, hcomm, mul_assoc]
  exact congrArg (fun a : ExteriorAlgebra K M => z * a) hdiv

/-- The singleton-preserving inverse has precisely the required homogeneous
degree.  Its formula uses the same singleton word and only unoccupied pairs. -/
theorem singleton_state_division_exists [CharZero K]
    (u v : ι → M) (S : Finset ι) (L : List M)
    (hL : ∀ i ∈ S, u i ∈ L ∨ v i ∈ L)
    (n : ℕ) (hι : Fintype.card {i : ι // i ∉ S} = 2 * n + 1)
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
  exact local_exterior_pair_division_with_singletons u v S L hL n hι P

end FinitePairs

end PaperVerification.AlternatingForms
