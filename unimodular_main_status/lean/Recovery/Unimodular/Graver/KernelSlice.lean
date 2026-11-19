module

public import Recovery.Unimodular.Graver.RationalVertices
public import Mathlib.Data.Rat.Cast.Lemmas

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators Topology Matrix
open Set

namespace Unimodular.KernelSlice
open RationalVertices

variable {n m : ℕ}

/-- Nonnegativity, both signs of every kernel equation, and both sides of
normalization are an explicit finite family of integer halfspaces. -/
def normals (A : Matrix (Fin m) (Fin n) ℤ) :
    Fin (n + (m + (m + 2))) → Lattice n :=
  Fin.addCases (fun j => -Pi.single j 1)
    (Fin.addCases (fun i => A i)
      (Fin.addCases (fun i => -A i)
        (fun i : Fin 2 => if i = 0 then (fun _ => 1) else (fun _ => -1))))

def heights : Fin (n + (m + (m + 2))) → ℤ :=
  Fin.addCases (fun _ => 0) (Fin.addCases (fun _ => 0)
    (Fin.addCases (fun _ => 0) (fun i : Fin 2 => if i = 0 then 1 else -1)))

def slice (A : Matrix (Fin m) (Fin n) ℤ) : Set (Ambient n) :=
  {x | (∀ j, 0 ≤ x j) ∧ (A.map (fun z => (z : ℝ))) *ᵥ x = 0 ∧ ∑ j, x j = 1}

/-- A finite list computed directly from the input matrix. -/
def vertices (A : Matrix (Fin m) (Fin n) ℤ) : Finset (Fin n → ℚ) :=
  RationalVertices.vertices (normals A) heights

/-- A positive integer clearing every coordinate denominator. -/
def denominator (q : Fin n → ℚ) : ℕ := ∏ j, (q j).den

/-- The cleared vector uses products and numerators only, so is executable. -/
def cleared (q : Fin n → ℚ) : Lattice n := fun j =>
  (∏ k ∈ (Finset.univ.erase j), ((q k).den : ℤ)) * (q j).num

/-- The sum of the explicitly computed vertex denominators. -/
def bound (A : Matrix (Fin m) (Fin n) ℤ) : ℕ :=
  ∑ q ∈ vertices A, denominator q

noncomputable section

@[simp] theorem carrier_eq_slice (A : Matrix (Fin m) (Fin n) ℤ) :
    RationalVertices.carrier (normals A) heights = slice A := by
  ext x
  simp only [RationalVertices.carrier, Set.mem_setOf_eq, normals, heights,
    Fin.forall_fin_add, Fin.addCases_left, Fin.addCases_right, Fin.forall_fin_two,
    ite_true, Fin.one_eq_zero_iff, Nat.reduceEqDiff, ite_false]
  have hneg_single (j : Fin n) : pairing x (-Pi.single j 1) = -x j := by
    simp [pairing, Pi.single_apply, mul_ite, Finset.sum_ite_eq', Finset.sum_neg_distrib]
  have hrow (i : Fin m) : pairing x (A i) =
      ((A.map (fun z => (z : ℝ))) *ᵥ x) i := by
    simp only [pairing, Matrix.mulVec, dotProduct, Matrix.map_apply, mul_comm]
  have hnegrow (i : Fin m) : pairing x (-A i) =
      -((A.map (fun z => (z : ℝ))) *ᵥ x) i := by
    rw [← hrow]
    simp [pairing, Finset.sum_neg_distrib]
  have hone : pairing x (fun _ => 1) = ∑ j, x j := by simp [pairing]
  have hnegone : pairing x (fun _ => -1) = -(∑ j, x j) := by
    simp [pairing, Finset.sum_neg_distrib]
  simp only [hneg_single, hrow, hnegrow, hone, hnegone, Int.cast_zero,
    Int.cast_one, Int.cast_neg, neg_nonpos]
  change ((∀ j, 0 ≤ x j) ∧ (∀ i, _) ∧ (∀ i, _) ∧ _ ∧ _) ↔ _
  constructor
  · rintro ⟨hx, hle, hge, hsumle, hsumge⟩
    refine ⟨hx, ?_, le_antisymm hsumle (by linarith)⟩
    ext i
    exact le_antisymm (hle i) (hge i)
  · rintro ⟨hx, he, hs⟩
    refine ⟨hx, ?_, ?_, by rw [hs], by rw [hs]⟩
    · intro i
      rw [he]
      exact le_rfl
    · intro i
      rw [he]
      exact le_rfl

theorem slice_isCompact (A : Matrix (Fin m) (Fin n) ℤ) : IsCompact (slice A) := by
  apply (isCompact_Icc (a := (0 : Ambient n)) (b := fun _ => (1 : ℝ))).of_isClosed_subset
  · rw [← carrier_eq_slice]
    exact RationalVertices.carrier_isClosed _ _
  · intro x hx
    refine ⟨hx.1, ?_⟩
    intro j
    have h := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) => hx.1 k)
      (Finset.mem_univ j)
    exact h.trans_eq hx.2.2

theorem slice_eq_convexHull (A : Matrix (Fin m) (Fin n) ℤ) :
    slice A = convexHull ℝ (ratEmbed '' (vertices A : Set (Fin n → ℚ))) := by
  have h := RationalVertices.carrier_eq_convexHull_vertices (normals A) heights
    (by rw [carrier_eq_slice]; exact slice_isCompact A)
  simpa only [carrier_eq_slice, vertices] using h

theorem vertex_mem_slice (A : Matrix (Fin m) (Fin n) ℤ)
    {q : Fin n → ℚ} (hq : q ∈ vertices A) : ratEmbed q ∈ slice A := by
  rw [← carrier_eq_slice]
  exact RationalVertices.vertices_subset _ _ ⟨q, hq, rfl⟩

theorem denominator_pos (q : Fin n → ℚ) : 0 < denominator q := by
  exact Finset.prod_pos (fun j _ => Nat.pos_of_ne_zero (q j).den_ne_zero)

/-- Clearing denominators is exactly positive scalar multiplication in the
original real coordinates. -/
theorem embed_cleared (q : Fin n → ℚ) :
    embed (cleared q) = (denominator q : ℝ) • ratEmbed q := by
  ext j
  have hden : (denominator q : ℤ) =
      (∏ k ∈ Finset.univ.erase j, ((q k).den : ℤ)) * (q j).den := by
    unfold denominator
    rw [Nat.cast_prod]
    exact (Finset.prod_erase_mul (Finset.univ : Finset (Fin n))
      (fun k => ((q k).den : ℤ)) (Finset.mem_univ j)).symm
  have hdR : ((q j).den : ℝ) ≠ 0 := by exact_mod_cast (q j).den_ne_zero
  change (((∏ k ∈ Finset.univ.erase j, ((q k).den : ℤ)) * (q j).num : ℤ) : ℝ) =
    (denominator q : ℝ) * (q j : ℝ)
  rw [Int.cast_mul, Rat.cast_def]
  have hdenR := congrArg (fun z : ℤ => (z : ℝ)) hden
  simp only [Int.cast_mul, Int.cast_natCast] at hdenR
  rw [hdenR]
  field_simp <;> ring

theorem cleared_nonnegative (A : Matrix (Fin m) (Fin n) ℤ)
    {q : Fin n → ℚ} (hq : q ∈ vertices A) : ∀ j, 0 ≤ cleared q j := by
  intro j
  have h := (vertex_mem_slice A hq).1 j
  have he := congrFun (embed_cleared q) j
  change (cleared q j : ℝ) = (denominator q : ℝ) * (q j : ℝ) at he
  have hh : (0 : ℝ) ≤ cleared q j := by
    rw [he]
    exact mul_nonneg (Nat.cast_nonneg _) h
  exact_mod_cast hh

theorem cleared_sum (A : Matrix (Fin m) (Fin n) ℤ)
    {q : Fin n → ℚ} (hq : q ∈ vertices A) :
    ∑ j, cleared q j = (denominator q : ℤ) := by
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_sum]
  have he (j : Fin n) : (cleared q j : ℝ) = (denominator q : ℝ) * (q j : ℝ) :=
    congrFun (embed_cleared q) j
  simp_rw [he]
  have hsum : (∑ j, (q j : ℝ)) = 1 := (vertex_mem_slice A hq).2.2
  rw [← Finset.mul_sum, hsum, mul_one, Int.cast_natCast]

theorem cleared_ne_zero (A : Matrix (Fin m) (Fin n) ℤ)
    {q : Fin n → ℚ} (hq : q ∈ vertices A) : cleared q ≠ 0 := by
  intro he
  have hs := cleared_sum A hq
  rw [he] at hs
  have hz : (denominator q : ℤ) = 0 := by simpa using hs.symm
  have hp := denominator_pos q
  exact (Nat.ne_of_gt hp) (Int.natCast_eq_zero.1 hz)

theorem cleared_in_kernel (A : Matrix (Fin m) (Fin n) ℤ)
    {q : Fin n → ℚ} (hq : q ∈ vertices A) : A *ᵥ cleared q = 0 := by
  have he := (vertex_mem_slice A hq).2.1
  ext i
  apply Int.cast_injective (α := ℝ)
  have hc (j : Fin n) : (cleared q j : ℝ) = (denominator q : ℝ) * (q j : ℝ) :=
    congrFun (embed_cleared q) j
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Pi.zero_apply,
    Int.cast_zero]
  simp_rw [hc]
  have hi := congrFun he i
  change (∑ j, (A i j : ℝ) * (q j : ℝ)) = 0 at hi
  calc
    ∑ j, (A i j : ℝ) * ((denominator q : ℝ) * (q j : ℝ)) =
        (denominator q : ℝ) * ∑ j, (A i j : ℝ) * (q j : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = 0 := by rw [hi, mul_zero]

end
end Unimodular.KernelSlice

#print axioms Unimodular.KernelSlice.slice_eq_convexHull
#print axioms Unimodular.KernelSlice.embed_cleared
#print axioms Unimodular.KernelSlice.cleared_in_kernel
#check Unimodular.KernelSlice.cleared_in_kernel
