module

public import VolumePolynomials.RationalElimination
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.List.OfFn

@[expose] public section
set_option autoImplicit false

/-!
# Exact computable halfspaces for a finite rational convex hull

The algorithm writes the usual barycentric inequalities and eliminates the
barycentric variables with the proved rational Fourier--Motzkin algorithm.
Thus the output is a finite list of rational halfspaces whose real solution
set is exactly the convex hull, including empty and lower-dimensional hulls.
-/

open Set
open scoped BigOperators

namespace VolumePolynomials.RationalElimination

theorem convexHull_range_finiteWeights {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] (v : ι → E) :
    convexHull ℝ (range v) =
      {x | ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ ∑ i, w i • v i = x} := by
  first
  | classical
    apply Set.Subset.antisymm
    · apply convexHull_min
      · rintro x ⟨i, rfl⟩
        refine ⟨fun j => if j = i then 1 else 0, ?_, ?_, ?_⟩
        · intro j
          change 0 ≤ if j = i then (1 : ℝ) else 0
          split_ifs <;> norm_num
        · simp
        · simp
      · rintro x ⟨w, hw, hw1, rfl⟩ y ⟨z, hz, hz1, rfl⟩ a b ha hb hab
        refine ⟨fun i => a * w i + b * z i, ?_, ?_, ?_⟩
        · intro i
          exact add_nonneg (mul_nonneg ha (hw i)) (mul_nonneg hb (hz i))
        · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hw1, hz1, mul_one, hab]
        · simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
    · rintro x ⟨w, hw, hw1, hwx⟩
      exact mem_convexHull_of_exists_fintype w v hw hw1 (fun i => mem_range_self i) hwx

def negative {n : ℕ} (p : Inequality n) : Inequality n :=
  ⟨fun i => -p.coefficient i, -p.bound⟩

theorem negative_value {n : ℕ} (p : Inequality n) (x : Fin n → ℝ) :
    (negative p).value x = -p.value x := by
  first
  | simp [negative, Inequality.value, Finset.sum_neg_distrib]

def equality {n : ℕ} (a : Fin n → ℚ) (b : ℚ) : List (Inequality n) :=
  [⟨a, b⟩, negative ⟨a, b⟩]

theorem satisfies_equality {n : ℕ} (a : Fin n → ℚ) (b : ℚ) (x : Fin n → ℝ) :
    Satisfies (equality a b) x ↔ (∑ i, (a i : ℝ) * x i) = (b : ℝ) := by
  first
  | constructor
    · intro h
      have hu : (∑ i, (a i : ℝ) * x i) ≤ (b : ℝ) :=
        h (Inequality.mk a b) (by simp [equality])
      have hl := h (negative (Inequality.mk a b)) (by simp [equality])
      change (negative (Inequality.mk a b)).value x ≤
        ((negative (Inequality.mk a b)).bound : ℝ) at hl
      rw [negative_value] at hl
      have hl' : -(∑ i, (a i : ℝ) * x i) ≤ -(b : ℝ) := by
        simpa only [negative, Inequality.value, Rat.cast_neg] using hl
      exact le_antisymm hu (neg_le_neg_iff.mp hl')
    · intro h p hp
      have hp' : p = Inequality.mk a b ∨ p = negative (Inequality.mk a b) := by
        simpa [equality] using hp
      rcases hp' with rfl | rfl
      · exact h.le
      · change (negative (Inequality.mk a b)).value x ≤
          ((negative (Inequality.mk a b)).bound : ℝ)
        rw [negative_value]
        simpa only [negative, Inequality.value, Rat.cast_neg] using neg_le_neg h.ge

theorem satisfies_append {n : ℕ} (A B : List (Inequality n)) (x : Fin n → ℝ) :
    Satisfies (A ++ B) x ↔ Satisfies A x ∧ Satisfies B x := by
  first
  | constructor
    · intro h
      exact ⟨fun p hp => h p (List.mem_append.mpr (Or.inl hp)),
        fun p hp => h p (List.mem_append.mpr (Or.inr hp))⟩
    · rintro ⟨hA, hB⟩ p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hA p hp
      · exact hB p hp

theorem satisfies_ofFn {n m : ℕ} (p : Fin m → Inequality n) (x : Fin n → ℝ) :
    Satisfies (List.ofFn p) x ↔ ∀ j, (p j).Holds x := by
  first
  | simp [Satisfies, List.mem_ofFn]

theorem satisfies_flatten_ofFn {n m : ℕ} (p : Fin m → List (Inequality n))
    (x : Fin n → ℝ) :
    Satisfies (List.ofFn p).flatten x ↔ ∀ j, Satisfies (p j) x := by
  first
  | constructor
    · intro h j q hq
      exact h q (List.mem_flatten.mpr ⟨p j, List.mem_ofFn.mpr ⟨j, rfl⟩, hq⟩)
    · intro h q hq
      obtain ⟨L, hL, hqL⟩ := List.mem_flatten.mp hq
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hL
      exact h j q hqL

theorem value_append {n m : ℕ} (a : Fin n → ℚ) (b : Fin m → ℚ)
    (c : ℚ) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    (Inequality.mk (Fin.append a b) c).value (Fin.append x w) =
      (∑ i, (a i : ℝ) * x i) + ∑ j, (b j : ℝ) * w j := by
  first
  | rw [Inequality.value, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

def nonnegativeConstraint (n : ℕ) {m : ℕ} (j : Fin m) : Inequality (n + m) :=
  ⟨Fin.append (fun _ => 0) (fun k => if k = j then -1 else 0), 0⟩

theorem nonnegativeConstraint_holds (n : ℕ) {m : ℕ} (j : Fin m)
    (x : Fin n → ℝ) (w : Fin m → ℝ) :
    (nonnegativeConstraint n j).Holds (Fin.append x w) ↔ 0 ≤ w j := by
  first
  | simp only [Inequality.Holds, nonnegativeConstraint, value_append]
    simp [apply_ite, ite_mul]

def barycentricSystem {n m : ℕ} (v : Fin m → Fin n → ℚ) : List (Inequality (n + m)) :=
  List.ofFn (nonnegativeConstraint n) ++
    equality (Fin.append (fun _ : Fin n => 0) (fun _ : Fin m => 1)) 1 ++
    (List.ofFn fun i : Fin n =>
      equality (Fin.append (fun k => if k = i then 1 else 0) (fun j => -v j i)) 0).flatten

theorem barycentricSystem_correct {n m : ℕ} (v : Fin m → Fin n → ℚ)
    (x : Fin n → ℝ) (w : Fin m → ℝ) :
    Satisfies (barycentricSystem v) (Fin.append x w) ↔
      (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
        ∑ j, w j • (fun i => (v j i : ℝ)) = x := by
  first
  | rw [barycentricSystem, satisfies_append, satisfies_append, satisfies_ofFn,
      satisfies_equality, satisfies_flatten_ofFn]
    simp only [nonnegativeConstraint_holds]
    have hsum : (∑ k : Fin (n + m),
        ((Fin.append (fun _ : Fin n => (0 : ℚ)) (fun _ : Fin m => 1)) k : ℝ) *
          Fin.append x w k) = ∑ j, w j := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Rat.cast_zero, Rat.cast_one,
        zero_mul, one_mul, Finset.sum_const_zero, zero_add]
    rw [hsum]
    have hcoord : (∀ i : Fin n,
        Satisfies (equality (Fin.append (fun k => if k = i then 1 else 0)
          (fun j => -v j i)) 0) (Fin.append x w)) ↔
        ∑ j, w j • (fun i => (v j i : ℝ)) = x := by
      simp only [satisfies_equality]
      have heval : ∀ i : Fin n,
          (∑ k : Fin (n + m),
            ((Fin.append (fun k => if k = i then (1 : ℚ) else 0) (fun j => -v j i)) k : ℝ) *
              Fin.append x w k) = x i - ∑ j, (v j i : ℝ) * w j := by
        intro i
        rw [Fin.sum_univ_add]
        simp [Fin.append_left, Fin.append_right, apply_ite, ite_mul,
          Finset.sum_neg_distrib, sub_eq_add_neg]
      simp only [heval, Rat.cast_zero, sub_eq_zero]
      constructor
      · intro h
        funext i
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using (h i).symm
      · intro h i
        have hi := congrFun h i
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hi.symm
    rw [hcoord]
    simp only [Rat.cast_one, and_assoc]

/-- A finite executable rational halfspace representation of the hull. -/
def hullHalfspaces {n m : ℕ} (v : Fin m → Fin n → ℚ) : List (Inequality n) :=
  eliminateSuffix n m (barycentricSystem v)

/-- The computed halfspaces describe the literal real convex hull. -/
theorem hullHalfspaces_correct {n m : ℕ} (v : Fin m → Fin n → ℚ) (x : Fin n → ℝ) :
    Satisfies (hullHalfspaces v) x ↔
      x ∈ convexHull ℝ (range (fun j => fun i => (v j i : ℝ))) := by
  first
  | rw [hullHalfspaces, eliminateSuffix_correct, convexHull_range_finiteWeights]
    simp only [Set.mem_setOf_eq, barycentricSystem_correct]

end VolumePolynomials.RationalElimination
