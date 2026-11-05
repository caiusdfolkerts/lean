module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega

/-!
# Odd edge fibers of a walk in a closed strip

The fiber at height a consists of the actual times at which the walk crosses
the edge from a to a+1. Crossings alternate up and down. A walk from zero to
the top of its strip crosses every edge an odd number of times, and its
down-steps are precisely the odd positions within these ordered fibers.

The statements use arbitrary length and width; width zero is not excluded.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms.EvenWalkPartition

open scoped BigOperators

/-- A literal unit step, retaining both orientations. -/
def UnitStep (h : ℕ → ℕ) (i : ℕ) : Prop :=
  h (i + 1) = h i + 1 ∨ h i = h (i + 1) + 1

/-- Crossing the edge with lower endpoint a. -/
def Crosses (h : ℕ → ℕ) (a i : ℕ) : Prop :=
  min (h i) (h (i + 1)) = a

instance crosses_decidable (h : ℕ → ℕ) (a i : ℕ) :
    Decidable (Crosses h a i) := inferInstanceAs (Decidable (_ = _))

/-- The actual set of crossing times before a specified time. -/
def crossingTimes (h : ℕ → ℕ) (a t : ℕ) : Finset ℕ :=
  (Finset.range t).filter (Crosses h a)

def crossingCount (h : ℕ → ℕ) (a t : ℕ) : ℕ :=
  (crossingTimes h a t).card

@[simp] theorem mem_crossingTimes (h : ℕ → ℕ) (a t i : ℕ) :
    i ∈ crossingTimes h a t ↔ i < t ∧ Crosses h a i := by
  simp [crossingTimes]

@[simp] theorem crossingCount_zero (h : ℕ → ℕ) (a : ℕ) :
    crossingCount h a 0 = 0 := by
  simp [crossingCount, crossingTimes]

theorem crossingCount_succ (h : ℕ → ℕ) (a t : ℕ) :
    crossingCount h a (t + 1) =
      crossingCount h a t + if Crosses h a t then 1 else 0 := by
  classical
  unfold crossingCount crossingTimes
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases hc : Crosses h a t
  · simp only [hc, if_true]
    rw [Finset.card_insert_of_notMem]
    simp
  · simp [hc]

/-- The parity of the number of crossings records the side of an edge. -/
theorem crossingCount_parity (h : ℕ → ℕ) (a n : ℕ) (hzero : h 0 = 0)
    (hstep : ∀ i < n, UnitStep h i) :
    crossingCount h a n % 2 = if a < h n then 1 else 0 := by
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    have hn := ih (fun i hi => hstep i (by omega))
    have hs := hstep n (by omega)
    rw [crossingCount_succ]
    rcases hs with hs | hs
    · have hmin : min (h n) (h (n + 1)) = h n := min_eq_left (by omega)
      by_cases he : h n = a
      · have hc : Crosses h a n := hmin.trans he
        have hlo : ¬ a < h n := by omega
        have hhi : a < h (n + 1) := by omega
        rw [if_pos hc, if_pos hhi]
        have hpar : crossingCount h a n % 2 = 0 := by
          simpa only [if_neg hlo] using hn
        omega
      · have hc : ¬ Crosses h a n := fun hc => he (hmin.symm.trans hc)
        rw [if_neg hc, Nat.add_zero]
        have hi : a < h (n + 1) ↔ a < h n := by omega
        simpa only [hi] using hn
    · have hmin : min (h n) (h (n + 1)) = h (n + 1) := min_eq_right (by omega)
      by_cases he : h (n + 1) = a
      · have hc : Crosses h a n := hmin.trans he
        have hlo : a < h n := by omega
        have hhi : ¬ a < h (n + 1) := by omega
        rw [if_pos hc, if_neg hhi]
        have hpar : crossingCount h a n % 2 = 1 := by
          simpa only [if_pos hlo] using hn
        omega
      · have hc : ¬ Crosses h a n := fun hc => he (hmin.symm.trans hc)
        rw [if_neg hc, Nat.add_zero]
        have hi : a < h (n + 1) ↔ a < h n := by omega
        simpa only [hi] using hn

/-- Every edge of the strip is crossed an odd number of times. -/
theorem crossingTimes_odd (h : ℕ → ℕ) (n L a : ℕ) (hzero : h 0 = 0)
    (hfinal : h n = L) (hstep : ∀ i < n, UnitStep h i) (ha : a < L) :
    Odd (crossingTimes h a n).card := by
  apply Nat.odd_iff.mpr
  simpa only [crossingCount, hfinal, ha, if_true] using
    crossingCount_parity h a n hzero hstep

/-- The actual increasing enumeration of a crossing fiber. -/
def crossingEnumeration (h : ℕ → ℕ) (a n : ℕ) :
    Fin (crossingTimes h a n).card ↪o ℕ :=
  (crossingTimes h a n).orderEmbOfFin rfl

@[simp] theorem crossingEnumeration_mem (h : ℕ → ℕ) (a n : ℕ)
    (j : Fin (crossingTimes h a n).card) :
    crossingEnumeration h a n j ∈ crossingTimes h a n :=
  Finset.orderEmbOfFin_mem _ _ _

/-- Exactly j crossings occur before the j-th crossing. -/
theorem crossingCount_at_enumeration (h : ℕ → ℕ) (a n : ℕ)
    (j : Fin (crossingTimes h a n).card) :
    crossingCount h a (crossingEnumeration h a n j) = j.val := by
  classical
  let s := crossingTimes h a n
  let e := s.orderEmbOfFin rfl
  have hej : e j < n := (mem_crossingTimes h a n (e j)).mp
    (Finset.orderEmbOfFin_mem _ _ _) |>.1
  have himage : crossingTimes h a (e j) = (Finset.Iio j).image e := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxj, hxc⟩ := (mem_crossingTimes h a (e j) x).mp hx
      have hxs : x ∈ s := (mem_crossingTimes h a n x).mpr ⟨lt_trans hxj hej, hxc⟩
      obtain ⟨i, hi⟩ := (s.orderIsoOfFin rfl).surjective ⟨x, hxs⟩
      have he : e i = x := congrArg Subtype.val hi
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_Iio.mpr ?_, he⟩
      apply e.lt_iff_lt.mp
      simpa only [he] using hxj
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have his : e i ∈ s := Finset.orderEmbOfFin_mem _ _ _
      have hic := ((mem_crossingTimes h a n (e i)).mp his).2
      exact (mem_crossingTimes h a (e j) (e i)).mpr
        ⟨e.strictMono (Finset.mem_Iio.mp hi), hic⟩
  change (crossingTimes h a (e j)).card = j.val
  rw [himage, Finset.card_image_of_injective _ e.injective, Fin.card_Iio]

theorem downward_iff_above (h : ℕ → ℕ) (a i : ℕ)
    (hstep : UnitStep h i) (hcross : Crosses h a i) :
    h (i + 1) + 1 = h i ↔ a < h i := by
  unfold UnitStep at hstep
  unfold Crosses at hcross
  rcases hstep with hup | hdown
  · have hmin : min (h i) (h (i + 1)) = h i := min_eq_left (by omega)
    rw [hmin] at hcross
    omega
  · have hmin : min (h i) (h (i + 1)) = h (i + 1) := min_eq_right (by omega)
    rw [hmin] at hcross
    omega

/-- Odd ordinal positions in each edge fiber are precisely the down-steps. -/
theorem enumeration_downward_iff_odd (h : ℕ → ℕ) (a n : ℕ) (hzero : h 0 = 0)
    (hstep : ∀ i < n, UnitStep h i)
    (j : Fin (crossingTimes h a n).card) :
    h (crossingEnumeration h a n j + 1) + 1 =
        h (crossingEnumeration h a n j) ↔ Odd j.val := by
  let t := crossingEnumeration h a n j
  have ht : t < n ∧ Crosses h a t :=
    (mem_crossingTimes h a n t).mp (crossingEnumeration_mem h a n j)
  have hpar := crossingCount_parity h a t hzero
    (fun i hi => hstep i (lt_trans hi ht.1))
  rw [crossingCount_at_enumeration] at hpar
  have hpar' : j.val % 2 = if a < h t then 1 else 0 := hpar
  change h (t+1)+1=h t ↔ Odd j.val
  rw [downward_iff_above h a t (hstep t ht.1) ht.2, Nat.odd_iff]
  by_cases ha : a < h t
  · exact ⟨fun _ => by simpa only [ha, if_true] using hpar', fun _ => ha⟩
  · constructor
    · intro h
      exact (ha h).elim
    · intro hj
      have hz : j.val % 2 = 0 := by simpa only [ha, if_false] using hpar'
      omega

/-- The actual edge crossed by any step lies below the strip's top. -/
theorem crossed_edge_lt (h : ℕ → ℕ) (n L i : ℕ)
    (hbound : ∀ j ≤ n, h j ≤ L) (hstep : ∀ j < n, UnitStep h j) (hi : i < n) :
    min (h i) (h (i + 1)) < L := by
  have h₁ := hbound i (by omega)
  have h₂ := hbound (i + 1) (by omega)
  have hs := hstep i hi
  unfold UnitStep at hs
  rcases hs with hs | hs
  · rw [min_eq_left (by omega : h i ≤ h (i + 1))]
    omega
  · rw [min_eq_right (by omega : h (i + 1) ≤ h i)]
    omega

/-- The edge fibers partition all time positions, with their actual cardinalities. -/
theorem sum_crossingTimes_card (h : ℕ → ℕ) (n L : ℕ)
    (hbound : ∀ j ≤ n, h j ≤ L) (hstep : ∀ j < n, UnitStep h j) :
    (∑ a ∈ Finset.range L, (crossingTimes h a n).card) = n := by
  have hs := Finset.card_eq_sum_card_fiberwise
    (s := Finset.range n) (t := Finset.range L)
    (f := fun i => min (h i) (h (i + 1)))
    (fun i hi => Finset.mem_range.mpr
      (crossed_edge_lt h n L i hbound hstep (Finset.mem_range.mp hi)))
  have hset (a : ℕ) : crossingTimes h a n =
      (Finset.range n).filter (fun i => min (h i) (h (i + 1)) = a) := by
    ext i
    simp only [mem_crossingTimes, Finset.mem_filter, Finset.mem_range, Crosses]
  calc
    (∑ a ∈ Finset.range L, (crossingTimes h a n).card) =
        ∑ a ∈ Finset.range L,
          ((Finset.range n).filter (fun i => min (h i) (h (i + 1)) = a)).card := by
      apply Finset.sum_congr rfl
      intro a ha
      exact congrArg Finset.card (hset a)
    _ = n := by simpa only [Finset.card_range] using hs.symm

/-- The sum of the determinant degrees of the odd edge fibers is the number
of down-steps prescribed by the length and endpoint. -/
theorem sum_fiber_half_card (h : ℕ → ℕ) (n L q : ℕ) (hzero : h 0 = 0)
    (hfinal : h n = L) (hbound : ∀ j ≤ n, h j ≤ L)
    (hstep : ∀ i < n, UnitStep h i) (hsize : n = 2 * q + L) :
    (∑ a ∈ Finset.range L, (crossingTimes h a n).card / 2) = q := by
  have hodd (a : ℕ) (ha : a ∈ Finset.range L) :
      (crossingTimes h a n).card =
        2 * ((crossingTimes h a n).card / 2) + 1 := by
    have hm := Nat.odd_iff.mp
      (crossingTimes_odd h n L a hzero hfinal hstep (Finset.mem_range.mp ha))
    omega
  have hc := sum_crossingTimes_card h n L hbound hstep
  have hsum :
      (∑ a ∈ Finset.range L, (crossingTimes h a n).card) =
        2 * (∑ a ∈ Finset.range L, (crossingTimes h a n).card / 2) + L := by
    simp_rw [Finset.sum_congr rfl hodd]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range, smul_eq_mul, mul_one]
  omega

end PaperVerification.AlternatingForms.EvenWalkPartition

