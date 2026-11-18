module

public import Recovery.Unimodular.GraphicSectionRing.Height
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub

/-!
# The unique staircase monomial in every graphic toric fiber

The fiber remembers the number of lattice points and their vector sum.  A
multiset is standard exactly when every pair belongs to a common staircase
simplex.  No full-dimensionality or generic-position hypothesis is used.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Unimodular.GraphicSectionRing

/-- Standard monomials are precisely the pairwise compatible multisets. -/
def Standard {n : ℕ} (M : Multiset (Lattice n)) : Prop :=
  ∀ x ∈ M, ∀ y ∈ M, Compatible x y

theorem compatible_comparable {n : ℕ} {x y : Lattice n}
    (h : Compatible x y) : x ≤ y ∨ y ≤ x := by
  classical
  by_cases hxy : x ≤ y
  · exact Or.inl hxy
  · right
    change ¬ (∀ i, x i ≤ y i) at hxy
    push_neg at hxy
    obtain ⟨i, hi⟩ := hxy
    intro j
    have hij := (h (some i) (some j)).2
    simp only [difference, anchored_some] at hij
    change y j ≤ x j
    omega

theorem compatible_coordinate_spread {n : ℕ} {x y : Lattice n}
    (h : Compatible x y) (i : Fin n) : -1 ≤ x i - y i ∧ x i - y i ≤ 1 := by
  simpa only [difference, anchored_some, anchored_none, sub_zero] using h (some i) none

theorem standard_of_cons {n : ℕ} {a : Lattice n} {M : Multiset (Lattice n)}
    (h : Standard (a ::ₘ M)) : Standard M := by
  intro x hx y hy
  exact h x (Multiset.mem_cons_of_mem hx) y (Multiset.mem_cons_of_mem hy)

theorem standard_exists_min {n : ℕ} {M : Multiset (Lattice n)}
    (hM : Standard M) (hne : M ≠ 0) : ∃ a ∈ M, ∀ y ∈ M, a ≤ y := by
  induction M using Multiset.induction_on with
  | empty => exact (hne rfl).elim
  | @cons a M ih =>
    by_cases hzero : M = 0
    · subst M
      exact ⟨a, by simp, by simp⟩
    · obtain ⟨b, hb, hmin⟩ := ih (standard_of_cons hM) hzero
      rcases compatible_comparable (hM a (by simp) b (Multiset.mem_cons_of_mem hb)) with hab | hba
      · refine ⟨a, by simp, ?_⟩
        intro y hy
        rcases Multiset.mem_cons.mp hy with rfl | hy
        · exact le_rfl
        · exact le_trans hab (hmin y hy)
      · refine ⟨b, Multiset.mem_cons_of_mem hb, ?_⟩
        intro y hy
        rcases Multiset.mem_cons.mp hy with rfl | hy
        · exact hba
        · exact hmin y hy

theorem multiset_sum_apply {n : ℕ} (M : Multiset (Lattice n)) (i : Fin n) :
    M.sum i = (M.map (fun x => x i)).sum := by
  induction M using Multiset.induction_on with
  | empty => rfl
  | cons a M ih => simpa using congrArg (fun t : ℤ => a i + t) ih

/-- The least vertex of a standard monomial is its coordinatewise integral mean. -/
theorem standard_min_formula {n : ℕ} {M : Multiset (Lattice n)} (hM : Standard M)
    {a : Lattice n} (ha : a ∈ M) (hmin : ∀ y ∈ M, a ≤ y) (i : Fin n) :
    a i = M.sum i / (M.card : ℤ) := by
  obtain ⟨N, rfl⟩ := Multiset.exists_cons_of_mem ha
  have hbounds : ∀ y ∈ N, a i ≤ y i ∧ y i ≤ a i + 1 := by
    intro y hy
    have hc := compatible_coordinate_spread
      (hM y (Multiset.mem_cons_of_mem hy) a (by simp)) i
    exact ⟨hmin y (Multiset.mem_cons_of_mem hy) i, by omega⟩
  have hlo := Multiset.card_nsmul_le_sum (s := N.map (fun y => y i))
    (a := a i) (by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
      exact (hbounds y hy).1)
  have hhi := Multiset.sum_le_card_nsmul (N.map (fun y => y i)) (a i + 1) (by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
    exact (hbounds y hy).2)
  simp only [Multiset.card_map, nsmul_eq_mul] at hlo hhi
  symm
  apply (Int.ediv_eq_iff_of_pos (by simp : (0 : ℤ) < ((a ::ₘ N).card : ℤ))).mpr
  rw [Multiset.card_cons, Nat.cast_add, Nat.cast_one, Multiset.sum_cons]
  change a i * ((N.card : ℤ) + 1) ≤ a i + N.sum i ∧
    a i + N.sum i < a i * ((N.card : ℤ) + 1) + ((N.card : ℤ) + 1)
  rw [multiset_sum_apply]
  constructor <;> nlinarith

/-- Distinct standard monomials never have the same toric degree. -/
theorem standard_unique {n : ℕ} (M N : Multiset (Lattice n))
    (hM : Standard M) (hN : Standard N)
    (hcard : M.card = N.card) (hsum : M.sum = N.sum) : M = N := by
  classical
  suffices H : ∀ k, ∀ M N : Multiset (Lattice n), M.card = k → N.card = k →
      Standard M → Standard N → M.sum = N.sum → M = N by
    exact H M.card M N rfl hcard.symm hM hN hsum
  intro k
  induction k with
  | zero =>
    intro M N hM hN _ _ _
    have hMz : M = 0 := Multiset.card_eq_zero.mp hM
    have hNz : N = 0 := Multiset.card_eq_zero.mp hN
    exact hMz.trans hNz.symm
  | succ k ih =>
    intro M N hMc hNc hM hN hs
    have hMne : M ≠ 0 := by intro h; simp [h] at hMc
    have hNne : N ≠ 0 := by intro h; simp [h] at hNc
    obtain ⟨a, ha, hamin⟩ := standard_exists_min hM hMne
    obtain ⟨b, hb, hbmin⟩ := standard_exists_min hN hNne
    have hab : a = b := by
      funext i
      rw [standard_min_formula hM ha hamin, standard_min_formula hN hb hbmin,
        hMc, hNc, hs]
    subst b
    obtain ⟨M', rfl⟩ := Multiset.exists_cons_of_mem ha
    obtain ⟨N', rfl⟩ := Multiset.exists_cons_of_mem hb
    have hcM : M'.card = k := by simpa using hMc
    have hcN : N'.card = k := by simpa using hNc
    have hss : M'.sum = N'.sum := by simpa only [Multiset.sum_cons, add_left_cancel_iff] using hs
    exact congrArg (Multiset.cons a) (ih M' N' hcM hcN (standard_of_cons hM)
      (standard_of_cons hN) hss)

theorem balanced_anchored_mono {n k : ℕ} (m : Lattice n) {r s : Fin k}
    (hrs : r ≤ s) (a : Coordinate n) :
    anchored (balanced m r) a ≤ anchored (balanced m s) a := by
  rw [anchored_balanced, anchored_balanced]
  exact Int.ediv_le_ediv (by exact_mod_cast Nat.zero_lt_of_lt r.isLt)
    (by
      have hrs' : (r : ℤ) ≤ (s : ℤ) := by exact_mod_cast hrs
      simpa [add_comm] using add_le_add_left hrs' (anchored m a))

theorem balanced_anchored_spread {n k : ℕ} (m : Lattice n) (r s : Fin k)
    (a : Coordinate n) :
    anchored (balanced m r) a - anchored (balanced m s) a ≤ 1 := by
  rw [anchored_balanced, anchored_balanced]
  have hk : (0 : ℤ) < k := by exact_mod_cast Nat.zero_lt_of_lt r.isLt
  have hr : (r : ℤ) < k := by exact_mod_cast r.isLt
  have hs : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg _
  simpa using ediv_difference_le (anchored m a + (r : ℕ))
    (anchored m a + (s : ℕ)) 1 k 0 hk (by omega)

theorem compatible_balanced {n k : ℕ} (m : Lattice n) (r s : Fin k) :
    Compatible (balanced m r) (balanced m s) := by
  intro a b
  rcases le_total r s with hrs | hsr
  · have ha := balanced_anchored_mono m hrs a
    have hb := balanced_anchored_mono m hrs b
    have ha' := balanced_anchored_spread m s r a
    have hb' := balanced_anchored_spread m s r b
    simp only [difference]
    omega
  · have ha := balanced_anchored_mono m hsr a
    have hb := balanced_anchored_mono m hsr b
    have ha' := balanced_anchored_spread m r s a
    have hb' := balanced_anchored_spread m r s b
    simp only [difference]
    omega

/-- The canonical multiset is defined even in degree zero. -/
def canonical {n : ℕ} (k : ℕ) (m : Lattice n) : Multiset (Lattice n) :=
  Finset.univ.val.map (fun r : Fin k => balanced m r)

@[simp] theorem canonical_card {n k : ℕ} (m : Lattice n) :
    (canonical k m).card = k := by
  simp [canonical]

theorem canonical_sum {n k : ℕ} (hk : 0 < k) (m : Lattice n) :
    (canonical k m).sum = m := by
  change (∑ r : Fin k, balanced m r) = m
  exact balanced_sum hk m

theorem canonical_standard {n k : ℕ} (m : Lattice n) : Standard (canonical k m) := by
  intro x hx y hy
  obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨s, _, rfl⟩ := Multiset.mem_map.mp hy
  exact compatible_balanced m r s

theorem canonical_satisfies {n k : ℕ} (hk : 0 < k) {C : Set (Constraint n)}
    (m : Lattice n) (hm : ∀ c ∈ C, difference m c.left c.right ≤ (k : ℤ) * c.bound)
    {x : Lattice n} (hx : x ∈ canonical k m) : Satisfies C x := by
  obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp hx
  exact balanced_satisfies hk m hm r

/-- This is uniqueness in the actual degree-and-lattice-sum fiber. -/
theorem eq_canonical_of_standard {n : ℕ} (M : Multiset (Lattice n))
    (hM : Standard M) : M = canonical M.card M.sum := by
  by_cases hzero : M = 0
  · subst M
    symm
    apply Multiset.card_eq_zero.mp
    exact canonical_card (k := 0) (0 : Lattice n)
  · exact standard_unique M (canonical M.card M.sum) hM (canonical_standard _)
      (canonical_card _).symm (canonical_sum (Multiset.card_pos.mpr hzero) _).symm

#print axioms standard_unique
#print axioms eq_canonical_of_standard
#print axioms canonical_satisfies

end Unimodular.GraphicSectionRing
