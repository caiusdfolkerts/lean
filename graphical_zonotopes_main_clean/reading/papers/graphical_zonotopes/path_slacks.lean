module

public import Papers.GraphicalZonotopes.PathTight
public import Papers.GraphicalZonotopes.BooleanSlacks

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open Finset
open scoped BigOperators

/-- A window bound proved directly in natural arithmetic, without an inline
reflection proof in a dependent finite-index expression. -/
theorem window_index_bound {n p k : ℕ} (i : Fin (n-p)) (hk : k ≤ p) :
    i.val+k<n :=
  (Nat.add_le_add_left hk i.val).trans_lt (Nat.lt_sub_iff_add_lt.mp i.isLt)

theorem eq_vertex_iff_integer {n i a : ℕ} (h : i+a<n) (u : Fin n) :
    u = vertex n i a h ↔ (u.val : ℤ) = (i : ℤ)+a := by
  constructor
  · rintro rfl
    simp [vertex]
  · intro he
    apply Fin.ext
    dsimp [vertex]
    exact_mod_cast he

theorem membershipBit_vertex {n i a : ℕ} (h : i+a<n) (S : Finset (Fin n)) :
    membershipBit S (vertex n i a h) = integerBit S ((i : ℤ)+a) := by
  rw [← integerBit_cast]
  simp [vertex]

theorem sum_window_pair_single {n p a b c : ℕ}
    (ha : a ≤ p) (hb : b ≤ p) (hc : c ≤ p)
    (u v : Fin n) (S : Finset (Fin n))
    (hsupport : (v.val : ℤ) = u.val + ((b : ℤ)-a) →
      integerBit S ((u.val : ℤ)-a+c) ≠ 0 →
      0 ≤ (u.val : ℤ)-a ∧ (u.val : ℤ)-a < ((n-p : ℕ) : ℤ)) :
    (∑ i : Fin (n-p),
      if u = vertex n i.val a (by omega) ∧ v = vertex n i.val b (by omega)
      then membershipBit S (vertex n i.val c (by omega)) else 0) =
      if (v.val : ℤ) = u.val + ((b : ℤ)-a)
      then integerBit S ((u.val : ℤ)-a+c) else 0 := by
  simp_rw [eq_vertex_iff_integer, membershipBit_vertex]
  exact sum_pair_start (n-p) a b u.val v.val (fun j => integerBit S (j+c)) hsupport

theorem sum_window_pair_double {n p a b c d : ℕ}
    (ha : a ≤ p) (hb : b ≤ p) (hc : c ≤ p) (hd : d ≤ p)
    (u v : Fin n) (S : Finset (Fin n))
    (hsupport : (v.val : ℤ) = u.val + ((b : ℤ)-a) →
      integerBit S ((u.val : ℤ)-a+c) * integerBit S ((u.val : ℤ)-a+d) ≠ 0 →
      0 ≤ (u.val : ℤ)-a ∧ (u.val : ℤ)-a < ((n-p : ℕ) : ℤ)) :
    (∑ i : Fin (n-p),
      if u = vertex n i.val a (by omega) ∧ v = vertex n i.val b (by omega)
      then membershipBit S (vertex n i.val c (by omega)) *
        membershipBit S (vertex n i.val d (by omega)) else 0) =
      if (v.val : ℤ) = u.val + ((b : ℤ)-a)
      then integerBit S ((u.val : ℤ)-a+c) * integerBit S ((u.val : ℤ)-a+d) else 0 := by
  simp_rw [eq_vertex_iff_integer, membershipBit_vertex]
  exact sum_pair_start (n-p) a b u.val v.val
    (fun j => integerBit S (j+c) * integerBit S (j+d)) hsupport

/-- The complete contribution of all consecutive triples, including those
adjacent to the two ends of the finite path. -/
theorem delta_consecutive_triples {n : ℕ} {u v : Fin n} {S : Finset (Fin n)}
    (huv : u < v) (hu : u ∉ S) (hv : v ∉ S) :
    delta (∑ i : Fin (n-2), setMonomial (window n i.val {0,1,2})) u v S =
      (if (v.val : ℤ) = u.val+1 then integerBit S (u.val+2) else 0) +
      (if (v.val : ℤ) = u.val+2 then integerBit S (u.val+1) else 0) +
      (if (v.val : ℤ) = u.val+1 then integerBit S ((u.val : ℤ)-1) else 0) := by
  rw [delta_sum]
  have hrow (i : Fin (n-2)) :
      delta (setMonomial (window n i.val {0,1,2})) u v S =
        (if u = vertex n i.val 0 (window_index_bound (n := n) (p := 2) i (by decide)) ∧ v = vertex n i.val 1 (window_index_bound (n := n) (p := 2) i (by decide))
          then membershipBit S (vertex n i.val 2 (window_index_bound (n := n) (p := 2) i (by decide))) else 0) +
        (if u = vertex n i.val 0 (window_index_bound (n := n) (p := 2) i (by decide)) ∧ v = vertex n i.val 2 (window_index_bound (n := n) (p := 2) i (by decide))
          then membershipBit S (vertex n i.val 1 (window_index_bound (n := n) (p := 2) i (by decide))) else 0) +
        (if u = vertex n i.val 1 (window_index_bound (n := n) (p := 2) i (by decide)) ∧ v = vertex n i.val 2 (window_index_bound (n := n) (p := 2) i (by decide))
          then membershipBit S (vertex n i.val 0 (window_index_bound (n := n) (p := 2) i (by decide))) else 0) := by
    rw [window_triple_eq (window_index_bound (n := n) (p := 2) i (by decide))
      (window_index_bound (n := n) (p := 2) i (by decide)) (window_index_bound (n := n) (p := 2) i (by decide))]
    exact delta_monomial_three (by change (i.val + 0 : ℕ) < (i.val + 1 : ℕ); omega)
      (by change (i.val + 1 : ℕ) < (i.val + 2 : ℕ); omega) huv hu hv
  simp_rw [hrow]
  rw [sum_add_distrib, sum_add_distrib]
  rw [sum_window_pair_single (by decide : 0 ≤ 2) (by decide : 1 ≤ 2) (by decide : 2 ≤ 2) u v S (by
    intro hdist hr
    have hb := integerBit_bounds_of_ne_zero hr
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  rw [sum_window_pair_single (by decide : 0 ≤ 2) (by decide : 2 ≤ 2) (by decide : 1 ≤ 2) u v S (by
    intro hdist hr
    have hb := integerBit_bounds_of_ne_zero hr
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  rw [sum_window_pair_single (by decide : 1 ≤ 2) (by decide : 2 ≤ 2) (by decide : 0 ≤ 2) u v S (by
    intro hdist hr
    have hb := integerBit_bounds_of_ne_zero hr
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  norm_num

/-- The complete contribution of all `023` triples. -/
theorem delta_skipped_triples {n : ℕ} {u v : Fin n} {S : Finset (Fin n)}
    (huv : u < v) (hu : u ∉ S) (hv : v ∉ S) :
    delta (∑ i : Fin (n-3), setMonomial (window n i.val {0,2,3})) u v S =
      (if (v.val : ℤ) = u.val+2 then integerBit S (u.val+3) else 0) +
      (if (v.val : ℤ) = u.val+3 then integerBit S (u.val+2) else 0) +
      (if (v.val : ℤ) = u.val+1 then integerBit S ((u.val : ℤ)-2) else 0) := by
  rw [delta_sum]
  have hrow (i : Fin (n-3)) :
      delta (setMonomial (window n i.val {0,2,3})) u v S =
        (if u = vertex n i.val 0 (window_index_bound (n := n) (p := 3) i (by decide)) ∧ v = vertex n i.val 2 (window_index_bound (n := n) (p := 3) i (by decide))
          then membershipBit S (vertex n i.val 3 (window_index_bound (n := n) (p := 3) i (by decide))) else 0) +
        (if u = vertex n i.val 0 (window_index_bound (n := n) (p := 3) i (by decide)) ∧ v = vertex n i.val 3 (window_index_bound (n := n) (p := 3) i (by decide))
          then membershipBit S (vertex n i.val 2 (window_index_bound (n := n) (p := 3) i (by decide))) else 0) +
        (if u = vertex n i.val 2 (window_index_bound (n := n) (p := 3) i (by decide)) ∧ v = vertex n i.val 3 (window_index_bound (n := n) (p := 3) i (by decide))
          then membershipBit S (vertex n i.val 0 (window_index_bound (n := n) (p := 3) i (by decide))) else 0) := by
    rw [window_triple_eq (window_index_bound (n := n) (p := 3) i (by decide))
      (window_index_bound (n := n) (p := 3) i (by decide)) (window_index_bound (n := n) (p := 3) i (by decide))]
    exact delta_monomial_three (by change (i.val + 0 : ℕ) < (i.val + 2 : ℕ); omega)
      (by change (i.val + 2 : ℕ) < (i.val + 3 : ℕ); omega) huv hu hv
  simp_rw [hrow]
  rw [sum_add_distrib, sum_add_distrib]
  rw [sum_window_pair_single (by decide : 0 ≤ 3) (by decide : 2 ≤ 3) (by decide : 3 ≤ 3) u v S (by
    intro hdist hr
    have hb := integerBit_bounds_of_ne_zero hr
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  rw [sum_window_pair_single (by decide : 0 ≤ 3) (by decide : 3 ≤ 3) (by decide : 2 ≤ 3) u v S (by
    intro hdist hr
    have hb := integerBit_bounds_of_ne_zero hr
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  rw [sum_window_pair_single (by decide : 2 ≤ 3) (by decide : 3 ≤ 3) (by decide : 0 ≤ 3) u v S (by
    intro hdist hr
    have hb := integerBit_bounds_of_ne_zero hr
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  norm_num

/-- All six pair contributions of the four-vertex windows. -/
theorem delta_tetrahedra {n : ℕ} {u v : Fin n} {S : Finset (Fin n)}
    (huv : u < v) (hu : u ∉ S) (hv : v ∉ S) :
    delta (∑ i : Fin (n-3), setMonomial (window n i.val {0,1,2,3})) u v S =
      (if (v.val : ℤ) = u.val+1 then integerBit S (u.val+2) * integerBit S (u.val+3) else 0) +
      (if (v.val : ℤ) = u.val+2 then integerBit S (u.val+1) * integerBit S (u.val+3) else 0) +
      (if (v.val : ℤ) = u.val+3 then integerBit S (u.val+1) * integerBit S (u.val+2) else 0) +
      (if (v.val : ℤ) = u.val+1 then integerBit S ((u.val : ℤ)-1) * integerBit S (u.val+2) else 0) +
      (if (v.val : ℤ) = u.val+2 then integerBit S ((u.val : ℤ)-1) * integerBit S (u.val+1) else 0) +
      (if (v.val : ℤ) = u.val+1 then integerBit S ((u.val : ℤ)-2) * integerBit S ((u.val : ℤ)-1) else 0) := by
  rw [delta_sum]
  have hrow (i : Fin (n-3)) := delta_monomial_four
    (a := vertex n i.val 0 (window_index_bound (n := n) (p := 3) i (by decide))) (b := vertex n i.val 1 (window_index_bound (n := n) (p := 3) i (by decide)))
    (c := vertex n i.val 2 (window_index_bound (n := n) (p := 3) i (by decide))) (d := vertex n i.val 3 (window_index_bound (n := n) (p := 3) i (by decide)))
    (by change (i.val + 0 : ℕ) < (i.val + 1 : ℕ); omega) (by change (i.val + 1 : ℕ) < (i.val + 2 : ℕ); omega)
    (by change (i.val + 2 : ℕ) < (i.val + 3 : ℕ); omega) huv hu hv
  have hw (i : Fin (n-3)) : window n i.val {0,1,2,3} =
      {vertex n i.val 0 (window_index_bound (n := n) (p := 3) i (by decide)), vertex n i.val 1 (window_index_bound (n := n) (p := 3) i (by decide)),
       vertex n i.val 2 (window_index_bound (n := n) (p := 3) i (by decide)), vertex n i.val 3 (window_index_bound (n := n) (p := 3) i (by decide))} :=
    window_quad_eq (window_index_bound (n := n) (p := 3) i (by decide))
      (window_index_bound (n := n) (p := 3) i (by decide)) (window_index_bound (n := n) (p := 3) i (by decide))
      (window_index_bound (n := n) (p := 3) i (by decide))
  simp_rw [hw, hrow]
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_add_distrib]
  rw [sum_window_pair_double (by decide : 0 ≤ 3) (by decide : 1 ≤ 3)
    (by decide : 2 ≤ 3) (by decide : 3 ≤ 3) u v S (by
    intro hdist hr
    obtain ⟨h1,h2⟩ := mul_ne_zero_iff.mp hr
    have hb1 := integerBit_bounds_of_ne_zero h1
    have hb2 := integerBit_bounds_of_ne_zero h2
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  rw [sum_window_pair_double (by decide : 0 ≤ 3) (by decide : 2 ≤ 3)
    (by decide : 1 ≤ 3) (by decide : 3 ≤ 3) u v S (by
    intro hdist hr
    obtain ⟨h1,h2⟩ := mul_ne_zero_iff.mp hr
    have hb1 := integerBit_bounds_of_ne_zero h1
    have hb2 := integerBit_bounds_of_ne_zero h2
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  rw [sum_window_pair_double (by decide : 0 ≤ 3) (by decide : 3 ≤ 3)
    (by decide : 1 ≤ 3) (by decide : 2 ≤ 3) u v S (by
    intro hdist hr
    obtain ⟨h1,h2⟩ := mul_ne_zero_iff.mp hr
    have hb1 := integerBit_bounds_of_ne_zero h1
    have hb2 := integerBit_bounds_of_ne_zero h2
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  rw [sum_window_pair_double (by decide : 1 ≤ 3) (by decide : 2 ≤ 3)
    (by decide : 0 ≤ 3) (by decide : 3 ≤ 3) u v S (by
    intro hdist hr
    obtain ⟨h1,h2⟩ := mul_ne_zero_iff.mp hr
    have hb1 := integerBit_bounds_of_ne_zero h1
    have hb2 := integerBit_bounds_of_ne_zero h2
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  rw [sum_window_pair_double (by decide : 1 ≤ 3) (by decide : 3 ≤ 3)
    (by decide : 0 ≤ 3) (by decide : 2 ≤ 3) u v S (by
    intro hdist hr
    obtain ⟨h1,h2⟩ := mul_ne_zero_iff.mp hr
    have hb1 := integerBit_bounds_of_ne_zero h1
    have hb2 := integerBit_bounds_of_ne_zero h2
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  rw [sum_window_pair_double (by decide : 2 ≤ 3) (by decide : 3 ≤ 3)
    (by decide : 0 ≤ 3) (by decide : 1 ≤ 3) u v S (by
    intro hdist hr
    obtain ⟨h1,h2⟩ := mul_ne_zero_iff.mp hr
    have hb1 := integerBit_bounds_of_ne_zero h1
    have hb2 := integerBit_bounds_of_ne_zero h2
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  have h13 : (u.val : ℤ)-1+3=u.val+2 := by omega
  have h12 : (u.val : ℤ)-1+2=u.val+1 := by omega
  have h21 : (u.val : ℤ)-2+1=(u.val : ℤ)-1 := by omega
  norm_num [h13,h12,h21]

/-- Exact arbitrary-length slack formula, with no omitted endpoint cases. -/
theorem delta_formula {n : ℕ} {u v : Fin n} {S : Finset (Fin n)}
    (huv : u < v) (hu : u ∉ S) (hv : v ∉ S) :
    delta (setFunction n) u v S =
      if (v.val : ℤ) = u.val+1 then
        integerBit S ((u.val : ℤ)-2) * (1-integerBit S ((u.val : ℤ)-1)) +
        integerBit S ((u.val : ℤ)-1) * (1-integerBit S (u.val+2)) +
        integerBit S (u.val+2) * (1-integerBit S (u.val+3))
      else if (v.val : ℤ) = u.val+2 then
        integerBit S (u.val+1) * (1-integerBit S ((u.val : ℤ)-1)) +
        integerBit S (u.val+3) * (1-integerBit S (u.val+1))
      else if (v.val : ℤ) = u.val+3 then
        integerBit S (u.val+2) * (1-integerBit S (u.val+1))
      else 0 := by
  rw [setFunction_expansion, delta_sub, delta_add,
    delta_consecutive_triples huv hu hv, delta_skipped_triples huv hu hv,
    delta_tetrahedra huv hu hv]
  by_cases h1 : (v.val : ℤ) = u.val+1
  · have h2 : ¬(v.val : ℤ) = u.val+2 := by omega
    have h3 : ¬(v.val : ℤ) = u.val+3 := by omega
    simp only [if_pos h1, if_neg h2, if_neg h3]
    ring
  · by_cases h2 : (v.val : ℤ) = u.val+2
    · have h3 : ¬(v.val : ℤ) = u.val+3 := by omega
      simp only [if_neg h1, if_pos h2, if_neg h3]
      ring
    · by_cases h3 : (v.val : ℤ) = u.val+3
      · simp only [if_neg h1, if_neg h2, if_pos h3]
        ring
      · simp [h1,h2,h3]

theorem delta_symm {V : Type*} [Fintype V] [DecidableEq V]
    (f : SetFunction V) (u v : V) (S : Finset V) : delta f u v S = delta f v u S := by
  unfold delta
  rw [insert_comm]
  ring

theorem slack_bounds {n : ℕ} {u v : Fin n} (huv : u ≠ v) {S : Finset (Fin n)}
    (hu : u ∉ S) (hv : v ∉ S) :
    0 ≤ delta (setFunction n) u v S ∧ delta (setFunction n) u v S ≤ 2 := by
  have hordered : ∀ a b : Fin n, a < b → a ∉ S → b ∉ S →
      0 ≤ delta (setFunction n) a b S ∧ delta (setFunction n) a b S ≤ 2 := by
    intro a b hab ha hb
    rw [delta_formula hab ha hb]
    split
    · exact path_boolean_slack_one (integerBit_zero_or_one _ _) (integerBit_zero_or_one _ _)
        (integerBit_zero_or_one _ _) (integerBit_zero_or_one _ _)
    · split
      · have h := path_boolean_slack_two (integerBit_zero_or_one S ((a.val : ℤ)-1))
          (integerBit_zero_or_one S (a.val+1)) (integerBit_zero_or_one S (a.val+3))
        exact ⟨h.1, h.2.trans (by norm_num)⟩
      · split
        · have h := path_boolean_slack_three (integerBit_zero_or_one S (a.val+1))
            (integerBit_zero_or_one S (a.val+2))
          exact ⟨h.1, h.2.trans (by norm_num)⟩
        · norm_num
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · exact hordered u v hlt hu hv
  · rw [delta_symm]
    exact hordered v u hgt hv hu

theorem setFunction_supermodular (n : ℕ) : Supermodular (setFunction n) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  exact (slack_bounds huv hu hv).1

end Path
end GraphicalZonotopes
