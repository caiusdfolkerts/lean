import cubical.fogelsanger
import cubical.simplicial_face_graph
import cubical.simplicial_ridge_count
import Mathlib.Data.Nat.Choose.Basic

/-! # The simplicial lower bound theorem from minimal-cycle rigidity

All face numbers count actual finite vertex subsets. The induction uses actual
vertex links, and every edge lower bound is supplied by the kernel-checked
Fogelsanger theorem. No lower bound is assumed in the complex hypotheses.
-/

namespace Cubical.Simplicial

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

theorem IsFacetCircuit.two_faces_lower_bound {n : ℕ} {s : Finset (Finset V)}
    (hs : IsFacetCircuit id s) (hn : 3 ≤ n) (hpure : Pure n id s) :
    n * (vertices id s).card ≤ (faces s 2).card + (n + 1).choose 2 := by
  classical
  have h := hs.edge_count hn hpure
  rw [← Nat.card_eq_fintype_card, supportGraph_edge_count_eq_faces] at h
  exact h

/-- The binomial arithmetic in the McMullen--Perles--Walkup induction. -/
theorem simplicial_mpw_step {n r N e F : ℕ} (hn : 0 < n) (hr : 2 ≤ r)
    (hedge : n * N ≤ e + (n + 1).choose 2)
    (hlink : 2 * (n - 1).choose (r - 2) * e ≤
      r * F + (r - 2) * n.choose (r - 1) * N) :
    n.choose (r - 1) * N ≤ F + (r - 1) * (n + 1).choose r := by
  let A := (n - 1).choose (r - 2)
  let B := n.choose (r - 1)
  let C := (n + 1).choose r
  let T := (n + 1).choose 2
  have hA : n * A = B * (r - 1) := by
    have h := Nat.add_one_mul_choose_eq (n - 1) (r - 2)
    have hn' : n - 1 + 1 = n := by omega
    have hr' : r - 2 + 1 = r - 1 := by omega
    simpa only [hn', hr'] using h
  have hB : (n + 1) * B = C * r := by
    have h := Nat.add_one_mul_choose_eq n (r - 1)
    have hr' : r - 1 + 1 = r := by omega
    simpa only [hr'] using h
  have hT : (n + 1) * n = T * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq n 1
  have hconst : 2 * A * T = r * ((r - 1) * C) := by
    calc
      2 * A * T = A * ((n + 1) * n) := by rw [hT]; ring
      _ = (n + 1) * (n * A) := by ring
      _ = (n + 1) * (B * (r - 1)) := by rw [hA]
      _ = ((n + 1) * B) * (r - 1) := by ring
      _ = (C * r) * (r - 1) := by rw [hB]
      _ = r * ((r - 1) * C) := by ring
  have hcoeff : r * (B * N) + (r - 2) * B * N = 2 * A * (n * N) := by
    have hrarith : r + (r - 2) = 2 * (r - 1) := by omega
    calc
      r * (B * N) + (r - 2) * B * N = (r + (r - 2)) * B * N := by ring
      _ = (2 * (r - 1)) * B * N := by rw [hrarith]
      _ = 2 * (B * (r - 1)) * N := by ring
      _ = 2 * (n * A) * N := by rw [← hA]
      _ = 2 * A * (n * N) := by ring
  have hfinal : r * (B * N) + (r - 2) * B * N ≤
      r * (F + (r - 1) * C) + (r - 2) * B * N := by
    calc
      r * (B * N) + (r - 2) * B * N = 2 * A * (n * N) := hcoeff
      _ ≤ 2 * A * (e + T) := Nat.mul_le_mul_left _ hedge
      _ = 2 * A * e + 2 * A * T := by ring
      _ ≤ (r * F + (r - 2) * B * N) + 2 * A * T := Nat.add_le_add_right hlink _
      _ = r * (F + (r - 1) * C) + (r - 2) * B * N := by rw [hconst]; ring
  have hmul : r * (B * N) ≤ r * (F + (r - 1) * C) :=
    Nat.le_of_add_le_add_right hfinal
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

/-- Every lower-dimensional face-number bound for a pure finite simplicial
family whose links of dimension at least two are minimal mod-two cycles. -/
theorem simplicial_lower_bound {n : ℕ} (hn : 3 ≤ n)
    {s : Finset (Finset V)} (hne : s.Nonempty) (hpure : Pure n id s)
    (hlinks : HasCircuitLinks n s) {r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n - 1) :
    n.choose (r - 1) * (vertices id s).card ≤
      (faces s r).card + (r - 1) * (n + 1).choose r := by
  classical
  induction n using Nat.strong_induction_on generalizing s r with
  | h n ih =>
    by_cases hr1 : r = 1
    · subst r
      simp
    have hr2 : 2 ≤ r := by omega
    have hedge := (hlinks.circuit hn hne).two_faces_lower_bound hn hpure
    by_cases hr_eq : r = 2
    · subst r
      simpa using hedge
    have hr3 : 3 ≤ r := by omega
    have hn4 : 4 ≤ n := by omega
    have hlocal : ∀ v ∈ vertices id s,
        (n - 1).choose (r - 2) * (vertices id (link s {v})).card ≤
          (faces (link s {v}) (r - 1)).card +
            (r - 2) * n.choose (r - 1) := by
      intro v hv
      have hlpure : Pure (n - 1) id (link s {v}) := by simpa using hpure.link {v}
      have h := ih (n - 1) (by omega) (by omega : 3 ≤ n - 1)
        (link_vertex_nonempty hv) hlpure (hlinks.link_vertex v)
        (r := r - 1) (by omega) (by omega)
      have hr' : r - 1 - 1 = r - 2 := by omega
      have hn' : n - 1 + 1 = n := by omega
      simpa only [hr', hn'] using h
    have hsum := Finset.sum_le_sum hlocal
    have hsumlinks := sum_link_faces s (r - 1)
    have hr' : r - 1 + 1 = r := by omega
    rw [hr'] at hsumlinks
    have hlink : 2 * (n - 1).choose (r - 2) * (faces s 2).card ≤
        r * (faces s r).card + (r - 2) * n.choose (r - 1) * (vertices id s).card := by
      simpa only [← Finset.mul_sum, Finset.sum_add_distrib, sum_link_vertices,
        hsumlinks, Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm] using hsum
    exact simplicial_mpw_step (by omega) hr2 hedge hlink

/-- The facet form of the simplicial lower bound theorem. -/
theorem simplicial_facet_lower_bound {n : ℕ} (hn : 3 ≤ n)
    {s : Finset (Finset V)} (hne : s.Nonempty) (hpure : Pure n id s)
    (hlinks : HasCircuitLinks n s) (hdeg : RidgeDegreeTwo s) :
    (n - 1) * (vertices id s).card ≤ s.card + (n - 2) * (n + 1) := by
  have hlower := simplicial_lower_bound hn hne hpure hlinks
    (r := n - 1) (by omega) le_rfl
  have hsub : n - 1 - 1 = n - 2 := by omega
  rw [hsub] at hlower
  have hchoose₁ : 2 * n.choose (n - 2) = n * (n - 1) := by
    rw [Nat.choose_symm (by omega : 2 ≤ n)]
    have h := Nat.add_one_mul_choose_eq (n - 1) 1
    have hn' : n - 1 + 1 = n := by omega
    simpa only [hn', Nat.choose_one_right, Nat.mul_comm] using h.symm
  have hchoose₂ : 2 * (n + 1).choose (n - 1) = n * (n + 1) := by
    have hidx : n - 1 = n + 1 - 2 := by omega
    rw [hidx, Nat.choose_symm (by omega : 2 ≤ n + 1)]
    have h := Nat.add_one_mul_choose_eq n 1
    simpa only [Nat.choose_one_right, Nat.mul_comm] using h.symm
  have hridges := hdeg.ridge_incidence (by omega : 0 < n) hpure
  have hmul := Nat.mul_le_mul_left 2 hlower
  have hrew : n * ((n - 1) * (vertices id s).card) ≤
      n * (s.card + (n - 2) * (n + 1)) := by
    calc
      n * ((n - 1) * (vertices id s).card) =
          (2 * n.choose (n - 2)) * (vertices id s).card := by rw [hchoose₁]; ring
      _ ≤ 2 * ((faces s (n - 1)).card + (n - 2) * (n + 1).choose (n - 1)) := by
        simpa only [Nat.mul_assoc] using hmul
      _ = 2 * (faces s (n - 1)).card +
          (n - 2) * (2 * (n + 1).choose (n - 1)) := by ring
      _ = n * s.card + (n - 2) * (n * (n + 1)) := by rw [← hridges, hchoose₂]
      _ = n * (s.card + (n - 2) * (n + 1)) := by ring
  exact Nat.le_of_mul_le_mul_left hrew (by omega)

end Cubical.Simplicial
