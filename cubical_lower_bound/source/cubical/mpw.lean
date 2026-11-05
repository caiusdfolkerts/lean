import cubical.simplicial_lower_bound

/-! # The cubical McMullen--Perles--Walkup reduction

The statements use integral scalings, retaining the exact constants and the
color-imbalance improvement. The simplicial bounds used here have been proved
from the full minimal-cycle rigidity theorem.
-/

namespace Cubical.MPW

open Cubical.Simplicial
open scoped BigOperators

theorem face_bound_from_incidence {d i N e F Δ : ℕ} (hd : 1 ≤ d) (hi : 1 ≤ i)
    (hedge : (d + 1) * N + (d - 1) * Δ ≤ 2 * e + 2 ^ d)
    (hinc : 2 * (d - 1).choose (i - 1) * e ≤
      2 ^ i * F + (i - 1) * d.choose i * N) :
    (d.choose i + (d - 1).choose (i - 1)) * N +
        (d - 1) * (d - 1).choose (i - 1) * Δ ≤
      2 ^ i * F + 2 ^ d * (d - 1).choose (i - 1) := by
  let A := (d - 1).choose (i - 1)
  let B := d.choose i
  have hA : d * A = B * i := by
    have h := Nat.add_one_mul_choose_eq (d - 1) (i - 1)
    have hd' : d - 1 + 1 = d := by omega
    have hi' : i - 1 + 1 = i := by omega
    simpa only [hd', hi'] using h
  have hcoeff : (B + A) * N + (i - 1) * B * N = (d + 1) * A * N := by
    have hi' : i - 1 + 1 = i := by omega
    calc
      (B + A) * N + (i - 1) * B * N = (B * ((i - 1) + 1) + A) * N := by ring
      _ = (B * i + A) * N := by rw [hi']
      _ = (d * A + A) * N := by rw [← hA]
      _ = (d + 1) * A * N := by ring
  have hfinal : ((B + A) * N + (d - 1) * A * Δ) + (i - 1) * B * N ≤
      (2 ^ i * F + 2 ^ d * A) + (i - 1) * B * N := by
    calc
      ((B + A) * N + (d - 1) * A * Δ) + (i - 1) * B * N =
          ((B + A) * N + (i - 1) * B * N) + (d - 1) * A * Δ := by ring
      _ = (d + 1) * A * N + (d - 1) * A * Δ := by rw [hcoeff]
      _ = A * ((d + 1) * N + (d - 1) * Δ) := by ring
      _ ≤ A * (2 * e + 2 ^ d) := Nat.mul_le_mul_left A hedge
      _ = 2 * A * e + 2 ^ d * A := by ring
      _ ≤ (2 ^ i * F + (i - 1) * B * N) + 2 ^ d * A := Nat.add_le_add_right hinc _
      _ = (2 ^ i * F + 2 ^ d * A) + (i - 1) * B * N := by ring
  exact Nat.le_of_add_le_add_right hfinal

theorem facet_bound_from_incidence {d N e F Δ : ℕ} (hd : 3 ≤ d)
    (hedge : (d + 1) * N + (d - 1) * Δ ≤ 2 * e + 2 ^ d)
    (hinc : 2 * (d - 2) * e ≤ 2 ^ (d - 1) * F + d * (d - 3) * N) :
    2 * (d - 1) * N + (d - 1) * (d - 2) * Δ ≤
      2 ^ (d - 1) * F + (d - 2) * 2 ^ d := by
  have hcoeff : (d - 2) * (d + 1) = 2 * (d - 1) + d * (d - 3) := by
    have h1 : d - 1 + 1 = d := by omega
    have h2 : d - 2 + 2 = d := by omega
    have h3 : d - 3 + 3 = d := by omega
    nlinarith
  have hfinal : (2 * (d - 1) * N + (d - 1) * (d - 2) * Δ) + d * (d - 3) * N ≤
      (2 ^ (d - 1) * F + (d - 2) * 2 ^ d) + d * (d - 3) * N := by
    calc
      (2 * (d - 1) * N + (d - 1) * (d - 2) * Δ) + d * (d - 3) * N =
          (2 * (d - 1) + d * (d - 3)) * N + (d - 1) * (d - 2) * Δ := by ring
      _ = (d - 2) * ((d + 1) * N + (d - 1) * Δ) := by rw [← hcoeff]; ring
      _ ≤ (d - 2) * (2 * e + 2 ^ d) := Nat.mul_le_mul_left _ hedge
      _ = 2 * (d - 2) * e + (d - 2) * 2 ^ d := by ring
      _ ≤ (2 ^ (d - 1) * F + d * (d - 3) * N) + (d - 2) * 2 ^ d :=
        Nat.add_le_add_right hinc _
      _ = (2 ^ (d - 1) * F + (d - 2) * 2 ^ d) + d * (d - 3) * N := by ring
  exact Nat.le_of_add_le_add_right hfinal

theorem facet_bound_unstrengthened {d N e F : ℕ} (hd : 3 ≤ d)
    (hedge : (d + 1) * N ≤ 2 * e + 2 ^ d)
    (hinc : 2 * (d - 2) * e ≤ 2 ^ (d - 1) * F + d * (d - 3) * N) :
    (d - 1) * N ≤ 2 ^ (d - 2) * F + (d - 2) * 2 ^ (d - 1) := by
  have h := facet_bound_from_incidence (Δ := 0) hd (by simpa using hedge) hinc
  simp only [Nat.mul_zero, Nat.add_zero] at h
  have h1 : d - 2 + 1 = d - 1 := by omega
  have h2 : d - 1 + 1 = d := by omega
  have hp1 : 2 ^ (d - 1) = 2 * 2 ^ (d - 2) := by rw [← h1, pow_succ]; ring
  have hp2 : 2 ^ d = 2 * 2 ^ (d - 1) := by
    calc
      2 ^ d = 2 ^ ((d - 1) + 1) := congrArg (fun k : ℕ => 2 ^ k) h2.symm
      _ = 2 * 2 ^ (d - 1) := by rw [pow_succ]; ring
  have hmul : 2 * ((d - 1) * N) ≤
      2 * (2 ^ (d - 2) * F + (d - 2) * 2 ^ (d - 1)) := by
    simpa only [hp1, hp2, Nat.mul_add, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using h
  exact Nat.le_of_mul_le_mul_left hmul (by decide)

section Families

variable {X : Type*} [Fintype X] {V : X → Type*} [∀ x, DecidableEq (V x)]

/-- Sum the established simplicial lower bounds over the actual vertex
figures, then substitute the cubical edge bound. -/
theorem face_bound_of_simplicial_links {d i e F Δ : ℕ} (hd : 4 ≤ d)
    (hi : 1 ≤ i) (hid : i ≤ d - 2)
    (s : ∀ x, Finset (Finset (V x)))
    (hne : ∀ x, (s x).Nonempty) (hpure : ∀ x, Pure (d - 1) id (s x))
    (hlinks : ∀ x, HasCircuitLinks (d - 1) (s x))
    (hdegree : (∑ x, (vertices id (s x)).card) = 2 * e)
    (hincidence : (∑ x, (faces (s x) i).card) = 2 ^ i * F)
    (hedge : (d + 1) * Fintype.card X + (d - 1) * Δ ≤ 2 * e + 2 ^ d) :
    (d.choose i + (d - 1).choose (i - 1)) * Fintype.card X +
        (d - 1) * (d - 1).choose (i - 1) * Δ ≤
      2 ^ i * F + 2 ^ d * (d - 1).choose (i - 1) := by
  have hlocal : ∀ x, (d - 1).choose (i - 1) * (vertices id (s x)).card ≤
      (faces (s x) i).card + (i - 1) * d.choose i := by
    intro x
    have h := simplicial_lower_bound (by omega : 3 ≤ d - 1) (hne x) (hpure x)
      (hlinks x) hi (by omega : i ≤ d - 1 - 1)
    have hdi : d - 1 + 1 = d := by omega
    simpa only [hdi] using h
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hlocal x)
  have hinc : 2 * (d - 1).choose (i - 1) * e ≤
      2 ^ i * F + (i - 1) * d.choose i * Fintype.card X := by
    simpa only [← Finset.mul_sum, Finset.sum_add_distrib, hdegree, hincidence,
      Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
      Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using hsum
  exact face_bound_from_incidence (by omega) hi hedge hinc

/-- The separate top-dimensional incidence substitution, with the full
imbalance term. -/
theorem facet_bound_of_simplicial_links {d e F Δ : ℕ} (hd : 4 ≤ d)
    (s : ∀ x, Finset (Finset (V x)))
    (hne : ∀ x, (s x).Nonempty) (hpure : ∀ x, Pure (d - 1) id (s x))
    (hlinks : ∀ x, HasCircuitLinks (d - 1) (s x))
    (hdeg : ∀ x, RidgeDegreeTwo (s x))
    (hdegree : (∑ x, (vertices id (s x)).card) = 2 * e)
    (hincidence : (∑ x, (s x).card) = 2 ^ (d - 1) * F)
    (hedge : (d + 1) * Fintype.card X + (d - 1) * Δ ≤ 2 * e + 2 ^ d) :
    2 * (d - 1) * Fintype.card X + (d - 1) * (d - 2) * Δ ≤
      2 ^ (d - 1) * F + (d - 2) * 2 ^ d := by
  have hlocal : ∀ x, (d - 2) * (vertices id (s x)).card ≤
      (s x).card + d * (d - 3) := by
    intro x
    have h := simplicial_facet_lower_bound (by omega : 3 ≤ d - 1) (hne x)
      (hpure x) (hlinks x) (hdeg x)
    have h1 : d - 1 - 1 = d - 2 := by omega
    have h2 : d - 1 - 2 = d - 3 := by omega
    have h3 : d - 1 + 1 = d := by omega
    simpa only [h1, h2, h3, Nat.mul_comm] using h
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hlocal x)
  have hinc : 2 * (d - 2) * e ≤
      2 ^ (d - 1) * F + d * (d - 3) * Fintype.card X := by
    simpa only [← Finset.mul_sum, Finset.sum_add_distrib, hdegree, hincidence,
      Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
      Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using hsum
  exact facet_bound_from_incidence (by omega) hedge hinc

end Families

end Cubical.MPW
