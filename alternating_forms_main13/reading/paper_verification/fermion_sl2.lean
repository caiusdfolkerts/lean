module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.Divisibility.Units
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Ring

/-!
# The primitive-degree obstruction

This is the representation-theoretic core of the degree bound in Lemma 3.1.
The proof works over arbitrary commutative coefficient rings with the required
small integer factors invertible. No semisimplicity hypothesis is used.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.Fermion

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The two commutator relations needed for a raising/lowering argument. -/
structure RaisingLowering (e f h : Module.End R M) : Prop where
  lower_raise : e * f = f * e + h
  weight_raise : h * f = f * h - (2 : R) • f

namespace RaisingLowering

variable {e f h : Module.End R M} (H : RaisingLowering e f h)

include H

theorem lower_raise_apply (z : M) : e (f z) = f (e z) + h z := by
  simpa only [Module.End.mul_apply, LinearMap.add_apply] using
    congrArg (fun a : Module.End R M ↦ a z) H.lower_raise

theorem weight_raise_apply (z : M) : h (f z) = f (h z) - (2 : R) • f z := by
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply] using
    congrArg (fun a : Module.End R M ↦ a z) H.weight_raise

/-- The weight drops by two under each application of the raising operator. -/
theorem weight_pow_apply (c : R) (w : M) (hw : h w = c • w) (j : ℕ) :
    h ((f ^ j) w) = (c - 2 * (j : R)) • (f ^ j) w := by
  induction j with
  | zero => simpa using hw
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, H.weight_raise_apply, ih, map_smul,
      ← sub_smul]
    congr 1
    push_cast
    ring

/-- The exact `sl₂` coefficient in the paper's primitive-vector argument. -/
theorem lower_pow_apply (c : R) (w : M) (he : e w = 0) (hh : h w = c • w)
    (j : ℕ) :
    e ((f ^ (j + 1)) w) = (((j + 1 : ℕ) : R) * (c - (j : R))) • (f ^ j) w := by
  induction j with
  | zero =>
    simpa [he, hh] using H.lower_raise_apply w
  | succ j ih =>
    calc
      e ((f ^ (j + 1 + 1)) w) = e (f ((f ^ (j + 1)) w)) := by
        rw [pow_succ', Module.End.mul_apply]
      _ = f (e ((f ^ (j + 1)) w)) + h ((f ^ (j + 1)) w) :=
        H.lower_raise_apply _
      _ = (((j + 1 : ℕ) : R) * (c - (j : R))) • f ((f ^ j) w) +
          (c - 2 * ((j + 1 : ℕ) : R)) • (f ^ (j + 1)) w := by
        rw [ih, map_smul, H.weight_pow_apply c w hh]
      _ = ((((j + 1 : ℕ) : R) * (c - (j : R))) +
          (c - 2 * ((j + 1 : ℕ) : R))) • (f ^ (j + 1)) w := by
        rw [pow_succ', Module.End.mul_apply, add_smul]
      _ = (((j + 1 + 1 : ℕ) : R) * (c - ((j + 1 : ℕ) : R))) •
          (f ^ (j + 1)) w := by
        congr 1
        push_cast
        ring

end RaisingLowering

/-- Every positive integer up to `n` is a unit when `n!` is a unit. -/
theorem unit_natCast_of_factorial {n m : ℕ} (hn : IsUnit (n.factorial : R))
    (hm : 0 < m) (hmn : m ≤ n) : IsUnit (m : R) := by
  apply isUnit_of_dvd_unit _ hn
  obtain ⟨q, hq⟩ := Nat.dvd_factorial hm hmn
  refine ⟨(q : R), ?_⟩
  simpa only [Nat.cast_mul] using congrArg (fun a : ℕ ↦ (a : R)) hq

/-- Every smaller factorial is a unit under the paper's factorial hypothesis. -/
theorem unit_factorialCast_of_le {n d : ℕ} (hn : IsUnit (n.factorial : R))
    (hd : d ≤ n) : IsUnit (d.factorial : R) := by
  apply isUnit_of_dvd_unit _ hn
  obtain ⟨q, hq⟩ := Nat.factorial_dvd_factorial hd
  refine ⟨(q : R), ?_⟩
  simpa only [Nat.cast_mul] using congrArg (fun a : ℕ ↦ (a : R)) hq

/-- A primitive string cannot vanish before its nonnegative highest weight.

The unit assumption is only the factorial bound. In particular, this argument
works in all coefficient rings allowed by the paper, including positive
characteristic and nonreduced rings.
-/
theorem primitive_raising_power_eq_zero_iff
    (e f h : Module.End R M) (H : RaisingLowering e f h)
    (d c : ℕ) (hfac : IsUnit (d.factorial : R)) (hc : c ≤ d)
    (w : M) (he : e w = 0) (hh : h w = (c : R) • w) (j : ℕ) :
    j ≤ c → ((f ^ j) w = 0 ↔ w = 0) := by
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    constructor
    · intro hz
      have hjc : j ≤ c := by omega
      have hcast : (c : R) - (j : R) = ((c - j : ℕ) : R) := (Nat.cast_sub hjc).symm
      have hunit : IsUnit (((j + 1 : ℕ) : R) * ((c : R) - (j : R))) := by
        apply IsUnit.mul (unit_natCast_of_factorial hfac (by omega) (by omega))
        rw [hcast]
        exact unit_natCast_of_factorial hfac (by omega) (by omega)
      have hdown := H.lower_pow_apply (c : R) w he hh j
      rw [hz, map_zero] at hdown
      exact (ih hjc).mp (hunit.smul_eq_zero.mp hdown.symm)
    · intro hw
      simp [hw]

/-- A primitive vector in exterior degree greater than the number of pairs is zero.

The last hypothesis is precisely the degree bound for exterior powers: applying
`f` `j` times adds `2j` to exterior degree, and the algebra vanishes above `2d`.
This abstract statement makes all arithmetic and nilpotence dependencies explicit.
-/
theorem primitive_eq_zero_of_degree_gt
    (e f h : Module.End R M) (H : RaisingLowering e f h)
    (d k : ℕ) (hfac : IsUnit (d.factorial : R)) (hkd : d < k)
    (w : M) (he : e w = 0) (hh : h w = ((d : R) - (k : R)) • w)
    (hdegree : ∀ j : ℕ, 2 * d < k + 2 * j → (f ^ j) w = 0) : w = 0 := by
  classical
  by_contra hw
  have hd : (f ^ d) w = 0 := hdegree d (by omega)
  have hex : ∃ j : ℕ, (f ^ j) w = 0 := ⟨d, hd⟩
  let m : ℕ := Nat.find hex
  have hm : (f ^ m) w = 0 := Nat.find_spec hex
  have hm_le : m ≤ d := Nat.find_min' hex hd
  have hm_pos : 0 < m := by
    by_contra hn
    have hm0 : m = 0 := by omega
    exact hw (by simpa [hm0] using hm)
  let L := m - 1
  have hLm : L + 1 = m := by omega
  have hL : (f ^ L) w ≠ 0 := by
    exact Nat.find_min hex (by dsimp [L]; omega)
  have htotal : k + 2 * L ≤ 2 * d := by
    by_contra hn
    exact hL (hdegree L (by omega))
  let t := k + L - d
  have ht_pos : 0 < t := by omega
  have ht_le : t ≤ d := by omega
  have htd : t + d = k + L := by omega
  have htdR : (t : R) + (d : R) = (k : R) + (L : R) := by
    simpa only [Nat.cast_add] using congrArg (fun a : ℕ ↦ (a : R)) htd
  have hcoeff : (d : R) - (k : R) - (L : R) = -(t : R) := by
    calc
      (d : R) - (k : R) - (L : R) = (d : R) - ((k : R) + (L : R)) := by ring
      _ = (d : R) - ((t : R) + (d : R)) := by rw [htdR]
      _ = -(t : R) := by ring
  have hu₁ : IsUnit ((L + 1 : ℕ) : R) :=
    unit_natCast_of_factorial hfac (by omega) (by omega)
  have hu₂ : IsUnit ((d : R) - (k : R) - (L : R)) := by
    rw [hcoeff]
    exact (unit_natCast_of_factorial hfac ht_pos ht_le).neg
  have hz := H.lower_pow_apply ((d : R) - (k : R)) w he hh L
  have hm' : (f ^ (L + 1)) w = 0 := by simpa only [hLm] using hm
  rw [hm', map_zero] at hz
  exact hL ((hu₁.mul hu₂).smul_eq_zero.mp hz.symm)

end PaperVerification.Fermion
