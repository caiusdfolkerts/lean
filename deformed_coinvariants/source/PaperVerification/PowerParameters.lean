module

public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
# Exact parameter conditions for weighted power tails

The nonresonance condition retains every nonempty subset and every integer in
the unbounded range specified by the paper. These lemmas verify its behavior
under the coefficient shifts used in the induction and identify the exact
Hivert–Thiéry exceptional set in characteristic zero.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {R ι : Type*} [CommRing R]

/-- The full condition `NR_m` from equation (2.1), with no degree truncation. -/
def Nonresonant (c : ι → R) (lam : R) (m : ℕ) : Prop :=
  ∀ I : Finset ι, I.Nonempty → ∀ s : ℕ, m * I.card ≤ s →
    (∑ i ∈ I, c i) + lam * (s : R) ≠ 0

theorem Nonresonant.mono {c : ι → R} {lam : R} {m m' : ℕ}
    (hnr : Nonresonant c lam m) (hmm' : m ≤ m') : Nonresonant c lam m' := by
  intro I hI s hs
  exact hnr I hI s ((Nat.mul_le_mul_right I.card hmm').trans hs)

/-- Restricting to any subset of coordinates preserves every subset condition. -/
theorem Nonresonant.comap {κ : Type*} {c : ι → R} {lam : R} {m : ℕ}
    (hnr : Nonresonant c lam m) (f : κ ↪ ι) :
    Nonresonant (c ∘ f) lam m := by
  intro I hI s hs
  simpa only [Finset.sum_map, Finset.card_map, Function.comp_apply] using
    hnr (I.map f) (hI.map (f := f)) s (by simpa only [Finset.card_map] using hs)

/-- Adding arbitrary nonnegative integral Euler shifts preserves nonresonance. -/
theorem Nonresonant.shift {c : ι → R} {lam : R} {m : ℕ}
    (hnr : Nonresonant c lam m) (q : ι → ℕ) :
    Nonresonant (fun i => c i + lam * (q i : R)) lam m := by
  intro I hI s hs
  have h := hnr I hI (s + ∑ i ∈ I, q i) (hs.trans (Nat.le_add_right _ _))
  have he : (∑ i ∈ I, (c i + lam * (q i : R))) + lam * (s : R) =
      (∑ i ∈ I, c i) + lam * ((s + ∑ i ∈ I, q i : ℕ) : R) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Nat.cast_add, Nat.cast_sum]
    ring
  rwa [he]

/-- Removing a full-support factor lowers the tail index and shifts every coefficient. -/
theorem Nonresonant.lower_tail {c : ι → R} {lam : R} {m : ℕ}
    (hnr : Nonresonant c lam (m + 1)) :
    Nonresonant (fun i => c i + lam) lam m := by
  intro I hI s hs
  have hb : (m + 1) * I.card ≤ s + I.card := by
    rw [Nat.add_mul, one_mul]
    exact Nat.add_le_add_right hs _
  have h := hnr I hI (s + I.card) hb
  have he : (∑ i ∈ I, (c i + lam)) + lam * (s : R) =
      (∑ i ∈ I, c i) + lam * ((s + I.card : ℕ) : R) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_add]
    ring
  rwa [he]

/-- The exact exceptional set `E_n` in Theorem 1.1. -/
def exceptionalSet (K : Type*) [Field K] (n : ℕ) : Set K :=
  {α | ∃ r s : ℕ, 1 ≤ r ∧ r ≤ n ∧ r ≤ s ∧ α = -(r : K) / (s : K)}

variable {K : Type*} [Field K] [CharZero K] [Fintype ι]

/-- The subset nonresonance condition is precisely the paper's excluded rational set. -/
theorem nonresonant_one_iff (α : K) :
    Nonresonant (fun _ : ι => (1 : K)) α 1 ↔
      α ∉ exceptionalSet K (Fintype.card ι) := by
  classical
  constructor
  · intro hnr hbad
    obtain ⟨r, s, hr, hrn, hrs, hα⟩ := hbad
    obtain ⟨I, _, hIcard⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset ι)) (by simpa only [Finset.card_univ] using hrn)
    have hI : I.Nonempty := Finset.card_pos.mp (by omega)
    have hs : (s : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    apply hnr I hI s (by simpa only [one_mul, hIcard] using hrs)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hIcard, hα]
    rw [div_mul_cancel₀ _ hs, add_neg_cancel]
  · intro hgood I hI s hs hz
    apply hgood
    have hspos : 0 < s := (Finset.card_pos.mpr hI).trans_le (by simpa using hs)
    have hsne : (s : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hspos)
    refine ⟨I.card, s, hI.card_pos, Finset.card_le_univ I, ?_, ?_⟩
    · simpa only [one_mul] using hs
    · rw [eq_div_iff hsne]
      have hz' : (I.card : K) + α * (s : K) = 0 := by
        simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hz
      calc
        α * (s : K) = ((I.card : K) + α * (s : K)) - (I.card : K) := by ring
        _ = -(I.card : K) := by rw [hz']; simp

end PaperVerification.PowerOperators
