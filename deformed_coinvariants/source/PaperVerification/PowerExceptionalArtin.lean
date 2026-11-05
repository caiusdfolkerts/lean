module

public import PaperVerification.PowerCoordinateRestriction
public import PaperVerification.PowerResonantStandard
public import PaperVerification.PowerCoinvariantStandardBridge

/-!
# Failure of the Artin span at every exceptional parameter

The resonant standard representation occurs in degree `s`, while the ordinary
coinvariant representation has no standard constituent in degrees at least
the number of variables. Literal Artin spanning would force an equivalence
of those exact degree representations. Restriction to the first variables
and the identity `-1/s = -2/(2s)` cover the entire printed exceptional set.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation

namespace PaperVerification.PowerOperators

open PowerStandardHarmonics

variable {K : Type*} [Field K] [CharZero K]

theorem resonant_original_artin_not_spanning (n s : ℕ) (hs : n+2 ≤ s)
    (α : K) (hα : α = -((n+2 : ℕ) : K)/(s : K)) :
    (artinSpan K (n+2) 1).map
      (originalTailHit (fun _ : Fin (n+2) => (1 : K)) α 1).mkQ ≠ ⊤ := by
  intro hspan
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  let G : Subgroup (Equiv.Perm (Fin (n+2))) := ⊤
  have hres : (Fintype.card (Fin (n+2)) : K) + α*(q+1 : ℕ) = 0 := by
    simp only [Fintype.card_fin, hα, Nat.succ_eq_add_one]
    rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero q)), add_neg_cancel]
  obtain ⟨f, hf⟩ := exists_resonant_standard_subrepresentation α q hres G
  obtain ⟨e⟩ := original_degree_coinvariant_equiv_of_artin_span α (q+1) hspan G
  let t := e.toIntertwiningMap.comp f
  have ht : t = 0 :=
    PowerCoinvariantStabilizer.standard_elementary_degree_intertwiner_eq_zero
      (n := n+1) (q+1) hs t
  have hti : Function.Injective t := by
    intro v w h
    exact hf (e.injective h)
  let i : Fin (n+2) := ⟨0, by omega⟩
  let j : Fin (n+2) := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hval := congrArg Fin.val h
    exact Nat.zero_ne_one hval
  apply differenceVector_ne_zero (K := K) i j hij
  apply hti
  rw [ht]
  rfl

theorem exceptional_numerator_at_least_two {n : ℕ} (hn : 2 ≤ n)
    (α : K) (hα : α ∈ exceptionalSet K n) :
    ∃ r s : ℕ, 2 ≤ r ∧ r ≤ n ∧ r ≤ s ∧ α = -(r : K)/(s : K) := by
  obtain ⟨r, s, hr, hrn, hrs, hα⟩ := hα
  by_cases hr1 : r = 1
  · refine ⟨2, 2*s, le_rfl, hn, by omega, ?_⟩
    have hs : (s : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [hα, hr1]
    push_cast
    field_simp [hs]
    <;> ring
  · exact ⟨r, s, by omega, hrn, hrs, hα⟩

/-- The exact converse from Theorem 1.1, including nonreduced fractions in
the exceptional set and every number of variables at least two. -/
theorem paper_theorem_1_1_artin_necessity {n : ℕ} (hn : 2 ≤ n) (α : K)
    (hspan : (artinSpan K n 1).map
      (originalTailHit (fun _ : Fin n => (1 : K)) α 1).mkQ = ⊤) :
    α ∉ exceptionalSet K n := by
  intro hbad
  obtain ⟨r, s, hr, hrn, hrs, hα⟩ := exceptional_numerator_at_least_two hn α hbad
  have hsmall := original_artin_span_restrict hrn α 1 Nat.zero_lt_one hspan
  obtain ⟨a, rfl⟩ : ∃ a, r = a+2 := ⟨r-2, by omega⟩
  exact resonant_original_artin_not_spanning a s hrs α hα hsmall

theorem original_artin_spanning_iff {n : ℕ} (hn : 2 ≤ n) (α : K) :
    (artinSpan K n 1).map
      (originalTailHit (fun _ : Fin n => (1 : K)) α 1).mkQ = ⊤ ↔
      α ∉ exceptionalSet K n :=
  ⟨paper_theorem_1_1_artin_necessity hn α,
    fun hα => (Submodule.map_mkQ_eq_top _ _).mpr
      (original_artin_spanning_outside_exceptional α hα)⟩

end PaperVerification.PowerOperators
