module
prelude
public import RawGeneratorWords
public import RawNatGrowthSoundness
public import FiniteChecks

@[expose] public section

/-! A change in the storage format of generator maps does not change the
action of any valid word. This lemma lets the finite checker use one packed
integer per generator while retaining the original geometric map interface. -/
namespace Papers.RationalityTen.FastGeneratorWords

open CheckedGraphGrowthWords

theorem rawApply_eq_of_bounded_eq
    {n g : Nat} (fast original : Nat → Nat → Nat)
    (heq : ∀ a, a < g → ∀ c, c < n → fast a c = original a c)
    (hbound : ∀ a c, original a c < n)
    (word : List Nat) (hword : ∀ a ∈ word, a < g)
    (c : Nat) (hc : c < n) :
    rawApply fast word c = rawApply original word c := by
  induction word generalizing c with
  | nil => rfl
  | cons a rest ih =>
    have ha : a < g := hword a (by simp)
    have hr : ∀ b ∈ rest, b < g := by
      intro b hb
      exact hword b (by simp only [List.mem_cons]; exact Or.inr hb)
    simp only [rawApply]
    rw [heq a ha c hc]
    exact ih hr (original a c) (hbound a c)

theorem bounded_eq_of_interval
    {n g : Nat} (hn : 0 < n) (fast original : Nat → Nat → Nat)
    (h : FiniteChecks.Interval
      (fun i => fast (i / n) (i % n) == original (i / n) (i % n)) 0 (g * n)) :
    ∀ a, a < g → ∀ c, c < n → fast a c = original a c := by
  intro a ha c hc
  have hindex : c + a * n < g * n := by
    have h1 : c + a * n < n + a * n := Nat.add_lt_add_right hc _
    have h2 : n + a * n = (a + 1) * n := by
      simp only [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    have h3 : (a + 1) * n ≤ g * n := Nat.mul_le_mul_right n ha
    exact Nat.lt_of_lt_of_le (h2 ▸ h1) h3
  have checked := h (c + a * n) (Nat.zero_le _) hindex
  have hdiv : (c + a * n) / n = a := by
    rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hc, Nat.zero_add]
  have hmod : (c + a * n) % n = c := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  dsimp only at checked
  rw [hdiv, hmod] at checked
  exact eq_of_beq checked

#print axioms rawApply_eq_of_bounded_eq
#print axioms bounded_eq_of_interval

end Papers.RationalityTen.FastGeneratorWords
