module

public import FiniteCycleIntervals
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# Exact enumeration of injections by falling-factorial codes

At each coordinate a code chooses one of the still unused labels. The
remaining labels retain their order. Surjectivity is proved for every
injection, so the reduced certificate domain loses no candidate cycle.
-/

namespace Papers.RationalityTen.FiniteCycleCandidates

/-- Number of ordered choices without replacement. -/
def injectionCount : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => (n + 1) * injectionCount n k

/-- Decode the successive choices, inserting the omitted label back at
its correct position with `Fin.succAbove`. -/
def decodeInjection : (n k : ℕ) → k ≤ n → ℕ → (Fin k → Fin n)
  | _, 0, _, _ => fun i => i.elim0
  | 0, k + 1, h, _ => False.elim (Nat.not_succ_le_zero k h)
  | n + 1, k + 1, h, code =>
      let a : Fin (n + 1) := ⟨code % (n + 1), Nat.mod_lt _ (Nat.zero_lt_succ n)⟩
      Fin.cons a (fun i => a.succAbove
        (decodeInjection n k (Nat.le_of_succ_le_succ h) (code / (n + 1)) i))

/-- Every injective labeling has a bounded code whose decoding agrees at
every coordinate. No hypothesis about a finite producer is used. -/
theorem exists_injection_code {n k : ℕ} (hk : k ≤ n) (f : Fin k → Fin n)
    (hf : Function.Injective f) :
    ∃ code, code < injectionCount n k ∧ decodeInjection n k hk code = f := by
  induction k generalizing n with
  | zero =>
    refine ⟨0, by simp only [injectionCount]; decide, ?_⟩
    funext i
    exact i.elim0
  | succ k ih =>
    cases n with
    | zero => exact (Nat.not_succ_le_zero k hk).elim
    | succ n =>
      let a := f 0
      have hne (i : Fin k) : f i.succ ≠ a := by
        intro h
        exact Fin.succ_ne_zero i (hf h)
      let g : Fin k → Fin n := fun i => (finSuccAboveEquiv a).symm ⟨f i.succ, hne i⟩
      have hrestore (i : Fin k) : a.succAbove (g i) = f i.succ := by
        exact congrArg Subtype.val ((finSuccAboveEquiv a).apply_symm_apply ⟨f i.succ, hne i⟩)
      have hg : Function.Injective g := by
        intro i j hij
        have heq := congrArg a.succAbove hij
        rw [hrestore, hrestore] at heq
        exact Fin.succ_injective _ (hf heq)
      obtain ⟨code, hcode, hdecode⟩ := ih (Nat.le_of_succ_le_succ hk) g hg
      refine ⟨a.val + (n + 1) * code, ?_, ?_⟩
      · change a.val + (n + 1) * code < (n + 1) * injectionCount n k
        calc
          _ < (n + 1) + (n + 1) * code := Nat.add_lt_add_right a.isLt _
          _ = (n + 1) * (code + 1) := by
            simp only [Nat.mul_add, Nat.mul_one, Nat.add_comm]
          _ ≤ _ := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hcode)
      · have hmod : (a.val + (n + 1) * code) % (n + 1) = a.val := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
        have hdiv : (a.val + (n + 1) * code) / (n + 1) = code := by
          rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_succ n),
            Nat.div_eq_of_lt a.isLt, Nat.zero_add]
        have hhead : (⟨(a.val + (n + 1) * code) % (n + 1),
            Nat.mod_lt _ (Nat.zero_lt_succ n)⟩ : Fin (n + 1)) = a := Fin.ext hmod
        simp only [decodeInjection]
        rw [hhead, hdiv, hdecode]
        funext i
        refine Fin.cases rfl (fun j => ?_) i
        exact hrestore j

/-- A bounded Boolean replay of the reduced code domain proves a property
for every injective function in the full mathematical domain. -/
theorem all_injections_of_code_interval {n k : ℕ} (hk : k ≤ n)
    (P : (Fin k → Fin n) → Prop) [DecidablePred P]
    (h : CodeInterval (fun code => decide (P (decodeInjection n k hk code)))
      0 (injectionCount n k)) :
    ∀ f : Fin k → Fin n, Function.Injective f → P f := by
  intro f hf
  obtain ⟨code, hcode, hdecode⟩ := exists_injection_code hk f hf
  have hp := of_decide_eq_true (h code (Nat.zero_le _) hcode)
  simpa only [hdecode] using hp

end Papers.RationalityTen.FiniteCycleCandidates
