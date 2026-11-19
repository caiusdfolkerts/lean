module

public import Mathlib.Tactic.Sat.FromLRAT
public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Function.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Acyclic counter circuits and their CNF semantics

This module is intended as the semantic layer between a literal finite
facet encoding and a kernel-checked LRAT refutation. Gate outputs are fixed
by their positions in the circuit, and every input precedes its output.
Thus the auxiliary variables cannot introduce circular assumptions.

DRAFT: prepared during an unavailable execution environment; not compiled.
-/

noncomputable section
namespace Papers.RationalityTen.SatCircuit

structure Gate where
  input : ℕ
  previousHigh : ℕ
  previousLow : ℕ
deriving DecidableEq

def Gate.WellFormed (g : Gate) (output : ℕ) : Prop :=
  g.input < output ∧ g.previousHigh < output ∧ g.previousLow < output

def Gate.Satisfied (g : Gate) (output : ℕ) (v : Sat.Valuation) : Prop :=
  v output ↔ v g.previousHigh ∨ (v g.input ∧ v g.previousLow)

def Gate.clauses (g : Gate) (output : ℕ) : Sat.Fmla :=
  [[.neg g.previousHigh, .pos output],
   [.neg g.input, .neg g.previousLow, .pos output],
   [.neg output, .pos g.previousHigh, .pos g.input],
   [.neg output, .pos g.previousHigh, .pos g.previousLow]]

theorem Gate.clauses_sound (g : Gate) (output : ℕ) (v : Sat.Valuation)
    (h : g.Satisfied output v) : v.satisfies_fmla (g.clauses output) := by
  refine ⟨?_⟩
  intro c hc
  have hc' : c = [.neg g.previousHigh, .pos output] ∨
      c = [.neg g.input, .neg g.previousLow, .pos output] ∨
      c = [.neg output, .pos g.previousHigh, .pos g.input] ∨
      c = [.neg output, .pos g.previousHigh, .pos g.previousLow] := by
    rcases List.mem_cons.mp hc with h | h
    · exact Or.inl h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inr (Or.inl h)
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (List.mem_singleton.mp h)))
  rcases hc' with rfl | rfl | rfl | rfl
  · exact fun hp hn => hn (h.mpr (Or.inl hp))
  · exact fun hx hq hn => hn (h.mpr (Or.inr ⟨hx, hq⟩))
  · intro hc hp hx
    rcases h.mp hc with hprev | ⟨hinput, _⟩
    · exact hp hprev
    · exact hx hinput
  · intro hc hp hq
    rcases h.mp hc with hprev | ⟨_, hlow⟩
    · exact hp hprev
    · exact hq hlow

def extend (v : Sat.Valuation) (output : ℕ) (g : Gate) : Sat.Valuation :=
  Function.update v output (v g.previousHigh ∨ (v g.input ∧ v g.previousLow))

def evaluate : ℕ → List Gate → Sat.Valuation → Sat.Valuation
  | _, [], v => v
  | output, g :: gs, v => evaluate (output + 1) gs (extend v output g)

def WellFormed : ℕ → List Gate → Prop
  | _, [] => True
  | output, g :: gs => g.WellFormed output ∧ WellFormed (output + 1) gs

def clauses : ℕ → List Gate → Sat.Fmla
  | _, [] => []
  | output, g :: gs => g.clauses output ++ clauses (output + 1) gs

theorem evaluate_preserves_below (gs : List Gate) (output : ℕ) (v : Sat.Valuation)
    {i : ℕ} (hi : i < output) : evaluate output gs v i = v i := by
  induction gs generalizing output v with
  | nil => rfl
  | cons g gs ih =>
    change evaluate (output + 1) gs (extend v output g) i = v i
    rw [ih (output + 1) (extend v output g) (Nat.lt_succ_of_lt hi)]
    exact Function.update_of_ne (Nat.ne_of_lt hi) _ v

theorem extend_satisfied (g : Gate) (output : ℕ) (v : Sat.Valuation)
    (h : g.WellFormed output) : g.Satisfied output (extend v output g) := by
  rcases h with ⟨hx, hp, hq⟩
  change ℕ → Prop at v
  unfold Gate.Satisfied extend
  rw [Function.update_self,Function.update_of_ne (Nat.ne_of_lt hx),
    Function.update_of_ne (Nat.ne_of_lt hp),Function.update_of_ne (Nat.ne_of_lt hq)]

theorem evaluate_head_satisfied (g : Gate) (gs : List Gate) (output : ℕ)
    (v : Sat.Valuation) (h : g.WellFormed output) :
    g.Satisfied output (evaluate output (g :: gs) v) := by
  rcases h with ⟨hx, hp, hq⟩
  change evaluate (output + 1) gs (extend v output g) output ↔
    evaluate (output + 1) gs (extend v output g) g.previousHigh ∨
      (evaluate (output + 1) gs (extend v output g) g.input ∧
        evaluate (output + 1) gs (extend v output g) g.previousLow)
  rw [evaluate_preserves_below gs (output + 1) _ (Nat.lt_succ_self output),
      evaluate_preserves_below gs (output + 1) _ (Nat.lt_succ_of_lt hp),
      evaluate_preserves_below gs (output + 1) _ (Nat.lt_succ_of_lt hx),
      evaluate_preserves_below gs (output + 1) _ (Nat.lt_succ_of_lt hq)]
  exact extend_satisfied g output v ⟨hx, hp, hq⟩

/-- Every base assignment extends to a model of the entire gate CNF. -/
theorem evaluate_satisfies (gs : List Gate) (output : ℕ) (v : Sat.Valuation)
    (h : WellFormed output gs) :
    (evaluate output gs v).satisfies_fmla (clauses output gs) := by
  induction gs generalizing output v with
  | nil => exact ⟨fun c hc => False.elim (List.not_mem_nil hc)⟩
  | cons g gs ih =>
    have hhead := g.clauses_sound output (evaluate output (g :: gs) v)
      (evaluate_head_satisfied g gs output v h.1)
    have htail := ih (output + 1) (extend v output g) h.2
    refine ⟨?_⟩
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hhead.prop c hc
    · exact htail.prop c hc

def prefixCount (x : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | i + 1 => prefixCount x i + if x i then 1 else 0

theorem prefix_threshold_step (x : ℕ → Bool) (i j : ℕ) :
    j + 1 ≤ prefixCount x (i + 1) ↔
      j + 1 ≤ prefixCount x i ∨ (x i = true ∧ j ≤ prefixCount x i) := by
  cases hx : x i <;> simp [prefixCount, hx] <;> omega

/-- The gate recurrence determines precisely the intended prefix counts.
Only the finite range 0≤j≤bound is required. -/
theorem prefix_counter_truth (x : ℕ → Bool) (u : ℕ → ℕ → Prop) (bound : ℕ)
    (hzero : ∀ i, u i 0)
    (hnil : ∀ j, 0 < j → j ≤ bound → ¬u 0 j)
    (hstep : ∀ i j, j < bound →
      (u (i + 1) (j + 1) ↔ u i (j + 1) ∨ (x i = true ∧ u i j))) :
    ∀ i j, j ≤ bound → (u i j ↔ j ≤ prefixCount x i) := by
  intro i
  induction i with
  | zero =>
    intro j hj
    cases j with
    | zero => simp [hzero, prefixCount]
    | succ j => simp [hnil (j + 1) (by omega) hj, prefixCount]
  | succ i ih =>
    intro j hj
    cases j with
    | zero => simp [hzero]
    | succ j =>
      rw [hstep i j (by omega), ih (j + 1) hj, ih j (by omega)]
      exact (prefix_threshold_step x i j).symm

theorem ridge_count_clauses_sound (v : Sat.Valuation) (one two three count : ℕ)
    (h1 : v one ↔ 1 ≤ count) (h2 : v two ↔ 2 ≤ count)
    (h3 : v three ↔ 3 ≤ count) (hcount : count = 0 ∨ count = 2) :
    v.satisfies_fmla [[.neg one, .pos two], [.neg three]] := by
  refine ⟨?_⟩
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · intro hOne hNotTwo
    apply hNotTwo
    apply h2.mpr
    have hOne' := h1.mp hOne
    omega
  · have heq := List.mem_singleton.mp hc
    subst c
    intro hThree
    have hThree' := h3.mp hThree
    omega

theorem root_ridge_count_clauses_sound (v : Sat.Valuation) (one two count : ℕ)
    (h1 : v one ↔ 1 ≤ count) (h2 : v two ↔ 2 ≤ count) (hcount : count = 1) :
    v.satisfies_fmla [[.pos one], [.neg two]] := by
  refine ⟨?_⟩
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · intro hNotOne
    exact hNotOne (h1.mpr (by omega))
  · have heq := List.mem_singleton.mp hc
    subst c
    intro hTwo
    have hTwo' := h2.mp hTwo
    omega

theorem exact_count_clauses_sound (v : Sat.Valuation) (lower upper count required : ℕ)
    (hlower : v lower ↔ required ≤ count)
    (hupper : v upper ↔ required + 1 ≤ count) (hcount : count = required) :
    v.satisfies_fmla [[.pos lower], [.neg upper]] := by
  refine ⟨?_⟩
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · intro hNotLower
    exact hNotLower (hlower.mpr (by omega))
  · have heq := List.mem_singleton.mp hc
    subst c
    intro hUpper
    have hUpper' := hupper.mp hUpper
    omega

theorem negative_clause_iff (v : Sat.Valuation) (xs : List ℕ) :
    v.satisfies (xs.map Sat.Literal.neg) ↔ ¬∀ i ∈ xs, v i := by
  induction xs with
  | nil => simp [Sat.Valuation.satisfies]
  | cons x xs ih =>
    change (v x → v.satisfies (xs.map Sat.Literal.neg)) ↔ ¬∀ i ∈ x :: xs, v i
    constructor
    · intro h hall
      apply (ih.mp (h (hall x (by simp))))
      intro i hi
      exact hall i (by simp [hi])
    · intro h hx
      apply ih.mpr
      intro htail
      apply h
      intro i hi
      rcases List.mem_cons.mp hi with heq | hmem
      · simpa only [heq] using hx
      · exact htail i hmem

/-- The LRAT proof is applied to an explicit model, rather than treated
as an oracle assertion that a search succeeded. -/
theorem false_of_refutation (formula : Sat.Fmla) (h : formula.proof [])
    (v : Sat.Valuation) (hv : v.satisfies_fmla formula) : False :=
  h v hv

end Papers.RationalityTen.SatCircuit
