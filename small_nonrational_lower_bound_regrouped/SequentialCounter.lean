module
prelude
public import Init

@[expose] public section

/-!
# Propositional models of sequential cardinality counters

The auxiliary variable for prefix `xs` and threshold `j` means that at least
`j` selected elements occur in `xs`.  Appending one vertex gives the familiar
counter recurrence.  Its four CNF clauses are supplied below as ordinary
curried implications to `False`, matching the clause representation used by
the proof-term RUP replay.

These are semantic lemmas, not a SAT solver or a trusted encoding assertion.
Every generated initial counter clause is an application of one of them.
-/

namespace Papers.RationalityTen.SequentialCounter

variable {α : Type} (selected : α → Prop) [DecidablePred selected]

def selectedCount (vertices : List α) : Nat :=
  (vertices.filter fun vertex => decide (selected vertex)).length

def reached (vertices : List α) (threshold : Nat) : Prop :=
  threshold ≤ selectedCount selected vertices

theorem selectedCount_appendList (left right : List α) :
    selectedCount selected (left ++ right) =
      selectedCount selected left + selectedCount selected right := by
  simp only [selectedCount, List.filter_append, List.length_append]

theorem selectedCount_append (vertices : List α) (vertex : α) :
    selectedCount selected (vertices ++ [vertex]) =
      selectedCount selected vertices + (if selected vertex then 1 else 0) := by
  simp only [selectedCount, List.filter_append, List.length_append]
  by_cases h : selected vertex <;> simp [h]

theorem reached_zero (vertices : List α) : reached selected vertices 0 :=
  Nat.zero_le _

/-- A leaf of a binary totalizer is its original selection proposition. -/
theorem reached_singleton (vertex : α) :
    reached selected [vertex] 1 ↔ selected vertex := by
  by_cases h : selected vertex <;> simp [reached, selectedCount, h]

theorem leaf_lower (vertex : α) :
    selected vertex → reached selected [vertex] 1 :=
  (reached_singleton selected vertex).mpr

theorem leaf_upper (vertex : α) :
    reached selected [vertex] 1 → selected vertex :=
  (reached_singleton selected vertex).mp

theorem not_reached_empty (threshold : Nat) (hpositive : 0 < threshold) :
    reached selected [] threshold → False := by
  intro h
  change threshold ≤ 0 at h
  omega

theorem not_reached_above_length (vertices : List α) (threshold : Nat)
    (hlarge : vertices.length < threshold) : reached selected vertices threshold → False := by
  intro h
  have hbound : selectedCount selected vertices ≤ vertices.length := List.length_filter_le ..
  change threshold ≤ selectedCount selected vertices at h
  omega

theorem reached_step (vertices : List α) (vertex : α) (threshold : Nat)
    (hpositive : 0 < threshold) :
    reached selected (vertices ++ [vertex]) threshold ↔
      reached selected vertices threshold ∨
        (selected vertex ∧ reached selected vertices (threshold - 1)) := by
  simp only [reached, selectedCount_append]
  by_cases h : selected vertex <;> simp only [h, ite_true, ite_false, true_and, false_and,
    or_false, Nat.add_zero] <;> omega

/-- Counter clause `¬previous ∨ current`. -/
theorem gate_carry (vertices : List α) (vertex : α) (threshold : Nat)
    (hpositive : 0 < threshold) :
    reached selected vertices threshold →
      (reached selected (vertices ++ [vertex]) threshold → False) → False := by
  intro previous notCurrent
  exact notCurrent ((reached_step selected vertices vertex threshold hpositive).mpr
    (Or.inl previous))

/-- Counter clause `¬selected ∨ ¬lowerPrevious ∨ current`. -/
theorem gate_take (vertices : List α) (vertex : α) (threshold : Nat)
    (hpositive : 0 < threshold) :
    selected vertex → reached selected vertices (threshold - 1) →
      (reached selected (vertices ++ [vertex]) threshold → False) → False := by
  intro chosen previous notCurrent
  exact notCurrent ((reached_step selected vertices vertex threshold hpositive).mpr
    (Or.inr ⟨chosen, previous⟩))

/-- Counter clause `¬current ∨ previous ∨ selected`. -/
theorem gate_previous_or_selected (vertices : List α) (vertex : α) (threshold : Nat)
    (hpositive : 0 < threshold) :
    reached selected (vertices ++ [vertex]) threshold →
      (reached selected vertices threshold → False) →
      (selected vertex → False) → False := by
  intro current notPrevious notSelected
  rcases (reached_step selected vertices vertex threshold hpositive).mp current with
    previous | ⟨chosen, _⟩
  · exact notPrevious previous
  · exact notSelected chosen

/-- Counter clause `¬current ∨ previous ∨ lowerPrevious`. -/
theorem gate_previous_or_lower (vertices : List α) (vertex : α) (threshold : Nat)
    (hpositive : 0 < threshold) :
    reached selected (vertices ++ [vertex]) threshold →
      (reached selected vertices threshold → False) →
      (reached selected vertices (threshold - 1) → False) → False := by
  intro current notPrevious notLower
  rcases (reached_step selected vertices vertex threshold hpositive).mp current with
    previous | ⟨_, lower⟩
  · exact notPrevious previous
  · exact notLower lower

/-- The same recurrence with a shared full list and a prefix index. -/
theorem reached_prefix_step (vertices : List α) (index threshold : Nat)
    (hindex : index < vertices.length) (hpositive : 0 < threshold) :
    reached selected (vertices.take (index + 1)) threshold ↔
      reached selected (vertices.take index) threshold ∨
        (selected vertices[index] ∧ reached selected (vertices.take index) (threshold - 1)) := by
  rw [List.take_succ_eq_append_getElem hindex]
  exact reached_step selected (vertices.take index) vertices[index] threshold hpositive

theorem prefix_carry (vertices : List α) (index threshold : Nat)
    (hindex : index < vertices.length) (hpositive : 0 < threshold) :
    reached selected (vertices.take index) threshold →
      (reached selected (vertices.take (index + 1)) threshold → False) → False := by
  intro previous notCurrent
  exact notCurrent ((reached_prefix_step selected vertices index threshold hindex hpositive).mpr
    (Or.inl previous))

theorem prefix_take (vertices : List α) (index threshold : Nat)
    (hindex : index < vertices.length) (hpositive : 0 < threshold) :
    selected vertices[index] → reached selected (vertices.take index) (threshold - 1) →
      (reached selected (vertices.take (index + 1)) threshold → False) → False := by
  intro chosen previous notCurrent
  exact notCurrent ((reached_prefix_step selected vertices index threshold hindex hpositive).mpr
    (Or.inr ⟨chosen, previous⟩))

theorem prefix_previous_or_selected (vertices : List α) (index threshold : Nat)
    (hindex : index < vertices.length) (hpositive : 0 < threshold) :
    reached selected (vertices.take (index + 1)) threshold →
      (reached selected (vertices.take index) threshold → False) →
      (selected vertices[index] → False) → False := by
  intro current notPrevious notSelected
  rcases (reached_prefix_step selected vertices index threshold hindex hpositive).mp current with
    previous | ⟨chosen, _⟩
  · exact notPrevious previous
  · exact notSelected chosen

theorem prefix_previous_or_lower (vertices : List α) (index threshold : Nat)
    (hindex : index < vertices.length) (hpositive : 0 < threshold) :
    reached selected (vertices.take (index + 1)) threshold →
      (reached selected (vertices.take index) threshold → False) →
      (reached selected (vertices.take index) (threshold - 1) → False) → False := by
  intro current notPrevious notLower
  rcases (reached_prefix_step selected vertices index threshold hindex hpositive).mp current with
    previous | ⟨_, lower⟩
  · exact notPrevious previous
  · exact notLower lower

/-- Final positive unit: the quota has been reached. -/
theorem quota_lower_of_le (vertices : List α) (quota : Nat)
    (hquota : quota ≤ selectedCount selected vertices) :
    (reached selected vertices quota → False) → False :=
  fun notReached => notReached hquota

/-- Final positive unit when the exact quota is known. -/
theorem quota_lower (vertices : List α) (quota : Nat)
    (hquota : selectedCount selected vertices = quota) :
    (reached selected vertices quota → False) → False := by
  intro notReached
  apply notReached
  simp only [reached, hquota, Nat.le_refl]

/-- Final negative unit: the quota has not been exceeded. -/
theorem quota_upper (vertices : List α) (quota : Nat)
    (hquota : selectedCount selected vertices = quota) :
    reached selected vertices (quota + 1) → False := by
  intro reachedTooMany
  simp only [reached, hquota] at reachedTooMany
  omega

/-- Forward binary-totalizer clause: reaching both child thresholds reaches
their sum in the concatenated list. -/
theorem merge_forward (left right : List α) (leftThreshold rightThreshold : Nat) :
    reached selected left leftThreshold → reached selected right rightThreshold →
      (reached selected (left ++ right) (leftThreshold + rightThreshold) → False) → False := by
  intro hleft hright notTotal
  apply notTotal
  change leftThreshold ≤ selectedCount selected left at hleft
  change rightThreshold ≤ selectedCount selected right at hright
  simp only [reached, selectedCount_appendList]
  omega

/-- Reverse binary-totalizer clause: a total above the sum of two upper bounds
forces at least one child above its proposed bound. -/
theorem merge_backward (left right : List α) (leftBound rightBound : Nat) :
    reached selected (left ++ right) (leftBound + rightBound + 1) →
      (reached selected left (leftBound + 1) → False) →
      (reached selected right (rightBound + 1) → False) → False := by
  intro htotal notLeft notRight
  have hleft : selectedCount selected left ≤ leftBound := Nat.le_of_not_gt notLeft
  have hright : selectedCount selected right ≤ rightBound := Nat.le_of_not_gt notRight
  simp only [reached, selectedCount_appendList] at htotal
  omega

#print axioms reached_step
#print axioms prefix_previous_or_lower
#print axioms quota_upper
#print axioms merge_forward
#print axioms merge_backward

end Papers.RationalityTen.SequentialCounter
