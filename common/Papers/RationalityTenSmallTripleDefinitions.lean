module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.Perm.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# The finite seven- and eight-point rank-three cores

After a point and its three rich triples are labeled 012, 034, 056, there
are eight candidate further triples on seven points and twenty candidates
on eight points. The exhaustive checks below inspect respectively seventy
four-subsets and 15,504 five-subsets, not all arbitrary triple systems.

This is the combinatorial part of the elementary replacement for Melchior's
inequality in Lemma 10. A geometric proof must still produce the normalized
labels and exclude the resulting Fano and MacLane configurations over ℝ.

DRAFT: prepared during an unavailable execution environment; not compiled.
-/

namespace Papers.RationalityTen.SmallTripleCores

abbrev Triple := Finset (Fin 8)
abbrev Family := Finset Triple

def rootStar : Family := {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}}
def neighbors : Finset (Fin 8) := {1, 2, 3, 4, 5, 6}

def degree (S : Family) (v : Fin 8) : ℕ := (S.filter fun T => v ∈ T).card

def pairSeparated (S : Family) : Prop :=
  ∀ ⦃A⦄, A∈S → ∀ ⦃B⦄, B∈S → A≠B → (A ∩ B).card ≤ 1

instance (S : Family) : Decidable (pairSeparated S) := by
  unfold pairSeparated
  exact @Finset.decidableDforallFinset Triple S
    (fun A _ => ∀ ⦃B⦄, B ∈ S → A ≠ B → (A ∩ B).card ≤ 1)
    (fun A _ => @Finset.decidableDforallFinset Triple S
      (fun B _ => A ≠ B → (A ∩ B).card ≤ 1) (fun B _ => inferInstance))

def goodSeven (S : Family) : Prop :=
  (∀ v ∈ neighbors, degree S v = 2) ∧ pairSeparated S

def goodEight (S : Family) : Prop :=
  (∀ v ∈ neighbors, degree S v = 2) ∧ degree S 7 = 3 ∧ pairSeparated S

instance (S : Family) : Decidable (goodSeven S) := by
  unfold goodSeven
  infer_instance

instance (S : Family) : Decidable (goodEight S) := by
  unfold goodEight
  infer_instance

attribute [local instance 2000] Finset.decidableDforallFinset

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sevenCandidates : Family := {{1, 3, 5}, {1, 3, 6}, {1, 4, 5}, {1, 4, 6}, {2, 3, 5}, {2, 3, 6}, {2, 4, 5}, {2, 4, 6}}

def eightCandidates : Family := {{1, 3, 5}, {1, 3, 6}, {1, 3, 7}, {1, 4, 5}, {1, 4, 6}, {1, 4, 7}, {1, 5, 7}, {1, 6, 7}, {2, 3, 5}, {2, 3, 6}, {2, 3, 7}, {2, 4, 5}, {2, 4, 6}, {2, 4, 7}, {2, 5, 7}, {2, 6, 7}, {3, 5, 7}, {3, 6, 7}, {4, 5, 7}, {4, 6, 7}}

def sevenModels : Fin 2 → Family :=
  ![{{1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}, {{1, 3, 6}, {1, 4, 5}, {2, 3, 5}, {2, 4, 6}}]

def eightModels : Fin 8 → Family :=
  ![{{1, 3, 5}, {1, 4, 7}, {2, 4, 6}, {2, 5, 7}, {3, 6, 7}}, {{1, 3, 5}, {1, 6, 7}, {2, 3, 7}, {2, 4, 6}, {4, 5, 7}}, {{1, 3, 6}, {1, 4, 7}, {2, 4, 5}, {2, 6, 7}, {3, 5, 7}}, {{1, 3, 6}, {1, 5, 7}, {2, 3, 7}, {2, 4, 5}, {4, 6, 7}}, {{1, 3, 7}, {1, 4, 5}, {2, 3, 6}, {2, 5, 7}, {4, 6, 7}}, {{1, 3, 7}, {1, 4, 6}, {2, 3, 5}, {2, 6, 7}, {4, 5, 7}}, {{1, 4, 5}, {1, 6, 7}, {2, 3, 6}, {2, 4, 7}, {3, 5, 7}}, {{1, 4, 6}, {1, 5, 7}, {2, 3, 5}, {2, 4, 7}, {3, 6, 7}}]


end Papers.RationalityTen.SmallTripleCores
