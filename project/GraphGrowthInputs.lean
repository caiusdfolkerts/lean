module
prelude
public import FasterGraphConditionedGrowth

@[expose] public section

/-!
# Literal inputs and independently proved cache laws

This record contains only the computational input to the growth checker.
`Valid` states exactly its finite consistency obligations.  Separating these
from node certificates permits independent checking; a complete application
must supply `Valid`, the graph renamings, and the actual target adapter.
No conclusion about a polytope is inferred from a conditional node check.
-/

namespace Papers.RationalityTen.GraphGrowthInputs

open ConcreteGrowth SparseGrowthDAG GrowthBitsets BatchedGrowthPruning GraphGrowthConstraints

structure Inputs (n r e v k : Nat) where
  ridgeList : Fin n → List (Fin r)
  compatible : Fin n → Fin n → Bool
  kind : Fin n → Nat
  quota : Nat → Nat
  candidates : Fin r → Nat
  incompatible : Fin n → Nat
  kinds : Nat → Nat
  vertexRows : Fin v → Nat
  edges : Fin n → Nat
  missing : Fin n → Nat
  edgeRows : Fin e → Nat
  missingRows : Fin e → Nat
  requiredEdges : Nat
  missingCount : Nat
  minimumIncidence : Nat

structure Valid {n r e v k : Nat} (I : Inputs n r e v k) : Prop where
  candidates_exact : ∀ q c,
    bitAt (I.candidates q) c.val = has (I.ridgeList c) q
  incompatible_sound : ∀ a c,
    bitAt (I.incompatible a) c.val = true → I.compatible a c = false
  kind_lt : ∀ c, I.kind c < k
  kind_exact : ∀ j : Fin k, ∀ c,
    (I.kinds j.val).testBit c.val = decide (I.kind c = j.val)
  edgeRows_exact : ∀ q c,
    (I.edgeRows q).testBit c.val = (I.edges c).testBit q.val
  missingRows_exact : ∀ q c,
    (I.missingRows q).testBit c.val = (I.missing c).testBit q.val

variable {n r e v k : Nat}

def Inputs.cache (I : Inputs n r e v k) (h : Valid I) :
    Cache I.ridgeList I.compatible I.kind where
  candidates := I.candidates
  incompatible := I.incompatible
  kinds := I.kinds
  keys := List.range k
  candidates_exact := h.candidates_exact
  incompatible_sound := h.incompatible_sound
  kind_sound := by
    intro j hj c hc
    have hj' : j < k := List.mem_range.mp hj
    have heq := h.kind_exact ⟨j, hj'⟩ c
    rw [bitAt_eq_testBit, heq] at hc
    exact of_decide_eq_true hc

def Inputs.problem (I : Inputs n r e v k) (h : Valid I) : Problem n r e v k where
  ridgeList := I.ridgeList
  compatible := I.compatible
  kind := I.kind
  quota := I.quota
  cache := I.cache h
  kind_lt := h.kind_lt
  kind_exact := h.kind_exact
  vertexRows := I.vertexRows
  edges := I.edges
  missing := I.missing
  edgeRows := I.edgeRows
  missingRows := I.missingRows
  edgeRows_exact := h.edgeRows_exact
  missingRows_exact := h.missingRows_exact
  requiredEdges := I.requiredEdges
  missingCount := I.missingCount
  minimumIncidence := I.minimumIncidence

theorem problem_proof_irrel (I : Inputs n r e v k) (h₁ h₂ : Valid I) :
    I.problem h₁ = I.problem h₂ := rfl

/-- Extract the exact same literal data from an already justified problem.
The finite key list is standardized to all kinds; correctness needs only the
existing exact kind rows. -/
def ofProblem (D : Problem n r e v k) : Inputs n r e v k where
  ridgeList := D.ridgeList
  compatible := D.compatible
  kind := D.kind
  quota := D.quota
  candidates := D.cache.candidates
  incompatible := D.cache.incompatible
  kinds := D.cache.kinds
  vertexRows := D.vertexRows
  edges := D.edges
  missing := D.missing
  edgeRows := D.edgeRows
  missingRows := D.missingRows
  requiredEdges := D.requiredEdges
  missingCount := D.missingCount
  minimumIncidence := D.minimumIncidence

theorem ofProblem_valid (D : Problem n r e v k) : Valid (ofProblem D) :=
  ⟨D.cache.candidates_exact, D.cache.incompatible_sound, D.kind_lt,
    D.kind_exact, D.edgeRows_exact, D.missingRows_exact⟩

#print axioms ofProblem_valid
end Papers.RationalityTen.GraphGrowthInputs
