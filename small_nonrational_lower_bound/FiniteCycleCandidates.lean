module

public import Papers.RationalityTenPolygonCatalogue
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.FinCases
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import MatroidChecked.LiteralLookup

@[expose] public section

/-!
# Computable finite cycle certificates

These definitions contain no convex-geometric objects or imported
classification. They coincide definitionally with the cycle/root objects
used by the actual-geometry bridge. Functions are quantified explicitly,
with injectivity as a decidable antecedent, avoiding a noncomputable
choice of an enumeration of embeddings.
-/

namespace Papers.RationalityTen.FiniteCycleCandidates

open Finset PolygonBoundaryCatalogue MatroidChecked

/-- All edges of the labeled cycle graph, with endpoint order canonical. -/
def cycle {k n : ℕ} (f : Fin k → Fin n) : Polygon n where
  vertices := (Finset.univ : Finset (Fin k)).image f
  edges := ((Finset.univ : Finset (Fin k × Fin k)).filter
    (fun ij => (SimpleGraph.cycleGraph k).Adj ij.1 ij.2)).image
      (fun ij => orderedEdge (f ij.1) (f ij.2))

def first (n k : ℕ) (hk : k ≤ n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin k)).image (Fin.castLE hk)

def triangle (n : ℕ) (hn : 3 ≤ n) : Polygon n where
  vertices := first n 3 hn
  edges := (Finset.univ : Finset (Fin n × Fin n)).filter fun e =>
    e.1 < e.2 ∧ e.1 ∈ first n 3 hn ∧ e.2 ∈ first n 3 hn

def baseEdge (n : ℕ) (hn : 3 ≤ n) : Fin n × Fin n :=
  (Fin.castLE hn (0 : Fin 3), Fin.castLE hn (1 : Fin 3))

def Covered {k n c : ℕ} (cells : Fin c → Polygon n) (root : Polygon n)
    (f : Fin k → Fin n) : Prop :=
  Function.Injective f →
    (cycle f = root ∨ compatible (cycle f) root) → ∃ i, cells i = cycle f

instance {k n c : ℕ} (cells : Fin c → Polygon n) (root : Polygon n)
    (f : Fin k → Fin n) : Decidable (Covered cells root f) := by
  unfold Covered
  infer_instance

def NeighborWitness {k n c p : ℕ} (cells : Fin c → Polygon n)
    (neighbors : Finset (Fin c)) (hn : 3 ≤ n) (perms : Fin p → Fin n → Fin n)
    (f : Fin k → Fin n) : Prop :=
  Function.Injective f → compatible (cycle f) (triangle n hn) →
    baseEdge n hn ∈ (cycle f).edges →
      ∃ a : Fin p, ∃ i ∈ neighbors, cells i = relabelPolygon (perms a) (cycle f)

instance {k n c p : ℕ} (cells : Fin c → Polygon n)
    (neighbors : Finset (Fin c)) (hn : 3 ≤ n) (perms : Fin p → Fin n → Fin n)
    (f : Fin k → Fin n) : Decidable (NeighborWitness cells neighbors hn perms f) := by
  unfold NeighborWitness
  infer_instance

/-- Splitting the first coordinate keeps the larger finite checks small. -/
theorem forall_functions_of_cons {α : Type*} {k : ℕ} (P : (Fin (k + 1) → α) → Prop)
    (h : ∀ a, ∀ f : Fin k → α, P (Fin.cons a f)) : ∀ f, P f := by
  intro f
  simpa only [Fin.cons_self_tail] using h (f 0) (Fin.tail f)

end Papers.RationalityTen.FiniteCycleCandidates
