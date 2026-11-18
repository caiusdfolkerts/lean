module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Tauto

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeFamily (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact univ.filter (fun C => C.card = 2 ∧ ∀ u ∈ C, ∀ v ∈ C, u ≠ v → G.Adj u v)

@[simp] theorem mem_edgeFamily (G : SimpleGraph V) (C : Finset V) :
    C ∈ edgeFamily G ↔ C.card = 2 ∧ ∀ u ∈ C, ∀ v ∈ C, u ≠ v → G.Adj u v := by
  classical
  simp [edgeFamily]

@[simp] theorem pair_mem_edgeFamily (G : SimpleGraph V) {u v : V} (huv : u ≠ v) :
    ({u, v} : Finset V) ∈ edgeFamily G ↔ G.Adj u v := by
  classical
  rw [mem_edgeFamily]
  simp only [card_pair huv, true_and, mem_insert, mem_singleton]
  constructor
  · intro h
    exact h u (Or.inl rfl) v (Or.inr rfl) huv
  · intro h i hi j hj hij
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact False.elim (hij rfl)
    · exact h
    · exact G.adj_symm h
    · exact False.elim (hij rfl)

def cliqueGraph (C : Finset V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ u ∈ C ∧ v ∈ C
  symm := ⟨by intros; tauto⟩
  loopless := ⟨by intro v; simp⟩

def attachmentStar (u : V) (T : Finset V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ((v = u ∧ w ∈ T) ∨ (w = u ∧ v ∈ T))
  symm := ⟨by intros; tauto⟩
  loopless := ⟨by intro v; simp⟩

/-- The ordinary recursive definition of a 3-tree, on its complete active
vertex set. Vertices outside `S` are isolated throughout the construction. -/
inductive ThreeTreeOn : Finset V → SimpleGraph V → Prop
  | tetrahedron (C : Finset V) (hC : C.card = 4) : ThreeTreeOn C (cliqueGraph C)
  | attach {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
      (u : V) (hu : u ∉ S) (T : Finset V) (hT : T.card = 3)
      (hTS : T ⊆ S) (hcl : G.IsClique T) :
      ThreeTreeOn (insert u S) (G ⊔ attachmentStar u T)

def IsThreeTree (G : SimpleGraph V) : Prop := ThreeTreeOn univ G

def tetrahedra (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact univ.filter (fun C => C.card = 4 ∧ G.IsClique C)

def triangleMultiplicity (G : SimpleGraph V) (T : Finset V) : ℕ := by
  classical
  exact ((tetrahedra G).filter (fun C => T ⊆ C)).card

def Admissible (G : SimpleGraph V) : Prop :=
  ∀ T : Finset V, T.card = 3 → G.IsClique T → triangleMultiplicity G T ≤ 3

def HasAdmissibleSpanningThreeTree (G : SimpleGraph V) : Prop :=
  ∃ H : SimpleGraph V, H ≤ G ∧ IsThreeTree H ∧ Admissible H


def cliqueBook (s k : ℕ) : SimpleGraph (Fin s ⊕ Fin k) where
  Adj u v := u ≠ v ∧ (u.isLeft ∨ v.isLeft)
  symm := ⟨by intros; tauto⟩
  loopless := ⟨by intro v; simp⟩

def cliqueCapacity (s : ℕ) : ℕ :=
  s.choose 2 * 2^(s-2) - (2^s-s-1) + 1

def saturatedHubNeighbors (s : ℕ) : ℕ :=
  if s = 2 then 1 else cliqueCapacity s - cliqueCapacity (s-1) + 1

def fourPartite (a : Fin 4 → ℕ) : SimpleGraph (Σ i : Fin 4, Fin (a i)) :=
  SimpleGraph.completeMultipartiteGraph (fun i => Fin (a i))

def twoSingletonGraph (p b : ℕ) := fourPartite ![1,1,p,b]

def doubledPartGraph (r : ℕ) : SimpleGraph (Fin r × Fin 2) where
  Adj u v := u.1 ≠ v.1
  symm := ⟨fun _ _ => Ne.symm⟩
  loopless := ⟨fun _ h => h rfl⟩


end GraphicalZonotopes
