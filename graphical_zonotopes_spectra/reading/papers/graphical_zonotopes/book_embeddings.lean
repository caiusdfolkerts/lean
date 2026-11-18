module

public import Papers.GraphicalZonotopes.LatticeExtremeEmbedding
public import Papers.GraphicalZonotopes.GraphModels
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators

/-- Promoting one outer vertex to a hub preserves all existing edges. -/
def bookPromote (s k : ℕ) : (Fin s⊕Fin (k+1)) ≃ (Fin (s+1)⊕Fin k) where
  toFun
    | .inl i => .inl i.succ
    | .inr j => Fin.cases (.inl 0) (fun i => .inr i) j
  invFun
    | .inl i => Fin.cases (.inr 0) (fun j => .inl j) i
    | .inr j => .inr j.succ
  left_inv x := by
    cases x with
    | inl i => rfl
    | inr j => exact Fin.cases rfl (fun _ => rfl) j
  right_inv x := by
    cases x with
    | inl i => exact Fin.cases rfl (fun _ => rfl) i
    | inr j => rfl

theorem bookPromote_edges (s k : ℕ) :
    cliqueBook s (k+1)≤(cliqueBook (s+1) k).comap (bookPromote s k) := by
  intro u v h
  change u≠v ∧ (u.isLeft ∨ v.isLeft) at h
  change (bookPromote s k u)≠(bookPromote s k v) ∧
    ((bookPromote s k u).isLeft ∨ (bookPromote s k v).isLeft)
  have hleft : ∀ x : Fin s⊕Fin (k+1),x.isLeft → (bookPromote s k x).isLeft := by
    intro x hx
    cases x with
    | inl i => rfl
    | inr j => exact False.elim (by simpa using hx)
  exact ⟨fun he => h.1 ((bookPromote s k).injective he),h.2.elim
    (fun hu => Or.inl (hleft u hu)) (fun hv => Or.inr (hleft v hv))⟩

def bookOuterEmbedding (s : ℕ) {k l : ℕ} (hkl : k≤l) : (Fin s⊕Fin k) ↪ (Fin s⊕Fin l) :=
  Function.Embedding.sumMap (Function.Embedding.refl _) (Fin.castLEEmb hkl)

theorem bookOuterEmbedding_edges (s : ℕ) {k l : ℕ} (hkl : k≤l) :
    cliqueBook s k≤(cliqueBook s l).comap (bookOuterEmbedding s hkl) := by
  intro u v h
  change u≠v ∧ (u.isLeft ∨ v.isLeft) at h
  change (bookOuterEmbedding s hkl u)≠(bookOuterEmbedding s hkl v) ∧
    ((bookOuterEmbedding s hkl u).isLeft ∨ (bookOuterEmbedding s hkl v).isLeft)
  constructor
  · exact fun he => h.1 ((bookOuterEmbedding s hkl).injective he)
  · cases u <;> cases v <;> simpa [bookOuterEmbedding] using h.2

theorem book_lattice_promote {s k M : ℕ}
    (h : LatticeExtremeAt (cliqueBook s (k+1)) (s+(k+1)-1) M) :
    LatticeExtremeAt (cliqueBook (s+1) k) (s+1+k-1) M := by
  simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
    h.embed (bookPromote s k).toEmbedding (bookPromote_edges s k)

theorem book_lattice_add_outer {s k l M : ℕ} (hkl : k≤l)
    (h : LatticeExtremeAt (cliqueBook s k) (s+k-1) M) :
    LatticeExtremeAt (cliqueBook s l) (s+k-1) M :=
  h.embed (bookOuterEmbedding s hkl) (bookOuterEmbedding_edges s hkl)

end GraphicalZonotopes
