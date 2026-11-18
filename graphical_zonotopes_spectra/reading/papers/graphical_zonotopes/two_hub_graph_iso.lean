module

public import Papers.GraphicalZonotopes.TwoHubGraph
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace TwoHub
open Finset
open scoped BigOperators
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

abbrev SigmaVertex (I J : Type*) [Fintype I] [Fintype J] :=
  Σ c : Fin 4,Fin (![1,1,Fintype.card I,Fintype.card J] c)

/-- Exact coordinate correspondence with the paper's four independent
parts. Both singleton vertices and every vertex in the other parts are kept. -/
def sigmaTo : (Bool⊕I)⊕J → SigmaVertex I J
  | .inl (.inl false) => ⟨0,⟨0,by simp⟩⟩
  | .inl (.inl true) => ⟨1,⟨0,by simp⟩⟩
  | .inl (.inr i) => ⟨2,Fintype.equivFin I i⟩
  | .inr j => ⟨3,Fintype.equivFin J j⟩

@[simp] theorem sigmaTo_color (x : (Bool⊕I)⊕J) : (sigmaTo x).1=color x := by
  rcases x with (e|i)|j
  · cases e <;> rfl
  · rfl
  · rfl

theorem sigmaTo_injective : Function.Injective (sigmaTo (I:=I) (J:=J)) := by
  intro x y h
  have hc := congrArg Sigma.fst h
  have hv := congrArg (fun x : SigmaVertex I J => x.2.val) h
  rcases x with (e|i)|j <;> rcases y with (f|k)|l
  · cases e <;> cases f <;> simp_all [sigmaTo]
  · cases e <;> simp_all [sigmaTo]
  · cases e <;> simp_all [sigmaTo]
  · cases f <;> simp_all [sigmaTo]
  · apply congrArg (fun i : I => (Sum.inl (Sum.inr i) : (Bool⊕I)⊕J))
    apply (Fintype.equivFin I).injective
    exact Fin.ext hv
  · simp_all [sigmaTo]
  · cases f <;> simp_all [sigmaTo]
  · simp_all [sigmaTo]
  · apply congrArg (Sum.inr : J → (Bool⊕I)⊕J)
    apply (Fintype.equivFin J).injective
    exact Fin.ext hv

def sigmaEquiv : ((Bool⊕I)⊕J) ≃ SigmaVertex I J :=
  Equiv.ofBijective sigmaTo ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨sigmaTo_injective,by
      simp [SigmaVertex,Fintype.card_sigma,Fin.sum_univ_succ,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]⟩)

def graphIso : graph (I:=I) (J:=J) ≃g
    twoSingletonGraph (Fintype.card I) (Fintype.card J) where
  toEquiv := sigmaEquiv
  map_rel_iff' := by
    intro x y
    change ((sigmaTo x).1≠(sigmaTo y).1) ↔ color x≠color y
    rw [sigmaTo_color,sigmaTo_color]

/-- The natural-parameter specialization has literal part sizes p and b,
so subsequent embeddings need no implicit cardinality casts. -/
def finGraphIso (p b : ℕ) : graph (I:=Fin p) (J:=Fin b)≃g twoSingletonGraph p b := by
  exact cast (by rw [Fintype.card_fin,Fintype.card_fin])
    (graphIso (I:=Fin p) (J:=Fin b))

theorem maximum_dimension_model_eq (p b : ℕ) :
    maximumIndecomposableDimension (graph (I:=Fin p) (J:=Fin b))=
      maximumIndecomposableDimension (twoSingletonGraph p b) := by
  exact maximumIndecomposableDimension_iso (finGraphIso p b)

end TwoHub
end GraphicalZonotopes
