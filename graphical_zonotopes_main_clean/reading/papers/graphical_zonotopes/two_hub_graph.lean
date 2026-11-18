module

public import Papers.GraphicalZonotopes.GraphModels
public import Papers.GraphicalZonotopes.GraphIsomorphismDimension

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace TwoHub
open Finset
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

variable {J : Type*} [Fintype J] [DecidableEq J]

def color : (Bool⊕I)⊕J → Fin 4
  | .inl (.inl false) => 0
  | .inl (.inl true) => 1
  | .inl (.inr _) => 2
  | .inr _ => 3

def graph : SimpleGraph ((Bool⊕I)⊕J) where
  Adj x y := color x≠color y
  symm := ⟨fun _ _ => Ne.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

instance graphDecidable : DecidableRel (graph (I:=I) (J:=J)).Adj :=
  fun x y => inferInstanceAs (Decidable (color x≠color y))


end TwoHub
end GraphicalZonotopes
