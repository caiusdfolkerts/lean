module

public import Papers.GraphicalZonotopes.TwoHubGraphIso

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset
variable {I J I' J' : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']

def vertexEmbedding (e : I↪I') (f : J↪J') : ((Bool⊕I)⊕J)↪((Bool⊕I')⊕J') :=
  Function.Embedding.sumMap (Function.Embedding.sumMap (Function.Embedding.refl Bool) e) f

@[simp] theorem vertexEmbedding_color (e : I↪I') (f : J↪J') (x : (Bool⊕I)⊕J) :
    color (vertexEmbedding e f x)=color x := by
  rcases x with (v|i)|j
  · cases v <;> rfl
  · rfl
  · rfl

theorem graph_le_comap (e : I↪I') (f : J↪J') :
    graph (I:=I) (J:=J)≤(graph (I:=I') (J:=J')).comap (vertexEmbedding e f) := by
  intro x y hxy
  change color (vertexEmbedding e f x)≠color (vertexEmbedding e f y)
  simpa [graph] using hxy

def swapVertex : ((Bool⊕I)⊕J)→((Bool⊕J)⊕I)
  | .inl (.inl v) => .inl (.inl v)
  | .inl (.inr i) => .inr i
  | .inr j => .inl (.inr j)

@[simp] theorem swapVertex_swap (x : (Bool⊕I)⊕J) : swapVertex (swapVertex x)=x := by
  rcases x with (v|i)|j <;> rfl

def swapEquiv : ((Bool⊕I)⊕J)≃((Bool⊕J)⊕I) where
  toFun:=swapVertex
  invFun:=swapVertex
  left_inv:=swapVertex_swap
  right_inv:=swapVertex_swap

def swapGraphIso : graph (I:=I) (J:=J)≃g graph (I:=J) (J:=I) where
  toEquiv:=swapEquiv
  map_rel_iff':=by
    intro x y
    change color (swapVertex x)≠color (swapVertex y) ↔ color x≠color y
    rcases x with (v|i)|j <;> rcases y with (w|k)|l
    · cases v <;> cases w <;> simp [swapVertex,color]
    · cases v <;> simp [swapVertex,color]
    · cases v <;> simp [swapVertex,color]
    · cases w <;> simp [swapVertex,color]
    · simp [swapVertex,color]
    · simp [swapVertex,color]
    · cases w <;> simp [swapVertex,color]
    · simp [swapVertex,color]
    · simp [swapVertex,color]

def twoSingletonSwap (p b : ℕ) : twoSingletonGraph p b≃g twoSingletonGraph b p :=
  (finGraphIso p b).symm.trans
    ((swapGraphIso (I:=Fin p) (J:=Fin b)).trans (finGraphIso b p))

theorem maximum_dimension_swap (p b : ℕ) :
    maximumIndecomposableDimension (twoSingletonGraph p b)=
      maximumIndecomposableDimension (twoSingletonGraph b p) :=
  maximumIndecomposableDimension_iso (twoSingletonSwap p b)

end GraphicalZonotopes.TwoHub
