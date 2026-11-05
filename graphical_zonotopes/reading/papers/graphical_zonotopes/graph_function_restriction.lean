module

public import Papers.GraphicalZonotopes.SetFunctionEmbedding
public import Papers.GraphicalZonotopes.Zonotope
public import Papers.GraphicalZonotopes.Lattice

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace SetFunctionEmbedding
open Finset
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

@[simp] theorem restrict_add (e : W ↪ V) (f g : SetFunction V) :
    restrict e (f+g)=restrict e f+restrict e g := rfl

@[simp] theorem restrict_sub (e : W ↪ V) (f g : SetFunction V) :
    restrict e (f-g)=restrict e f-restrict e g := rfl

theorem integerValued_restrict (e : W ↪ V) {f : SetFunction V}
    (hf : IntegerValued f) : IntegerValued (restrict e f) := fun S => hf (S.map e)

/-- The induced-edge counting function restricts to the ordinary induced
graph, including all nonedges. -/
theorem graphFunction_restrict (e : W ↪ V) (G : SimpleGraph V) :
    restrict e (graphFunction G)=graphFunction (G.comap e) := by
  have hfn := restrict_translationNormalized e (graphFunction_translationNormalized G)
  have hgn := graphFunction_translationNormalized (G.comap e)
  have hn : TranslationNormalized (restrict e (graphFunction G)-graphFunction (G.comap e)) := by
    refine ⟨?_,?_⟩
    · change restrict e (graphFunction G) ∅-graphFunction (G.comap e) ∅=0
      rw [hfn.1,hgn.1,sub_self]
    · intro w
      change restrict e (graphFunction G) {w}-graphFunction (G.comap e) {w}=0
      rw [hfn.2 w,hgn.2 w,sub_self]
  apply sub_eq_zero.mp
  apply normalized_zero_elemental_eq_zero hn
  intro u v huv S hu hv
  rw [delta_sub,delta_restrict,
    graphFunction_delta G (fun he => huv (e.injective he)) (by simpa using hu) (by simpa using hv),
    graphFunction_delta (G.comap e) huv hu hv]
  exact sub_self _

end SetFunctionEmbedding
end GraphicalZonotopes
