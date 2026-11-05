module

public import Papers.GraphicalZonotopes.BooleanResponseCoordinates

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J]

/-- The genuine row belonging to a hub pair with every other hub present. -/
def fullRow (e : OrientedEdge (⊤ : SimpleGraph H)) : HubResponseRow H :=
  ⟨e,⟨commonNeighbors ⊤ e.1.1 e.1.2,mem_powerset.mpr (subset_refl _)⟩⟩

@[simp] theorem fullRow_edge (e : OrientedEdge (⊤ : SimpleGraph H)) :
    (fullRow e).1=e := rfl

@[simp] theorem rowClique_fullRow (e : OrientedEdge (⊤ : SimpleGraph H)) :
    rowClique (fullRow e)=univ := by
  ext a
  simp only [rowClique,fullRow,mem_insert,mem_commonNeighbors,SimpleGraph.top_adj,mem_univ,iff_true]
  by_cases ha : a=e.1.1
  · exact Or.inl ha
  · by_cases hb : a=e.1.2
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr ⟨Ne.symm ha,Ne.symm hb⟩)

def fullBlock (x : OrientedEdge (⊤ : SimpleGraph H) → ℝ) : HubResponseRow H → ℝ :=
  fun r => if rowClique r=univ then x r.1 else 0

/-- For an array supported on the full hub block, the actual integrability
condition is precisely equality of all pair coordinates of that block. -/
theorem fullBlock_constant_iff (x : OrientedEdge (⊤ : SimpleGraph H) → ℝ)
    [Nonempty (OrientedEdge (⊤ : SimpleGraph H))] :
    BlockConstant (fullBlock x) ↔ ∃ c : ℝ,∀ e,x e=c := by
  constructor
  · intro hx
    obtain ⟨e₀⟩:=‹Nonempty (OrientedEdge (⊤ : SimpleGraph H))›
    refine ⟨x e₀,?_⟩
    intro e
    have he : rowCliqueIndex (fullRow e)=rowCliqueIndex (fullRow e₀) := by
      apply Subtype.ext
      simp only [rowCliqueIndex,rowClique_fullRow]
    simpa only [fullBlock,rowClique_fullRow,ite_true,fullRow_edge] using hx _ _ he
  · rintro ⟨c,hc⟩ r t he
    have hrt : rowClique r=rowClique t:=congrArg Subtype.val he
    simp only [fullBlock,hrt,hc]

theorem rowLower_symm_weightedResponse (F : J → SetFunction H) (w : J → ℝ) :
    rowLowerEquiv.symm (weightedResponse F w)=
      ∑ j : J,w j • rowLowerEquiv.symm (responseVector (F j)) := by
  have he : weightedResponse F w=∑ j : J,w j • responseVector (F j) := by
    funext r
    simp only [weightedResponse,LinearMap.coe_mk,AddHom.coe_mk,
      Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [he,map_sum]
  apply sum_congr rfl
  intro j hj
  exact map_smul rowLowerEquiv.symm (w j) (responseVector (F j))

theorem weightedResponse_reindex {K : Type*} [Fintype K]
    (e : K≃J) (F : J → SetFunction H) (w : K → ℝ) :
    weightedResponse (fun k => F (e k)) w=
      weightedResponse F (fun j => w (e.symm j)) := by
  funext r
  change (∑ k : K,w k*responseVector (F (e k)) r)=
    ∑ j : J,w (e.symm j)*responseVector (F j) r
  simpa only [e.symm_apply_apply] using
    e.sum_comp (fun j => w (e.symm j)*responseVector (F j) r)

theorem compatible_reindex {K : Type*} [Fintype K]
    (e : K≃J) (z : SetFunction H) (F : J → SetFunction H) (w : K → ℝ) :
    Compatible z (fun k => F (e k)) w ↔
      Compatible z F (fun j => w (e.symm j)) := by
  have hs : ∀ u v S,(∑ k : K,w k*negativeResponse (F (e k)) u v S)=
      ∑ j : J,w (e.symm j)*negativeResponse (F j) u v S := by
    intro u v S
    simpa only [e.symm_apply_apply] using
      e.sum_comp (fun j => w (e.symm j)*negativeResponse (F j) u v S)
  unfold Compatible
  simp only [hs]

end BooleanModule
end GraphicalZonotopes
