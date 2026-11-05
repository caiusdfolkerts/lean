module

public import Papers.GraphicalZonotopes.SetFunctionEmbedding

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vanishing of all original elemental rows at a normalized vertex means
the function is independent of that vertex, on every subset. -/
theorem insert_eq_of_zero_incident {f : SetFunction V} (hn : TranslationNormalized f)
    (a : V) (hzero : ∀ v,a≠v → ∀ S : Finset V,a∉S → v∉S → delta f a v S=0) :
    ∀ S : Finset V,f (insert a S)=f S := by
  intro S
  by_cases ha : a∈S
  · rw [insert_eq_of_mem ha]
  · revert ha
    induction S using Finset.induction_on with
    | empty => simp only [insert_empty_eq,show f ∅=0 from hn.1,hn.2,implies_true]
    | @insert v S hv ih =>
      intro ha
      have hav : a≠v := fun he => ha (by simp [he])
      have haS : a∉S := fun h => ha (mem_insert_of_mem h)
      have hd := hzero v hav S haS hv
      have hi := ih haS
      unfold delta at hd
      linarith

theorem erase_eq_of_insert_eq {f : SetFunction V} {a : V}
    (hf : ∀ S : Finset V,f (insert a S)=f S) (S : Finset V) : f (S.erase a)=f S := by
  by_cases ha : a∈S
  · have h := hf (S.erase a)
    rw [insert_erase ha] at h
    exact h.symm
  · rw [erase_eq_of_notMem ha]

theorem delta_insert_eq_of_insert_eq {f : SetFunction V} {a : V}
    (hf : ∀ S : Finset V,f (insert a S)=f S) (u v : V) (S : Finset V) :
    delta f u v (insert a S)=delta f u v S := by
  simp only [delta,insert_comm u a,insert_comm v a,hf]

theorem delta_zero_of_insert_eq {f : SetFunction V} {a : V}
    (hf : ∀ S : Finset V,f (insert a S)=f S) (v : V) (S : Finset V) :
    delta f a v S=0 := by
  simp only [delta,hf]
  ring

namespace VertexDeletion

abbrev Retained (d : V) := {v : V // v≠d}

def embedding (d : V) : Retained d ↪ V := Function.Embedding.subtype _

@[simp] theorem deleted_not_range (d : V) : d∉Set.range (embedding d) := by
  rintro ⟨v,hv⟩
  exact v.2 hv

theorem map_pullSet (d : V) (S : Finset V) :
    (SetFunctionEmbedding.pullSet (embedding d) S).map (embedding d)=S.erase d := by
  ext v
  simp only [mem_map,SetFunctionEmbedding.mem_pullSet,mem_erase]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w.2,hw⟩
  · rintro ⟨hv,hS⟩
    exact ⟨⟨v,hv⟩,hS,rfl⟩

theorem extend_restrict (d : V) (f : SetFunction V) (S : Finset V) :
    SetFunctionEmbedding.extend (embedding d)
      (SetFunctionEmbedding.restrict (embedding d) f) S=f (S.erase d) := by
  simp only [SetFunctionEmbedding.extend,SetFunctionEmbedding.restrict,map_pullSet]

theorem delta_erase_function {f : SetFunction V} (d u v : V)
    (hu : u≠d) (hv : v≠d) (S : Finset V) :
    delta (fun T => f (T.erase d)) u v S=delta f u v (S.erase d) := by
  simp only [delta,erase_insert_of_ne hu,erase_insert_of_ne hv]

theorem delta_erase_eq_of_insert_eq {f : SetFunction V} {a : V}
    (hf : ∀ S : Finset V,f (insert a S)=f S) (u v : V)
    (hu : u≠a) (hv : v≠a) (S : Finset V) :
    delta f u v (S.erase a)=delta f u v S := by
  rw [← delta_erase_function a u v hu hv]
  have he : (fun T => f (T.erase a))=f := funext (erase_eq_of_insert_eq hf)
  rw [he]

theorem extended_tight_zero (d : V) (z : SetFunction V)
    (f : SetFunction (Retained d))
    (hzero : ∀ u v : Retained d,u≠v → ∀ S : Finset (Retained d),u∉S → v∉S →
      delta (SetFunctionEmbedding.restrict (embedding d) z) u v S=0 → delta f u v S=0)
    {u v : V} (huv : u≠v) (hud : u≠d) (hvd : v≠d)
    {S : Finset V} (hu : u∉S) (hv : v∉S) (hd : d∉S) (hz : delta z u v S=0) :
    delta (SetFunctionEmbedding.extend (embedding d) f) u v S=0 := by
  let u' : Retained d := ⟨u,hud⟩
  let v' : Retained d := ⟨v,hvd⟩
  have he := hzero u' v' (fun h => huv (congrArg Subtype.val h))
    (SetFunctionEmbedding.pullSet (embedding d) S) (by simpa [u',embedding] using hu) (by simpa [v',embedding] using hv)
  have hsmall : delta (SetFunctionEmbedding.restrict (embedding d) z) u' v'
      (SetFunctionEmbedding.pullSet (embedding d) S)=0 := by
    rw [SetFunctionEmbedding.delta_restrict,map_pullSet,erase_eq_of_notMem hd]
    exact hz
  have h := he hsmall
  simpa only [← SetFunctionEmbedding.delta_extend,embedding,u',v',Function.Embedding.coe_subtype] using h

/-- A graphical row is insensitive to deleting a nonneighbor of its first
endpoint. This follows from the full clique-coordinate dictionary. -/
theorem delta_delete_nonNeighbor {G : SimpleGraph V} {f : SetFunction V}
    (hn : TranslationNormalized f) (hG : Graphical G f)
    {d u v : V} (huv : u≠v) (hu : u≠d) (hv : v≠d) (hd : ¬G.Adj u d)
    {S : Finset V} (huS : u∉S) (hvS : v∉S) :
    delta (fun T => f (T.erase d)) u v S=delta f u v S := by
  rw [delta_erase_function d u v hu hv]
  rw [delta_commonNeighbors hn hG huv (by simpa [hu] using huS) (by simpa [hv] using hvS),
    delta_commonNeighbors hn hG huv huS hvS]
  have he : S.erase d∩commonNeighbors G u v=S∩commonNeighbors G u v := by
    ext w
    simp only [mem_inter,mem_erase]
    constructor
    · exact fun h => ⟨h.1.2,h.2⟩
    · intro h
      refine ⟨⟨?_,h.1⟩,h.2⟩
      intro hwd
      subst w
      exact hd ((mem_commonNeighbors G u v d).mp h.2).1
  rw [he]

end VertexDeletion
end GraphicalZonotopes
