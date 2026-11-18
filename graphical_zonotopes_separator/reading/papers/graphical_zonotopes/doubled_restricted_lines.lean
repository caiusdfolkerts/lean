module

public import Papers.GraphicalZonotopes.DoubledStarScales
public import Papers.GraphicalZonotopes.IgnoredVertices
public import Papers.GraphicalZonotopes.BooleanSlicing

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Only the contexts in the actual remaining-part cube are needed for one
row-line argument; graphicality itself is an independently proved premise. -/
theorem graphical_row_line_of_profile {z f : SetFunction (I×Fin 2)}
    (hzn : TranslationNormalized z) (hzG : Graphical (graph I) z)
    (hfn : TranslationNormalized f) (hfG : Graphical (graph I) f)
    {u v : I×Fin 2} (huv : (graph I).Adj u v) [Nonempty (Remaining u v)]
    (H : Cube (Remaining u v) → ℝ) (hH : ∀ x,H x=1 ∨ H x= -1)
    (hsep : Nonseparable H)
    (hprofile : ∀ uv,delta z u v (edgeContext u v (coordinateChange.symm uv))=faceFunction H uv)
    (hzero : ∀ uv,faceFunction H uv=0 →
      delta f u v (edgeContext u v (coordinateChange.symm uv))=0) :
    ∃ t : ℝ,∀ S : Finset (I×Fin 2),u∉S → v∉S → delta f u v S=t*delta z u v S := by
  let p : (Cube (Remaining u v) × Cube (Remaining u v)) → ℝ :=
    fun uv => delta f u v (edgeContext u v (coordinateChange.symm uv))
  have hp : p∈tensorSpace :=
    graphical_edgeProfile_mem_tensorSpace hfn hfG ((graph I).ne_of_adj huv)
  obtain ⟨t,ht⟩ := (boolean_face_line hH hsep p hp).mp hzero
  refine ⟨t,?_⟩
  intro S hu hv
  let s := bitsOfSubset (remainingPart u v S)
  let uv := coordinateChange s
  have h := congrFun ht uv
  change delta f u v (edgeContext u v (coordinateChange.symm uv))=t*faceFunction H uv at h
  rw [← hprofile] at h
  have he : edgeContext u v (coordinateChange.symm uv)=S∩commonNeighbors (graph I) u v := by
    rw [show coordinateChange.symm uv=s by simp [uv]]
    exact edgeContext_remainingPart u v S
  rw [he] at h
  rw [delta_commonNeighbors hfn hfG ((graph I).ne_of_adj huv) hu hv,
    delta_commonNeighbors hzn hzG ((graph I).ne_of_adj huv) hu hv]
  exact h

theorem same_part_not_mem_edgeContext {a d v : I×Fin 2} (hd : d.1=a.1)
    (s : Cube (Remaining a v) × Cube (Remaining a v)) : d∉edgeContext a v s := by
  intro hm
  obtain ⟨w,hw,he⟩ := mem_map.mp hm
  have hh : w.1.1=a.1 := (congrArg Prod.fst he).trans hd
  exact w.1.2.1 hh

/-- Every edge at the singleton retains exactly its full Boolean-face line
after the other vertex in that part is deleted. The kernel vector is lifted
from the actual retained coordinate space. -/
theorem deletion_incident_row_line (hI : 3≤Fintype.card I)
    (a d : I×Fin 2) (had : a≠d) (hpart : d.1=a.1)
    {z : SetFunction (I×Fin 2)} (hzn : TranslationNormalized z)
    (hzG : Graphical (graph I) z)
    (hlocalPhase : ∀ v : AtVertex a,∃ H : Cube (Remaining a v.1) → ℝ,
      (∀ x,H x=1 ∨ H x= -1) ∧ Nonseparable H ∧
      ∀ uv,delta z a v.1 (edgeContext a v.1 (coordinateChange.symm uv))=faceFunction H uv)
    (f : SetFunction (VertexDeletion.Retained d)) (hfn : TranslationNormalized f)
    (hzero : ∀ u v : VertexDeletion.Retained d,u≠v →
      ∀ S : Finset (VertexDeletion.Retained d),u∉S → v∉S →
      delta (SetFunctionEmbedding.restrict (VertexDeletion.embedding d) z) u v S=0 →
      delta f u v S=0) :
    ∀ v : AtVertex a,∃ t : ℝ,∀ S : Finset (I×Fin 2),a∉S → v.1∉S →
      delta (SetFunctionEmbedding.extend (VertexDeletion.embedding d) f) a v.1 S=
        t*delta z a v.1 S := by
  let e := VertexDeletion.embedding d
  have hfG : Graphical ((graph I).comap e) f := by
    intro u v huv hnon S hu hv
    exact hzero u v huv S hu hv
      (SetFunctionEmbedding.restrict_graphical e hzG u v huv hnon S hu hv)
  have hFn := SetFunctionEmbedding.extend_translationNormalized e hfn
  have hFG := SetFunctionEmbedding.extend_graphical e hfG
  intro v
  letI := remaining_nonempty hI a v.1
  obtain ⟨H,hH,hsep,hprofile⟩ := hlocalPhase v
  apply graphical_row_line_of_profile hzn hzG hFn hFG v.2 H hH hsep hprofile
  intro uv hz
  let S := edgeContext a v.1 (coordinateChange.symm uv)
  have hdS : d∉S := same_part_not_mem_edgeContext hpart _
  have hvd : v.1≠d := by
    intro he
    exact v.2 ((congrArg Prod.fst he).trans hpart).symm
  let a' : VertexDeletion.Retained d := ⟨a,had⟩
  let v' : VertexDeletion.Retained d := ⟨v.1,hvd⟩
  have hav' : a'≠v' := fun he => (graph I).ne_of_adj v.2 (congrArg Subtype.val he)
  have haS : a'∉SetFunctionEmbedding.pullSet e S := by
    simpa only [SetFunctionEmbedding.mem_pullSet,e,S,a',VertexDeletion.embedding,Function.Embedding.coe_subtype] using left_not_mem_edgeContext a v.1 _
  have hvS : v'∉SetFunctionEmbedding.pullSet e S := by
    simpa only [SetFunctionEmbedding.mem_pullSet,e,S,v',VertexDeletion.embedding,Function.Embedding.coe_subtype] using right_not_mem_edgeContext a v.1 _
  have hsmall : delta (SetFunctionEmbedding.restrict e z) a' v'
      (SetFunctionEmbedding.pullSet e S)=0 := by
    rw [SetFunctionEmbedding.delta_restrict]
    change delta z a v.1 ((SetFunctionEmbedding.pullSet e S).map e)=0
    rw [VertexDeletion.map_pullSet,erase_eq_of_notMem hdS]
    exact (hprofile uv).trans hz
  have he := hzero a' v' hav' _ haS hvS hsmall
  simpa only [← SetFunctionEmbedding.delta_extend,e,S,a',v',VertexDeletion.embedding,Function.Embedding.coe_subtype] using he

end DoubledParts
end GraphicalZonotopes
