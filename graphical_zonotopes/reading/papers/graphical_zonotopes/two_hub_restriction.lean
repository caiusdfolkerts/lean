module

public import Papers.GraphicalZonotopes.TwoHubGeometry
public import Papers.GraphicalZonotopes.CubeCells
public import Papers.GraphicalZonotopes.SetFunctionEmbeddingGeometry

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset SetFunctionEmbedding
open scoped BigOperators Pointwise
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Adding genuinely ignored variables preserves private rigidity. Tight
zero covers force every variation to ignore those same variables. -/
theorem PrivateRigid.extend {F : SetFunction W} (hF : PrivateRigid F) (e : W ↪ V) :
    PrivateRigid (SetFunctionEmbedding.extend e F) := by
  intro f hf hcover hdelta
  let g:=SetFunctionEmbedding.restrict e f
  have hg : g ∅=0 := by simpa [g,SetFunctionEmbedding.restrict] using hf
  have hgcover : ∀ w X,w∉X → F (insert w X)-F X=0 → g (insert w X)-g X=0 := by
    intro w X hw hzero
    change f ((insert w X).map e)-f (X.map e)=0
    rw [map_insert]
    apply hcover (e w) (X.map e) (by simpa using hw)
    simpa only [SetFunctionEmbedding.extend,pullSet_insert_image,pullSet_map] using hzero
  have hgdelta : ∀ w v,w≠v → ∀ X,w∉X → v∉X → delta F w v X=0 → delta g w v X=0 := by
    intro w v hwv X hw hv hz
    rw [show g=SetFunctionEmbedding.restrict e f from rfl,delta_restrict]
    apply hdelta (e w) (e v) (fun he => hwv (e.injective he)) (X.map e)
      (by simpa using hw) (by simpa using hv)
    simpa only [delta_extend,pullSet_map] using hz
  obtain ⟨c,hc⟩:=hF g hg hgcover hgdelta
  have hrec : SetFunctionEmbedding.extend e g=f := by
    apply reconstruct_of_insert_absent
    intro v hv X
    by_cases hx : v∈X
    · simp [insert_eq_of_mem hx]
    · apply sub_eq_zero.mp
      apply hcover v X hx
      rw [extend_insert_absent e F v hv X,sub_self]
  refine ⟨c,?_⟩
  rw [←hrec,hc,extend_smul]

end BooleanModule

namespace TwoHub
open Finset BooleanModule SetFunctionEmbedding
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]


def Cell.embedding (C : Cell I) : Hub C.fixed ↪ Hub I :=
  Function.Embedding.sumMap (Function.Embedding.refl Bool)
    ⟨Subtype.val,Subtype.val_injective⟩

def Cell.function (C : Cell I) : SetFunction (Hub I) :=
  extend C.embedding (moduleFunction C.assignment)

@[simp] theorem Cell.embed_a (C : Cell I) : C.embedding a=a := rfl
@[simp] theorem Cell.embed_b (C : Cell I) : C.embedding b=b := rfl
@[simp] theorem Cell.embed_u (C : Cell I) (i : C.fixed) : C.embedding (u i)=u i.1 := rfl

theorem Cell.pullSet_outers (C : Cell I) (S : Finset (Hub I)) :
    outers (pullSet C.embedding S)=C.pull (outers S) := by
  ext i
  simp [Cell.embedding,u]

theorem Cell.pullSet_a (C : Cell I) (S : Finset (Hub I)) :
    a∈pullSet C.embedding S ↔ a∈S := by simp

theorem Cell.pullSet_b (C : Cell I) (S : Finset (Hub I)) :
    b∈pullSet C.embedding S ↔ b∈S := by simp

theorem Cell.range_u (C : Cell I) (i : I) : u i∈Set.range C.embedding ↔ i∈C.fixed := by
  constructor
  · rintro ⟨x,hx⟩
    rcases x with e|j
    · cases e <;> simp [Cell.embedding,a,b,u] at hx
    · have hh : j.1=i := Sum.inr_injective hx
      exact hh ▸ j.2
  · intro hi
    exact ⟨u (⟨i,hi⟩ : C.fixed),rfl⟩

theorem Cell.privateRigid (C : Cell I) (hC : C.fixed.Nonempty) : PrivateRigid C.function := by
  letI : Nonempty C.fixed:=⟨⟨hC.choose,hC.choose_spec⟩⟩
  exact (module_private_rigid C.assignment).extend C.embedding

theorem Cell.empty (C : Cell I) : C.function ∅=0 := by
  simp [Cell.function,extend]

theorem Cell.cover_nonnegative (C : Cell I) (hC : C.fixed.Nonempty)
    (v : Hub I) (S : Finset (Hub I)) : 0≤C.function (insert v S)-C.function S := by
  letI : Nonempty C.fixed:=⟨⟨hC.choose,hC.choose_spec⟩⟩
  by_cases hv : v∈Set.range C.embedding
  · obtain ⟨w,rfl⟩:=hv
    simpa only [Cell.function,extend,pullSet_insert_image] using
      module_cover_nonnegative C.assignment w (pullSet C.embedding S)
  · simp only [Cell.function,extend_insert_absent C.embedding _ v hv S,sub_self,le_refl]

theorem Cell.ab_response (C : Cell I) (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
    negativeResponse C.function a b S=if C.Matches (outers S) then 1 else 0 := by
  change max 0 (-delta (extend C.embedding (moduleFunction C.assignment))
    (C.embedding a) (C.embedding b) S)=_
  rw [delta_extend]
  change negativeResponse (moduleFunction C.assignment) a b (pullSet C.embedding S)=_
  rw [module_ab_response_all C.assignment _ (by simpa using ha) (by simpa using hb),Cell.pullSet_outers]
  rfl

theorem Cell.ai_response (C : Cell I) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) : negativeResponse C.function a (u i) S=0 := by
  by_cases hc : i∈C.fixed
  · let j : C.fixed:=⟨i,hc⟩
    change max 0 (-delta (extend C.embedding (moduleFunction C.assignment))
      (C.embedding a) (C.embedding (u j)) S)=0
    rw [delta_extend]
    exact module_ai_response C.assignment j _ (by simpa using ha) (by simpa [j] using hi)
  · have hh : u i∉Set.range C.embedding := fun h => hc ((C.range_u i).mp h)
    rw [negativeResponse,delta_comm a (u i)]
    change max 0 (-delta (extend C.embedding _) (u i) a S)=0
    rw [delta_extend_not_range C.embedding _ _ _ hh,neg_zero,max_self]

theorem Cell.bi_response (C : Cell I) (i : I) (S : Finset (Hub I))
    (hb : b∉S) (hi : u i∉S) :
    negativeResponse C.function b (u i) S=
      if i∈C.fixed ∧ i∉C.ones then (if a∈S then 0 else 1) else 0 := by
  by_cases hc : i∈C.fixed
  · let j : C.fixed:=⟨i,hc⟩
    change max 0 (-delta (extend C.embedding (moduleFunction C.assignment))
      (C.embedding b) (C.embedding (u j)) S)=_
    rw [delta_extend]
    change negativeResponse (moduleFunction C.assignment) b (u j) (pullSet C.embedding S)=_
    rw [module_bi_response _ _ _ (by simpa using hb) (by simpa [j] using hi)]
    by_cases ho : i∈C.ones <;> simp [hc,ho,j]
  · have hh : u i∉Set.range C.embedding := fun h => hc ((C.range_u i).mp h)
    rw [negativeResponse,delta_comm b (u i)]
    change max 0 (-delta (extend C.embedding _) (u i) b S)=_
    rw [delta_extend_not_range C.embedding _ _ _ hh]
    simp [hc]

theorem Cell.outer_zero (C : Cell I) : OuterZero C.function := by
  intro i j hij S hi hj
  by_cases hci : i∈C.fixed
  · by_cases hcj : j∈C.fixed
    · let i' : C.fixed:=⟨i,hci⟩
      let j' : C.fixed:=⟨j,hcj⟩
      change delta (extend C.embedding _) (C.embedding (u i')) (C.embedding (u j')) S=0
      rw [delta_extend]
      exact module_outer_zero C.assignment i' j' (fun he => hij (congrArg Subtype.val he))
        _ (by simpa [Cell.embedding,i',u] using hi) (by simpa [Cell.embedding,j',u] using hj)
    · change delta C.function (u i) (u j) S=0
      rw [delta_comm (u i) (u j)]
      exact delta_extend_not_range C.embedding _ _ _
        (fun h => hcj ((C.range_u j).mp h)) S
  · exact delta_extend_not_range C.embedding _ _ _
      (fun h => hci ((C.range_u i).mp h)) S

theorem Cell.integer (C : Cell I) : IntegerValued C.function :=
  extend_integer C.embedding (module_integer C.assignment)

theorem Cell.a_essential (C : Cell I) : Essential C.function a := by
  obtain ⟨X,hX,hval⟩:=module_a_essential C.assignment
  refine ⟨X.map C.embedding,?_,?_⟩
  · change C.embedding a∉X.map C.embedding
    intro hx
    obtain ⟨y,hy,he⟩:=Finset.mem_map.mp hx
    exact hX (C.embedding.injective he ▸ hy)
  · change extend C.embedding (moduleFunction C.assignment)
        (insert (C.embedding a) (X.map C.embedding))-
        extend C.embedding (moduleFunction C.assignment) (X.map C.embedding)=1
    simpa only [extend,pullSet_insert_image,pullSet_map] using hval

theorem Cell.b_essential (C : Cell I) (hC : C.fixed.Nonempty) : Essential C.function b := by
  letI : Nonempty C.fixed:=⟨⟨hC.choose,hC.choose_spec⟩⟩
  obtain ⟨X,hX,hval⟩:=module_b_essential C.assignment
  refine ⟨X.map C.embedding,?_,?_⟩
  · change C.embedding b∉X.map C.embedding
    intro hx
    obtain ⟨y,hy,he⟩:=Finset.mem_map.mp hx
    exact hX (C.embedding.injective he ▸ hy)
  · change extend C.embedding (moduleFunction C.assignment)
        (insert (C.embedding b) (X.map C.embedding))-
        extend C.embedding (moduleFunction C.assignment) (X.map C.embedding)=1
    simpa only [extend,pullSet_insert_image,pullSet_map] using hval

theorem balancing_b_essential (i : I) : Essential (balancing i) b := by
  refine ⟨{a},by simp [a,b],?_⟩
  simp [balancing,a,b,u]

theorem balancing_u_essential (i : I) : Essential (balancing i) (u i) := by
  refine ⟨{a},by simp [a,u],?_⟩
  simp [balancing,a,b,u]

end TwoHub
end GraphicalZonotopes
