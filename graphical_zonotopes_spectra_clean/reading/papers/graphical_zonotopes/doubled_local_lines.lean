module

public import Papers.GraphicalZonotopes.DoubledPhase
public import Papers.GraphicalZonotopes.LocalSlopes

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem remaining_nonempty (hI : 3≤Fintype.card I) (u v : I×Fin 2) :
    Nonempty (Remaining u v) := by
  have hcard : ({u.1,v.1} : Finset I).card<(univ : Finset I).card := by
    have h : ({u.1,v.1} : Finset I).card≤2 := card_le_two
    simpa only [card_univ] using (lt_of_le_of_lt h (by omega : 2<Fintype.card I))
  obtain ⟨i,hi,hn⟩ := exists_mem_notMem_of_card_lt_card hcard
  have he : i≠u.1 ∧ i≠v.1 := by simpa using hn
  exact ⟨⟨i,he⟩⟩

theorem complementFunction_graphical : Graphical (graph I) (complementFunction (I := I)) := by
  intro u v huv hnon S hu hv
  rw [complementFunction,delta_sub,graphFunction_delta _ huv hu hv,
    if_neg hnon,setFunction_graphical u v huv hnon S hu hv,sub_self]

/-- A complete original row is forced to a single scale by its exact Boolean
zero pattern. All nonedge constraints are recovered before the tensor lemma
is used. -/
theorem local_row_line_of_phase {z : SetFunction (I×Fin 2)}
    (hzn : TranslationNormalized z) (hzG : Graphical (graph I) z)
    {u v : I×Fin 2} (huv : (graph I).Adj u v) [Nonempty (Remaining u v)]
    (H : Cube (Remaining u v) → ℝ) (hH : ∀ x,H x=1 ∨ H x= -1)
    (hsep : Nonseparable H)
    (hprofile : ∀ uv,delta z u v (edgeContext u v (coordinateChange.symm uv))=
      faceFunction H uv)
    (f : SetFunction (I×Fin 2)) (hfn : TranslationNormalized f)
    (hzero : ∀ a b,a≠b → ∀ S : Finset (I×Fin 2),a∉S → b∉S →
      delta z a b S=0 → delta f a b S=0) :
    ∃ c : ℝ,∀ S : Finset (I×Fin 2),u∉S → v∉S → delta f u v S=c*delta z u v S := by
  have hfG : Graphical (graph I) f := by
    intro a b hab hnon S ha hb
    exact hzero a b hab S ha hb (hzG a b hab hnon S ha hb)
  let p : (Cube (Remaining u v) × Cube (Remaining u v)) → ℝ :=
    fun uv => delta f u v (edgeContext u v (coordinateChange.symm uv))
  have hp : p∈tensorSpace :=
    graphical_edgeProfile_mem_tensorSpace hfn hfG ((graph I).ne_of_adj huv)
  have hzeros : ∀ uv,faceFunction H uv=0 → p uv=0 := by
    intro uv he
    apply hzero u v ((graph I).ne_of_adj huv) _
      (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _)
    rwa [hprofile]
  obtain ⟨c,hc⟩ := (boolean_face_line hH hsep p hp).mp hzeros
  refine ⟨c,?_⟩
  intro S hu hv
  let s := bitsOfSubset (remainingPart u v S)
  let uv := coordinateChange s
  have he := congrFun hc uv
  change delta f u v (edgeContext u v (coordinateChange.symm uv))=
    c*faceFunction H uv at he
  rw [← hprofile uv] at he
  have hcontext : edgeContext u v (coordinateChange.symm uv)=
      S∩commonNeighbors (graph I) u v := by
    rw [show coordinateChange.symm uv=s by simp [uv]]
    exact edgeContext_remainingPart u v S
  rw [hcontext] at he
  rw [delta_commonNeighbors hfn hfG ((graph I).ne_of_adj huv) hu hv,
    delta_commonNeighbors hzn hzG ((graph I).ne_of_adj huv) hu hv]
  exact he

theorem setFunction_local_row_lines (hI : 3≤Fintype.card I)
    (f : SetFunction (I×Fin 2)) (hfn : TranslationNormalized f)
    (hzero : ∀ a b,a≠b → ∀ S : Finset (I×Fin 2),a∉S → b∉S →
      delta setFunction a b S=0 → delta f a b S=0)
    (e : SlopeEdge (graph I)) :
    ∃ c : ℝ,∀ S : Finset (I×Fin 2),e.1.1∉S → e.1.2∉S →
      delta f e.1.1 e.1.2 S=c*delta setFunction e.1.1 e.1.2 S := by
  letI := remaining_nonempty hI e.1.1 e.1.2
  exact local_row_line_of_phase setFunction_translationNormalized setFunction_graphical e.2
    (rowPhase e.1.1 e.1.2) (rowPhase_isSign _ _) (rowPhase_nonseparable _ _)
    (setFunction_edgeProfile e.2) f hfn hzero

theorem complementFunction_local_row_lines (hI : 3≤Fintype.card I)
    (f : SetFunction (I×Fin 2)) (hfn : TranslationNormalized f)
    (hzero : ∀ a b,a≠b → ∀ S : Finset (I×Fin 2),a∉S → b∉S →
      delta complementFunction a b S=0 → delta f a b S=0)
    (e : SlopeEdge (graph I)) :
    ∃ c : ℝ,∀ S : Finset (I×Fin 2),e.1.1∉S → e.1.2∉S →
      delta f e.1.1 e.1.2 S=c*delta complementFunction e.1.1 e.1.2 S := by
  letI := remaining_nonempty hI e.1.1 e.1.2
  apply local_row_line_of_phase complementFunction_translationNormalized complementFunction_graphical e.2
    (-rowPhase e.1.1 e.1.2) _ (rowPhase_nonseparable _ _).neg
    (complementFunction_edgeProfile e.2) f hfn hzero
  intro x
  rcases rowPhase_isSign e.1.1 e.1.2 x with h | h
  · exact Or.inr (by simpa using congrArg Neg.neg h)
  · exact Or.inl (by simpa using congrArg Neg.neg h)

theorem exists_nonzero_slack_of_phase {z : SetFunction (I×Fin 2)}
    {u v : I×Fin 2} [Nonempty (Remaining u v)]
    (H : Cube (Remaining u v) → ℝ) (hH : ∀ x,H x=1 ∨ H x= -1)
    (hprofile : ∀ uv,delta z u v (edgeContext u v (coordinateChange.symm uv))=
      faceFunction H uv) :
    ∃ S : Finset (I×Fin 2),u∉S ∧ v∉S ∧ delta z u v S≠0 := by
  have hne := faceFunction_ne_zero hH
  have hex : ∃ uv,faceFunction H uv≠0 := by
    by_contra! hall
    apply hne
    funext uv
    exact hall uv
  obtain ⟨uv,huv⟩ := hex
  refine ⟨edgeContext u v (coordinateChange.symm uv),
    left_not_mem_edgeContext _ _ _,right_not_mem_edgeContext _ _ _,?_⟩
  rwa [hprofile]

theorem setFunction_nonzero_slack (hI : 3≤Fintype.card I) {u v : I×Fin 2}
    (huv : (graph I).Adj u v) :
    ∃ S : Finset (I×Fin 2),u∉S ∧ v∉S ∧ delta setFunction u v S≠0 := by
  letI := remaining_nonempty hI u v
  exact exists_nonzero_slack_of_phase (rowPhase u v) (rowPhase_isSign u v)
    (setFunction_edgeProfile huv)

theorem complementFunction_nonzero_slack (hI : 3≤Fintype.card I) {u v : I×Fin 2}
    (huv : (graph I).Adj u v) :
    ∃ S : Finset (I×Fin 2),u∉S ∧ v∉S ∧ delta complementFunction u v S≠0 := by
  letI := remaining_nonempty hI u v
  apply exists_nonzero_slack_of_phase (-rowPhase u v) _ (complementFunction_edgeProfile huv)
  intro x
  rcases rowPhase_isSign u v x with h | h
  · exact Or.inr (by simpa using congrArg Neg.neg h)
  · exact Or.inl (by simpa using congrArg Neg.neg h)

end DoubledParts
end GraphicalZonotopes
