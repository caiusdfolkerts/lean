module

public import Papers.GraphicalZonotopes.DoubledSliceContexts

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual complete-quadratic row description, before any vertex is
deleted. Both members of the floor-half complementary pair satisfy it. -/
def CompleteQuadraticRows (z : SetFunction (I×Fin 2)) : Prop :=
  ∀ u v,(graph I).Adj u v → ∃ c : ℝ,∃ L : Finset (Remaining u v),
    (c=1 ∨ c= -1) ∧ ∀ uv,
      delta z u v (edgeContext u v (coordinateChange.symm uv))=
        faceFunction (completePhase c L) uv

theorem setFunction_completeQuadraticRows : CompleteQuadraticRows (setFunction (I := I)) := by
  intro u v huv
  refine ⟨if u.2=1 ∧ v.2=1 then -1 else 1,if u.2=v.2 then univ else ∅,?_,?_⟩
  · split_ifs <;> simp
  · exact setFunction_edgeProfile huv

theorem complementFunction_completeQuadraticRows :
    CompleteQuadraticRows (complementFunction (I := I)) := by
  intro u v huv
  refine ⟨-(if u.2=1 ∧ v.2=1 then -1 else 1),if u.2=v.2 then univ else ∅,?_,?_⟩
  · split_ifs <;> norm_num
  · intro uv
    rw [complementFunction_edgeProfile huv]
    congr 1
    funext x
    simp only [rowPhase,Pi.neg_apply,completePhase]
    ring

theorem remaining_deleted_nonempty (hI : 4≤Fintype.card I)
    (u v : I×Fin 2) (a : Remaining u v) : Nonempty (DeletedIndex a) := by
  obtain ⟨i,hi,hn⟩ := exists_mem_notMem_of_card_lt_card
    (show ({u.1,v.1,a.1} : Finset I).card<(univ : Finset I).card by
      have h : ({u.1,v.1,a.1} : Finset I).card≤3 := card_le_three
      simpa only [card_univ] using (lt_of_le_of_lt h (by omega : 3<Fintype.card I)))
  have hnot : i≠u.1 ∧ i≠v.1 ∧ i≠a.1 := by simpa using hn
  exact ⟨⟨⟨i,hnot.1,hnot.2.1⟩,fun he => hnot.2.2 (congrArg Subtype.val he)⟩⟩

/-- The complete tight kernel after deleting one of the paired vertices is
still a line. All retained contexts are used, and the proof derives the
missing row equations by the two distinct Boolean slices. -/
theorem one_singleton_tight_kernel (hI : 4≤Fintype.card I) (a : I)
    {z : SetFunction (I×Fin 2)} (hzn : TranslationNormalized z)
    (hzG : Graphical (graph I) z) (hphase : CompleteQuadraticRows z)
    (hfour : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0)
    (f : SetFunction (VertexDeletion.Retained (a,(1 : Fin 2)))) (hfn : TranslationNormalized f)
    (hzero : ∀ u v : VertexDeletion.Retained (a,(1 : Fin 2)),u≠v →
      ∀ S : Finset (VertexDeletion.Retained (a,(1 : Fin 2))),u∉S → v∉S →
      delta (SetFunctionEmbedding.restrict (VertexDeletion.embedding (a,1)) z) u v S=0 →
      delta f u v S=0) :
    ∃ t : ℝ,f=t • SetFunctionEmbedding.restrict (VertexDeletion.embedding (a,1)) z := by
  let d : I×Fin 2 := (a,1)
  let s : I×Fin 2 := (a,0)
  let e := VertexDeletion.embedding d
  let F := SetFunctionEmbedding.extend e f
  let Z := SetFunctionEmbedding.extend e (SetFunctionEmbedding.restrict e z)
  have hsd : s≠d := by simp [s,d]
  have hfG : Graphical ((graph I).comap e) f := by
    intro u v huv hnon S hu hv
    exact hzero u v huv S hu hv
      (SetFunctionEmbedding.restrict_graphical e hzG u v huv hnon S hu hv)
  have hFn : TranslationNormalized F := SetFunctionEmbedding.extend_translationNormalized e hfn
  have hFG : Graphical (graph I) F := SetFunctionEmbedding.extend_graphical e hfG
  have hZn : TranslationNormalized Z := SetFunctionEmbedding.extend_translationNormalized e
    (SetFunctionEmbedding.restrict_translationNormalized e hzn)
  have hZG : Graphical (graph I) Z := SetFunctionEmbedding.extend_graphical e
    (SetFunctionEmbedding.restrict_graphical e hzG)
  have hlocal := deletion_incident_row_line (by omega : 3≤Fintype.card I) s d hsd rfl
    hzn hzG (fun v => by
      obtain ⟨c,L,hc,hp⟩ := hphase s v.1 v.2
      have hc0 : c≠0 := by rcases hc with rfl | rfl <;> norm_num
      exact ⟨completePhase c L,completePhase_isSign hc L,completePhase_nonseparable hc0 L,hp⟩)
    f hfn hzero
  choose scale hscale using hlocal
  obtain ⟨t,ht⟩ := star_scales_constant hI s z F hfour scale hscale
  let R : SetFunction (I×Fin 2) := F-t • Z
  have hRn : TranslationNormalized R := by
    refine ⟨?_,?_⟩
    · change F ∅-t*Z ∅=0
      rw [hFn.1,hZn.1]
      ring
    · intro v
      change F {v}-t*Z {v}=0
      rw [hFn.2 v,hZn.2 v]
      ring
  have hRG : Graphical (graph I) R := by
    intro u v huv hnon S hu hv
    rw [show R=F-t • Z from rfl,delta_sub,delta_smul,
      hFG u v huv hnon S hu hv,hZG u v huv hnon S hu hv]
    ring
  have hignoreD : ∀ S : Finset (I×Fin 2),R (insert d S)=R S := by
    intro S
    simp only [R,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,F,Z,
      SetFunctionEmbedding.extend_insert_absent e _ d (VertexDeletion.deleted_not_range d)]
  have hrowS : ∀ v,s≠v → ∀ S : Finset (I×Fin 2),s∉S → v∉S → delta R s v S=0 := by
    intro v hsv S hs hv
    by_cases hadj : (graph I).Adj s v
    · let v' : AtVertex s := ⟨v,hadj⟩
      have hvd : v≠d := by intro he; exact hadj (by simpa [s,d] using congrArg Prod.fst he.symm)
      have hz : delta Z s v S=delta z s v S := by
        have he : Z=(fun T => z (T.erase d)) := funext (VertexDeletion.extend_restrict d z)
        rw [he]
        exact VertexDeletion.delta_delete_nonNeighbor hzn hzG hsv hsd hvd (by simp [s,d,graph]) hs hv
      rw [show R=F-t • Z from rfl,delta_sub,delta_smul,hscale v' S hs hv,ht v',hz]
      ring
    · exact hRG s v hsv hadj S hs hv
  have hignoreS := insert_eq_of_zero_incident hRn s hrowS
  have hRzero {u v : I×Fin 2} (huv : u≠v) (hud : u≠d) (hvd : v≠d)
      {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) (hd : d∉S)
      (hz : delta z u v S=0) : delta R u v S=0 := by
    have hF0 : delta F u v S=0 := VertexDeletion.extended_tight_zero d z f hzero huv hud hvd hu hv hd hz
    have hZ0 : delta Z u v S=0 := by
      have he : Z=(fun T => z (T.erase d)) := funext (VertexDeletion.extend_restrict d z)
      rw [he,VertexDeletion.delta_erase_function d u v hud hvd,erase_eq_of_notMem hd]
      exact hz
    rw [show R=F-t • Z from rfl,delta_sub,delta_smul,hF0,hZ0]
    ring
  have hother {u v : I×Fin 2} (hua : u.1≠a) (hva : v.1≠a)
      (huv : (graph I).Adj u v) :
      ∀ S : Finset (I×Fin 2),u∉S → v∉S → delta R u v S=0 := by
    let a' : Remaining u v := ⟨a,Ne.symm hua,Ne.symm hva⟩
    letI := remaining_deleted_nonempty hI u v a'
    obtain ⟨c,L,hc,hprofile⟩ := hphase u v huv
    have hc0 : c≠0 := by rcases hc with rfl | rfl <;> norm_num
    let p : (Cube (DeletedIndex a') × Cube (DeletedIndex a')) → ℝ :=
      fun uv => delta R u v (edgeContext u v (coordinateChange.symm (slicedPair a' false uv)))
    have hp : p∈tensorSpace := tensorSpace_slice a' false false
      (graphical_edgeProfile_mem_tensorSpace hRn hRG ((graph I).ne_of_adj huv))
    have hslice (b : Bool) (uv : Cube (DeletedIndex a') × Cube (DeletedIndex a'))
        (hz : faceFunction (slicePhase a' c L b) uv=0) :
        delta R u v (edgeContext u v (coordinateChange.symm (slicedPair a' b uv)))=0 := by
      apply hRzero ((graph I).ne_of_adj huv)
        (fun he => hua (congrArg Prod.fst he)) (fun he => hva (congrArg Prod.fst he))
        (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _)
        (missing_one_not_mem_edge_slice u v a' b uv)
      rw [hprofile]
      exact (faceFunction_slice a' c L b uv).trans hz
    have hp0 : p=0 := by
      apply boolean_slice_intersection (slicePhase_isSign a' hc L false)
        (slicePhase_isSign a' hc L true) (slicePhase_nonseparable a' hc0 L false)
        (slicePhase_nonseparable a' hc0 L true) (slicePhase_distinct a' hc0 L) p hp
      · exact hslice false
      · intro uv hz
        have h := hslice true uv hz
        rw [edgeContext_slice_true,delta_insert_eq_of_insert_eq hignoreS] at h
        exact h
    intro S hu hv
    obtain ⟨uv,he⟩ := exists_zero_slice_context u v a' S
    have h := congrFun hp0 uv
    change delta R u v (edgeContext u v (coordinateChange.symm (slicedPair a' false uv)))=0 at h
    rw [he] at h
    rw [VertexDeletion.delta_erase_eq_of_insert_eq hignoreD u v
        (fun he => hua (congrArg Prod.fst he)) (fun he => hva (congrArg Prod.fst he)),
      VertexDeletion.delta_erase_eq_of_insert_eq hignoreS u v
        (fun he => hua (congrArg Prod.fst he)) (fun he => hva (congrArg Prod.fst he))] at h
    rw [delta_commonNeighbors hRn hRG ((graph I).ne_of_adj huv) hu hv]
    exact h
  have hR : R=0 := by
    apply normalized_zero_elemental_eq_zero hRn
    intro u v huv S hu hv
    by_cases hua : u.1=a
    · rcases u with ⟨i,b⟩
      change i=a at hua
      subst i
      fin_cases b
      · exact delta_zero_of_insert_eq hignoreS v S
      · exact delta_zero_of_insert_eq hignoreD v S
    · by_cases hva : v.1=a
      · rw [delta_comm]
        rcases v with ⟨i,b⟩
        change i=a at hva
        subst i
        fin_cases b
        · exact delta_zero_of_insert_eq hignoreS u S
        · exact delta_zero_of_insert_eq hignoreD u S
      · by_cases hadj : (graph I).Adj u v
        · exact hother hua hva hadj S hu hv
        · exact hRG u v huv hadj S hu hv
  refine ⟨t,?_⟩
  have he : F=t • Z := sub_eq_zero.mp hR
  have hsmall := congrArg (SetFunctionEmbedding.restrict e) he
  simpa only [F,Z,SetFunctionEmbedding.restrict_smul,SetFunctionEmbedding.restrict_extend] using hsmall

end DoubledParts
end GraphicalZonotopes
