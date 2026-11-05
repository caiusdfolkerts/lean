module

public import Papers.GraphicalZonotopes.DoubledRestrictedLines

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
variable {I : Type*} [Fintype I] [DecidableEq I]

def slicedPair (a : I) (b : Bool)
    (uv : Cube (DeletedIndex a) × Cube (DeletedIndex a)) : Cube I × Cube I :=
  (extendCube a b uv.1,extendCube a b uv.2)

theorem subsetOfBits_slice_false (a : I)
    (uv : Cube (DeletedIndex a) × Cube (DeletedIndex a)) :
    subsetOfBits (coordinateChange.symm (slicedPair a false uv))=
      (subsetOfBits (coordinateChange.symm uv)).map
        (pairedEmbedding (Function.Embedding.subtype (fun i : I => i≠a))) := by
  ext w
  rcases w with ⟨i,b⟩
  fin_cases b <;> dsimp only
  · conv_lhs => simp [subsetOfBits]
    constructor
    · intro hi
      have hia : i≠a := by
        intro he
        subst i
        simpa [coordinateChange,slicedPair] using hi
      refine mem_map.mpr ⟨(⟨i,hia⟩,0),?_,rfl⟩
      simpa [coordinateChange,slicedPair,extendCube,hia] using hi
    · intro hi
      obtain ⟨⟨j,b⟩,hj,he⟩ := mem_map.mp hi
      have hb : b=0 := congrArg Prod.snd he
      subst b
      have hji : j.1=i := congrArg Prod.fst he
      subst i
      simpa [coordinateChange,slicedPair,extendCube,j.2] using hj
  · conv_lhs => simp [subsetOfBits]
    constructor
    · intro hi
      have hia : i≠a := by
        intro he
        subst i
        simpa [coordinateChange,slicedPair] using hi
      refine mem_map.mpr ⟨(⟨i,hia⟩,1),?_,rfl⟩
      simpa [coordinateChange,slicedPair,extendCube,hia] using hi
    · intro hi
      obtain ⟨⟨j,b⟩,hj,he⟩ := mem_map.mp hi
      have hb : b=1 := congrArg Prod.snd he
      subst b
      have hji : j.1=i := congrArg Prod.fst he
      subst i
      simpa [coordinateChange,slicedPair,extendCube,j.2] using hj

theorem subsetOfBits_slice_true (a : I)
    (uv : Cube (DeletedIndex a) × Cube (DeletedIndex a)) :
    subsetOfBits (coordinateChange.symm (slicedPair a true uv))=
      insert (a,0) (subsetOfBits (coordinateChange.symm (slicedPair a false uv))) := by
  ext w
  rcases w with ⟨i,b⟩
  fin_cases b <;> by_cases hi : i=a
  · subst i
    simp [subsetOfBits,coordinateChange,slicedPair,extendCube]
  · simp [subsetOfBits,coordinateChange,slicedPair,extendCube,hi]
  · subst i
    simp [subsetOfBits,coordinateChange,slicedPair,extendCube]
  · simp [subsetOfBits,coordinateChange,slicedPair,extendCube,hi]

theorem missing_one_not_mem_slice (a : I) (b : Bool)
    (uv : Cube (DeletedIndex a) × Cube (DeletedIndex a)) :
    (a,1)∉subsetOfBits (coordinateChange.symm (slicedPair a b uv)) := by
  cases b <;> simp [subsetOfBits,coordinateChange,slicedPair,extendCube]

theorem edgeContext_slice_true (u v : I×Fin 2) (a : Remaining u v)
    (uv : Cube (DeletedIndex a) × Cube (DeletedIndex a)) :
    edgeContext u v (coordinateChange.symm (slicedPair a true uv))=
      insert (a.1,0) (edgeContext u v (coordinateChange.symm (slicedPair a false uv))) := by
  simp only [edgeContext,subsetOfBits_slice_true,map_insert]
  rfl

theorem missing_one_not_mem_edge_slice (u v : I×Fin 2) (a : Remaining u v) (b : Bool)
    (uv : Cube (DeletedIndex a) × Cube (DeletedIndex a)) :
    (a.1,1)∉edgeContext u v (coordinateChange.symm (slicedPair a b uv)) := by
  intro h
  obtain ⟨w,hw,he⟩ := mem_map.mp h
  have he' : w=(a,1) := (remainingEmbedding u v).injective he
  exact missing_one_not_mem_slice a b uv (he' ▸ hw)

theorem paired_map_pullSet (a : I) (S : Finset (I×Fin 2)) :
    (SetFunctionEmbedding.pullSet
      (pairedEmbedding (Function.Embedding.subtype (fun i : I => i≠a))) S).map
        (pairedEmbedding (Function.Embedding.subtype (fun i : I => i≠a)))=
      (S.erase (a,0)).erase (a,1) := by
  ext w
  rcases w with ⟨i,b⟩
  simp only [mem_map,SetFunctionEmbedding.mem_pullSet,mem_erase]
  constructor
  · rintro ⟨⟨j,c⟩,hj,he⟩
    have hia : i≠a := by
      have hji : j.1=i := congrArg Prod.fst he
      exact hji ▸ j.2
    refine ⟨?_,?_,?_⟩
    · intro h
      exact hia (congrArg Prod.fst h)
    · intro h
      exact hia (congrArg Prod.fst h)
    · simpa only [he] using hj
  · rintro ⟨h1,h0,hw⟩
    have hia : i≠a := by
      intro hi
      subst i
      fin_cases b
      · exact h0 rfl
      · exact h1 rfl
    exact ⟨(⟨i,hia⟩,b),hw,rfl⟩

/-- Every context, after deleting both vertices of one part, is one of the
zero-bit slices of the remaining-part cube. This is the surjectivity needed
when the slice argument is applied back to the complete elemental kernel. -/
theorem exists_zero_slice_context (u v : I×Fin 2) (a : Remaining u v)
    (S : Finset (I×Fin 2)) :
    ∃ uv : Cube (DeletedIndex a) × Cube (DeletedIndex a),
      edgeContext u v (coordinateChange.symm (slicedPair a false uv))=
        ((S∩commonNeighbors (graph I) u v).erase (a.1,0)).erase (a.1,1) := by
  let T := remainingPart u v S
  let e := pairedEmbedding (Function.Embedding.subtype (fun i : Remaining u v => i≠a))
  let U := SetFunctionEmbedding.pullSet e T
  let uv := coordinateChange (bitsOfSubset U)
  refine ⟨uv,?_⟩
  rw [edgeContext,subsetOfBits_slice_false]
  have hU : subsetOfBits (coordinateChange.symm uv)=U := by simp [uv]
  rw [hU]
  change (U.map e).map (remainingEmbedding u v)=_
  rw [show U.map e=(T.erase (a,0)).erase (a,1) from paired_map_pullSet a T]
  rw [map_erase,map_erase]
  have hT : T.map (remainingEmbedding u v)=S∩commonNeighbors (graph I) u v := by
    simpa only [edgeContext,subsetOfBits_bitsOfSubset] using edgeContext_remainingPart u v S
  rw [hT]
  rfl

end DoubledParts
end GraphicalZonotopes
