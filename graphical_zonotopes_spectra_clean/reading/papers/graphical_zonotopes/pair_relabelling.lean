module

public import Papers.GraphicalZonotopes.PairCounting
public import Papers.GraphicalZonotopes.PairTensor

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
open scoped BigOperators symmDiff
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def pairedEmbedding (e : I ↪ J) : I×Fin 2 ↪ J×Fin 2 :=
  e.prodMap (Function.Embedding.refl (Fin 2))

theorem firstSet_map (e : I ↪ J) (S : Finset (I×Fin 2)) :
    firstSet (S.map (pairedEmbedding e))=(firstSet S).map e := by
  ext j
  rw [mem_firstSet,mem_map,mem_map]
  constructor
  · rintro ⟨⟨i,b⟩,hi,h⟩
    have hb : b=0 := congrArg Prod.snd h
    subst b
    exact ⟨i,(mem_firstSet _ _).mpr hi,congrArg Prod.fst h⟩
  · rintro ⟨i,hi,h⟩
    exact ⟨(i,0),(mem_firstSet _ _).mp hi,Prod.ext h rfl⟩

theorem secondSet_map (e : I ↪ J) (S : Finset (I×Fin 2)) :
    secondSet (S.map (pairedEmbedding e))=(secondSet S).map e := by
  ext j
  rw [mem_secondSet,mem_map,mem_map]
  constructor
  · rintro ⟨⟨i,b⟩,hi,h⟩
    have hb : b=1 := congrArg Prod.snd h
    subst b
    exact ⟨i,(mem_secondSet _ _).mpr hi,congrArg Prod.fst h⟩
  · rintro ⟨i,hi,h⟩
    exact ⟨(i,1),(mem_secondSet _ _).mp hi,Prod.ext h rfl⟩

theorem integerData_map (e : I ↪ J) (S : Finset (I×Fin 2)) :
    integerData (S.map (pairedEmbedding e))=integerData S := by
  have h1 := integerData_count_identity (S.map (pairedEmbedding e))
  have h2 := integerData_count_identity S
  rw [firstSet_map,secondSet_map,← map_inter,card_map,card_map,card_map] at h1
  omega

def remainingPartEmbedding (u v : I×Fin 2) : Remaining u v ↪ I :=
  ⟨Subtype.val,Subtype.val_injective⟩

theorem remainingEmbedding_eq (u v : I×Fin 2) :
    remainingEmbedding u v=pairedEmbedding (remainingPartEmbedding u v) := by
  apply Function.Embedding.ext
  intro w
  rfl

theorem integerData_edgeContext (u v : I×Fin 2)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) :
    integerData (edgeContext u v s)=integerData (subsetOfBits s) := by
  rw [edgeContext,remainingEmbedding_eq,integerData_map]

@[simp] theorem edgeContext_card (u v : I×Fin 2)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) :
    (edgeContext u v s).card=(subsetOfBits s).card := by
  simp only [edgeContext,card_map]

theorem edgeContext_remainingPart (u v : I×Fin 2) (S : Finset (I×Fin 2)) :
    edgeContext u v (bitsOfSubset (remainingPart u v S))=
      S∩commonNeighbors (graph I) u v := by
  rw [edgeContext,subsetOfBits_bitsOfSubset]
  ext w
  constructor
  · intro hw
    obtain ⟨w',hw',rfl⟩ := mem_map.mp hw
    refine mem_inter.mpr ⟨(mem_remainingPart _ _ _ _).mp hw',?_⟩
    exact (mem_commonNeighbors _ _ _ _).mpr ⟨Ne.symm w'.1.2.1,Ne.symm w'.1.2.2⟩
  · intro hw
    rcases mem_inter.mp hw with ⟨hw,hn⟩
    rcases (mem_commonNeighbors _ _ _ _).mp hn with ⟨hu,hv⟩
    let w' : Remaining u v × Fin 2 := (⟨w.1,Ne.symm hu,Ne.symm hv⟩,w.2)
    exact mem_map.mpr ⟨w',(mem_remainingPart _ _ _ _).mpr hw,rfl⟩

theorem edgeContext_all_adj (u v : I×Fin 2)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) :
    ∀ w∈edgeContext u v s,(graph I).Adj u w ∧ (graph I).Adj v w := by
  intro w hw
  obtain ⟨w',hw',rfl⟩ := mem_map.mp hw
  exact ⟨Ne.symm w'.1.2.1,Ne.symm w'.1.2.2⟩

theorem integerData_insert_common (u : I×Fin 2) (S : Finset (I×Fin 2))
    (hu : u∉S) (ha : ∀ w∈S,(graph I).Adj u w) :
    integerData (insert u S)=integerData S+(S.card : ℤ)+firstWeight u := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  simp only [cast_integerData]
  rw [graphFunction_insert _ u S hu]
  have he : (∑ w∈S,if (graph I).Adj u w then (1 : ℝ) else 0)=(S.card : ℝ) := by
    simp only [sum_ite_of_true ha,sum_const,nsmul_eq_mul,mul_one]
  rw [he]
  simp only [modular,subsetSum,sum_insert hu]
  ring

theorem firstWeight_isBit (u : I×Fin 2) : firstWeight u=0 ∨ firstWeight u=1 := by
  unfold firstWeight
  split_ifs <;> simp

end DoubledParts
end GraphicalZonotopes
