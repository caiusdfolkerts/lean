module

public import Papers.GraphicalZonotopes.MultipartitePairCounting
public import Papers.GraphicalZonotopes.MultipartiteSizes
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.OfFn

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
namespace SmallCount
open Finset
open scoped BigOperators

namespace SizeModel
variable {I : Type*} [Fintype I] [DecidableEq I] (p : I → ℕ)
abbrev Vertex:=Σ i : I,Fin (p i)

def embedding {s : ℕ} (hsize : (∑ i,p i)≤s) : Vertex p ↪ Fin s :=
  (Fintype.equivFin (Vertex p)).toEmbedding.trans (Fin.castLEEmb (by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using hsize))

def block {s : ℕ} (hsize : (∑ i,p i)≤s) (i : I) : Finset (Fin s):=
  univ.map ((Function.Embedding.sigmaMk i).trans (embedding p hsize))

@[simp] theorem block_card {s : ℕ} (hsize : (∑ i,p i)≤s) (i : I) :
    (block p hsize i).card=p i := by simp only [block,card_map,card_univ,Fintype.card_fin]

theorem block_disjoint {s : ℕ} (hsize : (∑ i,p i)≤s) {i j : I} (hij : i≠j) :
    Disjoint (block p hsize i) (block p hsize j) := by
  apply disjoint_left.mpr
  intro x hi hj
  obtain ⟨a,_,ha⟩:=mem_map.mp hi
  obtain ⟨b,_,hb⟩:=mem_map.mp hj
  have he : (⟨i,a⟩ : Vertex p)=⟨j,b⟩:=
    (embedding p hsize).injective (ha.trans hb.symm)
  exact hij (congrArg Sigma.fst he)

theorem block_nonempty {s : ℕ} (hsize : (∑ i,p i)≤s)
    (hpos : ∀ i,0<p i) (i : I) : (block p hsize i).Nonempty := by
  rw [← card_pos,block_card]
  exact hpos i

theorem block_injective {s : ℕ} (hsize : (∑ i,p i)≤s) (hpos : ∀ i,0<p i) :
    Function.Injective (block p hsize) := by
  intro i j he
  by_contra hij
  obtain ⟨x,hx⟩:=block_nonempty p hsize hpos i
  exact (disjoint_left.mp (block_disjoint p hsize hij)) hx (he ▸ hx)

def blocks {s : ℕ} (hsize : (∑ i,p i)≤s) : Finset (Finset (Fin s)):=
  univ.image (block p hsize)

theorem blocks_nonempty {s : ℕ} (hsize : (∑ i,p i)≤s) (hpos : ∀ i,0<p i) :
    ∀ B∈blocks p hsize,B.Nonempty := by
  intro B hB
  obtain ⟨i,_,rfl⟩:=mem_image.mp hB
  exact block_nonempty p hsize hpos i

theorem blocks_disjoint {s : ℕ} (hsize : (∑ i,p i)≤s) :
    ∀ A∈blocks p hsize,∀ B∈blocks p hsize,A≠B → Disjoint A B := by
  intro A hA B hB hAB
  obtain ⟨i,_,rfl⟩:=mem_image.mp hA
  obtain ⟨j,_,rfl⟩:=mem_image.mp hB
  exact block_disjoint p hsize (fun h => hAB (congrArg (block p hsize) h))

theorem blockUnion_card {s : ℕ} (hsize : (∑ i,p i)≤s) :
    (blockUnion (blocks p hsize)).card=∑ i,p i := by
  have he : blockUnion (blocks p hsize)=univ.biUnion (block p hsize) := by
    ext x
    simp only [blockUnion,blocks,mem_biUnion,mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨B,⟨i,rfl⟩,hx⟩
      exact ⟨i,hx⟩
    · rintro ⟨i,hx⟩
      exact ⟨block p hsize i,⟨i,rfl⟩,hx⟩
  rw [he,card_biUnion]
  · simp only [block_card]
  · intro i hi j hj hij
    exact block_disjoint p hsize hij

theorem within_count {s : ℕ} (hsize : (∑ i,p i)≤s) (hpos : ∀ i,0<p i) :
    (∑ B∈blocks p hsize,B.card.choose 2)=∑ i,(p i).choose 2 := by
  rw [blocks,sum_image]
  · simp only [block_card]
  · intro i hi j hj he
    exact block_injective p hsize hpos he

theorem crossing_count {s : ℕ} (hsize : (∑ i,p i)≤s) (hpos : ∀ i,0<p i) :
    (crossingPairs (blocks p hsize)).card=(∑ i,p i).choose 2-∑ i,(p i).choose 2 := by
  rw [crossingPairs_card_formula _ (blocks_disjoint p hsize),
    blockUnion_card,within_count p hsize hpos]

end SizeModel

/-- The finite blocks in the Boolean construction exist for every positive
proper pair count, including counts whose pattern uses fewer than all hubs. -/
theorem exists_complement_family_count (s m : ℕ) (hm : 0<m) (hmax : m<s.choose 2) :
    ∃ blocks : Finset (Finset (Fin s)),
      ComplementFamily (univ : Finset (Fin s)) blocks ∧
      (crossingPairs blocks).card=m ∧
      ∃ e : OrientedEdge (⊤ : SimpleGraph (Fin s)),e∉crossingPairs blocks := by
  obtain ⟨sizes,hpos,hsize,hcount⟩:=exists_multipartite_sizes s m hmax.le
  let p : Fin sizes.length → ℕ:=sizes.get
  have hsum : (∑ i,p i)=sizes.sum := by
    rw [← List.sum_ofFn]
    exact congrArg List.sum (List.ofFn_get sizes)
  have hinside : (∑ i,(p i).choose 2)=(sizes.map (fun n => n.choose 2)).sum := by
    rw [← List.sum_ofFn]
    change (List.ofFn ((fun n : ℕ => n.choose 2) ∘ sizes.get)).sum=_
    rw [← List.map_ofFn,List.ofFn_get]
  have hp : ∀ i,0<p i:=fun i => hpos (sizes.get i) (List.get_mem sizes i)
  have hsize' : (∑ i,p i)≤s:=by rw [hsum]; exact hsize
  let blocks:=SizeModel.blocks p hsize'
  have hc : (crossingPairs blocks).card=m := by
    rw [SizeModel.crossing_count p hsize' hp,hsum,hinside]
    exact hcount
  have hnon : (crossingPairs blocks).Nonempty:=card_pos.mp (hc.symm ▸ hm)
  refine ⟨blocks,⟨crossingPairs_nonempty_gives_two blocks hnon,
    fun B hB => subset_univ _,SizeModel.blocks_nonempty p hsize' hp,
    SizeModel.blocks_disjoint p hsize'⟩,hc,?_⟩
  have hlt : (crossingPairs blocks).card<
      (univ : Finset (OrientedEdge (⊤ : SimpleGraph (Fin s)))).card := by
    rw [hc,card_univ,completePair_card,Fintype.card_fin]
    exact hmax
  obtain ⟨e,_,he⟩:=exists_mem_notMem_of_card_lt_card hlt
  exact ⟨e,he⟩

end SmallCount
end BooleanModule
end GraphicalZonotopes
