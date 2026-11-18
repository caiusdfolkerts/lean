module

public import Papers.GraphicalZonotopes.PurePivotSplitting
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

/-- An actual family of Boolean modules, independent in the complete
response quotient, whose unit-weight sum is the prescribed class. -/
structure PureDecomposition (C : Finset H) (v : ResponseQuotient H) (k : ℕ) where
  functions : Fin k → SetFunction H
  monotone_boolean : ∀ i, IsMonotoneBoolean (functions i)
  essential : ∀ i a, a∈C → Essential (functions i) a
  ignored : ∀ i a, a∉C → ∀ X, functions i (insert a X)=functions i X
  block_supported : ∀ i, ∃ x : PairIn C → ℝ, responseClass (functions i)=blockClass C x
  independent : LinearIndependent ℝ (fun i => responseClass (functions i))
  sum_eq : (∑ i,responseClass (functions i))=v

theorem pureDecomposition_of_vectors {C : Finset H} {J : Type*} [Fintype J]
    (x : J → PairIn C → ℝ) (hx : ∀ j,PureRealizable C (x j))
    (hind : LinearIndependent ℝ (fun j => blockClass C (x j)))
    {v : ResponseQuotient H} (hsum : (∑ j,blockClass C (x j))=v)
    {k : ℕ} (hk : Fintype.card J=k) : Nonempty (PureDecomposition C v k) := by
  classical
  choose F hF he hi hr using hx
  let e : Fin k ≃ J := (finCongr hk.symm).trans (Fintype.equivFin J).symm
  refine ⟨⟨fun i => F (e i),fun i => hF (e i),fun i a => he (e i) a,
    fun i a => hi (e i) a,fun i => ⟨x (e i),hr (e i)⟩,?_,?_⟩⟩
  · have h : LinearIndependent ℝ (fun j => responseClass (F j)) := by
      simpa only [hr] using hind
    exact h.comp e e.injective
  · calc
      _ = ∑ j : J,responseClass (F j) := e.sum_comp _
      _ = v := by simpa only [hr] using hsum

def starVector (C : Finset H) (a : H) : PairIn C → ℝ :=
  pairIndicator (starPairs C a (C.erase a))

theorem starVector_eq (C : Finset H) (a : H) (e : PairIn C) :
    starVector C a e=if a=e.1.1.1 ∨ a=e.1.1.2 then 1 else 0 := by
  have hu := e.2.1
  have hv := e.2.2
  have huv : e.1.1.1≠e.1.1.2 := ne_of_lt e.1.2.1
  simp only [starVector,pairIndicator,mem_starPairs,StarPair,mem_erase]
  congr 1
  apply propext
  constructor
  · rintro (⟨h,_⟩ | ⟨h,_⟩)
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact Or.inl ⟨h.symm,fun hh => huv (h.symm.trans hh.symm),hv⟩
    · exact Or.inr ⟨h.symm,fun hh => huv (hh.trans h),hu⟩

theorem clique_without_vertex_class (C : Finset H) (a : H) :
    blockClass C (pairIndicator (cliquePairs C (C.erase a))) =
      -blockClass C (starVector C a) := by
  have he : pairIndicator (cliquePairs C (C.erase a))=
      (fun _ : PairIn C => (1 : ℝ))-starVector C a := by
    funext e
    simp only [Pi.sub_apply]
    rw [starVector_eq]
    simp only [pairIndicator,mem_cliquePairs,mem_erase]
    by_cases hu : a=e.1.1.1 <;> by_cases hv : a=e.1.1.2 <;>
      simp [eq_comm,hu,hv,e.2.1,e.2.2]
  rw [he,map_sub]
  have hz : blockClass C (fun _ : PairIn C => (1 : ℝ))=0 := by
    change coefficientClass (blockCoordinates C (fun _ => 1))=0
    have hco : blockCoordinates C (fun _ : PairIn C => (1 : ℝ))=
        fun r : HubResponseRow H => if rowClique r=C then 1 else 0 := by
      funext r
      change (if _h : rowClique r=C then (1 : ℝ) else 0)=_
      split <;> rfl
    rw [hco]
    exact coefficientClass_block_zero C
  rw [hz,zero_sub]

theorem positive_star_small_interpolation (C : Finset H) (hC : 3≤C.card)
    (a : H) (ha : a∈C) {k : ℕ} (hk : 1≤k) (hkC : k≤C.card-1) :
    Nonempty (PureDecomposition C (blockClass C (starVector C a)) k) := by
  have hcard : (C.erase a).card=C.card-1 := card_erase_of_mem ha
  have hn : (C.erase a).Nonempty := card_pos.mp (by omega)
  have hsub : C.erase a⊆C := erase_subset _ _
  obtain ⟨Q,hQ,hreal,hind,hsum⟩ := pureEdgeChunk_partition C
    (Or.inl ⟨a,C.erase a,ha,hsub,notMem_erase _ _,rfl⟩)
    (starPairs_nonempty C ha hsub (notMem_erase _ _) hn) hk
    (by simpa only [starPairs_card C ha hsub (notMem_erase _ _),hcard] using hkC)
  obtain ⟨e₀,he₀⟩ := cliquePairs_nonempty C (C.erase a) hsub (by omega)
  have hzero : ∀ B : Q.parts,pairIndicator B.1 e₀=0 := by
    intro B
    have hnot : e₀∉B.1 := by
      intro h
      have hs := mem_starPairs.mp ((Q.le B.2) h)
      obtain ⟨hu,hv⟩ := mem_cliquePairs.mp he₀
      rcases hs with ⟨hh,_⟩ | ⟨hh,_⟩
      · exact (mem_erase.mp hu).1 hh
      · exact (mem_erase.mp hv).1 hh
    exact ite_eq_right hnot
  apply pureDecomposition_of_vectors _ hreal
    (blockClass_linearIndependent_of_reference C e₀ _ hind hzero) _
    (by simpa only [Fintype.card_coe] using hQ)
  rw [← map_sum,hsum]
  rfl

theorem negative_star_small_interpolation (C : Finset H) (hC : 3≤C.card)
    (a : H) (ha : a∈C) {k : ℕ} (hk : 1≤k) (hkC : k≤(C.card-1).choose 2) :
    Nonempty (PureDecomposition C (-blockClass C (starVector C a)) k) := by
  have hcard : (C.erase a).card=C.card-1 := card_erase_of_mem ha
  have hsub : C.erase a⊆C := erase_subset _ _
  obtain ⟨Q,hQ,hreal,hind,hsum⟩ := pureEdgeChunk_partition C
    (Or.inr ⟨C.erase a,hsub,rfl⟩)
    (cliquePairs_nonempty C (C.erase a) hsub (by omega)) hk
    (by simpa only [cliquePairs_card C (C.erase a) hsub,hcard] using hkC)
  obtain ⟨b,hb⟩ := card_pos.mp (show 0<(C.erase a).card by omega)
  have hab : a≠b := Ne.symm (mem_erase.mp hb).1
  let e₀ := pairOfNe C a b hab ha (mem_of_mem_erase hb)
  have hzero : ∀ B : Q.parts,pairIndicator B.1 e₀=0 := by
    intro B
    have hnot : e₀∉B.1 := by
      intro h
      obtain ⟨hu,hv⟩ := mem_cliquePairs.mp ((Q.le B.2) h)
      rcases pairOfNe_endpoints C a b hab ha (mem_of_mem_erase hb) with hh | hh
      · exact (mem_erase.mp hu).1 hh.1
      · exact (mem_erase.mp hv).1 hh.2
    exact ite_eq_right hnot
  apply pureDecomposition_of_vectors _ hreal
    (blockClass_linearIndependent_of_reference C e₀ _ hind hzero) _
    (by simpa only [Fintype.card_coe] using hQ)
  rw [← map_sum,hsum]
  exact clique_without_vertex_class C a

end BooleanModule
end GraphicalZonotopes
