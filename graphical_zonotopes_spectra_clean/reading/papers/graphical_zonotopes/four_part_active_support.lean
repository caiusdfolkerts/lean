module

public import Papers.GraphicalZonotopes.FourPartGraphRecognition

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.FourPartGraphRecognition
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A Cartesian tetrahedron family gives the literal complete four-partite
graph on its active vertices. No coverage of the ambient vertex type is
assumed: every vertex outside the four displayed parts is isolated. -/
theorem product_unionGraph_adj_iff {F : Finset (Finset V)} {A : Fin 4 → Finset V}
    (hne : ∀ i,(A i).Nonempty) (hdis : ∀ i j,i ≠ j → Disjoint (A i) (A j))
    (hprod : ProductFamily F A) (u v : V) :
    (unionGraph F).Adj u v ↔ ∃ i j : Fin 4,i ≠ j ∧ u ∈ A i ∧ v ∈ A j := by
  constructor
  · rintro ⟨huv,D,hD,hu,hv⟩
    obtain ⟨w,hw,rfl⟩ := (hprod D).mp hD
    obtain ⟨i,_,hi⟩ := mem_image.mp hu
    obtain ⟨j,_,hj⟩ := mem_image.mp hv
    refine ⟨i,j,?_,hi ▸ hw i,hj ▸ hw j⟩
    intro hij
    subst j
    exact huv (hi.symm.trans hj)
  · rintro ⟨i,j,hij,hu,hv⟩
    let w : Fin 4 → V := fun k =>
      if k = i then u else if k = j then v else Classical.choose (hne k)
    have hw : ∀ k,w k ∈ A k := by
      intro k
      dsimp [w]
      split_ifs with hki hkj
      · simpa only [hki] using hu
      · simpa only [hkj] using hv
      · exact Classical.choose_spec (hne k)
    have hwi : w i = u := by simp [w]
    have hwj : w j = v := by simp [w,Ne.symm hij]
    have huv : u ≠ v := by
      intro he
      exact Finset.disjoint_left.mp (hdis i j hij) hu (he.symm ▸ hv)
    refine ⟨huv,univ.image w,(hprod _).mpr ⟨w,hw,rfl⟩,?_,?_⟩
    · exact mem_image.mpr ⟨i,mem_univ _,hwi⟩
    · exact mem_image.mpr ⟨j,mem_univ _,hwj⟩

/-- The nonisolated vertices are exactly the union of the four parts. This
is the precise dictionary needed when the ambient polytope is not full
dimensional and unused coordinates remain in the ambient type. -/
theorem product_unionGraph_support {F : Finset (Finset V)} {A : Fin 4 → Finset V}
    (hne : ∀ i,(A i).Nonempty) (hdis : ∀ i j,i ≠ j → Disjoint (A i) (A j))
    (hprod : ProductFamily F A) :
    (unionGraph F).support = ((univ.biUnion A : Finset V) : Set V) := by
  ext u
  rw [SimpleGraph.mem_support]
  constructor
  · rintro ⟨v,huv⟩
    obtain ⟨i,j,hij,hu,hv⟩ := (product_unionGraph_adj_iff hne hdis hprod u v).mp huv
    exact mem_biUnion.mpr ⟨i,mem_univ _,hu⟩
  · intro hu
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hu
    obtain ⟨j,hji⟩ := exists_ne i
    obtain ⟨v,hv⟩ := hne j
    exact ⟨v,(product_unionGraph_adj_iff hne hdis hprod u v).mpr ⟨i,j,Ne.symm hji,hi,hv⟩⟩

end GraphicalZonotopes.FourPartGraphRecognition
