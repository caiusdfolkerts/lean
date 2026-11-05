module
public import consolidated.deletion_geometry
public import consolidated_dev.abstract_lower_bound
public import papers.simple_four_finite_obstruction

set_option Elab.async false

section BundlePart0
/- Source: Papers/SimpleFourDualComplex.lean -/





@[expose] public section

/-! # From genuine indexed facet incidences to the dual circuit links -/

noncomputable section
namespace Papers.SimpleFour

open Cubical.Simplicial
open scoped Classical

variable {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]

def erasedFamily (σ : I → Finset V) (v : V) : {i : I // v ∈ σ i} → Finset V :=
  fun i => (σ i.val).erase v

theorem insert_mem_boundary_iff {s r : Finset V} {v : V}
    (hv : v ∈ s) (hvr : v ∉ r) :
    insert v r ∈ simplexBoundary s ↔ r ∈ simplexBoundary (s.erase v) := by
  rw [mem_simplexBoundary_iff,mem_simplexBoundary_iff]
  have hs := Finset.card_erase_add_one hv
  rw [Finset.card_insert_of_notMem hvr]
  constructor
  · rintro ⟨hsub,hcard⟩
    refine ⟨?_,by omega⟩
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun h => hvr (h ▸ hx),hsub (Finset.mem_insert_of_mem hx)⟩
  · rintro ⟨hsub,hcard⟩
    refine ⟨?_,by omega⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · simpa only [h] using hv
    · exact Finset.mem_of_mem_erase (hsub h)

theorem erasedFamily_ridgePairing (σ : I → Finset V) (v : V)
    (hp : RidgePairing σ) : RidgePairing (erasedFamily σ v) := by
  intro i r hr
  have hvr : v ∉ r := fun hv =>
    (Finset.mem_erase.mp (simplexBoundary_subset hr hv)).1 rfl
  have hR := (insert_mem_boundary_iff i.property hvr).mpr hr
  obtain ⟨j,hij,hocc⟩ := hp i.val (insert v r) hR
  have hjR : insert v r ∈ simplexBoundary (σ j) := (hocc j).mpr (Or.inr rfl)
  have hvj : v ∈ σ j := simplexBoundary_subset hjR (Finset.mem_insert_self _ _)
  let jj : {i : I // v ∈ σ i} := ⟨j,hvj⟩
  refine ⟨jj,fun h => hij (congrArg Subtype.val h),?_⟩
  intro k
  change r ∈ simplexBoundary ((σ k.val).erase v) ↔ k = i ∨ k = jj
  rw [← insert_mem_boundary_iff k.property hvr,hocc]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem erasedFamily_injective (σ : I → Finset V) (v : V)
    (hi : Function.Injective σ) : Function.Injective (erasedFamily σ v) := by
  intro i j h
  apply Subtype.ext
  apply hi
  have h' := congrArg (fun s : Finset V => insert v s) h
  simpa only [erasedFamily,Finset.insert_erase i.property,Finset.insert_erase j.property] using h'

theorem erasedFamily_image_eq_link (σ : I → Finset V) (v : V) :
    Finset.univ.image (erasedFamily σ v) = link (Finset.univ.image σ) {v} := by
  ext r
  rw [mem_link]
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    refine ⟨by simp [erasedFamily],i.val,?_⟩
    simpa only [erasedFamily,Finset.singleton_union,Finset.insert_erase i.property]
  · rintro ⟨hdisj,i,hi⟩
    have hvr : v ∉ r := by simpa using hdisj
    have hvi : v ∈ σ i := by rw [hi]; simp
    refine ⟨⟨i,hvi⟩,?_⟩
    change (σ i).erase v = r
    rw [hi,Finset.singleton_union,Finset.erase_insert hvr]

theorem ridgePairing_image_degreeTwo (σ : I → Finset V)
    (hi : Function.Injective σ) (hp : RidgePairing σ) :
    Cubical.Simplicial.RidgeDegreeTwo (Finset.univ.image σ) := by
  intro r
  by_cases hex : ∃ i, r ∈ simplexBoundary (σ i)
  · obtain ⟨i,hir⟩ := hex
    obtain ⟨j,hij,hocc⟩ := hp i r hir
    right
    have heq : (Finset.univ.image σ).filter (fun t => r ∈ simplexBoundary t) =
        {σ i,σ j} := by
      ext t
      simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and,
        Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro ⟨⟨k,rfl⟩,hkr⟩
        rcases (hocc k).mp hkr with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨⟨i,rfl⟩,(hocc i).mpr (Or.inl rfl)⟩
        · exact ⟨⟨j,rfl⟩,(hocc j).mpr (Or.inr rfl)⟩
    rw [heq,Finset.card_pair (fun h => hij (hi h))]
  · left
    have heq : (Finset.univ.image σ).filter (fun t => r ∈ simplexBoundary t) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨ht,hrt⟩ := Finset.mem_filter.mp ht
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
      exact hex ⟨i,hrt⟩
    simp only [heq,Finset.card_empty]

theorem dual_four_hasCircuitLinks (σ : I → Finset V)
    (hi : Function.Injective σ) (hp : RidgePairing σ)
    (hc : (indexedFacetGraph σ).Connected)
    (hl : ∀ v ∈ vertices σ Finset.univ,
      (indexedFacetGraph (erasedFamily σ v)).Connected) :
    HasCircuitLinks 4 (Finset.univ.image σ) := by
  have hmain := (facetCircuit_of_ridgePairing_connected hp hc).image hi.injOn
  intro a ha hcard
  by_cases haz : a = ∅
  · simpa only [haz,link_empty] using hmain
  have hpos : 0 < a.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr haz)
  have hcard1 : a.card = 1 := by omega
  obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hcard1
  obtain ⟨t,ht,hvt⟩ := ha
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
  have hv : v ∈ vertices σ Finset.univ :=
    (mem_vertices σ Finset.univ v).mpr
      ⟨i,Finset.mem_univ i,hvt (Finset.mem_singleton_self v)⟩
  rw [← erasedFamily_image_eq_link]
  exact (facetCircuit_of_ridgePairing_connected (erasedFamily_ridgePairing σ v hp)
    (hl v hv)).image (erasedFamily_injective σ v hi).injOn

end Papers.SimpleFour

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/SimpleFourCircuitObstruction.lean -/





@[expose] public section

/-!
# The lower-bound reduction for a dual tetrahedral complex

The lower bound is the proved Fogelsanger/MPW theorem from the recovered
library.  Its circuit-link and ridge-pairing hypotheses are explicit here;
the actual polytope adapter establishes them separately.
-/

noncomputable section
namespace Papers.SimpleFour

open Cubical.Simplicial
open scoped Classical

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

theorem ridgeDegreeTwo_mapFamily (e : V ↪ W) (s : Finset (Finset V))
    (hdeg : Cubical.Simplicial.RidgeDegreeTwo s) :
    Cubical.Simplicial.RidgeDegreeTwo (mapFamily e s) := by
  intro r
  by_cases hex : ∃ t ∈ s, r ∈ simplexBoundary (t.map e)
  · obtain ⟨t,ht,hrt⟩ := hex
    have hrsub := simplexBoundary_subset hrt
    have hrpow : r ∈ (t.map e).powersetCard r.card :=
      Finset.mem_powersetCard.mpr ⟨hrsub,rfl⟩
    rw [Finset.powersetCard_map] at hrpow
    obtain ⟨a,ha,heq⟩ := Finset.mem_map.mp hrpow
    change a.map e = r at heq
    subst r
    have hiff (b : Finset V) :
        a.map e ∈ simplexBoundary (b.map e) ↔ a ∈ simplexBoundary b := by
      simp only [mem_simplexBoundary_iff,Finset.map_subset_map,Finset.card_map]
    have heq : (mapFamily e s).filter (fun b => a.map e ∈ simplexBoundary b) =
        mapFamily e (s.filter (fun b => a ∈ simplexBoundary b)) := by
      ext b
      simp only [Finset.mem_filter,mem_mapFamily]
      constructor
      · rintro ⟨⟨c,hc,rfl⟩,ha⟩
        exact ⟨c,⟨hc,(hiff c).mp ha⟩,rfl⟩
      · rintro ⟨c,⟨hc,ha⟩,rfl⟩
        exact ⟨⟨c,hc,rfl⟩,(hiff c).mpr ha⟩
    rw [heq,card_mapFamily]
    exact hdeg a
  · left
    have hz : (mapFamily e s).filter (fun b => r ∈ simplexBoundary b) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro b hb
      obtain ⟨hbs,hrb⟩ := Finset.mem_filter.mp hb
      obtain ⟨t,ht,rfl⟩ := (mem_mapFamily e s b).mp hbs
      exact hex ⟨t,ht,hrb⟩
    simp only [hz,Finset.card_empty]

theorem tetrahedral_circuit_not_ten [Fintype V]
    (s : Finset (Finset V)) (hpure : Pure 4 id s)
    (hlinks : HasCircuitLinks 4 s) (hdeg : Cubical.Simplicial.RidgeDegreeTwo s)
    (hcover : vertices id s = Finset.univ) (hcard : s.card = 10) : False := by
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  have hbound := simplicial_facet_lower_bound (by decide : 3 ≤ 4) hne hpure hlinks hdeg
  rw [hcover,Finset.card_univ,hcard] at hbound
  have hV : Fintype.card V ≤ Fintype.card (Fin 6) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨e : V ↪ Fin 6⟩ := Function.Embedding.nonempty_of_card_le hV
  let t := mapFamily e s
  have ht : Pure 4 id t := hpure.mapFamily e
  have htc : t.card = 10 := (card_mapFamily e s).trans hcard
  have htd := ridgeDegreeTwo_mapFamily e s hdeg
  apply Papers.SimpleFourFiniteObstruction.no_ten_of_pure t
    (fun a ha => ht a ha) htc
  intro r hr
  have hrc : r.card = 3 := (Finset.mem_powersetCard.mp hr).2
  have heq : t.filter (fun a => r ⊆ a) =
      t.filter (fun a => r ∈ simplexBoundary a) := by
    ext a
    simp only [Finset.mem_filter,mem_simplexBoundary_iff]
    constructor
    · rintro ⟨ha,hra⟩
      exact ⟨ha,hra,by have h := ht a ha; change a.card = 4 at h; omega⟩
    · rintro ⟨ha,hra,_⟩
      exact ⟨ha,hra⟩
  rw [heq]
  exact htd r

end Papers.SimpleFour

end
end
end BundlePart1
