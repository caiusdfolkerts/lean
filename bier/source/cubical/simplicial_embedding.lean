import cubical.simplicial_faces
import cubical.simplicial_reindex

/-! # Injective changes of the ambient vertex type -/

namespace Cubical.Simplicial

open scoped BigOperators

variable {V W I : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq I]

noncomputable def mapChain (e : V ↪ W) : Chain V →ₗ[ZMod 2] Chain W :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (Finset.map e)

@[simp]
theorem mapChain_single (e : V ↪ W) (s : Finset V) (a : ZMod 2) :
    mapChain e (Finsupp.single s a) = Finsupp.single (s.map e) a := by
  simp [mapChain]

theorem mapChain_injective (e : V ↪ W) : Function.Injective (mapChain e) :=
  Finsupp.mapDomain_injective (Finset.map_injective e)

theorem mapChain_boundary_single (e : V ↪ W) (s : Finset V) (a : ZMod 2) :
    mapChain e (boundary (Finsupp.single s a)) =
      boundary (Finsupp.single (s.map e) a) := by
  simp only [boundary_single, map_sum, mapChain_single, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.map_erase]

theorem mapChain_boundary (e : V ↪ W) (c : Chain V) :
    mapChain e (boundary c) = boundary (mapChain e c) := by
  have heq : (mapChain e).comp boundary = boundary.comp (mapChain e) := by
    apply Finsupp.lhom_ext
    intro t a
    simpa only [LinearMap.comp_apply, mapChain_single] using mapChain_boundary_single e t a
  exact LinearMap.congr_fun heq c

theorem IsFacetCircuit.mapVertices {σ : I → Finset V} {s : Finset I}
    (h : IsFacetCircuit σ s) (e : V ↪ W) :
    IsFacetCircuit (fun i => (σ i).map e) s := by
  refine ⟨h.nonempty, ?_, ?_⟩
  · simp_rw [← mapChain_boundary_single]
    rw [← map_sum, h.sum_eq_zero, map_zero]
  · intro t hts htne htz
    apply h.minimal t hts htne
    apply mapChain_injective e
    simp only [map_sum, map_zero, mapChain_boundary_single]
    exact htz

def mapFamily (e : V ↪ W) (s : Finset (Finset V)) : Finset (Finset W) :=
  s.image (Finset.map e)

@[simp]
theorem mem_mapFamily (e : V ↪ W) (s : Finset (Finset V)) (t : Finset W) :
    t ∈ mapFamily e s ↔ ∃ a ∈ s, a.map e = t := Finset.mem_image

theorem IsFacetCircuit.mapFamily {s : Finset (Finset V)}
    (h : IsFacetCircuit id s) (e : V ↪ W) : IsFacetCircuit id (mapFamily e s) := by
  exact (h.mapVertices e).image (Finset.map_injective e).injOn

theorem Pure.mapFamily {n : ℕ} {s : Finset (Finset V)}
    (h : Pure n id s) (e : V ↪ W) : Pure n id (mapFamily e s) := by
  intro t ht
  obtain ⟨a, ha, rfl⟩ := (mem_mapFamily e s t).mp ht
  simpa using h a ha

@[simp]
theorem card_mapFamily (e : V ↪ W) (s : Finset (Finset V)) :
    (mapFamily e s).card = s.card :=
  Finset.card_image_of_injective _ (Finset.map_injective e)

theorem vertices_mapFamily (e : V ↪ W) (s : Finset (Finset V)) :
    vertices id (mapFamily e s) = (vertices id s).map e := by
  ext w
  simp only [mem_vertices, mem_mapFamily, Finset.mem_map, id_eq]
  aesop

theorem faces_mapFamily (e : V ↪ W) (s : Finset (Finset V)) (r : ℕ) :
    faces (mapFamily e s) r = mapFamily e (faces s r) := by
  simp only [faces, mapFamily, Finset.image_biUnion, Finset.biUnion_image,
    Finset.powersetCard_map]
  simp only [Finset.map_eq_image]
  rfl

@[simp]
theorem faces_mapFamily_card (e : V ↪ W) (s : Finset (Finset V)) (r : ℕ) :
    (faces (mapFamily e s) r).card = (faces s r).card := by
  rw [faces_mapFamily, card_mapFamily]

theorem link_mapFamily (e : V ↪ W) (s : Finset (Finset V)) (a : Finset V) :
    link (mapFamily e s) (a.map e) = mapFamily e (link s a) := by
  simp only [link, mapFamily, Finset.filter_image, Finset.map_subset_map,
    Finset.image_image, Function.comp_def, Finset.map_sdiff]

theorem HasCircuitLinks.mapFamily {n : ℕ} {s : Finset (Finset V)}
    (h : HasCircuitLinks n s) (e : V ↪ W) : HasCircuitLinks n (mapFamily e s) := by
  intro a ha hcard
  obtain ⟨t, ht, hat⟩ := ha
  obtain ⟨t', ht', rfl⟩ := (mem_mapFamily e s t).mp ht
  have hap : a ∈ (t'.map e).powersetCard a.card := Finset.mem_powersetCard.mpr ⟨hat, rfl⟩
  rw [Finset.powersetCard_map] at hap
  obtain ⟨a', ha', heq⟩ := Finset.mem_map.mp hap
  change a'.map e = a at heq
  subst a
  rw [link_mapFamily]
  apply IsFacetCircuit.mapFamily
  apply h a' ⟨t', ht', (Finset.mem_powersetCard.mp ha').1⟩
  simpa using hcard

/-- A recursive criterion for the all-links condition. This lets a geometric
development use its actual vertex figures repeatedly. -/
theorem HasCircuitLinks.of_vertex_links {n : ℕ} {s : Finset (Finset V)}
    (hs : IsFacetCircuit id s)
    (hvertex : ∀ v ∈ vertices id s, HasCircuitLinks (n - 1) (link s {v})) :
    HasCircuitLinks n s := by
  intro a ha hcard
  by_cases haempty : a = ∅
  · simpa [haempty] using hs
  obtain ⟨v, hva⟩ := Finset.nonempty_iff_ne_empty.mpr haempty
  obtain ⟨t, ht, hat⟩ := ha
  have hvt : v ∈ t := hat hva
  have hvs : v ∈ vertices id s := (mem_vertices id s v).mpr ⟨t, ht, hvt⟩
  have hface : ∃ f ∈ link s {v}, a.erase v ⊆ f := by
    refine ⟨t.erase v, (mem_link s {v} (t.erase v)).mpr ⟨by simp, ?_⟩, ?_⟩
    · simpa only [Finset.singleton_union, Finset.insert_erase hvt] using ht
    · exact Finset.erase_subset_erase v hat
  have hdim : (a.erase v).card + 3 ≤ n - 1 := by
    have hc := Finset.card_erase_add_one hva
    omega
  have h := hvertex v hvs (a.erase v) hface hdim
  rw [link_link s (by simp : Disjoint ({v} : Finset V) (a.erase v))] at h
  simpa only [Finset.singleton_union, Finset.insert_erase hva] using h

end Cubical.Simplicial
