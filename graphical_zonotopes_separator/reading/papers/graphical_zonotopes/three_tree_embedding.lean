module

public import Papers.GraphicalZonotopes.ThreeTreeIncidence
public import Papers.GraphicalZonotopes.SetFunctionEmbedding
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace GraphicalZonotopes
open Finset
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem map_cliqueGraph (e : V ↪ W) (C : Finset V) :
    (cliqueGraph C).map e=cliqueGraph (C.map e) := by
  ext u v
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨a,b,⟨hab,ha,hb⟩,rfl,rfl⟩
    exact ⟨fun he => hab (e.injective he),mem_map.mpr ⟨a,ha,rfl⟩,mem_map.mpr ⟨b,hb,rfl⟩⟩
  · rintro ⟨huv,hu,hv⟩
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hv
    exact ⟨a,b,⟨fun he => huv (congrArg e he),ha,hb⟩,rfl,rfl⟩

theorem map_attachmentStar (e : V ↪ W) (u : V) (T : Finset V) :
    (attachmentStar u T).map e=attachmentStar (e u) (T.map e) := by
  ext a b
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨v,w,⟨hvw,hstar⟩,rfl,rfl⟩
    refine ⟨fun he => hvw (e.injective he),?_⟩
    rcases hstar with ⟨rfl,hw⟩ | ⟨rfl,hv⟩
    · exact Or.inl ⟨rfl,mem_map.mpr ⟨w,hw,rfl⟩⟩
    · exact Or.inr ⟨rfl,mem_map.mpr ⟨v,hv,rfl⟩⟩
  · rintro ⟨hab,hstar⟩
    rcases hstar with ⟨rfl,hb⟩ | ⟨rfl,ha⟩
    · obtain ⟨w,hw,rfl⟩ := mem_map.mp hb
      exact ⟨u,w,⟨fun he => hab (congrArg e he),Or.inl ⟨rfl,hw⟩⟩,rfl,rfl⟩
    · obtain ⟨v,hv,rfl⟩ := mem_map.mp ha
      exact ⟨v,u,⟨fun he => hab (congrArg e he),Or.inr ⟨rfl,hv⟩⟩,rfl,rfl⟩

theorem map_sup_embedding (e : V ↪ W) (G H : SimpleGraph V) :
    (G⊔H).map e=G.map e⊔H.map e := by
  ext u v
  simp only [SimpleGraph.map_adj,SimpleGraph.sup_adj]
  aesop

theorem ThreeTreeOn.map {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (e : V ↪ W) : ThreeTreeOn (S.map e) (G.map e) := by
  induction h with
  | tetrahedron C hC =>
    rw [map_cliqueGraph]
    exact ThreeTreeOn.tetrahedron _ (by simpa only [card_map] using hC)
  | @attach S G h u hu T hT hTS hcl ih =>
    rw [map_insert,map_sup_embedding,map_attachmentStar]
    exact ThreeTreeOn.attach ih (e u) (by simpa using hu) (T.map e)
      (by simpa only [card_map] using hT) (map_subset_map.mpr hTS) hcl.finsetMap

namespace SetFunctionEmbedding

theorem map_pullSet_of_subset (e : V ↪ W) (S : Finset W)
    (hS : ∀ v∈S,v∈Set.range e) : (pullSet e S).map e=S := by
  ext v
  constructor
  · rintro hv
    obtain ⟨w,hw,rfl⟩ := mem_map.mp hv
    exact (mem_pullSet e S w).mp hw
  · intro hv
    obtain ⟨w,rfl⟩ := hS v hv
    exact mem_map.mpr ⟨w,(mem_pullSet e S w).mpr hv,rfl⟩

theorem card_pullSet_of_subset (e : V ↪ W) (S : Finset W)
    (hS : ∀ v∈S,v∈Set.range e) : (pullSet e S).card=S.card := by
  rw [← card_map e, map_pullSet_of_subset e S hS]

end SetFunctionEmbedding

theorem comap_cliqueGraph (e : V ↪ W) (C : Finset W) :
    (cliqueGraph C).comap e=cliqueGraph (SetFunctionEmbedding.pullSet e C) := by
  ext u v
  change (e u≠e v ∧ e u∈C ∧ e v∈C) ↔
    (u≠v ∧ u∈SetFunctionEmbedding.pullSet e C ∧ v∈SetFunctionEmbedding.pullSet e C)
  simp [e.injective.eq_iff]

theorem comap_attachmentStar (e : V ↪ W) (u : V) (T : Finset W) :
    (attachmentStar (e u) T).comap e=
      attachmentStar u (SetFunctionEmbedding.pullSet e T) := by
  ext a b
  change (e a≠e b ∧ ((e a=e u ∧ e b∈T) ∨ (e b=e u ∧ e a∈T))) ↔ _
  simp [attachmentStar,SetFunctionEmbedding.mem_pullSet,e.injective.eq_iff]

theorem ThreeTreeOn.comap {S : Finset W} {G : SimpleGraph W}
    (h : ThreeTreeOn S G) (e : V ↪ W) (hS : ∀ v∈S,v∈Set.range e) :
    ThreeTreeOn (SetFunctionEmbedding.pullSet e S) (G.comap e) := by
  induction h with
  | tetrahedron C hC =>
    rw [comap_cliqueGraph]
    exact ThreeTreeOn.tetrahedron _
      ((SetFunctionEmbedding.card_pullSet_of_subset e C hS).trans hC)
  | @attach S G h u hu T hT hTS hcl ih =>
    have hS' : ∀ v∈S,v∈Set.range e := fun v hv => hS v (mem_insert_of_mem hv)
    have hT' : ∀ v∈T,v∈Set.range e := fun v hv => hS' v (hTS hv)
    obtain ⟨w,hw⟩ := hS u (mem_insert_self _ _)
    subst u
    rw [SetFunctionEmbedding.pullSet_insert_image]
    have hsup : (G⊔attachmentStar (e w) T).comap e=
        G.comap e⊔(attachmentStar (e w) T).comap e := rfl
    rw [hsup,comap_attachmentStar]
    apply ThreeTreeOn.attach (ih hS') w (by simpa using hu)
      (SetFunctionEmbedding.pullSet e T)
      ((SetFunctionEmbedding.card_pullSet_of_subset e T hT').trans hT)
    · intro v hv
      exact (SetFunctionEmbedding.mem_pullSet e S v).mpr
        (hTS ((SetFunctionEmbedding.mem_pullSet e T v).mp hv))
    · intro a ha b hb hab
      exact hcl ((SetFunctionEmbedding.mem_pullSet e T a).mp ha)
        ((SetFunctionEmbedding.mem_pullSet e T b).mp hb) (fun he => hab (e.injective he))

theorem ThreeTreeOn.induce {S : Finset V} {G : SimpleGraph V}
    [DecidableEq S] (h : ThreeTreeOn S G) : IsThreeTree (G.induce (S : Set V)) := by
  let e : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have hh := h.comap e (fun v hv => ⟨⟨v,hv⟩,rfl⟩)
  have hset : SetFunctionEmbedding.pullSet e S=univ := by
    ext v
    simp [SetFunctionEmbedding.mem_pullSet,e,v.property]
  rw [hset] at hh
  exact hh

theorem ThreeTreeOn.reachable_active {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : ∀ u∈S,∀ v∈S,G.Reachable u v := by
  induction h with
  | tetrahedron C hC =>
    intro u hu v hv
    by_cases huv : u=v
    · subst v; exact SimpleGraph.Reachable.rfl
    · exact SimpleGraph.Adj.reachable ⟨huv,hu,hv⟩
  | @attach S G h w hw T hT hTS hcl ih =>
    obtain ⟨a,ha⟩ := card_pos.mp (show 0<T.card by omega)
    have hwa : (G⊔attachmentStar w T).Reachable w a :=
      SimpleGraph.Adj.reachable ((attached_vertex_adj_iff h hw hTS a).mpr ha)
    intro u hu v hv
    rcases mem_insert.mp hu with hue | huS
    · subst u
      rcases mem_insert.mp hv with hve | hvS
      · subst v; exact SimpleGraph.Reachable.rfl
      · exact hwa.trans ((ih a (hTS ha) v hvS).mono le_sup_left)
    · rcases mem_insert.mp hv with hve | hvS
      · subst v
        exact ((ih u huS a (hTS ha)).mono le_sup_left).trans hwa.symm
      · exact (ih u huS v hvS).mono le_sup_left

theorem IsThreeTree.connected {G : SimpleGraph V} (h : IsThreeTree G) : G.Connected := by
  obtain ⟨v,hv⟩ := card_pos.mp (show 0<(univ : Finset V).card from lt_of_lt_of_le (by norm_num) h.active_card_ge_four)
  letI : Nonempty V := ⟨v⟩
  exact ⟨fun u v => h.reachable_active u (mem_univ _) v (mem_univ _)⟩

@[simp] theorem mem_tetrahedra_iff (G : SimpleGraph V) (C : Finset V) :
    C∈tetrahedra G ↔ C.card=4 ∧ G.IsClique C := by
  classical
  simp only [tetrahedra,mem_filter,mem_univ,true_and]

theorem tetrahedra_map (e : V ↪ W) (G : SimpleGraph V) :
    tetrahedra (G.map e)=(tetrahedra G).image (fun C => C.map e) := by
  classical
  ext D
  constructor
  · intro hD
    obtain ⟨hd,hcl⟩ := (mem_tetrahedra_iff (G.map e) D).mp hD
    obtain ⟨C,hC,rfl⟩ := (SimpleGraph.isClique_map_finset_iff_of_nontrivial
      (G := G) (f := e) (show D.Nontrivial from one_lt_card_iff_nontrivial.mp (by omega))).mp hcl
    refine mem_image.mpr ⟨C,(mem_tetrahedra_iff G C).mpr ⟨?_,hC⟩,rfl⟩
    simpa only [card_map] using hd
  · intro hD
    obtain ⟨C,hC,rfl⟩ := mem_image.mp hD
    obtain ⟨hc,hcl⟩ := (mem_tetrahedra_iff G C).mp hC
    exact (mem_tetrahedra_iff (G.map e) (C.map e)).mpr
      ⟨by simpa only [card_map] using hc,hcl.finsetMap⟩

theorem triangleMultiplicity_map (e : V ↪ W) (G : SimpleGraph V) (T : Finset V) :
    triangleMultiplicity (G.map e) (T.map e)=triangleMultiplicity G T := by
  have he : (tetrahedra (G.map e)).filter (fun C => T.map e⊆C)=
      ((tetrahedra G).filter (fun C => T⊆C)).image (fun C => C.map e) := by
    rw [tetrahedra_map]
    ext D
    simp only [mem_filter,mem_image]
    constructor
    · rintro ⟨⟨C,hC,rfl⟩,hTC⟩
      exact ⟨C,⟨hC,map_subset_map.mp hTC⟩,rfl⟩
    · rintro ⟨C,⟨hC,hTC⟩,rfl⟩
      exact ⟨⟨C,hC,rfl⟩,map_subset_map.mpr hTC⟩
  unfold triangleMultiplicity
  rw [he,card_image_of_injective _ (Finset.map_injective e)]

theorem Admissible.map {G : SimpleGraph V} (h : Admissible G) (e : V ↪ W) :
    Admissible (G.map e) := by
  intro T hT hcl
  obtain ⟨S,hS,rfl⟩ := (SimpleGraph.isClique_map_finset_iff_of_nontrivial
    (G := G) (f := e) (show T.Nontrivial from one_lt_card_iff_nontrivial.mp (by omega))).mp hcl
  rw [triangleMultiplicity_map]
  exact h S (by simpa only [card_map] using hT) hS

theorem Admissible.of_map {G : SimpleGraph V} (e : V ↪ W)
    (h : Admissible (G.map e)) : Admissible G := by
  intro T hT hcl
  have hh := h (T.map e) (by simpa only [card_map] using hT) hcl.finsetMap
  rwa [triangleMultiplicity_map] at hh

theorem IsThreeTree.map_equiv {G : SimpleGraph V} (h : IsThreeTree G) (e : V ≃ W) :
    IsThreeTree (G.map e.toEmbedding) := by
  have hh := h.map e.toEmbedding
  change ThreeTreeOn univ _
  simpa only [Finset.map_univ_equiv] using hh

theorem HasAdmissibleSpanningThreeTree.map_equiv {G : SimpleGraph V}
    (h : HasAdmissibleSpanningThreeTree G) (e : V ≃ W) :
    HasAdmissibleSpanningThreeTree (G.map e.toEmbedding) := by
  obtain ⟨H,hHG,hT,hA⟩ := h
  exact ⟨H.map e.toEmbedding,SimpleGraph.map_monotone e hHG,
    hT.map_equiv e,hA.map e.toEmbedding⟩

theorem ThreeTreeOn.exists_edge {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : ∃ u v,G.Adj u v := by
  obtain ⟨C,hC⟩ := h.tetrahedra_nonempty
  obtain ⟨hc,hcl⟩ := (mem_filter.mp hC).2
  obtain ⟨u,hu⟩ := card_pos.mp (show 0<C.card by omega)
  obtain ⟨v,hv,hvu⟩ := exists_mem_ne (show 1<C.card by omega) u
  exact ⟨u,v,hcl hu hv (Ne.symm hvu)⟩

theorem map_comap_of_supported (e : V ↪ W) (G : SimpleGraph W)
    (hs : ∀ u v,G.Adj u v → u∈Set.range e) : (G.comap e).map e=G := by
  ext u v
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨a,b,hab,rfl,rfl⟩
    exact hab
  · intro huv
    obtain ⟨a,rfl⟩ := hs u v huv
    obtain ⟨b,rfl⟩ := hs v (e a) (G.adj_symm huv)
    exact ⟨a,b,huv,rfl,rfl⟩

end GraphicalZonotopes
