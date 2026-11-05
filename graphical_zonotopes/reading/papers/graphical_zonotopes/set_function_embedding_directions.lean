module

public import Papers.GraphicalZonotopes.SetFunctionEmbeddingGeometry
public import Papers.GraphicalZonotopes.RefinedSupport

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace GraphicalZonotopes
open Finset

private def missingPairGraph {V : Type*} (u v : V) : SimpleGraph V where
  Adj a b := a≠b ∧ (a≠u ∨ b≠v) ∧ (a≠v ∨ b≠u)
  symm := ⟨by intro a b h; tauto⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Actual exposed root edges are precisely the nonzero elemental rows,
with existence of a genuine conditioning context in both directions. -/
theorem actualRootEdge_iff_nonzero_delta {V : Type*} [Fintype V] [LinearOrder V]
    {f : SetFunction V} (hn : Normalized f) (hs : Supermodular f) (u v : V) :
    ActualRootEdge (basePolytope f) u v ↔ u≠v ∧
      ∃ S : Finset V,u∉S ∧ v∉S ∧ delta f u v S≠0 := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    by_contra hnone
    push_neg at hnone
    have hg : Graphical (missingPairGraph u v) f := by
      intro a b hab hnon S ha hb
      have hp : (a=u ∧ b=v) ∨ (a=v ∧ b=u) := by
        change ¬(a≠b ∧ (a≠u ∨ b≠v) ∧ (a≠v ∨ b≠u)) at hnon
        tauto
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hnone S ha hb
      · rw [delta_comm]
        exact hnone S hb ha
    have hh := RefinedTriangleComponents.actualRootEdge_of_graphical hn hs hg h
    exact hh.2.1.elim (fun hn => hn rfl) (fun hn => hn rfl)
  · rintro ⟨huv,S,hu,hv,hd⟩
    exact exposedSegment_of_positive_delta hn hs huv hu hv
      (lt_of_le_of_ne (hs.elemental u v huv S hu hv) (Ne.symm hd))

namespace SetFunctionEmbedding
variable {V W : Type*} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]

theorem reconstruct_of_graphical_supported (e : W ↪ V) {G : SimpleGraph V}
    {f : SetFunction V} (hn : TranslationNormalized f) (hG : Graphical G f)
    (hS : ∀ u v,G.Adj u v → u∈Set.range e) : extend e (restrict e f)=f := by
  apply reconstruct_of_insert_absent e f
  intro u hu
  apply insert_absent_of_zero_deltas hn u
  intro v huv S huS hvS
  exact hG u v huv (fun hadj => hu (hS u v hadj)) S huS hvS

theorem extreme_restrict_of_reconstruction (e : W ↪ V) {f : SetFunction V}
    (hf : ExtremeSupermodular f) (hrec : extend e (restrict e f)=f) :
    ExtremeSupermodular (restrict e f) := by
  refine ⟨restrict_translationNormalized e hf.1,restrict_supermodular e hf.2.1,?_,?_⟩
  · intro he
    apply hf.2.2.1
    rw [← hrec,he]
    funext S
    rfl
  · intro g h hgn hhn hgs hhs he
    have hsum : extend e g+extend e h=f := by
      rw [← hrec,← he]
      rfl
    obtain ⟨a,ha,hscale⟩ := hf.2.2.2 (extend e g) (extend e h)
      (extend_translationNormalized e hgn) (extend_translationNormalized e hhn)
      (extend_supermodular e hgs) (extend_supermodular e hhs) hsum
    refine ⟨a,ha,?_⟩
    have hh := congrArg (restrict e) hscale
    simpa only [restrict_extend,restrict_smul] using hh

/-- The complete actual direction graph is transported by the embedding;
new coordinates have no edges, and every retained edge stays exposed. -/
theorem actualDirectionGraph_extend (e : W ↪ V) {f : SetFunction W}
    (hn : TranslationNormalized f) (hs : Supermodular f) :
    actualDirectionGraph (basePolytope (extend e f))=
      (actualDirectionGraph (basePolytope f)).map e := by
  ext u v
  rw [SimpleGraph.map_adj]
  constructor
  · intro huv
    obtain ⟨hne,S,hu,hv,hd⟩ := (actualRootEdge_iff_nonzero_delta
      (extend_translationNormalized e hn).1 (extend_supermodular e hs) u v).mp huv
    have huR : u∈Set.range e := by
      by_contra h
      exact hd (delta_extend_not_range e f u v h S)
    have hvR : v∈Set.range e := by
      by_contra h
      rw [delta_comm] at hd
      exact hd (delta_extend_not_range e f v u h S)
    obtain ⟨a,rfl⟩ := huR
    obtain ⟨b,rfl⟩ := hvR
    refine ⟨a,b,?_,rfl,rfl⟩
    apply (actualRootEdge_iff_nonzero_delta hn.1 hs a b).mpr
    refine ⟨fun he => hne (congrArg e he),pullSet e S,by simpa using hu,by simpa using hv,?_⟩
    simpa only [delta_extend] using hd
  · rintro ⟨a,b,hab,rfl,rfl⟩
    obtain ⟨hne,S,ha,hb,hd⟩ := (actualRootEdge_iff_nonzero_delta hn.1 hs a b).mp hab
    apply (actualRootEdge_iff_nonzero_delta (extend_translationNormalized e hn).1
      (extend_supermodular e hs) (e a) (e b)).mpr
    refine ⟨fun he => hne (e.injective he),S.map e,by simpa using ha,by simpa using hb,?_⟩
    simpa only [delta_extend,pullSet_map] using hd

theorem actualDirectionGraph_restrict (e : W ↪ V) {f : SetFunction V}
    (hn : TranslationNormalized f) (hs : Supermodular f)
    (hrec : extend e (restrict e f)=f) :
    actualDirectionGraph (basePolytope (restrict e f))=
      (actualDirectionGraph (basePolytope f)).comap e := by
  have he := actualDirectionGraph_extend e (restrict_translationNormalized e hn)
    (restrict_supermodular e hs)
  rw [hrec] at he
  have hh := congrArg (fun G : SimpleGraph V => G.comap e) he
  simpa only [SimpleGraph.comap_map_eq] using hh.symm

theorem edgeFamily_map (e : W ↪ V) (G : SimpleGraph W) :
    edgeFamily (G.map e)=(edgeFamily G).image (fun C => C.map e) := by
  ext D
  constructor
  · intro hD
    obtain ⟨hd,hcl⟩ := (mem_edgeFamily _ _).mp hD
    obtain ⟨C,hC,rfl⟩ := (SimpleGraph.isClique_map_finset_iff_of_nontrivial
      (G := G) (f := e) (show D.Nontrivial from one_lt_card_iff_nontrivial.mp (by omega))).mp hcl
    refine mem_image.mpr ⟨C,(mem_edgeFamily G C).mpr ⟨?_,hC⟩,rfl⟩
    simpa only [card_map] using hd
  · intro hD
    obtain ⟨C,hC,rfl⟩ := mem_image.mp hD
    obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ _).mp hC
    exact (mem_edgeFamily _ _).mpr ⟨by simpa only [card_map] using hc,
      (show G.IsClique C from hcl).finsetMap⟩

/-- The number of genuine root directions is preserved under every
injective coordinate embedding, including arbitrary coordinate relabelings. -/
theorem directionCount_extend (e : W ↪ V) {f : SetFunction W}
    (hn : TranslationNormalized f) (hs : Supermodular f) :
    directionCount (basePolytope (extend e f))=directionCount (basePolytope f) := by
  unfold directionCount
  rw [actualDirectionGraph_extend e hn hs,edgeFamily_map,
    card_image_of_injective _ (Finset.map_injective e)]

end SetFunctionEmbedding
end GraphicalZonotopes
