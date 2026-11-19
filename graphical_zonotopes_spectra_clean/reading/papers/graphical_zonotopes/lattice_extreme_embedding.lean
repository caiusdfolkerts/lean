module

public import Papers.GraphicalZonotopes.SetFunctionEmbeddingGeometry
public import Papers.GraphicalZonotopes.Dilation
public import Papers.GraphicalZonotopes.GraphDefinitions
public import Papers.GraphicalZonotopes.WeakSummandReduction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- An actual integral extreme graphical set function with exact dimension
and a uniform integral elemental-slack bound. -/
def LatticeExtremeAt (G : SimpleGraph V) (d M : ℕ) : Prop :=
  ∃ f : SetFunction V,TranslationNormalized f ∧ IntegerValued f ∧
    ExtremeSupermodular f ∧ Graphical G f ∧
    Module.finrank ℝ (vectorSpan ℝ (basePolytope f))=d ∧
    ∀ u v,u≠v → ∀ S,u∉S → v∉S → delta f u v S≤(M : ℝ)

theorem LatticeExtremeAt.of_lattice_complement {G : SimpleGraph V} {f : SetFunction V}
    (hn : TranslationNormalized f) (hi : IntegerValued f) (he : ExtremeSupermodular f)
    (hG : Graphical G f) {d M : ℕ} (hd : Module.finrank ℝ (vectorSpan ℝ (basePolytope f))=d)
    {R : Set (V → ℝ)} (hR : LatticePolytope R) (hRn : R.Nonempty)
    (hsum : basePolytope f+R=(M : ℝ) • graphicalZonotope G) : LatticeExtremeAt G d M := by
  have hsummand : IsMinkowskiSummand (basePolytope f) ((M : ℝ) • graphicalZonotope G) :=
    ⟨R,hR.compact,hR.convex,hRn,hsum⟩
  have hb := ((isMinkowskiSummand_graphical_iff hn.1 he.2.1 (Nat.cast_nonneg M)).mp hsummand).2
  refine ⟨f,hn,hi,he,hG,hd,?_⟩
  intro u v huv S hu hv
  by_cases hedge : G.Adj u v
  · exact hb u v huv hedge S hu hv
  · rw [hG u v huv hedge S hu hv]
    exact Nat.cast_nonneg M

theorem LatticeExtremeAt.mono_dilation {G : SimpleGraph V} {d M N : ℕ}
    (h : LatticeExtremeAt G d M) (hMN : M≤N) : LatticeExtremeAt G d N := by
  obtain ⟨f,hn,hi,he,hG,hd,hb⟩ := h
  exact ⟨f,hn,hi,he,hG,hd,fun u v huv S hu hv =>
    (hb u v huv S hu hv).trans (by exact_mod_cast hMN)⟩

theorem LatticeExtremeAt.embed {G : SimpleGraph V} {H : SimpleGraph W}
    {d M : ℕ} (h : LatticeExtremeAt G d M) (e : V ↪ W) (hGH : G≤H.comap e) :
    LatticeExtremeAt H d M := by
  obtain ⟨f,hn,hi,he,hG,hd,hb⟩ := h
  let g := SetFunctionEmbedding.extend e f
  refine ⟨g,SetFunctionEmbedding.extend_translationNormalized e hn,
    SetFunctionEmbedding.extend_integer e hi,SetFunctionEmbedding.extend_extreme e he,
    SetFunctionEmbedding.extend_graphical e (hG.mono_graph hGH),?_,?_⟩
  · rw [SetFunctionEmbedding.finrank_vectorSpan_extend e hn]
    exact hd
  · intro u v huv S hu hv
    by_cases huR : u∈Set.range e
    · obtain ⟨a,rfl⟩ := huR
      by_cases hvR : v∈Set.range e
      · obtain ⟨b,rfl⟩ := hvR
        rw [SetFunctionEmbedding.delta_extend]
        exact hb a b (fun h => huv (congrArg e h)) _
          (by simpa using hu) (by simpa using hv)
      · rw [delta_comm,SetFunctionEmbedding.delta_extend_not_range e f v (e a) hvR]
        exact Nat.cast_nonneg M
    · rw [SetFunctionEmbedding.delta_extend_not_range e f u v huR]
      exact Nat.cast_nonneg M

theorem LatticeExtremeAt.polytope {G : SimpleGraph V} {d M : ℕ}
    (h : LatticeExtremeAt G d M) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=d ∧
      IsMinkowskiSummand Q ((M : ℝ) • graphicalZonotope G) := by
  obtain ⟨f,hn,hi,he,hG,hd,hb⟩ := h
  exact ⟨basePolytope f,hi.basePolytope hn.1 he.2.1,he.minkowskiIndecomposable,hd,
    (isMinkowskiSummand_graphical_iff hn.1 he.2.1 (Nat.cast_nonneg M)).mpr
      ⟨hG,fun u v huv _ S hu hv => hb u v huv S hu hv⟩⟩

theorem LatticeExtremeAt.dimension_le_maximum {G : SimpleGraph V} {d M : ℕ}
    (h : LatticeExtremeAt G d M) : d≤maximumIndecomposableDimension G := by
  obtain ⟨f,hn,hi,he,hG,hd,hb⟩ := h
  rw [← hd]
  exact GraphicalZonotopes.dimension_le_maximum (show IsGeneralizedPermutahedron (basePolytope f) from ⟨f,hn.1,he.2.1,rfl⟩).finitePolytope
    he.minkowskiIndecomposable ((isWeakMinkowskiSummand_graphical_iff hn.1 he.2.1).mpr hG)

theorem LatticeExtremeAt.supports_full {G : SimpleGraph V} {M : ℕ}
    (h : LatticeExtremeAt G (Fintype.card V-1) M) : SupportsFullIndecomposable G := by
  obtain ⟨f,hn,hi,he,hG,hd,hb⟩ := h
  exact ⟨basePolytope f,(show IsGeneralizedPermutahedron (basePolytope f) from ⟨f,hn.1,he.2.1,rfl⟩).finitePolytope,
    he.minkowskiIndecomposable,hd,(isWeakMinkowskiSummand_graphical_iff hn.1 he.2.1).mpr hG⟩

end GraphicalZonotopes
