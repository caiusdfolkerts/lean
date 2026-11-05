import cubical.pl.facet_topology

/-! # Ridge-connected facets of a cubical PL sphere

The top-dimensional simplices of the face-chain triangulation are
connected across ridges. Projecting each such chain to its largest
cell gives the required cubical facet connectivity.
-/

noncomputable section

namespace Cubical.PL.CubeComplex

open Set Classical
open DifferentialGeometry.Topology.PiecewiseLinear

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] (K : CubeComplex V)

abbrev TopChain (m : ℕ) :=
  {C : Finset K.Cell // C ∈ K.orderComplex.faces ∧ C.card = m + 1}

def topChainEquiv (m : ℕ) : K.TopChain m ≃ TopFacet K.realization m :=
  Equiv.ofBijective
    (fun C => ⟨C.val.image standardVertex,
      (image_mem_standardRealization_iff K.orderComplex C.val).mpr C.property.1,
      by rw [Finset.card_image_of_injective _ standardVertex_injective, C.property.2]⟩)
    ⟨by
      intro C D h
      exact Subtype.ext (Finset.image_injective standardVertex_injective
        (congrArg Subtype.val h)),
    by
      intro t
      obtain ⟨C, hC, heq⟩ := t.property.1
      have hc : C.card = m + 1 := by
        have hh := t.property.2
        rw [← heq] at hh
        change (C.image standardVertex).card = m + 1 at hh
        rw [Finset.card_image_of_injective _ standardVertex_injective] at hh
        exact hh
      exact ⟨⟨C, hC, hc⟩, Subtype.ext heq⟩⟩

def topChainGraph (m : ℕ) : SimpleGraph (K.TopChain m) where
  Adj C D := C ≠ D ∧ ∃ R ∈ K.orderComplex.faces,
    R.card = m ∧ R ⊆ C.val ∧ R ⊆ D.val
  symm := ⟨by
    rintro C D ⟨hne, R, hR, hc, hRC, hRD⟩
    exact ⟨hne.symm, R, hR, hc, hRD, hRC⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def topChainGraphIso (m : ℕ) : K.topChainGraph m ≃g dualGraph m K.realization where
  __ := K.topChainEquiv m
  map_rel_iff' := by
    intro C D
    constructor
    · rintro ⟨hne, r, hr, hc, hrC, hrD⟩
      obtain ⟨R, hR, rfl⟩ := hr
      refine ⟨fun h => hne (congrArg (K.topChainEquiv m) h), R, hR, ?_, ?_, ?_⟩
      · change (R.image standardVertex).card = m at hc
        rwa [Finset.card_image_of_injective _ standardVertex_injective] at hc
      · exact (Finset.image_subset_image_iff standardVertex_injective).mp hrC
      · exact (Finset.image_subset_image_iff standardVertex_injective).mp hrD
    · rintro ⟨hne, R, hR, hc, hRC, hRD⟩
      refine ⟨fun h => hne ((K.topChainEquiv m).injective h),
        R.image standardVertex,
        (image_mem_standardRealization_iff K.orderComplex R).mpr hR, ?_, ?_, ?_⟩
      · rw [Finset.card_image_of_injective _ standardVertex_injective, hc]
      · exact Finset.image_subset_image hRC
      · exact Finset.image_subset_image hRD

theorem topChainGraph_preconnected {m : ℕ} (hK : K.IsSphere m) (hm : 1 ≤ m) :
    (K.topChainGraph m).Preconnected := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  apply (K.topChainGraphIso (j + 1)).preconnected_iff.mpr
  exact hK.isCombinatorialManifold.isCombinatorialManifoldWithBoundary.dualGraph_preconnected
    hK.isConnected.isPreconnected

def chainFacet {m : ℕ} (hK : K.IsSphere m) (C : K.TopChain m) : K.Facet m :=
  ⟨(K.top_chain_has_dimension hK C.property.1 C.property.2 m le_rfl).choose,
    (K.top_chain_has_dimension hK C.property.1 C.property.2 m le_rfl).choose_spec.2⟩

theorem chainFacet_mem {m : ℕ} (hK : K.IsSphere m) (C : K.TopChain m) :
    (K.chainFacet hK C).val ∈ C.val :=
  (K.top_chain_has_dimension hK C.property.1 C.property.2 m le_rfl).choose_spec.1

theorem chainFacet_ge {m : ℕ} (hK : K.IsSphere m) (C : K.TopChain m)
    (F : K.Cell) (hF : F ∈ C.val) : F ≤ (K.chainFacet hK C).val :=
  K.top_cell_ge_chain hK C.property.1 (K.chainFacet_mem hK C)
    (K.chainFacet hK C).property F hF

def facetFlag {m : ℕ} (F : K.Facet m) : K.TopChain m :=
  ⟨K.completeFlag F.val, K.completeFlag_mem F.val,
    by rw [K.completeFlag_card, F.property]⟩

@[simp] theorem chainFacet_facetFlag {m : ℕ} (hK : K.IsSphere m) (F : K.Facet m) :
    K.chainFacet hK (K.facetFlag F) = F := by
  apply Subtype.ext
  have hle := K.chainFacet_ge hK (K.facetFlag F) F.val (K.self_mem_completeFlag F.val)
  exact ((K.dimension_eq_iff_eq _ _ hle).mp
    (F.property.trans (K.chainFacet hK (K.facetFlag F)).property.symm)).symm

def facetStep (m : ℕ) (F G : K.Facet m) : Prop :=
  ∃ R : K.Cell, R ≤ F.val ∧ R ≤ G.val ∧ K.dimension R.val + 1 = m

theorem topChain_adj_step {m : ℕ} (hK : K.IsSphere m) (hm : 1 ≤ m)
    {C D : K.TopChain m} (hCD : (K.topChainGraph m).Adj C D) :
    K.chainFacet hK C = K.chainFacet hK D ∨
      K.facetStep m (K.chainFacet hK C) (K.chainFacet hK D) := by
  by_cases heq : K.chainFacet hK C = K.chainFacet hK D
  · exact Or.inl heq
  right
  obtain ⟨_, R, hR, hc, hRC, hRD⟩ := hCD
  have hbound : ∀ F ∈ R, K.dimension F.val < m := by
    intro F hF
    have hle := K.cell_dimension_le hK F
    apply lt_of_le_of_ne hle
    intro hdim
    apply heq
    have hFC : F = (K.chainFacet hK C).val :=
      (K.dimension_eq_iff_eq _ _ (K.chainFacet_ge hK C F (hRC hF))).mp
        (hdim.trans (K.chainFacet hK C).property.symm)
    have hFD : F = (K.chainFacet hK D).val :=
      (K.dimension_eq_iff_eq _ _ (K.chainFacet_ge hK D F (hRD hF))).mp
        (hdim.trans (K.chainFacet hK D).property.symm)
    exact Subtype.ext (hFC.symm.trans hFD)
  have hranks : R.image (fun F => K.dimension F.val) = Finset.range m := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr (hbound F hF)
    · rw [Finset.card_image_iff.mpr (K.chain_dimension_injective hR),
        Finset.card_range, hc]
  have hmem : m - 1 ∈ R.image (fun F => K.dimension F.val) := by
    rw [hranks]
    exact Finset.mem_range.mpr (by omega)
  obtain ⟨F, hF, hdF⟩ := Finset.mem_image.mp hmem
  exact ⟨F, K.chainFacet_ge hK C F (hRC hF),
    K.chainFacet_ge hK D F (hRD hF), by omega⟩

/-- The cubical facets are connected across genuine common ridges. -/
theorem facetStep_connected {m : ℕ} (hK : K.IsSphere m) (hm : 1 ≤ m)
    (F G : K.Facet m) : Relation.ReflTransGen (K.facetStep m) F G := by
  have hwalk : ∀ {C D : K.TopChain m}, (K.topChainGraph m).Walk C D →
      Relation.ReflTransGen (K.facetStep m) (K.chainFacet hK C) (K.chainFacet hK D) := by
    intro C D w
    induction w with
    | nil => exact .refl
    | @cons C D E hCD w ih =>
      rcases K.topChain_adj_step hK hm hCD with heq | hstep
      · simpa only [heq] using ih
      · exact (Relation.ReflTransGen.single hstep).trans ih
  obtain ⟨w⟩ := K.topChainGraph_preconnected hK hm (K.facetFlag F) (K.facetFlag G)
  simpa only [K.chainFacet_facetFlag] using hwalk w

end Cubical.PL.CubeComplex
