module
public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.Sets.VietorisTopology
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Tauto

@[expose] public section

/-!
# Compactness of bounded families of convex bodies

This module proves the hyperspace compactness needed in Section 2 from Mathlib's
Vietoris/Hausdorff topology on nonempty compact sets. Convexity and containing
the origin are closed conditions; no support-function representation is assumed.
-/

noncomputable section

open Set TopologicalSpace Metric Filter
open scoped Topology Pointwise

namespace VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def bodyToNonemptyCompacts (K : ConvexBody E) : NonemptyCompacts E :=
  ⟨⟨K, K.isCompact⟩, K.nonempty⟩

@[simp] theorem coe_bodyToNonemptyCompacts (K : ConvexBody E) :
    (bodyToNonemptyCompacts K : Set E) = (K : Set E) := rfl

theorem isometry_bodyToNonemptyCompacts : Isometry (bodyToNonemptyCompacts (E := E)) := by
  apply Isometry.of_dist_eq
  intro K L
  rfl

omit [NormedSpace ℝ E] in
theorem isClosed_compacts_subset_relation :
    IsClosed {p : NonemptyCompacts E × NonemptyCompacts E | p.1 ≤ p.2} := by
  have h := isClosed_eq (NonemptyCompacts.lipschitz_sup (α := E)).continuous continuous_snd
  simpa only [sup_eq_right] using h

def combinationImage (a b : ℝ) (K : NonemptyCompacts E) : NonemptyCompacts E :=
  (K ×ˢ K).map (fun p : E × E => a • p.1 + b • p.2) (by fun_prop)

theorem continuous_combinationImage (a b : ℝ) :
    Continuous (combinationImage (E := E) a b) := by
  exact (Continuous.nonemptyCompacts_map (by fun_prop :
    Continuous (fun p : E × E => a • p.1 + b • p.2))).comp
      (NonemptyCompacts.continuous_prod.comp (continuous_id.prodMk continuous_id))

theorem convex_iff_combinationImage_le (K : NonemptyCompacts E) :
    Convex ℝ (K : Set E) ↔
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → combinationImage a b K ≤ K := by
  constructor
  · intro h a b ha hb hab x hx
    rcases hx with ⟨⟨y,z⟩, ⟨hy,hz⟩, rfl⟩
    exact h hy hz ha hb hab
  · intro h x hx y hy a b ha hb hab
    exact h a b ha hb hab ⟨(x,y), ⟨hx,hy⟩, rfl⟩

theorem isClosed_compacts_convex :
    IsClosed {K : NonemptyCompacts E | Convex ℝ (K : Set E)} := by
  simp_rw [convex_iff_combinationImage_le]
  simp only [ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun _ha => isClosed_iInter fun _hb => isClosed_iInter fun _hab =>
      isClosed_compacts_subset_relation.preimage
        ((continuous_combinationImage a b).prodMk continuous_id)

theorem range_bodyToNonemptyCompacts :
    Set.range (bodyToNonemptyCompacts (E := E)) =
      {K : NonemptyCompacts E | Convex ℝ (K : Set E)} := by
  ext K
  constructor
  · rintro ⟨L, rfl⟩
    exact L.convex
  · intro h
    exact ⟨⟨K, h, K.isCompact, K.nonempty⟩, rfl⟩

instance completeSpace_convexBody [CompleteSpace E] : CompleteSpace (ConvexBody E) := by
  have hr : IsClosed (Set.range (bodyToNonemptyCompacts (E := E))) := by
    rw [range_bodyToNonemptyCompacts]
    exact isClosed_compacts_convex
  exact isometry_bodyToNonemptyCompacts.isUniformEmbedding.completeSpace hr.isComplete

theorem continuous_bodyToNonemptyCompacts : Continuous (bodyToNonemptyCompacts (E := E)) :=
  isometry_bodyToNonemptyCompacts.continuous

theorem bodyToNonemptyCompacts_add (K L : ConvexBody E) :
    bodyToNonemptyCompacts (K + L) =
      (bodyToNonemptyCompacts K ×ˢ bodyToNonemptyCompacts L).map
        (fun p : E × E => p.1 + p.2) (by fun_prop) := by
  apply NonemptyCompacts.ext
  ext x
  change x ∈ ((K : Set E) + (L : Set E)) ↔ _
  rw [Set.mem_add]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact ⟨(y, z), ⟨hy, hz⟩, rfl⟩
  · rintro ⟨⟨y, z⟩, ⟨hy, hz⟩, rfl⟩
    exact ⟨y, hy, z, hz, rfl⟩

theorem continuous_add_convexBody :
    Continuous (fun p : ConvexBody E × ConvexBody E => p.1 + p.2) := by
  apply isometry_bodyToNonemptyCompacts.comp_continuous_iff.mp
  simp only [Function.comp_def, bodyToNonemptyCompacts_add]
  exact (Continuous.nonemptyCompacts_map (by fun_prop :
    Continuous (fun p : E × E => p.1 + p.2))).comp
      (NonemptyCompacts.continuous_prod.comp
        ((continuous_bodyToNonemptyCompacts.comp continuous_fst).prodMk
          (continuous_bodyToNonemptyCompacts.comp continuous_snd)))

instance continuousAdd_convexBody : ContinuousAdd (ConvexBody E) :=
  ⟨continuous_add_convexBody⟩

theorem bodyToNonemptyCompacts_smul (r : ℝ) (K : ConvexBody E) :
    bodyToNonemptyCompacts (r • K) =
      (bodyToNonemptyCompacts K).map (fun x => r • x) (by fun_prop) := by
  apply NonemptyCompacts.ext
  rfl

theorem continuous_smul_convexBody :
    Continuous (fun p : ℝ × ConvexBody E => p.1 • p.2) := by
  apply isometry_bodyToNonemptyCompacts.comp_continuous_iff.mp
  simp only [Function.comp_def, bodyToNonemptyCompacts_smul]
  apply Continuous.nonemptyCompacts_map'
    (continuous_bodyToNonemptyCompacts.comp continuous_snd)
  fun_prop

instance continuousSMul_convexBody : ContinuousSMul ℝ (ConvexBody E) :=
  ⟨continuous_smul_convexBody⟩

omit [NormedSpace ℝ E] in
theorem isClosed_compacts_contains (x : E) :
    IsClosed {K : NonemptyCompacts E | x ∈ K} := by
  have h := isClosed_compacts_subset_relation.preimage
    (continuous_const.prodMk continuous_id :
      Continuous (fun K : NonemptyCompacts E => (({x} : NonemptyCompacts E), K)))
  simpa only [Set.preimage_ofPred_eq, NonemptyCompacts.singleton_le_iff] using h

theorem isCompact_normalized_compacts {C : Set E} (hC : IsCompact C) :
    IsCompact {K : NonemptyCompacts E |
      Convex ℝ (K : Set E) ∧ (0 : E) ∈ K ∧ (K : Set E) ⊆ C} := by
  have hbase := NonemptyCompacts.isCompact_subsets_of_isCompact hC
  have hclosed := isClosed_compacts_convex.inter (isClosed_compacts_contains (0 : E))
  have h := hbase.inter_right hclosed
  convert h using 1
  ext K
  simp only [mem_ofPred_eq, mem_inter_iff]
  tauto

theorem isCompact_bodies_in_compact {C : Set E} (hC : IsCompact C) :
    IsCompact {K : ConvexBody E | (0 : E) ∈ K ∧ (K : Set E) ⊆ C} := by
  have hr : IsClosed (Set.range (bodyToNonemptyCompacts (E := E))) := by
    rw [range_bodyToNonemptyCompacts]
    exact isClosed_compacts_convex
  have h := isometry_bodyToNonemptyCompacts.isUniformInducing.isInducing.isCompact_preimage
    hr (isCompact_normalized_compacts hC)
  convert h using 1
  ext K
  simp only [mem_ofPred_eq, mem_preimage, coe_bodyToNonemptyCompacts]
  exact ⟨fun hK => ⟨K.convex, hK⟩, fun hK => hK.2⟩

end VolumePolynomials
