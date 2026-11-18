module

public import Continuation.Graver.ConnectedRegions
public import Unimodular.FanConnectivity

/-!
# Primitive replacements for the paper's fan equation matrix

This file identifies the geometric signed-cycle kernel with the actual
matrix used in Theorem 3.1, including every allowed facet row. It then
states the closed-region and connected-interior conclusions of Section
3.3 directly for the paper's primitive moves.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open scoped Topology BigOperators
open Set

namespace Unimodular.AllowedBlocks

variable {E N V : Type*} [Fintype E] [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ι : N →+ V) (u : E → N)

/-- The literal stacked boundary/degree kernel equals the geometric
signed-cycle subgroup. The unused allowed facet rows are retained. -/
theorem equationMap_kernel_eq_zeroCycles
    (hnz : ∀ e, ι (u e) ≠ 0) (w : V) :
    (equationMap ι u w).ker = PrimitiveRegions.zeroCycles (family ι u) w := by
  ext c
  change equationMap ι u w c = 0 ↔
    (family ι u).IsCycle c ∧ (family ι u).multiplicity c w = 0
  constructor
  · intro h
    have hb : BoundaryCycle ι u c :=
      fun b => congrFun (congrArg Prod.fst h) b
    refine ⟨(boundaryCycle_iff ι u hnz c).mp hb, ?_⟩
    rw [← degree_eq_multiplicity ι u w c]
    exact congrArg Prod.snd h
  · rintro ⟨hc, hd⟩
    apply Prod.ext
    · exact funext ((boundaryCycle_iff ι u hnz c).mpr hc)
    · change (∑ s, degreeRow ι u w s * c s) = 0
      rw [degree_eq_multiplicity ι u w c]
      exact hd

/-- The closed region assembled from the positive entries of a signed
cone relation. The negative region is `replacementRegion ι u (-c)`. -/
def replacementRegion (c : FullBlock ι u → ℤ) : Set V :=
  {x | ∃ s, 0 < c s ∧ x ∈ blockCone ι u s.val}

theorem replacementRegion_eq_selected (c : FullBlock ι u → ℤ) :
    replacementRegion ι u c = (family ι u).Selected c := rfl

/-- Each replacement region is a closed union of actual polyhedral cones. -/
theorem replacementRegion_isClosed (c : FullBlock ι u → ℤ) :
    IsClosed (replacementRegion ι u c) :=
  (family ι u).selected_isClosed c

/-- Every primitive integer relation for the full fan matrix replaces
two assemblies covering exactly the same closed region, whose interior
is nonempty and connected. No simpliciality, unimodularity, projectivity,
or feasibility assumption is needed for this assertion. -/
theorem primitive_replacement_regions
    (hnz : ∀ e, ι (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => ι (u e))) = ⊤)
    {w : V} (hw : RayHyperplanes.GenericDirection (fun e => ι (u e)) w)
    {c : FullBlock ι u → ℤ} (hc : Graver.Primitive (equationMap ι u w).ker c) :
    replacementRegion ι u c = replacementRegion ι u (-c) ∧
      IsConnected (interior (replacementRegion ι u c)) := by
  have hw' := RayHyperplanes.generic_for_allowed ι u hnz
    (RayHyperplanes.span_range_eq_top_of_positive _ hpos) hw
  have hc' : Graver.Primitive (PrimitiveRegions.zeroCycles (family ι u) w) c := by
    simpa only [equationMap_kernel_eq_zeroCycles ι u hnz w] using hc
  exact ⟨PrimitiveRegions.selected_eq_neg (family ι u) c hc'.1.1 hw' hc'.1.2,
    PrimitiveRegions.primitive_region_connected (family ι u) hw' hc'⟩

end Unimodular.AllowedBlocks

#print axioms Unimodular.AllowedBlocks.equationMap_kernel_eq_zeroCycles
#print axioms Unimodular.AllowedBlocks.replacementRegion_isClosed
#print axioms Unimodular.AllowedBlocks.primitive_replacement_regions

