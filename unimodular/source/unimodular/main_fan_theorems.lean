module

public import Unimodular.FanGluing
public import Unimodular.RayHyperplanes

@[expose] public section

open scoped Pointwise Topology BigOperators
open Set TauCeti.Toric

namespace Unimodular.AllowedBlocks

attribute [local instance] Classical.propDecidable

variable {E N V : Type*} [Fintype E] [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ι : N →+ V) (u : E → N)

/-- Theorem 3.1 with the paper's exact ray-generated-hyperplane genericity condition.
All ranks, full parameter ranges, nonsimplicial cones, and nonprojective fans are included.
The matrix uses every allowed codimension-one block, and the output uses ordinary finite
rational salient fans with exactly the prescribed rays. -/
theorem theorem_3_1 (hι : IsIntegralLattice ι) (hnz : ∀ e, ι (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => ι (u e))) = ⊤)
    (c : FullBlock ι u → ℤ) {w : V}
    (hw : RayHyperplanes.GenericDirection (fun e => ι (u e)) w) :
    ((∀ s, 0 ≤ c s) ∧ BoundaryCycle ι u c ∧ (∑ s, degreeRow ι u w s * c s) = 1) ↔
      ∃ Φ : Fan ι, Φ.IsComplete ∧ HasRays ι u Φ ∧
        (∀ s, c s = if blockCone ι u s.1 ∈ Φ.cones then 1 else 0) := by
  exact theorem_3_1_generic ι u hι hnz c
    (RayHyperplanes.generic_for_allowed ι u hnz
      (RayHyperplanes.span_range_eq_top_of_positive _ hpos) hw)

theorem theorem_3_1_zero_one (hnz : ∀ e, ι (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => ι (u e))) = ⊤)
    (c : FullBlock ι u → ℤ) {w : V}
    (hw : RayHyperplanes.GenericDirection (fun e => ι (u e)) w)
    (hc0 : ∀ s, 0 ≤ c s) (hc : BoundaryCycle ι u c)
    (hd : (∑ s, degreeRow ι u w s * c s) = 1) :
    ∀ s, c s = 0 ∨ c s = 1 := by
  have hw' := RayHyperplanes.generic_for_allowed ι u hnz
    (RayHyperplanes.span_range_eq_top_of_positive _ hpos) hw
  rw [degree_eq_multiplicity ι u w c] at hd
  exact (family ι u).coeff_zero_or_one c hc0 ((boundaryCycle_iff ι u hnz c).1 hc) hw' hd

/-- The generic-direction degree row is independent of its direction on every signed
integer boundary cycle, as asserted immediately after Theorem 3.1. -/
theorem signed_degree_independent (hnz : ∀ e, ι (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => ι (u e))) = ⊤)
    (c : FullBlock ι u → ℤ) (hc : BoundaryCycle ι u c) {w z : V}
    (hw : RayHyperplanes.GenericDirection (fun e => ι (u e)) w)
    (hz : RayHyperplanes.GenericDirection (fun e => ι (u e)) z) :
    (∑ s, degreeRow ι u w s * c s) = ∑ s, degreeRow ι u z s * c s := by
  rw [degree_eq_multiplicity ι u w c, degree_eq_multiplicity ι u z c]
  have hspan := RayHyperplanes.span_range_eq_top_of_positive _ hpos
  exact (family ι u).multiplicity_eq c ((boundaryCycle_iff ι u hnz c).1 hc)
    (RayHyperplanes.generic_for_allowed ι u hnz hspan hw)
    (RayHyperplanes.generic_for_allowed ι u hnz hspan hz)

end Unimodular.AllowedBlocks
