module

public import Unimodular.FanConnectivity
public import TauCeti.Geometry.Toric.Algebraic.Regular

@[expose] public section

open scoped Pointwise Topology BigOperators
open Set TauCeti.Toric

namespace Unimodular.AllowedBlocks

attribute [local instance] Classical.propDecidable

variable {E N V : Type*} [Fintype E] [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ι : N →+ V) (u : E → N)

/-- A lattice-kernel replacement is permitted precisely when the resulting coefficients
are nonnegative. The degree and every facet equation are preserved automatically. -/
theorem replacement_allowed_iff (w : V) (c g : FullBlock ι u → ℤ)
    (hc : IsSolution ι u w c) (hg : g ∈ (equationMap ι u w).ker) :
    IsSolution ι u w (c + g) ↔ ∀ s, 0 ≤ (c + g) s := by
  rw [isSolution_iff]
  have hcg : equationMap ι u w (c + g) = (0, 1) := by
    rw [map_add, (isSolution_iff ι u w c).1 hc |>.2]
    change (0, 1) + equationMap ι u w g = (0, 1)
    rw [show equationMap ι u w g = 0 from hg, add_zero]
  exact and_iff_left hcg

/-- Endpoint-only maximal cones preserve every cone property inherited by faces. -/
theorem UsesEndpointCones.inherited (Φ Ψ Θ : FanOnRays ι u)
    (hΘ : UsesEndpointCones ι u Φ Ψ Θ)
    (P : PointedCone ℝ V → Prop)
    (hface : ∀ {C D}, C.IsFaceOf D → P D → P C)
    (hΦ : ∀ C ∈ Φ.1.cones, P C) (hΨ : ∀ C ∈ Ψ.1.cones, P C) :
    ∀ C ∈ Θ.1.cones, P C := by
  intro C hC
  obtain ⟨D, hD, hfull, hCD⟩ := FanMaximalCones.exists_full_supercone Θ.1 Θ.2.1 hC
  apply hface hCD
  rcases hΘ D hD hfull with h | h
  · exact hΦ D h
  · exact hΨ D h

theorem UsesEndpointCones.isRegular (Φ Ψ Θ : FanOnRays ι u)
    (hΘ : UsesEndpointCones ι u Φ Ψ Θ)
    (hΦ : Φ.1.IsRegular) (hΨ : Ψ.1.IsRegular) : Θ.1.IsRegular := by
  apply Fan.isRegular_iff.2
  exact UsesEndpointCones.inherited ι u Φ Ψ Θ hΘ
    (IsRegularCone ι) (fun h hD => hD.of_isFaceOf h)
    (Fan.isRegular_iff.1 hΦ) (Fan.isRegular_iff.1 hΨ)

/-- The smooth-connectivity assertion in the first paragraph of Corollary 4.3.
Smoothness is TauCeti's actual extending-integral-basis condition on every toric cone.
No projectivity condition or uniform-unimodularity condition is imposed. -/
theorem smooth_patch_connectivity (hι : IsIntegralLattice ι) (hnz : ∀ e, ι (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => ι (u e))) = ⊤)
    {w : V} (hw : RayHyperplanes.GenericDirection (fun e => ι (u e)) w)
    (Φ Ψ : FanOnRays ι u) (hΦ : Φ.1.IsRegular) (hΨ : Ψ.1.IsRegular) :
    ∃ G : Finset (FullBlock ι u → ℤ),
      (∀ g, g ∈ G ↔ Graver.Primitive (equationMap ι u w).ker g) ∧
      Relation.ReflTransGen
        (fun A B : FanOnRays ι u =>
          indicator ι u B - indicator ι u A ∈ G ∧
          UsesEndpointCones ι u Φ Ψ A ∧ UsesEndpointCones ι u Φ Ψ B ∧
          A.1.IsRegular ∧ B.1.IsRegular) Φ Ψ := by
  obtain ⟨G, hG, hpath⟩ := theorem_1_1_connectivity ι u hι hnz hpos hw Φ Ψ
  refine ⟨G, hG, ?_⟩
  apply Relation.ReflTransGen.mono (fun A B h => ?_) _ _ hpath
  exact ⟨h.1, h.2.1, h.2.2,
    UsesEndpointCones.isRegular ι u Φ Ψ A h.2.1 hΦ hΨ,
    UsesEndpointCones.isRegular ι u Φ Ψ B h.2.2 hΦ hΨ⟩

end Unimodular.AllowedBlocks
