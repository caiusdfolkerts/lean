module

public import Unimodular.FanConnectivity

@[expose] public section

open scoped Pointwise Topology BigOperators
open Set TauCeti.Toric

namespace Unimodular.AllowedBlocks

attribute [local instance] Classical.propDecidable

variable {E N V : Type*} [Fintype E] [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ι : N →+ V) (u : E → N)

/-- The actual inverse correspondence between fans and nonnegative integral
solutions. In particular, a solution determines a unique fan. -/
noncomputable def fanSolutionEquiv (hι : IsIntegralLattice ι)
    (hnz : ∀ e, ι (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => ι (u e))) = ⊤)
    {w : V} (hw : RayHyperplanes.GenericDirection (fun e => ι (u e)) w) :
    FanOnRays ι u ≃ {c : FullBlock ι u → ℤ // IsSolution ι u w c} where
  toFun Φ := ⟨indicator ι u Φ, indicator_isSolution ι u hι hnz hpos hw Φ⟩
  invFun c := realization ι u hι hnz hpos hw c.1 c.2
  left_inv Φ := by
    apply indicator_injective ι u hnz
    exact indicator_realization ι u hι hnz hpos hw _ _
  right_inv c := by
    apply Subtype.ext
    exact indicator_realization ι u hι hnz hpos hw c.1 c.2

theorem theorem_3_1_bijection (hι : IsIntegralLattice ι)
    (hnz : ∀ e, ι (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => ι (u e))) = ⊤)
    {w : V} (hw : RayHyperplanes.GenericDirection (fun e => ι (u e)) w) :
    Function.Bijective (fun Φ : FanOnRays ι u =>
      (⟨indicator ι u Φ, indicator_isSolution ι u hι hnz hpos hw Φ⟩ :
        {c : FullBlock ι u → ℤ // IsSolution ι u w c})) :=
  (fanSolutionEquiv ι u hι hnz hpos hw).bijective

/-- The maximal-cone interface is equivalent to the paper's assertion for all cones. -/
theorem usesEndpointCones_iff_all (Φ Ψ Θ : FanOnRays ι u) :
    UsesEndpointCones ι u Φ Ψ Θ ↔
      ∀ C ∈ Θ.1.cones, C ∈ Φ.1.cones ∨ C ∈ Ψ.1.cones := by
  constructor
  · intro h C hC
    obtain ⟨D, hD, hfull, hCD⟩ :=
      FanMaximalCones.exists_full_supercone Θ.1 Θ.2.1 hC
    rcases h D hD hfull with hΦ | hΨ
    · exact Or.inl (Φ.1.mem_of_isFaceOf hΦ hCD)
    · exact Or.inr (Ψ.1.mem_of_isFaceOf hΨ hCD)
  · intro h C hC _
    exact h C hC

theorem theorem_1_1_all_cones (hι : IsIntegralLattice ι) (hnz : ∀ e, ι (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => ι (u e))) = ⊤)
    {w : V} (hw : RayHyperplanes.GenericDirection (fun e => ι (u e)) w)
    (Φ Ψ : FanOnRays ι u) :
    ∃ G : Finset (FullBlock ι u → ℤ),
      (∀ g, g ∈ G ↔ Graver.Primitive (equationMap ι u w).ker g) ∧
      Relation.ReflTransGen
        (fun A B : FanOnRays ι u =>
          indicator ι u B - indicator ι u A ∈ G ∧
          (∀ C ∈ A.1.cones, C ∈ Φ.1.cones ∨ C ∈ Ψ.1.cones) ∧
          (∀ C ∈ B.1.cones, C ∈ Φ.1.cones ∨ C ∈ Ψ.1.cones)) Φ Ψ := by
  simpa only [usesEndpointCones_iff_all] using
    theorem_1_1_connectivity ι u hι hnz hpos hw Φ Ψ

/-- One generic direction and one finite move set work for every pair of fans.
Neither is an additional hypothesis on the ray configuration. -/
theorem theorem_1_1_uniform_connectivity (hι : IsIntegralLattice ι)
    (hnz : ∀ e, ι (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => ι (u e))) = ⊤) :
    ∃ (w : V) (G : Finset (FullBlock ι u → ℤ)),
      RayHyperplanes.GenericDirection (fun e => ι (u e)) w ∧
      (∀ g, g ∈ G ↔ Graver.Primitive (equationMap ι u w).ker g) ∧
      ∀ Φ Ψ : FanOnRays ι u,
        Relation.ReflTransGen
          (fun A B : FanOnRays ι u =>
            indicator ι u B - indicator ι u A ∈ G ∧
            (∀ C ∈ A.1.cones, C ∈ Φ.1.cones ∨ C ∈ Ψ.1.cones) ∧
            (∀ C ∈ B.1.cones, C ∈ Φ.1.cones ∨ C ∈ Ψ.1.cones)) Φ Ψ := by
  classical
  obtain ⟨w, hw⟩ :=
    (RayHyperplanes.genericDirection_dense (fun e => ι (u e))).nonempty
  let G := (Graver.primitive_finite (equationMap ι u w).ker).toFinset
  have hG : ∀ g, g ∈ G ↔ Graver.Primitive (equationMap ι u w).ker g := by
    intro g
    exact Set.Finite.mem_toFinset _
  refine ⟨w, G, hw, hG, ?_⟩
  intro Φ Ψ
  obtain ⟨G', hG', hpath⟩ := theorem_1_1_all_cones ι u hι hnz hpos hw Φ Ψ
  have hGG : G' = G := by
    ext g
    exact (hG' g).trans (hG g).symm
  simpa only [hGG] using hpath

/-- The complete statement of Theorem 1.1: the geometric correspondence, the
zero-one conclusion, and a universal finite primitive move set with actual
all-cone endpoint preservation. Every auxiliary choice is made in the conclusion. -/
theorem theorem_1_1 (hι : IsIntegralLattice ι) (hnz : ∀ e, ι (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => ι (u e))) = ⊤) :
    ∃ (w : V) (G : Finset (FullBlock ι u → ℤ)),
      RayHyperplanes.GenericDirection (fun e => ι (u e)) w ∧
      (∀ c : FullBlock ι u → ℤ,
        ((∀ s, 0 ≤ c s) ∧ BoundaryCycle ι u c ∧
          (∑ s, degreeRow ι u w s * c s) = 1) ↔
        ∃ Φ : Fan ι, Φ.IsComplete ∧ HasRays ι u Φ ∧
          ∀ s, c s = if blockCone ι u s.1 ∈ Φ.cones then 1 else 0) ∧
      (∀ c : FullBlock ι u → ℤ, (∀ s, 0 ≤ c s) → BoundaryCycle ι u c →
        (∑ s, degreeRow ι u w s * c s) = 1 → ∀ s, c s = 0 ∨ c s = 1) ∧
      (∀ g, g ∈ G ↔ Graver.Primitive (equationMap ι u w).ker g) ∧
      ∀ Φ Ψ : FanOnRays ι u,
        Relation.ReflTransGen
          (fun A B : FanOnRays ι u =>
            indicator ι u B - indicator ι u A ∈ G ∧
            (∀ C ∈ A.1.cones, C ∈ Φ.1.cones ∨ C ∈ Ψ.1.cones) ∧
            (∀ C ∈ B.1.cones, C ∈ Φ.1.cones ∨ C ∈ Ψ.1.cones)) Φ Ψ := by
  obtain ⟨w, G, hw, hG, hpath⟩ := theorem_1_1_uniform_connectivity ι u hι hnz hpos
  refine ⟨w, G, hw, ?_, ?_, hG, hpath⟩
  · intro c
    exact theorem_3_1 ι u hι hnz hpos c hw
  · intro c hc0 hc hd
    exact theorem_3_1_zero_one ι u hnz hpos c hw hc0 hc hd

end Unimodular.AllowedBlocks

#print axioms Unimodular.AllowedBlocks.usesEndpointCones_iff_all
#print axioms Unimodular.AllowedBlocks.fanSolutionEquiv
#print axioms Unimodular.AllowedBlocks.theorem_3_1_bijection
#print axioms Unimodular.AllowedBlocks.theorem_1_1_all_cones
#print axioms Unimodular.AllowedBlocks.theorem_1_1_uniform_connectivity
#print axioms Unimodular.AllowedBlocks.theorem_1_1
