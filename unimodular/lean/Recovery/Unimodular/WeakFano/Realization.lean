module

public import Recovery.Unimodular.WeakFano.AnticanonicalSupport
public import Recovery.Unimodular.WeakFano.CanonicalSeed
public import Recovery.Unimodular.PriorExtensions.LiteralA3Projectivity
public import TauCeti.Geometry.Toric.Algebraic.Fan.Subdivision

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TauCeti.Toric
attribute [local instance] Classical.propDecidable

namespace Unimodular.WeightedPolytopes

variable {n : ℕ}

namespace SmoothPresentation

/-- The constructed normal fan subdivides the actual canonical radial seed.
The conclusion uses TauCeti's conewise subdivision relation. -/
theorem normalFan_subdivision (P : SmoothPresentation n)
    (hweak : P.UnitCornerFeasible) (W : Finset (Lattice n))
    (hW : GenericReflexivity.polarCarrier P.normals =
      convexHull ℝ (embed '' (W : Set (Lattice n))))
    (hz : (0 : Ambient n) ∈ GenericReflexivity.rayHull P.normals) :
    P.normalFan.IsSubdivision (GenericReflexivity.seedFan P.normals W hW) where
  exists_cone_le := by
    intro C hC
    obtain ⟨v, hv⟩ := (P.mem_normalFan_cones C).1 hC
    let q := embed (latticeDualVertex (P.basis v))
    have hq : q ∈ GenericReflexivity.polarCarrier P.normals := by
      change embed (latticeDualVertex (P.basis v)) ∈
        WeightedPolytopes.carrier P.normals (fun _ => 1)
      rw [embed_latticeDualVertex]
      exact hweak v
    refine ⟨GenericProjectivity.normalCone (GenericReflexivity.polarCarrier P.normals) q,
      (GenericReflexivity.seedFan_cones_iff_normalCone P.normals W hW hz _).2
        ⟨q, hq, rfl⟩, ?_⟩
    intro x hx
    intro p hp
    apply P.unitCorner_maximizes v x _ p hp
    rw [basisCone_eq_pointed]
    exact hv.le hx
  support_eq := by
    ext x
    exact iff_of_true
      (P.normalFan.mem_support.2 ((Fan.isComplete_iff _).1 P.normalFan_complete x))
      ((GenericReflexivity.seedFan P.normals W hW).mem_support.2
        ((Fan.isComplete_iff _).1
          (GenericReflexivity.seedFan_complete P.normals W hW hz) x))

/-- The finite integral normal-polytope witness is the existing actual
normal-fan projectivity property, with every cone and lattice point retained. -/
theorem normalFan_integral (P : SmoothPresentation n) : LiteralA3Projectivity.HasIntegralNormalFan P.normalFan :=
  P.integral_normalFan

end SmoothPresentation

/-- Every nonzero positively spanning uniformly unimodular ray configuration
has a genuine smooth complete integral-polytope normal fan with exactly those
rays. None of the geometric conclusions is an input. -/
theorem smooth_projective_realization (U : Finset (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : (U : Set (Lattice n)) => u.val))
    (hpos : PointedCone.hull ℝ (embed '' (U : Set (Lattice n))) = ⊤)
    (hzero : (0 : Lattice n) ∉ U) :
    ∃ Φ : Fan (FanBridge.standardEmbedding n), Φ.IsComplete ∧ Φ.IsRegular ∧
      AllowedBlocks.HasRays (FanBridge.standardEmbedding n)
        (fun u : (U : Set (Lattice n)) => u.val) Φ ∧
      LiteralA3Projectivity.HasIntegralNormalFan Φ := by
  obtain ⟨h, hh⟩ := exists_regular_height U
  let P := smoothPresentation U h hU hpos hh
  have hweak : P.UnitCornerFeasible := smoothPresentation_unit_feasible U h hU hpos hh
  exact ⟨P.normalFan, P.normalFan_complete, P.normalFan_regular,
    P.normalFan_hasRays (P.normals_occur hweak hzero), P.normalFan_integral⟩

/-- All geometric and support-function clauses of Proposition 4.2, for every
dimension and every original ray system. The actual scheme-theoretic
identification of the anticanonical divisor and its nefness and bigness is a
separate obligation and is deliberately not asserted by this theorem. -/
theorem smooth_projective_seed_support (hn : 0 < n) (U : Finset (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : (U : Set (Lattice n)) => u.val))
    (hpos : PointedCone.hull ℝ (embed '' (U : Set (Lattice n))) = ⊤)
    (hzero : (0 : Lattice n) ∉ U) :
    ∃ (Φ Ψ : Fan (FanBridge.standardEmbedding n)),
      Φ.IsComplete ∧ Φ.IsRegular ∧
      AllowedBlocks.HasRays (FanBridge.standardEmbedding n)
        (fun u : (U : Set (Lattice n)) => u.val) Φ ∧
      LiteralA3Projectivity.HasIntegralNormalFan Φ ∧
      Ψ.IsComplete ∧
      AllowedBlocks.HasRays (FanBridge.standardEmbedding n)
        (fun u : (U : Set (Lattice n)) => u.val) Ψ ∧
      (∀ C, C ∈ Ψ.cones ↔ ∃ E : Set (Ambient n), Convex ℝ E ∧
        IsExtreme ℝ (GenericReflexivity.rayHull U) E ∧
        E ≠ GenericReflexivity.rayHull U ∧ C = PointedCone.hull ℝ E) ∧
      Φ.IsSubdivision Ψ ∧
      (∃ ψ : Ambient n → ℝ, Continuous ψ ∧ ConvexOn ℝ Set.univ ψ ∧
        (∀ u ∈ U, ψ (embed u) = 1) ∧
        (∀ C ∈ Φ.cones, ∃ f : Module.Dual ℝ (Ambient n),
          (∀ x : Lattice n, ∃ z : ℤ, f (embed x) = (z : ℝ)) ∧
          ∀ x ∈ C, ψ x = f x)) ∧
      (0 : Ambient n) ∈ interior (GenericReflexivity.polarCarrier U) ∧
      (∃ W : Finset (Lattice n), GenericReflexivity.polarCarrier U =
        convexHull ℝ (embed '' (W : Set (Lattice n)))) := by
  obtain ⟨h, hh⟩ := exists_regular_height U
  let P := smoothPresentation U h hU hpos hh
  have hweak : P.UnitCornerFeasible := smoothPresentation_unit_feasible U h hU hpos hh
  have ht := GenericReflexivity.terminal_reflexive_hull hn U hU hpos hzero
  have hz := interior_subset ht.1
  obtain ⟨W, hW⟩ := GenericReflexivity.polarCarrier_lattice_polytope U hU hpos
  let Ψ := GenericReflexivity.seedFan U W hW
  refine ⟨P.normalFan, Ψ, P.normalFan_complete, P.normalFan_regular,
    P.normalFan_hasRays (P.normals_occur hweak hzero), P.normalFan_integral,
    GenericReflexivity.seedFan_complete U W hW hz,
    GenericReflexivity.seedFan_hasRays U W hW hz hzero ht.2.2.1,
    GenericReflexivity.seedFan_cones_iff_proper_faces U W hW hz,
    P.normalFan_subdivision hweak W hW hz, ?_,
    GenericReflexivity.zero_mem_interior_polarCarrier U, ⟨W, hW⟩⟩
  exact ⟨P.antiSupport, P.antiSupport_continuous, P.antiSupport_convex,
    P.antiSupport_ray hweak hzero, P.antiSupport_on_cone hweak⟩

end Unimodular.WeightedPolytopes

#print axioms Unimodular.WeightedPolytopes.SmoothPresentation.normalFan_subdivision
#print axioms Unimodular.WeightedPolytopes.smooth_projective_realization
#print axioms Unimodular.WeightedPolytopes.smooth_projective_seed_support
#check Unimodular.WeightedPolytopes.smooth_projective_seed_support
