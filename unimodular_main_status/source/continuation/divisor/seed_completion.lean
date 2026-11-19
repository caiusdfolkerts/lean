module

public import Continuation.Divisor.NefClosure
public import Continuation.Divisor.CanonicalSeedPort
public import TauCeti.Geometry.Toric.Algebraic.Fan.Subdivision

/-!
# Proposition 4.2 with its canonical seed

The fan used for the projective scheme is the same normal fan as the
original smooth weighted presentation. Its cones, primitive rays, and
lattice embedding are retained by the scheme interface. Consequently
the geometric weak-Fano conclusion and the canonical subdivision
conclusion hold for one and the same fan.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open Set TauCeti.Toric AlgebraicGeometry CategoryTheory
open Unimodular.FanInterfaces Unimodular.Projectivity Unimodular.NefBig
open scoped Classical

namespace Unimodular.WeightedPolytopes.SmoothPresentation
variable {n : ℕ}

/-- The original normal fan subdivides the actual polar seed. The proof
is the recovered conewise subdivision proof, with no changed hypothesis. -/
theorem normalFan_canonicalSeed_subdivision (P : SmoothPresentation n)
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

/-- This is literally the same subdivision after the all-cone scheme
interface, not a second independently chosen smooth realization. -/
theorem schemeFan_canonicalSeed_subdivision (P : SmoothPresentation n)
    (hweak : P.UnitCornerFeasible) (W : Finset (Lattice n))
    (hW : GenericReflexivity.polarCarrier P.normals =
      convexHull ℝ (embed '' (W : Set (Lattice n))))
    (hz : (0 : Ambient n) ∈ GenericReflexivity.rayHull P.normals) :
    (dictionaryToricFan P.schemeFan).IsSubdivision
      (GenericReflexivity.seedFan P.normals W hW) := by
  rw [P.schemeFan_all_cones]
  exact P.normalFan_canonicalSeed_subdivision hweak W hW hz

end Unimodular.WeightedPolytopes.SmoothPresentation

namespace Unimodular.WeightedPolytopes
variable {n : ℕ}

/-- The complete Proposition 4.2. Positive rank is the convention of the
paper. The canonical seed has exactly the proper-face cones of the
terminal reflexive ray hull. The same smooth fan has the original rays,
subdivides that seed without new rays, and defines an actual smooth
projective scheme whose ordinary anticanonical bundle is nef and big. -/
theorem theorem_4_2_geometric_seed
    (k : Type u) [Field k] (hn : 0 < n) (U : Finset (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : (U : Set (Lattice n)) => u.val))
    (hpos : PointedCone.hull ℝ (embed '' (U : Set (Lattice n))) = ⊤)
    (hzero : (0 : Lattice n) ∉ U) :
    ∃ F : PaperVerification.ToricGeometry.SmoothCompleteFan n,
      ∃ a : Lattice n → ℤ, ∃ ha : F.IsStrictSupport (fun u => (a u : ℝ)),
      ∃ Ψ : Fan (FanBridge.standardEmbedding n),
      (∀ u, u ∈ F.rays ↔ u ∈ U) ∧
      Ψ.IsComplete ∧
      AllowedBlocks.HasRays (FanBridge.standardEmbedding n)
        (fun u : (U : Set (Lattice n)) => u.val) Ψ ∧
      (∀ C, C ∈ Ψ.cones ↔ ∃ E : Set (Ambient n), Convex ℝ E ∧
        IsExtreme ℝ (GenericReflexivity.rayHull U) E ∧
        E ≠ GenericReflexivity.rayHull U ∧ C = PointedCone.hull ℝ E) ∧
      (dictionaryToricFan F).IsSubdivision Ψ ∧
      (0 : Ambient n) ∈ interior (GenericReflexivity.rayHull U) ∧
      (∃ W : Finset (Lattice n),
        realPolar (GenericReflexivity.rayHull U) =
          convexHull ℝ (embed '' (W : Set (Lattice n)))) ∧
      (GenericReflexivity.rayHull U).extremePoints ℝ =
        embed '' (U : Set (Lattice n)) ∧
      (∀ x : Lattice n, embed x ∈ GenericReflexivity.rayHull U ↔ x = 0 ∨ x ∈ U) ∧
      Smooth (F.fanSchemeStructureMap k) ∧
      IsProper (F.fanSchemeStructureMap k) ∧
      IsClosedImmersion (strictSupportProjectiveEmbedding F a ha k) ∧
      strictSupportProjectiveEmbedding F a ha k ≫
        polynomialProjectiveToSpec k (WeightIndex.{u} (F := F)) =
          F.fanSchemeStructureMap k ∧
      topologicalKrullDim (F.fanScheme k) = n ∧
      AlgebraicGeometry.IsNef (baseField := k) (anticanonicalLineBundle F k).obj ∧
      IsBig k (anticanonicalLineBundle F k).obj := by
  obtain ⟨h, hh⟩ := exists_regular_height U
  let P := smoothPresentation U h hU hpos hh
  have hweak : P.UnitCornerFeasible := smoothPresentation_unit_feasible U h hU hpos hh
  let ha := P.schemeFan_height_strict_support hweak hzero
  let D := strictSupportVertexData P.schemeFan P.height ha
  have ht := GenericReflexivity.terminal_reflexive_hull hn U hU hpos hzero
  have hz := interior_subset ht.1
  obtain ⟨W, hW⟩ := GenericReflexivity.polarCarrier_lattice_polytope U hU hpos
  let Ψ := GenericReflexivity.seedFan U W hW
  obtain ⟨hnef, hbig⟩ := anticanonical_nef_and_big_of_support P.schemeFan k
    (P.schemeFan_unitBoundary_support hweak hzero)
  exact ⟨P.schemeFan, P.height, ha, Ψ, P.schemeFan_rays hweak hzero,
    GenericReflexivity.seedFan_complete U W hW hz,
    GenericReflexivity.seedFan_hasRays U W hW hz hzero ht.2.2.1,
    GenericReflexivity.seedFan_cones_iff_proper_faces U W hW hz,
    P.schemeFan_canonicalSeed_subdivision hweak W hW hz,
    ht.1, ht.2.1, ht.2.2.1, ht.2.2.2,
    fanScheme_smooth P.schemeFan k, D.fanScheme_isProper k, inferInstance,
    D.fanProjectiveEmbedding_toSpec k,
    P.schemeFan.fanScheme_topologicalKrullDim k P.schemeFan.isPure,
    isNef_of_isNefOnCurves k _ hnef, hbig⟩

#print axioms theorem_4_2_geometric_seed
end Unimodular.WeightedPolytopes
