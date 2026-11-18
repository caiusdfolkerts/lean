module

public import Continuation.Divisor.WeakFanoBridge
public import Continuation.Divisor.StrictProjectivity
public import Continuation.Divisor.ProjectiveOverField

/-! # Actual projectivity in the weak-Fano realization

The original integral height function is proved strictly supporting on
all cones of the original normal fan. The general monomial construction
then provides an actual closed immersion into finite projective space.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace Unimodular.WeightedPolytopes.SmoothPresentation
open Set TauCeti.Toric AlgebraicGeometry CategoryTheory
open Unimodular.FanInterfaces Unimodular.Projectivity Unimodular.NefBig
open scoped Classical BigOperators
variable {n : ℕ} (P : SmoothPresentation n)

theorem schemeFullCone_vertex_match (s : P.schemeFan.fullCones) :
    ∃ v : {v // v ∈ P.vertices}, ∃ e : Fin n ≃ Fin n,
      ∀ i, P.schemeFan.fullConeBasis s i = P.basis v (e i) := by
  have hC : PaperVerification.ToricGeometry.latticeRayCone s.val ∈ P.normalFan.cones := by
    rw [← P.schemeFan_all_cones]
    exact ⟨s.val, P.schemeFan.fullCones_mem s, rfl⟩
  have hfull : Submodule.span ℝ
      (PaperVerification.ToricGeometry.latticeRayCone s.val : Set (Ambient n)) = ⊤ := by
    rw [P.schemeFan.fullConeBasis_ray_set, latticeRayCone_full_basis]
    exact ConeBases.span_cone P.normalFan.lattice (P.schemeFan.fullConeBasis s)
  obtain ⟨v, hv⟩ := P.fullCone_eq_basisCone ⟨⟨_, hC⟩, hfull⟩
  have he : ConeBases.cone (ι := FanBridge.standardEmbedding n)
      (P.schemeFan.fullConeBasis s) =
      ConeBases.cone (ι := FanBridge.standardEmbedding n) (P.basis v) := by
    rw [← latticeRayCone_full_basis, ← P.schemeFan.fullConeBasis_ray_set]
    exact hv
  obtain ⟨e, he⟩ := ConeBases.basis_permutation_of_cone_eq P.normalFan.lattice _ _ he
  exact ⟨v, e, he⟩

/-- The original integer heights supply strict support, not only nef support. -/
theorem schemeFan_height_strict_support (hweak : P.UnitCornerFeasible)
    (hzero : (0 : Lattice n) ∉ P.normals) :
    P.schemeFan.IsStrictSupport (fun u => (P.height u : ℝ)) := by
  apply P.schemeFan.strictSupport_of_full_cartier_inequalities P.schemeFan.isPure
  intro s u hu hus
  obtain ⟨v, e, he⟩ := P.schemeFullCone_vertex_match s
  have hcart : P.schemeFan.cartierLatticePoint P.height s = -v.val := by
    symm
    apply P.schemeFan.eq_cartierLatticePoint_of_pairings
    intro w hw
    rw [P.schemeFan.fullConeBasis_ray_set] at hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    rw [he i]
    have h := P.basis_active v (e i)
    rw [pairing_embed] at h
    have hz : integerPairing v.val (P.basis v (e i)) = P.height (P.basis v (e i)) := by
      exact_mod_cast h
    calc
      PaperVerification.ToricGeometry.integerPairing (P.basis v (e i)) (-v.val) =
          -integerPairing v.val (P.basis v (e i)) := by
        simp only [PaperVerification.ToricGeometry.integerPairing, integerPairing,
          Pi.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, mul_comm]
      _ = -P.height (P.basis v (e i)) := by rw [hz]
  have hp : (dotProductEquiv ℝ (Fin n) (PaperVerification.ToricGeometry.embed n u))
      (P.schemeFan.cartierPoint (fun w => (P.height w : ℝ)) s) =
        -pairing (embed v.val) u := by
    rw [← P.schemeFan.embed_cartierLatticePoint P.height s, hcart]
    simp [dotProductEquiv, dotProduct, PaperVerification.ToricGeometry.embed,
      pairing, embed, mul_comm]
  rw [hp]
  have hun : u ∈ P.normals := (P.schemeFan_rays hweak hzero u).mp hu
  have hle := (P.mem_carrier_iff _).mp (P.vertex_mem v) u hun
  have hne : pairing (embed v.val) u ≠ P.height u := by
    intro h
    obtain ⟨j, hj⟩ := P.active_subset v u hun h
    obtain ⟨i, hi⟩ := e.surjective j
    apply hus
    rw [P.schemeFan.fullConeBasis_ray_set]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i,
      (he i).trans (by rw [hi]; exact hj)⟩
  linarith [lt_of_le_of_ne hle hne]
end Unimodular.WeightedPolytopes.SmoothPresentation

namespace Unimodular.WeightedPolytopes
open Set TauCeti.Toric AlgebraicGeometry CategoryTheory
open Unimodular.FanInterfaces Unimodular.Projectivity Unimodular.NefBig
variable {n : ℕ}

/-- Proposition4.2: the exact rays are realized by an actual smooth
projective scheme with the ordinary anticanonical bundle nef and big.
The displayed strict support and finite projective map are constructed
witnesses, not additional hypotheses. -/
theorem theorem_4_2_geometric
    (k : Type u) [Field k] (U : Finset (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : (U : Set (Lattice n)) => u.val))
    (hpos : PointedCone.hull ℝ (embed '' (U : Set (Lattice n))) = ⊤)
    (hzero : (0 : Lattice n) ∉ U) :
    ∃ F : PaperVerification.ToricGeometry.SmoothCompleteFan n,
      ∃ a : Lattice n → ℤ, ∃ ha : F.IsStrictSupport (fun u => (a u : ℝ)),
      (∀ u, u ∈ F.rays ↔ u ∈ U) ∧
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
  obtain ⟨hnef, hbig⟩ := anticanonical_nef_and_big_of_support P.schemeFan k
    (P.schemeFan_unitBoundary_support hweak hzero)
  refine ⟨P.schemeFan, P.height, ha, P.schemeFan_rays hweak hzero,
    fanScheme_smooth P.schemeFan k, D.fanScheme_isProper k, inferInstance,
    D.fanProjectiveEmbedding_toSpec k,
    P.schemeFan.fanScheme_topologicalKrullDim k P.schemeFan.isPure,
    isNef_of_isNefOnCurves k _ hnef, hbig⟩

#print axioms theorem_4_2_geometric
end Unimodular.WeightedPolytopes
