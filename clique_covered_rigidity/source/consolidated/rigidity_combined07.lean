module
import verification.internal.checkpoint
import verification.internal.extract
public import consolidated.pair_pin_progress01
import all consolidated.pair_pin_progress01
public import consolidated.pair_pin_progress02
import all consolidated.pair_pin_progress02
public import consolidated.rigidity_combined02
import all consolidated.rigidity_combined02
public import consolidated.rigidity_combined03
import all consolidated.rigidity_combined03
public import consolidated.rigidity_combined04
import all consolidated.rigidity_combined04
public import consolidated.rigidity_combined05
import all consolidated.rigidity_combined05
public import consolidated.rigidity_combined06
import all consolidated.rigidity_combined06
public import consolidated.rigidity_combined_prepared
import all consolidated.rigidity_combined_prepared
public import consolidated.rigidity_foundations01
import all consolidated.rigidity_foundations01
public import consolidated.rigidity_foundations02
import all consolidated.rigidity_foundations02
public import consolidated.rigidity_generic_tools
import all consolidated.rigidity_generic_tools
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.Basic
public import papers.rigidity_mode_splitting
import all papers.rigidity_mode_splitting

set_option Elab.async false

section BundleSource0001
/- Source: Papers/RigidityOwnedStationary.lean -/




@[expose] public section

/-!
# The actual stationary family for distinct incident maximal bodies

Only the deleted vertex is varied.  Genericity and geometric general
position hold on an actual open pin window.  At each such placement,
maximal-body nonmerging supplies a nonzero relative twist fixing the new
pin.  The old motion space and the relative-body operator are identified
literally under that replacement.

The dimension lower bound and singularity of a rank-three body image
are then consequences of the proved affine pin-rank lemmas.
The stationary-body argument supplies the required owner separation.
-/

noncomputable section
namespace Papers.Rigidity.VertexPin

open BarJoint CommonPinLowRank
open scoped Classical

variable {V : Type} [Fintype V]

theorem exists_open_generic_general_pin_window (p : Placement V 3) (v : V)
    (hgen : IsGenericPlacement p) (hgeom : GeneralPosition.InGeneralPosition p) :
    ∃ O : Set Vec3, IsOpen O ∧ p v ∈ O ∧
      ∀ q ∈ O, IsGenericPlacement (replacePlacement p v q) ∧
        GeneralPosition.InGeneralPosition (replacePlacement p v q) := by
  let O := {q : Vec3 | IsGenericPlacement (replacePlacement p v q)} ∩
    {q : Vec3 | GeneralPosition.InGeneralPosition (replacePlacement p v q)}
  refine ⟨O, ?_, ?_, fun _ h => h⟩
  · exact (isOpen_isGenericPlacement.preimage (continuous_replacePlacement p v)).inter
      (GeneralPosition.isOpen_generalPosition.preimage (continuous_replacePlacement p v))
  · simpa [O] using And.intro hgen hgeom

theorem MinimalCounterexample.owned_relative_stationary_family
    (C : MinimalCounterexample V) (v : V) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hgeom : GeneralPosition.InGeneralPosition p)
    (base b : OwnedIncidentTriangle C.graph v) (hne : b.owner ≠ base.owner) :
    let T := ownedIncidentTetrahedra C.graph v C.covered
    let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hgeom T
    let W := (T.relativeTwists p hn base b).range
    ∃ O : Set Vec3, IsOpen O ∧ p v ∈ O ∧
      ∀ q ∈ O, ∃ X : W, X ≠ 0 ∧ evaluateTwist q X.val = 0 := by
  intro T hn W
  obtain ⟨O, hO, hpO, hwindow⟩ := exists_open_generic_general_pin_window p v hgen hgeom
  refine ⟨O, hO, hpO, ?_⟩
  intro q hq
  let p' := replacePlacement p v q
  have hgq := (hwindow q hq).1
  have hgeomq := (hwindow q hq).2
  let hnq := GeneralPosition.InGeneralPosition.incident_noncollinear p' hgeomq T
  let htq := GeneralPosition.InGeneralPosition.incident_transverse p' hgeomq T
  obtain ⟨u, hu⟩ := Papers.Rigidity.VertexPin.MinimalCounterexample.owned_bodies_not_merged C v p' hgq hgeomq b base hne
  let old : DeletedMotions C.graph p v :=
    deletedMotionEquivReplace C.graph p v q (T.restrictFullMotion p' u)
  let X : W := ⟨T.relativeTwists p hn base b old, old, rfl⟩
  have htransfer (c : OwnedIncidentTriangle C.graph v) :
      T.bodyTwist p' hnq c (T.restrictFullMotion p' u) = T.bodyTwist p hn c old :=
    T.bodyTwist_replace p hn q c (T.restrictFullMotion p' u)
  refine ⟨X, ?_, ?_⟩
  · intro hz
    have hval := congrArg Subtype.val hz
    change T.bodyTwist p hn b old - T.bodyTwist p hn base old = 0 at hval
    apply hu
    rw [htransfer, htransfer]
    exact sub_eq_zero.mp hval
  · change evaluateTwist q
      (T.bodyTwist p hn b old - T.bodyTwist p hn base old) = 0
    rw [map_sub, ← htransfer b, ← htransfer base]
    have hb := T.fullMotion_at_vertex p' hnq htq u b
    have hbase := T.fullMotion_at_vertex p' hnq htq u base
    rw [show p' v = q by simp [p']] at hb hbase
    rw [← hb, ← hbase, sub_self]

theorem MinimalCounterexample.owned_relative_rank_ge_three
    (C : MinimalCounterexample V) (v : V) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hgeom : GeneralPosition.InGeneralPosition p)
    (base b : OwnedIncidentTriangle C.graph v) (hne : b.owner ≠ base.owner) :
    let T := ownedIncidentTetrahedra C.graph v C.covered
    let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hgeom T
    3 ≤ Module.finrank ℝ (T.relativeTwists p hn base b).range := by
  intro T hn
  obtain ⟨O, hO, hpO, hstationary⟩ :=
    Papers.Rigidity.VertexPin.MinimalCounterexample.owned_relative_stationary_family C v p hgen hgeom base b hne
  exact three_le_finrank_of_stationary_family_on_open _ O hO ⟨p v, hpO⟩ hstationary

theorem MinimalCounterexample.owned_rankThree_singular
    (C : MinimalCounterexample V) (v : V) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hgeom : GeneralPosition.InGeneralPosition p)
    (base b : OwnedIncidentTriangle C.graph v) (hne : b.owner ≠ base.owner)
    (hdim : Module.finrank ℝ
      ((ownedIncidentTetrahedra C.graph v C.covered).relativeTwists p
        (GeneralPosition.InGeneralPosition.incident_noncollinear p hgeom
          (ownedIncidentTetrahedra C.graph v C.covered)) base b).range = 3) :
    SingularPinSpace
      ((ownedIncidentTetrahedra C.graph v C.covered).relativeTwists p
        (GeneralPosition.InGeneralPosition.incident_noncollinear p hgeom
          (ownedIncidentTetrahedra C.graph v C.covered)) base b).range := by
  obtain ⟨O, hO, hpO, hstationary⟩ :=
    Papers.Rigidity.VertexPin.MinimalCounterexample.owned_relative_stationary_family C v p hgen hgeom base b hne
  exact singularPinSpace_of_stationary_family_on_open _ hdim O hO ⟨p v, hpO⟩ hstationary

end Papers.Rigidity.VertexPin

end
end
end BundleSource0001

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined07/block_0001/Consolidated/RigidityCombined07.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined07/checkpoint_0001.json"

section BundleSource0002
/- Source: Papers/RigidityOwnedChart.lean -/




@[expose] public section

/-!
# Surviving graph flexes in the actual grounded chart

Replacing the deleted vertex changes no old bar coordinate.  Restrict a
full motion at the replacement placement, identify its old kernel, and
subtract the reference-body twist.  The resulting actual chart tangent
fixes the new pin in every incident body.  Equality of two selected body
forms therefore forces an actual merger of their maximal owners.

The chart retains the original maximal-body owners.
-/

noncomputable section
namespace Papers.Rigidity.VertexPin.IncidentTetrahedra

open BarJoint Calculus
open scoped Classical

variable {V B : Type} [Fintype V] [Fintype B] {G : SimpleGraph V} {v : V}
variable (T : IncidentTetrahedra G v B) (p : Placement V 3)
  (hp : GeneralPosition.InGeneralPosition p) (base : B)
variable (C : SmoothLevelChart
  (groundedLengthMap (deletedGraph G v) (T.triangleEmbedding base))
  (deletedPlacement p v) (T.IncidentGroundedMotions p base))

def groundedFullMotionReplace (q : Vec3)
    (u : (rigidityOperator G (replacePlacement p v q)).ker) :
    T.IncidentGroundedMotions p base :=
  T.groundDeletedMotion p (GeneralPosition.InGeneralPosition.incident_noncollinear p hp T)
    base (deletedMotionEquivReplace G p v q (T.restrictFullMotion (replacePlacement p v q) u))

theorem incidentBodyForm_groundedFullMotionReplace (q : Vec3)
    (u : (rigidityOperator G (replacePlacement p v q)).ker) (b : B) :
    (T.incidentBodyRepresentation p hp base C b).form 0
        (T.groundedFullMotionReplace p hp base q u) =
      T.bodyTwist (replacePlacement p v q)
        (T.noncollinear_replace p
          (GeneralPosition.InGeneralPosition.incident_noncollinear p hp T) q) b
        (T.restrictFullMotion (replacePlacement p v q) u) -
      T.bodyTwist (replacePlacement p v q)
        (T.noncollinear_replace p
          (GeneralPosition.InGeneralPosition.incident_noncollinear p hp T) q) base
        (T.restrictFullMotion (replacePlacement p v q) u) := by
  rw [groundedFullMotionReplace, T.incidentBodyForm_at_zero, T.bodyTwist_groundDeletedMotion]
  change T.bodyTwist p _ b _ - T.bodyTwist p _ base _ = _
  rw [T.bodyTwist_replace, T.bodyTwist_replace]

theorem incidentBodyForm_groundedFullMotionReplace_stationary (q : Vec3)
    (hq : T.TransverseAt (replacePlacement p v q))
    (u : (rigidityOperator G (replacePlacement p v q)).ker) (b : B) :
    evaluateTwist q ((T.incidentBodyRepresentation p hp base C b).form 0
      (T.groundedFullMotionReplace p hp base q u)) = 0 := by
  rw [T.incidentBodyForm_groundedFullMotionReplace, map_sub]
  have hb := T.fullMotion_at_vertex (replacePlacement p v q)
    (T.noncollinear_replace p
      (GeneralPosition.InGeneralPosition.incident_noncollinear p hp T) q) hq u b
  have hbase := T.fullMotion_at_vertex (replacePlacement p v q)
    (T.noncollinear_replace p
      (GeneralPosition.InGeneralPosition.incident_noncollinear p hp T) q) hq u base
  rw [replacePlacement_vertex] at hb hbase
  rw [← hb, ← hbase, sub_self]

/-- A merger on the actual grounded chart identifies the two body twists
of every full motion at the replacement pin. The proof is independent of
the concrete family used to select the incident tetrahedra. -/
theorem bodyTwists_eq_of_grounded_pin_merger (q : Vec3)
    (hq : T.TransverseAt (replacePlacement p v q)) (b c : B)
    (hmerge : ∀ u : T.IncidentGroundedMotions p base,
      evaluateTwist q ((T.incidentBodyRepresentation p hp base C b).form 0 u) = 0 →
      evaluateTwist q ((T.incidentBodyRepresentation p hp base C c).form 0 u) = 0 →
        (T.incidentBodyRepresentation p hp base C b).form 0 u =
          (T.incidentBodyRepresentation p hp base C c).form 0 u)
    (u : (rigidityOperator G (replacePlacement p v q)).ker) :
    T.bodyTwist (replacePlacement p v q)
        (T.noncollinear_replace p
          (GeneralPosition.InGeneralPosition.incident_noncollinear p hp T) q) b
        (T.restrictFullMotion (replacePlacement p v q) u) =
      T.bodyTwist (replacePlacement p v q)
        (T.noncollinear_replace p
          (GeneralPosition.InGeneralPosition.incident_noncollinear p hp T) q) c
        (T.restrictFullMotion (replacePlacement p v q) u) := by
  have hh := hmerge (T.groundedFullMotionReplace p hp base q u)
    (T.incidentBodyForm_groundedFullMotionReplace_stationary p hp base C q hq u b)
    (T.incidentBodyForm_groundedFullMotionReplace_stationary p hp base C q hq u c)
  have hb := T.incidentBodyForm_groundedFullMotionReplace p hp base C q u b
  have hc := T.incidentBodyForm_groundedFullMotionReplace p hp base C q u c
  exact sub_left_inj.mp (hb.symm.trans (hh.trans hc))

end Papers.Rigidity.VertexPin.IncidentTetrahedra

namespace Papers.Rigidity.VertexPin

open BarJoint Calculus
open scoped Classical

variable {V : Type} [Fintype V]

variable (M : MinimalCounterexample V) (v : V) (p : Placement V 3)
  (hp : GeneralPosition.InGeneralPosition p)
  (base : OwnedIncidentTriangle M.graph v)


variable (C : SmoothLevelChart
  (groundedLengthMap (deletedGraph M.graph v) ((ownedIncidentTetrahedra M.graph v M.covered).triangleEmbedding base))
  (deletedPlacement p v) ((ownedIncidentTetrahedra M.graph v M.covered).IncidentGroundedMotions p base))

/-- A pointwise merger at a pin in the actual generic window already
contradicts maximality of the two owners. -/
theorem MinimalCounterexample.owned_pin_merger_contradiction
    (b c : OwnedIncidentTriangle M.graph v) (hne : b.owner ≠ c.owner)
    (q : Vec3) (hqgen : IsGenericPlacement (replacePlacement p v q))
    (hqgeom : GeneralPosition.InGeneralPosition (replacePlacement p v q))
    (hmerge : ∀ u : (ownedIncidentTetrahedra M.graph v M.covered).IncidentGroundedMotions p base,
      evaluateTwist q (((ownedIncidentTetrahedra M.graph v M.covered).incidentBodyRepresentation p hp base C b).form 0 u) = 0 →
      evaluateTwist q (((ownedIncidentTetrahedra M.graph v M.covered).incidentBodyRepresentation p hp base C c).form 0 u) = 0 →
        ((ownedIncidentTetrahedra M.graph v M.covered).incidentBodyRepresentation p hp base C b).form 0 u =
          ((ownedIncidentTetrahedra M.graph v M.covered).incidentBodyRepresentation p hp base C c).form 0 u) : False := by
  let T := ownedIncidentTetrahedra M.graph v M.covered
  let p' := replacePlacement p v q
  have ht := GeneralPosition.InGeneralPosition.incident_transverse p' hqgeom T
  obtain ⟨u, hu⟩ := Papers.Rigidity.VertexPin.MinimalCounterexample.owned_bodies_not_merged
    M v p' hqgen hqgeom b c hne
  exact hu (T.bodyTwists_eq_of_grounded_pin_merger p hp base C q ht b c hmerge u)

/-- An open-dense pin merger cannot occur for distinct actual maximal
bodies.  The generic placement is selected inside that set; no
algebraic-independence premise is silently added to the pointwise result. -/
theorem MinimalCounterexample.owned_dense_pin_merger_contradiction
    (hgen : IsGenericPlacement p)
    (b c : OwnedIncidentTriangle M.graph v) (hne : b.owner ≠ c.owner)
    (U : Set Vec3) (hUdense : Dense U)
    (hmerge : ∀ q ∈ U, ∀ u : (ownedIncidentTetrahedra M.graph v M.covered).IncidentGroundedMotions p base,
      evaluateTwist q (((ownedIncidentTetrahedra M.graph v M.covered).incidentBodyRepresentation p hp base C b).form 0 u) = 0 →
      evaluateTwist q (((ownedIncidentTetrahedra M.graph v M.covered).incidentBodyRepresentation p hp base C c).form 0 u) = 0 →
        ((ownedIncidentTetrahedra M.graph v M.covered).incidentBodyRepresentation p hp base C b).form 0 u =
          ((ownedIncidentTetrahedra M.graph v M.covered).incidentBodyRepresentation p hp base C c).form 0 u) : False := by
  obtain ⟨O, hO, hpO, hwindow⟩ := exists_open_generic_general_pin_window p v hgen hp
  obtain ⟨q, hqU, hqO⟩ := hUdense.exists_mem_open hO ⟨p v, hpO⟩
  exact Papers.Rigidity.VertexPin.MinimalCounterexample.owned_pin_merger_contradiction M v p hp base C b c hne q
    (hwindow q hqO).1 (hwindow q hqO).2 (hmerge q hqU)

/-- Even equality of the two complete grounded linear forms contradicts
their owners' distinctness. -/
theorem MinimalCounterexample.owned_incident_forms_ne
    (hgen : IsGenericPlacement p)
    (b c : OwnedIncidentTriangle M.graph v) (hne : b.owner ≠ c.owner) :
    ((ownedIncidentTetrahedra M.graph v M.covered).incidentBodyRepresentation p hp base C b).form 0 ≠
      ((ownedIncidentTetrahedra M.graph v M.covered).incidentBodyRepresentation p hp base C c).form 0 := by
  intro he
  apply Papers.Rigidity.VertexPin.MinimalCounterexample.owned_pin_merger_contradiction M v p hp base C b c hne (p v)
  · simpa using hgen
  · simpa using hp
  · intro u _ _
    exact congrArg (fun L : (ownedIncidentTetrahedra M.graph v M.covered).IncidentGroundedMotions p base →L[ℝ] Twist => L u) he

end Papers.Rigidity.VertexPin

end
end
end BundleSource0002

section BundleSource0003
/- Source: Papers/RigidityHypervertexFive.lean -/



@[expose] public section

/-!
# Excluding deletion loss five at an actual hypervertex

A hypervertex means membership in at least three distinct maximal
cliques of order at least four.  The three-dimensional grounded fiber
and its injective body projections are obtained from actual graph
motions.  Equality supplied by the Maurer--Cartan merger contradicts
the ambient-closure separation of two distinct maximal owners.

The argument excludes the deletion-rank-five hypervertex case in Proposition 4.1.
-/

noncomputable section
namespace Papers.Rigidity

open BarJoint VertexPin Calculus
open scoped Classical

variable {V : Type} [Fintype V]

def incidentBodies (G : SimpleGraph V) (v : V) : Finset (Finset V) :=
  Finset.univ.filter fun S => IsBody G S ∧ v ∈ S

/-- Exactly the paper's incidence definition, retaining all maximal bodies. -/
def IsHypervertex (G : SimpleGraph V) (v : V) : Prop :=
  3 ≤ (incidentBodies G v).card

theorem exists_ownedTriangle_of_body {G : SimpleGraph V} {v : V}
    (S : Finset V) (hS : IsBody G S) (hv : v ∈ S) :
    ∃ b : OwnedIncidentTriangle G v, b.owner = S := by
  have hc : 3 ≤ (S.erase v).card := by
    rw [Finset.card_erase_of_mem hv]
    have := hS.1
    omega
  obtain ⟨e : Fin 3 ↪ S.erase v⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin 3) (β := ↥(S.erase v))
    (by simpa only [Fintype.card_fin, Fintype.card_coe] using hc)
  let f : Fin 3 ↪ DeletedVertex v :=
    ⟨fun i => ⟨(e i).val, (Finset.mem_erase.mp (e i).property).1⟩,
      fun _ _ h => e.injective (Subtype.ext (congrArg (fun x : {w : V // w ≠ v} => x.val) h))⟩
  exact ⟨⟨(S, f), hS, hv, fun i => (Finset.mem_erase.mp (e i).property).2⟩, rfl⟩

theorem IsHypervertex.exists_three_owned {G : SimpleGraph V} {v : V}
    (hh : IsHypervertex G v) :
    ∃ b : Fin 3 → OwnedIncidentTriangle G v, Function.Injective (fun i => (b i).owner) := by
  obtain ⟨e : Fin 3 ↪ incidentBodies G v⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin 3) (β := ↥(incidentBodies G v))
    (by simpa only [IsHypervertex, Fintype.card_fin, Fintype.card_coe] using hh)
  have hex (i : Fin 3) : ∃ b : OwnedIncidentTriangle G v, b.owner = (e i).val := by
    have hm : IsBody G (e i).val ∧ v ∈ (e i).val := by
      exact (Finset.mem_filter.mp (e i).property).2
    exact exists_ownedTriangle_of_body (e i).val hm.1 hm.2
  choose b hb using hex
  refine ⟨b, ?_⟩
  intro i j hij
  apply e.injective
  apply Subtype.ext
  simpa only [hb] using hij

theorem IsHypervertex.exists_other_owned {G : SimpleGraph V} {v : V}
    (hh : IsHypervertex G v) (base b : OwnedIncidentTriangle G v) :
    ∃ c : OwnedIncidentTriangle G v, c.owner ≠ base.owner ∧ c.owner ≠ b.owner := by
  obtain ⟨f, hf⟩ := hh.exists_three_owned
  have h01 : (f 0).owner ≠ (f 1).owner := hf.ne (by decide)
  have h02 : (f 0).owner ≠ (f 2).owner := hf.ne (by decide)
  have h12 : (f 1).owner ≠ (f 2).owner := hf.ne (by decide)
  by_cases h0base : (f 0).owner = base.owner
  · by_cases h1b : (f 1).owner = b.owner
    · exact ⟨f 2, by simpa only [← h0base] using Ne.symm h02,
        by simpa only [← h1b] using Ne.symm h12⟩
    · exact ⟨f 1, by simpa only [← h0base] using Ne.symm h01, h1b⟩
  · by_cases h0b : (f 0).owner = b.owner
    · by_cases h1base : (f 1).owner = base.owner
      · exact ⟨f 2, by simpa only [← h1base] using Ne.symm h12,
          by simpa only [← h0b] using Ne.symm h02⟩
      · exact ⟨f 1, h1base, by simpa only [← h0b] using Ne.symm h01⟩
    · exact ⟨f 0, h0base, h0b⟩

theorem linearMap_injective_of_finrank_range_ge
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] (A : E →ₗ[ℝ] F)
    (h : Module.finrank ℝ E ≤ Module.finrank ℝ A.range) :
    Function.Injective A := by
  have hn := A.finrank_range_add_finrank_ker
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  omega

/-- The first excluded case of Proposition 4.1, on every actual
hypervertex of the selected counterexample. -/
theorem MinimalCounterexample.hypervertex_deletionRankDrop_ne_five
    (M : MinimalCounterexample V) (v : V) (hh : IsHypervertex M.graph v) :
    deletionRankDrop M.graph v ≠ 5 := by
  intro hdrop
  obtain ⟨b, hb⟩ := hh.exists_three_owned
  obtain ⟨p, hgen, hp⟩ := GeneralPosition.exists_generic_generalPosition (V := V)
  let T := ownedIncidentTetrahedra M.graph v M.covered
  let base := b 0
  let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hp T
  let C := groundedLengthFiberChart (deletedGraph M.graph v) (T.triangleEmbedding base)
    (T.clique base) (deletedPlacement p v)
    (generic_deletedPlacement p hgen v (deletedGraph M.graph v)) (hn base)
  have hE : Module.finrank ℝ (T.IncidentGroundedMotions p base) = 3 := by
    have h := M.grounded_incident_finrank v T p hgen hp base
    omega
  have hinj (i : Fin 3) (hi : i ≠ 0) :
      Function.Injective ((T.incidentBodyRepresentation p hp base C (b i)).form 0) := by
    apply linearMap_injective_of_finrank_range_ge
    rw [hE, T.incidentBodyForm_range_at_zero]
    exact Papers.Rigidity.VertexPin.MinimalCounterexample.owned_relative_rank_ge_three M v p hgen hp base (b i) (hb.ne hi)
  have heq := T.incidentBody_rankThree_forms_equal p hp base C hgen (by omega) hE
    (b 1) (b 2) (hinj 1 (by decide)) (hinj 2 (by decide))
  exact (Papers.Rigidity.VertexPin.MinimalCounterexample.owned_incident_forms_ne M v p hp base C hgen (b 2) (b 1)
    (hb.ne (by decide))) heq

end Papers.Rigidity

end
end
end BundleSource0003

section BundleSource0004
/- Source: Papers/RigiditySoftScalarGraph.lean -/





@[expose] public section

/-!
# The actual scalar-identification graph

Vertices are the soft point pins of the original graph. An edge records
an actual nonzero bar-coordinate functional inside a tetrahedral maximal
body. Each such edge identifies the two point-force scalars up to a
nonzero factor. The classification of all other boundary endpoints is
derived from actual two-body load projections.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

/-- Softness refers to the actual generic deletion rank, and the point
condition to the actual two maximal incident bodies. -/
def IsSoftPointPin (G : SimpleGraph V) (v : V) : Prop :=
  ∃ Q : TwoBodyPin G v, Q.IsPoint ∧ deletionRankDrop G v = 5

abbrev SoftPointPin (G : SimpleGraph V) := {v : V // IsSoftPointPin G v}

def SoftPointPin.pin {G : SimpleGraph V} (v : SoftPointPin G) : TwoBodyPin G v.val :=
  Classical.choose v.property

theorem SoftPointPin.isPoint {G : SimpleGraph V} (v : SoftPointPin G) : v.pin.IsPoint :=
  (Classical.choose_spec v.property).1

theorem SoftPointPin.drop_eq_five {G : SimpleGraph V} (v : SoftPointPin G) :
    deletionRankDrop G v.val = 5 := (Classical.choose_spec v.property).2

/-- Every vertex outside the hypervertex set has exactly two actual
maximal bodies, as data that can be used by the load constructions. -/
theorem nonempty_twoBodyPin_of_not_hypervertex
    (M : MinimalCounterexample V) (v : V) (hv : ¬ IsHypervertex M.graph v) :
    Nonempty (TwoBodyPin M.graph v) := by
  obtain ⟨S,T,hS,hT,hvS,hvT,hST⟩ := M.exists_two_bodies v
  refine ⟨⟨⟨S,hS⟩,⟨T,hT⟩,fun h => hST (congrArg Subtype.val h),hvS,hvT,?_⟩⟩
  intro C hvC
  by_contra h
  have hCS : C.val ≠ S := by
    intro heq
    exact h (Or.inl (Subtype.ext heq))
  have hCT : C.val ≠ T := by
    intro heq
    exact h (Or.inr (Subtype.ext heq))
  apply hv
  change 3 ≤ (incidentBodies M.graph v).card
  have hthree : 2 < (incidentBodies M.graph v).card := by
    apply Finset.two_lt_card_iff.mpr
    refine ⟨S,T,C.val,?_,?_,?_,hST,hCS.symm,hCT.symm⟩
    · simp only [incidentBodies, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hS,hvS⟩
    · simp only [incidentBodies, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hT,hvT⟩
    · simp only [incidentBodies, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨C.property,hvC⟩
  omega

theorem TwoBodyPin.point_or_hinge {G : SimpleGraph V} {v : V}
    (Q : TwoBodyPin G v) : Q.IsPoint ∨ Nonempty Q.Hinge := by
  by_cases hQ : Q.IsPoint
  · exact Or.inl hQ
  · right
    have hex : ∃ w ∈ Q.left.val ∩ Q.right.val, w ≠ v := by
      by_contra h
      push_neg at h
      apply hQ
      exact Finset.eq_singleton_iff_unique_mem.mpr
        ⟨Finset.mem_inter.mpr ⟨Q.left_mem,Q.right_mem⟩,h⟩
    obtain ⟨w,hw,hwv⟩ := hex
    exact ⟨⟨w,hwv.symm,(Finset.mem_inter.mp hw).1,(Finset.mem_inter.mp hw).2⟩⟩

theorem TwoBodyPin.not_hypervertex {G : SimpleGraph V} {v : V}
    (Q : TwoBodyPin G v) : ¬ IsHypervertex G v := by
  have hsub : incidentBodies G v ⊆ {Q.left.val,Q.right.val} := by
    intro S hS
    have hmem : IsBody G S ∧ v ∈ S := (Finset.mem_filter.mp hS).2
    rcases Q.exhaustive ⟨S,hmem.1⟩ hmem.2 with h | h
    · exact Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val h))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (congrArg Subtype.val h)))
  have hpair : ({Q.left.val,Q.right.val} : Finset (Finset V)).card = 2 :=
    Finset.card_pair (fun h => Q.distinct (Subtype.ext h))
  have hle : (incidentBodies G v).card ≤ 2 := by
    simpa only [hpair] using Finset.card_le_card hsub
  intro hh
  change 3 ≤ (incidentBodies G v).card at hh
  omega

theorem SoftPointPin.not_hypervertex {G : SimpleGraph V} (v : SoftPointPin G) :
    ¬ IsHypervertex G v.val := v.pin.not_hypervertex

/-- These are actual scalar coordinates on the actual stress space.
Existence below is derived from the exact rank of each point-force map. -/
structure SoftScalarSystem (M : MinimalCounterexample V) (p : Placement V 3) where
  scalar : SoftPointPin M.graph →
    Module.Dual ℝ (StressSpace (maskedGraph M.graph Finset.univ) p)
  axis : SoftPointPin M.graph → Vec3
  axis_ne_zero : ∀ v, axis v ≠ 0
  scalar_ne_zero : ∀ v, scalar v ≠ 0
  force_eq : ∀ v s,
    v.pin.pointForceOnWholePrefix v.isPoint M.covered p s = scalar v s • axis v

theorem exists_softScalarSystem
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p) :
    Nonempty (SoftScalarSystem M p) := by
  have hex (v : SoftPointPin M.graph) :=
    v.pin.exists_soft_wholePrefix_scalar M v.isPoint v.drop_eq_five p hgen hp
  choose axis scalar haxis hscalar hforce using hex
  exact ⟨⟨scalar,axis,haxis,hscalar,hforce⟩⟩

/-- The literal coefficient functional of the ordinary edge vw,
extended by zero when vw is not an edge. -/
def stressEdgeFunctional (G : SimpleGraph V) (p : Placement V 3) (v w : V) :
    Module.Dual ℝ (StressSpace (maskedGraph G Finset.univ) p) :=
  (LinearMap.proj w).comp ((starCoordinates (maskedGraph G Finset.univ) v).comp
    (StressSpace (maskedGraph G Finset.univ) p).subtype)

@[simp] theorem stressEdgeFunctional_apply
    (G : SimpleGraph V) (p : Placement V 3) (v w : V)
    (s : StressSpace (maskedGraph G Finset.univ) p) :
    stressEdgeFunctional G p v w s =
      starCoordinates (maskedGraph G Finset.univ) v s.val w := rfl

theorem stressEdgeFunctional_symm
    (G : SimpleGraph V) (p : Placement V 3) (v w : V) :
    stressEdgeFunctional G p v w = stressEdgeFunctional G p w v := by
  ext s
  exact starCoordinates_symm _ s.val v w

/-- A nonzero functional annihilating the kernel of a scalar coordinate
spans the same one-dimensional dual subspace. -/
theorem span_eq_of_nonzero_functional_kernel
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (lam μ : Module.Dual ℝ E) (hlam : lam ≠ 0) (hμ : μ ≠ 0)
    (hker : lam.ker ≤ μ.ker) : ℝ ∙ lam = ℝ ∙ μ := by
  obtain ⟨x₀,hx₀⟩ := exists_normalized_linear_functional lam hlam
  have heq : μ = μ x₀ • lam := by
    ext x
    have hx : x - lam x • x₀ ∈ lam.ker := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hx₀, smul_eq_mul, mul_one, sub_self]
    have h := LinearMap.mem_ker.mp (hker hx)
    rw [map_sub, map_smul, smul_eq_mul] at h
    simpa only [LinearMap.smul_apply, smul_eq_mul, mul_comm] using sub_eq_zero.mp h
  have hc : μ x₀ ≠ 0 := by
    intro hzero
    rw [hzero,zero_smul] at heq
    exact hμ heq
  rw [heq, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc)]

variable {M : MinimalCounterexample V} {p : Placement V 3}

/-- The scalar-identification graph uses nonzero ordinary graph-edge
functionals, not a prescribed relation on the scalar variables. -/
def SoftScalarSystem.graph (L : SoftScalarSystem M p) :
    SimpleGraph (SoftPointPin M.graph) where
  Adj v w := ∃ C : Body M.graph,
    C.val.card = 4 ∧ v.val ∈ C.val ∧ w.val ∈ C.val ∧
      stressEdgeFunctional M.graph p v.val w.val ≠ 0
  symm := by
    constructor
    rintro v w ⟨C,hC,hv,hw,he⟩
    exact ⟨C,hC,hw,hv,by rwa [stressEdgeFunctional_symm]⟩
  loopless := by
    constructor
    intro v h
    obtain ⟨C,hC,hv,hw,he⟩ := h
    apply he
    ext s
    exact starCoordinates_self _ _ _

theorem SoftScalarSystem.scalar_kernel_le_edge_kernel
    (L : SoftScalarSystem M p) (hp : GeneralPosition.InGeneralPosition p)
    (v : SoftPointPin M.graph) (C : Body M.graph)
    (hC : C.val.card = 4) (hv : v.val ∈ C.val) (w : V) (hw : w ∈ C.val) :
    (L.scalar v).ker ≤ (stressEdgeFunctional M.graph p v.val w).ker := by
  intro s hs
  have hz : v.pin.pointForceOnWholePrefix v.isPoint M.covered p s = 0 := by
    rw [L.force_eq, LinearMap.mem_ker.mp hs,zero_smul]
  exact v.pin.pointForce_zero_incident_tetrahedron_star v.isPoint M.covered
    C hv hC p hp s hz w hw

theorem SoftScalarSystem.edge_identifies_scalars
    (L : SoftScalarSystem M p) (hp : GeneralPosition.InGeneralPosition p)
    (v w : SoftPointPin M.graph) (hvw : L.graph.Adj v w) :
    ObserverCover.line L.scalar v = ObserverCover.line L.scalar w := by
  obtain ⟨C,hC,hv,hw,he⟩ := hvw
  have hvline := span_eq_of_nonzero_functional_kernel
    (L.scalar v) (stressEdgeFunctional M.graph p v.val w.val)
    (L.scalar_ne_zero v) he
    (L.scalar_kernel_le_edge_kernel hp v C hC hv w.val hw)
  have hwline := span_eq_of_nonzero_functional_kernel
    (L.scalar w) (stressEdgeFunctional M.graph p w.val v.val)
    (L.scalar_ne_zero w) (by rwa [stressEdgeFunctional_symm])
    (L.scalar_kernel_le_edge_kernel hp w C hC hw v.val hv)
  exact hvline.trans ((stressEdgeFunctional_symm M.graph p w.val v.val ▸ hwline).symm)

/-- Every nonzero tetrahedral edge from a soft pin ends at another
soft pin or at an actual hypervertex. The hinge and nonsoft exclusions
are consequences of their load spaces, not graph assumptions. -/
theorem tetrahedron_active_neighbor_soft_or_hyper
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (a : compatibleCopiedCoefficients M.graph p Finset.univ)
    (v : SoftPointPin M.graph) (C : Body M.graph) (hC : C.val.card = 4)
    (hvC : v.val ∈ C.val) (w : V) (hwC : w ∈ C.val)
    (hvw : starCoordinates (cliqueOn (C.val ∩ Finset.univ)) v.val
      (bodyCopyRestriction M.graph Finset.univ C a.val) w ≠ 0) :
    IsSoftPointPin M.graph w ∨ IsHypervertex M.graph w := by
  by_cases hh : IsHypervertex M.graph w
  · exact Or.inr hh
  obtain ⟨Q⟩ := nonempty_twoBodyPin_of_not_hypervertex M w hh
  have hvwne : v.val ≠ w := by
    intro heq
    exact hvw (by rw [heq,starCoordinates_self])
  have hreverse : starCoordinates (cliqueOn (C.val ∩ Finset.univ)) w
      (bodyCopyRestriction M.graph Finset.univ C a.val) v.val ≠ 0 := by
    rwa [starCoordinates_symm]
  rcases Q.point_or_hinge with hpoint | hHingeExists
  · by_cases hδ : deletionRankDrop M.graph w = 5
    · exact Or.inl ⟨Q,hpoint,hδ⟩
    · exact False.elim (hreverse (congrFun
        (tetrahedron_star_zero_at_nonsoft M p hgen hp a C hC w Q hwC hδ) v.val))
  · let H : Q.Hinge := Classical.choice hHingeExists
    have hvpartner : v.val ≠ H.partner := by
      intro heq
      have hvleft : v.val ∈ Q.left.val := heq.symm ▸ H.left_mem
      have hvright : v.val ∈ Q.right.val := heq.symm ▸ H.right_mem
      have hwv := v.isPoint.no_shared_edge Q.left Q.right Q.distinct
        hvleft hvright w Q.left_mem Q.right_mem
      exact hvwne hwv.symm
    exact False.elim (hreverse
      (tetrahedron_star_zero_at_hinge M p hgen hp a C hC w Q H hwC v.val hvpartner))

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0004

section BundleSource0005
/- Source: Papers/RigidityUniversalPinGeneric.lean -/




@[expose] public section

/-!
# Simultaneous genericity for all selected pair-pin frameworks

The observer argument uses finitely many possible pair-pin frameworks on
subsets of the original vertex labels.  Their maximum-rank conditions
are open and dense: each is an actual affine family of compatibility
operators, and any pin placement extends to all vertex labels.  Taking
the finite intersection therefore supplies these conditions together
with ordinary bar genericity and geometric general position.  This
avoids an unproved appeal to genericity of a subsequently selected
framework.
-/

noncomputable section
namespace Papers.Rigidity.PairPinGraph

open BarJoint Matrix
open scoped Classical Topology Matrix

variable {V B E : Type} [Fintype V] [Fintype B] [Fintype E]

instance finite_pairPinGraph : Finite (PairPinGraph B E) := by
  apply Finite.of_injective (fun J : PairPinGraph B E => (J.left, J.right))
  intro J H h
  rcases J with ⟨l, r, hlr⟩
  rcases H with ⟨l', r', hlr'⟩
  obtain ⟨hl, hr⟩ := Prod.mk.inj h
  cases hl
  cases hr
  rfl

/-- The angular part of the compatibility operator is linear in the
actual point coordinates.  Translation is its constant term. -/
def placementLinearPart (J : PairPinGraph B E) (e : E ↪ V) :
    Placement V 3 →ₗ[ℝ] ((B → Twist) →ₗ[ℝ] (E → Vec3)) where
  toFun p := LinearMap.pi fun i =>
    ((crossProduct (R := ℝ)).flip (p (e i))).comp
      ((LinearMap.fst ℝ Vec3 Vec3).comp
        (LinearMap.proj (R := ℝ) (φ := fun _ : B => Twist) (J.left i) -
          LinearMap.proj (R := ℝ) (φ := fun _ : B => Twist) (J.right i)))
  map_add' p q := by
    apply LinearMap.ext
    intro X
    funext i j
    exact congrFun (map_add (crossProduct ((X (J.left i)).1 - (X (J.right i)).1))
      (p (e i)) (q (e i))) j
  map_smul' c p := by
    apply LinearMap.ext
    intro X
    funext i j
    exact congrFun (map_smul (crossProduct ((X (J.left i)).1 - (X (J.right i)).1))
      c (p (e i))) j

theorem family_placementLinearPart (J : PairPinGraph B E) (e : E ↪ V)
    (p : Placement V 3) :
    AffineRank.family (compatibilityOperator J 0) (placementLinearPart J e) p =
      compatibilityOperator J (p ∘ e) := by
  apply LinearMap.ext
  intro X
  funext i j
  simp [AffineRank.family, placementLinearPart, compatibilityOperator,
    evaluateTwist, map_sub, LinearMap.sub_apply, Pi.sub_apply] <;> abel

theorem rankAt_placementLinearPart (J : PairPinGraph B E) (e : E ↪ V)
    (p : Placement V 3) :
    AffineRank.rankAt (compatibilityOperator J 0) (placementLinearPart J e) p =
      pinRank J (p ∘ e) := by
  unfold AffineRank.rankAt pinRank
  rw [family_placementLinearPart]

theorem isOpen_maximalRank_restriction (J : PairPinGraph B E) (e : E ↪ V) :
    IsOpen {p : Placement V 3 | pinRank J (p ∘ e) = genericPinRank J} := by
  have h := AffineRank.isOpen_setOf_le_rankAt
    (compatibilityOperator J 0) (placementLinearPart J e) (genericPinRank J)
  convert h using 1
  ext p
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, rankAt_placementLinearPart]
  exact ⟨fun h => h.ge, fun h => Nat.le_antisymm (pinRank_le_generic J _) h⟩

theorem dense_maximalRank_restriction (J : PairPinGraph B E) (e : E ↪ V) :
    Dense {p : Placement V 3 | pinRank J (p ∘ e) = genericPinRank J} := by
  obtain ⟨q, hq⟩ := genericPinRank_attained J
  let p : Placement V 3 := Function.extend e q 0
  have hcomp : p ∘ e = q := by
    funext i
    exact e.injective.extend_apply q 0 i
  have h := AffineRank.dense_setOf_le_rankAt
    (compatibilityOperator J 0) (placementLinearPart J e) (genericPinRank J)
    ⟨p, by rw [rankAt_placementLinearPart, hcomp, hq]⟩
  apply h.mono
  intro x hx
  rw [Set.mem_setOf_eq, rankAt_placementLinearPart] at hx
  exact Nat.le_antisymm (pinRank_le_generic J _) hx

/-- Every possible selected occurrence subset and endpoint assignment
has maximum rank at these same original coordinates. -/
def UniversalPinGeneric (B : Type) [Fintype B] (p : Placement V 3) : Prop :=
  ∀ S : Finset V, ∀ J : PairPinGraph B S,
    pinRank J (fun v => p v.val) = genericPinRank J

theorem isOpen_universalPinGeneric :
    IsOpen {p : Placement V 3 | UniversalPinGeneric B p} := by
  have heq : {p : Placement V 3 | UniversalPinGeneric B p} =
      ⋂ S : Finset V, ⋂ J : PairPinGraph B S,
        {p : Placement V 3 | pinRank J (fun v => p v.val) = genericPinRank J} := by
    ext p
    simp [UniversalPinGeneric]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro S
  apply isOpen_iInter_of_finite
  intro J
  exact isOpen_maximalRank_restriction J ⟨Subtype.val, Subtype.val_injective⟩

theorem dense_universalPinGeneric :
    Dense {p : Placement V 3 | UniversalPinGeneric B p} := by
  have heq : {p : Placement V 3 | UniversalPinGeneric B p} =
      ⋂ S : Finset V, ⋂ J : PairPinGraph B S,
        {p : Placement V 3 | pinRank J (fun v => p v.val) = genericPinRank J} := by
    ext p
    simp [UniversalPinGeneric]
  rw [heq]
  apply dense_iInter_of_isOpen
  · intro S
    exact isOpen_iInter_of_finite fun J =>
      isOpen_maximalRank_restriction J ⟨Subtype.val, Subtype.val_injective⟩
  · intro S
    exact dense_iInter_of_isOpen
      (fun J => isOpen_maximalRank_restriction J ⟨Subtype.val, Subtype.val_injective⟩)
      (fun J => dense_maximalRank_restriction J ⟨Subtype.val, Subtype.val_injective⟩)

/-- A single ordinary real placement satisfying every genericity
condition needed for the eventual observer argument exists. -/
theorem exists_generic_generalPosition_universalPin :
    ∃ p : Placement V 3, IsGenericPlacement p ∧
      GeneralPosition.InGeneralPosition p ∧ UniversalPinGeneric B p := by
  have hopen : IsOpen {p : Placement V 3 |
      IsGenericPlacement p ∧ GeneralPosition.InGeneralPosition p} :=
    isOpen_isGenericPlacement.inter GeneralPosition.isOpen_generalPosition
  have hne : ({p : Placement V 3 |
      IsGenericPlacement p ∧ GeneralPosition.InGeneralPosition p}).Nonempty :=
    GeneralPosition.exists_generic_generalPosition
  obtain ⟨p, hpin, hp⟩ :=
    (dense_universalPinGeneric (B := B)).exists_mem_open hopen hne
  exact ⟨p, hp.1, hp.2, hpin⟩

end Papers.Rigidity.PairPinGraph

end
end
end BundleSource0005

section BundleSource0006
/- Source: Papers/RigiditySelectedPointPins.lean -/





@[expose] public section

/-!
# Selected actual point pins have no supported compatible load

An arbitrary set of actual point pins defines a simple pair-pin graph
on the full set of original maximal bodies. Original graph motions
prove that its distinct bodies do not merge. At a placement generic for
all such selections, Theorem 5.1 gives surjectivity of its literal pin
operator. Virtual work then kills every compatible body load supported
on these selected pins.

This is the mechanical contradiction used after restricting a load to
an unobserved component. Balance of that restricted load remains an
explicit input; it is not part of a redefined stress notion.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint Matrix
open scoped Classical Matrix BigOperators

variable {V : Type} [Fintype V]

/-- The actual twist of an original maximal body in a full graph motion. -/
def fullBodyTwists (G : SimpleGraph V) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p)
    (u : (rigidityOperator G p).ker) : Body G → Twist :=
  fun C => Classical.choose (exists_twist_on_clique G p u.val hp u.property
    C.val (by have h := C.property.1; omega) C.property.2.1)

theorem fullBodyTwists_fit (G : SimpleGraph V) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p)
    (u : (rigidityOperator G p).ker) (C : Body G) (w : V) (hw : w ∈ C.val) :
    u.val w = evaluateTwist (p w) (fullBodyTwists G p hp u C) :=
  Classical.choose_spec (exists_twist_on_clique G p u.val hp u.property
    C.val (by have h := C.property.1; omega) C.property.2.1) w hw

/-- Maximality and ambient closure force every pair of different bodies
to be distinguished by an actual full graph motion. -/
theorem exists_fullBodyTwists_ne
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (C D : Body M.graph) (hne : C ≠ D) :
    ∃ u : (rigidityOperator M.graph p).ker,
      fullBodyTwists M.graph p hp u C ≠ fullBodyTwists M.graph p hp u D := by
  by_contra hn
  have heq : ∀ u : (rigidityOperator M.graph p).ker,
      fullBodyTwists M.graph p hp u C = fullBodyTwists M.graph p hp u D := by
    intro u
    by_contra h
    exact hn ⟨u,h⟩
  have hcluster : RigidCluster M.graph (C.val ∪ D.val) := by
    apply rigidCluster_of_motionRepresentation M.graph (C.val ∪ D.val) p hgen
    intro u
    refine ⟨fullBodyTwists M.graph p hp u C, ?_⟩
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact fullBodyTwists_fit M.graph p hp u C w hw
    · rw [heq u]
      exact fullBodyTwists_fit M.graph p hp u D w hw
  have hcard : 4 ≤ (C.val ∪ D.val).card :=
    C.property.1.trans (Finset.card_le_card Finset.subset_union_left)
  have hclique := M.rigidCluster_isClique (C.val ∪ D.val) hcard hcluster
  have hC := C.property.2.2 (C.val ∪ D.val) Finset.subset_union_left hclique
  have hD := D.property.2.2 (C.val ∪ D.val) Finset.subset_union_right hclique
  exact hne (Subtype.ext (Finset.Subset.antisymm
    (Finset.subset_union_left.trans hD) (Finset.subset_union_right.trans hC)))

/-- Every occurrence is its original vertex label; unused bodies remain
as isolated nodes. -/
def selectedPointPinGraph (G : SimpleGraph V) (S : Finset V)
    (Q : ∀ v : S, TwoBodyPin G v.val) : PairPinGraph (Body G) S where
  left v := (Q v).left
  right v := (Q v).right
  loopless v := (Q v).distinct

theorem selectedPointPinGraph_simple
    (G : SimpleGraph V) (S : Finset V)
    (Q : ∀ v : S, TwoBodyPin G v.val) (hQ : ∀ v, (Q v).IsPoint) :
    (selectedPointPinGraph G S Q).IsSimple := by
  intro v w h
  have hpair : s((Q v).left, (Q v).right) = s((Q w).left, (Q w).right) := h
  have hv : v.val ∈ (Q w).left.val ∩ (Q w).right.val := by
    rcases Sym2.eq_iff.mp hpair with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · exact Finset.mem_inter.mpr ⟨hl ▸ (Q v).left_mem, hr ▸ (Q v).right_mem⟩
    · exact Finset.mem_inter.mpr ⟨hr ▸ (Q v).right_mem, hl ▸ (Q v).left_mem⟩
  rw [hQ w, Finset.mem_singleton] at hv
  exact Subtype.ext hv

/-- Restricting a full graph motion gives a compatible twist assignment
on every subsequently selected point-pin graph. -/
theorem fullBodyTwists_mem_selected_kernel
    (G : SimpleGraph V) (S : Finset V)
    (Q : ∀ v : S, TwoBodyPin G v.val)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (u : (rigidityOperator G p).ker) :
    fullBodyTwists G p hp u ∈
      ((selectedPointPinGraph G S Q).compatibilityOperator (fun v => p v.val)).ker := by
  rw [LinearMap.mem_ker]
  ext v i
  rw [PairPinGraph.compatibilityOperator_apply]
  change (evaluateTwist (p v.val) (fullBodyTwists G p hp u (Q v).left) -
    evaluateTwist (p v.val) (fullBodyTwists G p hp u (Q v).right)) i = 0
  rw [← fullBodyTwists_fit G p hp u (Q v).left v.val (Q v).left_mem,
    ← fullBodyTwists_fit G p hp u (Q v).right v.val (Q v).right_mem, sub_self,
    Pi.zero_apply]

theorem selectedPointPinGraph_noMerged
    (M : MinimalCounterexample V) (S : Finset V)
    (Q : ∀ v : S, TwoBodyPin M.graph v.val)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hpin : PairPinGraph.UniversalPinGeneric (Body M.graph) p) :
    (selectedPointPinGraph M.graph S Q).NoMergedBodies := by
  intro C D hCD
  obtain ⟨u,hu⟩ := exists_fullBodyTwists_ne M p hgen hp C D hCD
  exact ⟨fun v => p v.val, hpin S (selectedPointPinGraph M.graph S Q),
    fullBodyTwists M.graph p hp u,
    fullBodyTwists_mem_selected_kernel M.graph S Q p hp u, hu⟩

/-- The literal three coordinate equations at each selected point pin
are independent at the same original real placement. -/
theorem selectedPointPinGraph_surjective
    (M : MinimalCounterexample V) (S : Finset V)
    (Q : ∀ v : S, TwoBodyPin M.graph v.val) (hQ : ∀ v, (Q v).IsPoint)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hpin : PairPinGraph.UniversalPinGeneric (Body M.graph) p) :
    Function.Surjective
      ((selectedPointPinGraph M.graph S Q).compatibilityOperator (fun v => p v.val)) := by
  have hpos : 0 < Fintype.card V := by have h := M.eight_le_card; omega
  letI : Nonempty V := Fintype.card_pos_iff.mp hpos
  obtain ⟨C,D,hC,_,_,_,_⟩ := M.exists_two_bodies (Classical.arbitrary V)
  letI : Nonempty (Body M.graph) := ⟨⟨C,hC⟩⟩
  apply (PairPinGraph.linearIndependent_pinRows_iff_surjective _ _).mp
  exact pairPin_simple_pinRows_independent (selectedPointPinGraph M.graph S Q)
    (selectedPointPinGraph_noMerged M S Q p hgen hp hpin)
    (selectedPointPinGraph_simple M.graph S Q hQ) (fun v => p v.val)
    (hpin S (selectedPointPinGraph M.graph S Q))

/-- At a two-body vertex virtual work is the first force paired with
the relative body velocity. -/
theorem TwoBodyPin.load_pairing_eq
    {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v)
    (p : Placement V 3) (F : compatibleBodyLoads G p Finset.univ)
    (g : Body G → Vec3) :
    (∑ C : Body G, (F.val C).val v ⬝ᵥ g C) =
      Q.loadProjection p F ⬝ᵥ (g Q.left - g Q.right) := by
  have hsub : (∑ C ∈ ({Q.left,Q.right} : Finset (Body G)),
      (F.val C).val v ⬝ᵥ g C) = ∑ C : Body G, (F.val C).val v ⬝ᵥ g C := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro C _ hC
    have hv : v ∉ C.val := by
      intro hv
      exact hC (by simpa only [Finset.mem_insert, Finset.mem_singleton]
        using Q.exhaustive C hv)
    rw [compatible_load_zero_outside_body G p F C v hv, zero_dotProduct]
  rw [← hsub, Finset.sum_pair Q.distinct, Q.load_right_eq_neg_left,
    neg_dotProduct, dotProduct_sub]
  exact (sub_eq_add_neg (Q.loadProjection p F ⬝ᵥ g Q.left)
    (Q.loadProjection p F ⬝ᵥ g Q.right)).symm

/-- The selected pin forces annihilate every literal compatible-row
output, by summing ordinary work over the balanced bodies. -/
theorem selected_load_virtual_work
    (G : SimpleGraph V) (S : Finset V)
    (Q : ∀ v : S, TwoBodyPin G v.val) (p : Placement V 3)
    (F : compatibleBodyLoads G p Finset.univ)
    (hF : ∀ C : Body G, ∀ w, w ∉ S → (F.val C).val w = 0)
    (X : Body G → Twist) :
    (∑ v : S, (Q v).loadProjection p F ⬝ᵥ
      (selectedPointPinGraph G S Q).compatibilityOperator (fun v => p v.val) X v) = 0 := by
  have hbody (C : Body G) :
      (∑ w : V, (F.val C).val w ⬝ᵥ evaluateTwist (p w) (X C)) = 0 := by
    simpa only [loadWorkEquiv_apply, globalTwistOperator_apply] using
      balanced_load_annihilates_twist p (F.val C).val (F.val C).property.1 (X C)
  calc
    (∑ v : S, (Q v).loadProjection p F ⬝ᵥ
        (selectedPointPinGraph G S Q).compatibilityOperator (fun v => p v.val) X v) =
      ∑ v : S, ∑ C : Body G, (F.val C).val v.val ⬝ᵥ
        evaluateTwist (p v.val) (X C) := by
          apply Finset.sum_congr rfl
          intro v _
          rw [(Q v).load_pairing_eq, PairPinGraph.compatibilityOperator_apply] <;> rfl
    _ = ∑ w ∈ S, ∑ C : Body G, (F.val C).val w ⬝ᵥ
        evaluateTwist (p w) (X C) := by
          rw [Finset.sum_coe_sort S (fun w : V => ∑ C : Body G,
            (F.val C).val w ⬝ᵥ evaluateTwist (p w) (X C))]
    _ = ∑ w : V, ∑ C : Body G, (F.val C).val w ⬝ᵥ
        evaluateTwist (p w) (X C) := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro w _ hw
          apply Finset.sum_eq_zero
          intro C _
          rw [hF C w hw, zero_dotProduct]
    _ = 0 := by rw [Finset.sum_comm]; simp only [hbody, Finset.sum_const_zero]

/-- Ordinary restriction of a force assignment to actual vertex labels. -/
def restrictLoadTo (S : Finset V) : (V → Vec3) →ₗ[ℝ] (V → Vec3) where
  toFun F w := if w ∈ S then F w else 0
  map_add' F H := by
    ext w i
    by_cases hw : w ∈ S <;> simp [hw]
  map_smul' c F := by
    ext w i
    by_cases hw : w ∈ S <;> simp [hw]

@[simp] theorem restrictLoadTo_apply (S : Finset V) (F : V → Vec3) (w : V) :
    restrictLoadTo S F w = if w ∈ S then F w else 0 := rfl

theorem sum_restricted_body_loads_eq_zero
    (G : SimpleGraph V) (S : Finset V) (p : Placement V 3)
    (F : compatibleBodyLoads G p Finset.univ) :
    (∑ C : Body G, restrictLoadTo S (F.val C).val) = 0 := by
  have hsum : (∑ C : Body G, (F.val C).val) = 0 := by
    ext w i
    have h := (mem_compatibleBodyLoads_iff G p Finset.univ F.val).mp F.property w
    simpa only [Finset.sum_apply, Pi.zero_apply] using congrFun h i
  rw [← map_sum, hsum, map_zero]

/-- If every body except one has a balanced restriction, cancellation
forces the remaining body to be balanced too. This includes the sole
large-body case of the no-observer argument. -/
theorem balanced_restricted_load_of_all_other_bodies
    (G : SimpleGraph V) (S : Finset V) (p : Placement V 3)
    (F : compatibleBodyLoads G p Finset.univ) (D : Body G)
    (hother : ∀ C : Body G, C ≠ D →
      restrictLoadTo S (F.val C).val ∈ balancedLoads p) :
    restrictLoadTo S (F.val D).val ∈ balancedLoads p := by
  have hsum :
      (∑ C ∈ Finset.univ.erase D, restrictLoadTo S (F.val C).val) +
        restrictLoadTo S (F.val D).val = 0 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ D)]
    exact sum_restricted_body_loads_eq_zero G S p F
  rw [eq_neg_of_add_eq_zero_right hsum]
  apply (balancedLoads p).neg_mem
  apply Submodule.sum_mem
  intro C hC
  exact hother C (Finset.mem_erase.mp hC).1

/-- A balanced restriction is a member of the original compatible-load
space; balance is proved before constructing this subtype. -/
def restrictCompatibleLoad
    (G : SimpleGraph V) (S : Finset V) (p : Placement V 3)
    (F : compatibleBodyLoads G p Finset.univ)
    (hbalanced : ∀ C : Body G, restrictLoadTo S (F.val C).val ∈ balancedLoads p) :
    compatibleBodyLoads G p Finset.univ := by
  let H : BodyBalancedFamily G p Finset.univ := fun C =>
    ⟨restrictLoadTo S (F.val C).val, hbalanced C, by
      intro w hw
      by_cases hwS : w ∈ S
      · simp only [restrictLoadTo_apply, if_pos hwS]
        exact (F.val C).property.2 w hw
      · simp only [restrictLoadTo_apply, if_neg hwS]⟩
  refine ⟨H, ?_⟩
  rw [compatibleBodyLoads, LinearMap.mem_ker, totalBodyLoad_apply]
  exact sum_restricted_body_loads_eq_zero G S p F

@[simp] theorem restrictCompatibleLoad_apply
    (G : SimpleGraph V) (S : Finset V) (p : Placement V 3)
    (F : compatibleBodyLoads G p Finset.univ)
    (hbalanced : ∀ C : Body G, restrictLoadTo S (F.val C).val ∈ balancedLoads p)
    (C : Body G) (w : V) :
    ((restrictCompatibleLoad G S p F hbalanced).val C).val w =
      if w ∈ S then (F.val C).val w else 0 := rfl

/-- No nonzero actual compatible body load can be supported solely on
a set of actual point pins. This is the row-stress contradiction used
in the no-observer step, with no presumed genericity of a later choice. -/
theorem compatible_load_eq_zero_of_supported_on_pointPins
    (M : MinimalCounterexample V) (S : Finset V)
    (Q : ∀ v : S, TwoBodyPin M.graph v.val) (hQ : ∀ v, (Q v).IsPoint)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hpin : PairPinGraph.UniversalPinGeneric (Body M.graph) p)
    (F : compatibleBodyLoads M.graph p Finset.univ)
    (hF : ∀ C : Body M.graph, ∀ w, w ∉ S → (F.val C).val w = 0) : F = 0 := by
  have hsurj := selectedPointPinGraph_surjective M S Q hQ p hgen hp hpin
  have hzero (v : S) : (Q v).loadProjection p F = 0 := by
    obtain ⟨X,hX⟩ := hsurj (Pi.single v ((Q v).loadProjection p F))
    have hwork := selected_load_virtual_work M.graph S Q p F hF X
    rw [hX] at hwork
    have heq : (∑ w : S, (Q w).loadProjection p F ⬝ᵥ
        ((Pi.single v ((Q v).loadProjection p F) : S → Vec3) w)) =
        (Q v).loadProjection p F ⬝ᵥ (Q v).loadProjection p F := by
      rw [Finset.sum_eq_single v]
      · simp
      · intro w _ hw
        rw [Pi.single_eq_of_ne hw, dotProduct_zero]
      · simp
    rw [heq] at hwork
    exact dotProduct_self_eq_zero.mp hwork
  apply Subtype.ext
  funext C
  apply Subtype.ext
  funext w
  by_cases hw : w ∈ S
  · by_cases hwC : w ∈ C.val
    · rcases (Q ⟨w,hw⟩).exhaustive C hwC with hC | hC
      · subst C
        exact hzero ⟨w,hw⟩
      · subst C
        rw [(Q ⟨w,hw⟩).load_right_eq_neg_left, hzero, neg_zero] <;> rfl
    · exact compatible_load_zero_outside_body M.graph p F C w hwC
  · exact hF C w hw

/-- The form needed for a component cut: if the actual restrictions of
all body loads are balanced, every selected point-pin force is zero. -/
theorem load_zero_on_pointPins_of_balanced_restrictions
    (M : MinimalCounterexample V) (S : Finset V)
    (Q : ∀ v : S, TwoBodyPin M.graph v.val) (hQ : ∀ v, (Q v).IsPoint)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hpin : PairPinGraph.UniversalPinGeneric (Body M.graph) p)
    (F : compatibleBodyLoads M.graph p Finset.univ)
    (hbalanced : ∀ C : Body M.graph, restrictLoadTo S (F.val C).val ∈ balancedLoads p) :
    ∀ C : Body M.graph, ∀ w ∈ S, (F.val C).val w = 0 := by
  let H := restrictCompatibleLoad M.graph S p F hbalanced
  have hHzero : H = 0 := compatible_load_eq_zero_of_supported_on_pointPins
    M S Q hQ p hgen hp hpin H (by
      intro C w hw
      simp only [H, restrictCompatibleLoad_apply, if_neg hw])
  intro C w hw
  have h := congrArg (fun A : compatibleBodyLoads M.graph p Finset.univ =>
    (A.val C).val w) hHzero
  change (H.val C).val w = (0 : Vec3) at h
  simpa only [H, restrictCompatibleLoad_apply, if_pos hw] using h

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0006

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined07/block_0006/Consolidated/RigidityCombined07.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined07/checkpoint_0006.json"

section BundleSource0007
/- Source: Papers/RigidityScalarObservers.lean -/




@[expose] public section

/-!
# Actual observers of scalar components

The observers are precisely hypervertex stars and maximal bodies of
order at least five. A component with no hypervertex observer must meet
two large bodies. The proof restricts actual copied bar coefficients,
proves balance of the resulting body loads, and invokes the verified
row-independence statement for the literal selected point-pin graph.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

abbrev Hypervertex (G : SimpleGraph V) := {v : V // IsHypervertex G v}
abbrev LargeBody (G : SimpleGraph V) := {C : Body G // 5 ≤ C.val.card}
abbrev ScalarObserver (G : SimpleGraph V) := Hypervertex G ⊕ LargeBody G

variable {M : MinimalCounterexample V} {p : Placement V 3}

def SoftScalarSystem.seed (L : SoftScalarSystem M p) :
    ScalarObserver M.graph → Finset (SoftPointPin M.graph)
  | Sum.inl h => Finset.univ.filter fun v => ∃ C : Body M.graph,
      C.val.card = 4 ∧ v.val ∈ C.val ∧ h.val ∈ C.val ∧
        stressEdgeFunctional M.graph p v.val h.val ≠ 0
  | Sum.inr C => Finset.univ.filter fun v => v.val ∈ C.val.val

def SoftScalarSystem.observers (L : SoftScalarSystem M p)
    (c : L.graph.ConnectedComponent) : Finset (ScalarObserver M.graph) :=
  ObserverCover.observers L.graph L.seed c

/-- Actual graph vertices in the scalar component. -/
def SoftScalarSystem.vertices (L : SoftScalarSystem M p)
    (c : L.graph.ConnectedComponent) : Finset V :=
  Finset.univ.filter fun v => ∃ hv : IsSoftPointPin M.graph v,
    L.graph.connectedComponentMk ⟨v,hv⟩ = c

theorem SoftScalarSystem.mem_vertices
    (L : SoftScalarSystem M p) (c : L.graph.ConnectedComponent) (v : V) :
    v ∈ L.vertices c ↔ ∃ hv : IsSoftPointPin M.graph v,
      L.graph.connectedComponentMk ⟨v,hv⟩ = c := by
  simp only [SoftScalarSystem.vertices,Finset.mem_filter,Finset.mem_univ,true_and]

theorem SoftScalarSystem.soft_of_mem_vertices
    (L : SoftScalarSystem M p) (c : L.graph.ConnectedComponent) (v : V)
    (hv : v ∈ L.vertices c) : IsSoftPointPin M.graph v :=
  Classical.choose ((L.mem_vertices c v).mp hv)

theorem SoftScalarSystem.mk_eq_of_mem_vertices
    (L : SoftScalarSystem M p) (c : L.graph.ConnectedComponent)
    (v : SoftPointPin M.graph) (hv : v.val ∈ L.vertices c) :
    L.graph.connectedComponentMk v = c := by
  obtain ⟨h,hc⟩ := (L.mem_vertices c v.val).mp hv
  exact hc

theorem SoftScalarSystem.hyper_mem_observers
    (L : SoftScalarSystem M p) (c : L.graph.ConnectedComponent)
    (h : Hypervertex M.graph) :
    Sum.inl h ∈ L.observers c ↔
      ∃ v : SoftPointPin M.graph, L.graph.connectedComponentMk v = c ∧
        ∃ C : Body M.graph, C.val.card = 4 ∧ v.val ∈ C.val ∧ h.val ∈ C.val ∧
          stressEdgeFunctional M.graph p v.val h.val ≠ 0 := by
  constructor
  · intro hh
    have hobs : ∃ v ∈ L.seed (Sum.inl h), L.graph.connectedComponentMk v = c :=
      (Finset.mem_filter.mp hh).2
    obtain ⟨v,hv,hc⟩ := hobs
    exact ⟨v,hc,(Finset.mem_filter.mp hv).2⟩
  · rintro ⟨v,hc,hv⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,hc⟩

theorem SoftScalarSystem.large_mem_observers
    (L : SoftScalarSystem M p) (c : L.graph.ConnectedComponent)
    (C : LargeBody M.graph) :
    Sum.inr C ∈ L.observers c ↔ ∃ v ∈ L.vertices c, v ∈ C.val.val := by
  constructor
  · intro hh
    have hobs : ∃ v ∈ L.seed (Sum.inr C), L.graph.connectedComponentMk v = c :=
      (Finset.mem_filter.mp hh).2
    obtain ⟨v,hv,hc⟩ := hobs
    exact ⟨v.val,(L.mem_vertices c v.val).mpr ⟨v.property,hc⟩,
      (Finset.mem_filter.mp hv).2⟩
  · rintro ⟨v,hv,hvC⟩
    obtain ⟨hsoft,hc⟩ := (L.mem_vertices c v).mp hv
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,⟨v,hsoft⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvC⟩,hc⟩

/-- With no hypervertex observer, no copied tetrahedral coefficient
crosses the component boundary. Each possible endpoint is classified
using its actual load projection. -/
theorem SoftScalarSystem.tetrahedron_crossing_zero
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (c : L.graph.ConnectedComponent)
    (hhyper : ∀ h : Hypervertex M.graph, Sum.inl h ∉ L.observers c)
    (a : compatibleCopiedCoefficients M.graph p Finset.univ)
    (C : Body M.graph) (hC : C.val.card = 4) :
    ∀ v ∈ L.vertices c, ∀ w, w ∉ L.vertices c →
      starCoordinates (cliqueOn (C.val ∩ Finset.univ)) v
        (bodyCopyRestriction M.graph Finset.univ C a.val) w = 0 := by
  intro v hv w hw
  by_contra hcoef
  have hadj : (cliqueOn (C.val ∩ Finset.univ)).Adj v w := by
    by_contra h
    exact hcoef (starCoordinates_of_not_adj _ _ _ _ h)
  have hvC : v ∈ C.val := (Finset.mem_inter.mp hadj.2.1).1
  have hwC : w ∈ C.val := (Finset.mem_inter.mp hadj.2.2).1
  let sv : SoftPointPin M.graph := ⟨v,L.soft_of_mem_vertices c v hv⟩
  have hsvc : L.graph.connectedComponentMk sv = c := L.mk_eq_of_mem_vertices c sv hv
  have heval : stressEdgeFunctional M.graph p v w
      (copiedToStress M.graph p Finset.univ a) ≠ 0 := by
    rw [stressEdgeFunctional_apply,
      sv.isPoint.copied_body_star a C hvC w hwC hadj.1]
    exact hcoef
  have he : stressEdgeFunctional M.graph p v w ≠ 0 := by
    intro hz
    exact heval (by rw [hz,LinearMap.zero_apply])
  rcases tetrahedron_active_neighbor_soft_or_hyper M p hgen hp a sv C hC hvC w hwC hcoef
      with hsoft | hhyperw
  · let sw : SoftPointPin M.graph := ⟨w,hsoft⟩
    have hedge : L.graph.Adj sv sw := ⟨C,hC,hvC,hwC,he⟩
    have hcw : L.graph.connectedComponentMk sw = c :=
      (SimpleGraph.ConnectedComponent.sound hedge.reachable).symm.trans hsvc
    exact hw ((L.mem_vertices c w).mpr ⟨hsoft,hcw⟩)
  · exact hhyper ⟨w,hhyperw⟩ ((L.hyper_mem_observers c ⟨w,hhyperw⟩).mpr
      ⟨sv,hsvc,C,hC,hvC,hwC,he⟩)

/-- An unobserved large body has no selected component vertex and
hence has identically zero restricted load. -/
theorem SoftScalarSystem.restricted_load_zero_of_large_unobserved
    (L : SoftScalarSystem M p) (c : L.graph.ConnectedComponent)
    (F : compatibleBodyLoads M.graph p Finset.univ)
    (C : Body M.graph) (hC : 5 ≤ C.val.card)
    (hnot : Sum.inr (⟨C,hC⟩ : LargeBody M.graph) ∉ L.observers c) :
    restrictLoadTo (L.vertices c) (F.val C).val = 0 := by
  funext v
  by_cases hv : v ∈ L.vertices c
  · rw [restrictLoadTo_apply,if_pos hv]
    apply compatible_load_zero_outside_body M.graph p F C v
    intro hvC
    exact hnot ((L.large_mem_observers c ⟨C,hC⟩).mpr ⟨v,hv,hvC⟩)
  · rw [restrictLoadTo_apply,if_neg hv]
    rfl

/-- A scalar component cannot have no hypervertex observer and at most
one large-body observer. All premises here name actual observers of
actual nonzero edge functionals. -/
theorem SoftScalarSystem.not_unobserved_except_one_body
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hpin : PairPinGraph.UniversalPinGeneric (Body M.graph) p)
    (c : L.graph.ConnectedComponent) (D : Body M.graph)
    (hhyper : ∀ h : Hypervertex M.graph, Sum.inl h ∉ L.observers c)
    (hlarge : ∀ C : LargeBody M.graph, C.val ≠ D → Sum.inr C ∉ L.observers c) :
    False := by
  obtain ⟨v,hvc⟩ := c.exists_rep
  obtain ⟨s,hs⟩ := exists_normalized_linear_functional (L.scalar v) (L.scalar_ne_zero v)
  obtain ⟨a,ha⟩ := copiedToStress_surjective M.graph M.covered p Finset.univ s
  let F := copiedToLoads M.graph p Finset.univ a
  have hother (C : Body M.graph) (hCD : C ≠ D) :
      restrictLoadTo (L.vertices c) (F.val C).val ∈ balancedLoads p := by
    by_cases hC : C.val.card = 4
    · change (fun w => if w ∈ L.vertices c then
          forceOperator (cliqueOn (C.val ∩ Finset.univ)) p
            (bodyCopyRestriction M.graph Finset.univ C a.val) w else 0) ∈ balancedLoads p
      exact restricted_force_balanced _ p (L.vertices c) _
        (L.tetrahedron_crossing_zero hgen hp c hhyper a C hC)
    · have hbig : 5 ≤ C.val.card := by have := C.property.1; omega
      rw [L.restricted_load_zero_of_large_unobserved c F C hbig (hlarge ⟨C,hbig⟩ hCD)]
      exact Submodule.zero_mem _
  have hbalanced (C : Body M.graph) :
      restrictLoadTo (L.vertices c) (F.val C).val ∈ balancedLoads p := by
    by_cases hCD : C = D
    · subst C
      exact balanced_restricted_load_of_all_other_bodies M.graph (L.vertices c) p F D hother
    · exact hother C hCD
  let Q : ∀ w : L.vertices c, TwoBodyPin M.graph w.val :=
    fun w => SoftPointPin.pin (⟨w.val,L.soft_of_mem_vertices c w.val w.property⟩ : SoftPointPin M.graph)
  have hQ : ∀ w, (Q w).IsPoint := fun w =>
    SoftPointPin.isPoint (⟨w.val,L.soft_of_mem_vertices c w.val w.property⟩ : SoftPointPin M.graph)
  have hzero := load_zero_on_pointPins_of_balanced_restrictions M (L.vertices c) Q hQ
    p hgen hp hpin F hbalanced v.pin.left v.val
    ((L.mem_vertices c v.val).mpr ⟨v.property,hvc⟩)
  have hforce : v.pin.pointForceOnWholePrefix v.isPoint M.covered p s = 0 := by
    rw [← ha,v.pin.pointForceOnWholePrefix_copied]
    exact hzero
  rw [L.force_eq,hs,one_smul] at hforce
  exact L.axis_ne_zero v hforce

/-- The precise observer alternative: every scalar component either
is read at a hypervertex or meets two distinct large maximal bodies. -/
theorem SoftScalarSystem.component_observer_alternative
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hpin : PairPinGraph.UniversalPinGeneric (Body M.graph) p)
    (c : L.graph.ConnectedComponent) :
    (∃ h : Hypervertex M.graph, Sum.inl h ∈ L.observers c) ∨
      ∃ C D : LargeBody M.graph, C ≠ D ∧
        Sum.inr C ∈ L.observers c ∧ Sum.inr D ∈ L.observers c := by
  by_cases hhyper : ∃ h : Hypervertex M.graph, Sum.inl h ∈ L.observers c
  · exact Or.inl hhyper
  have hnohyper : ∀ h : Hypervertex M.graph, Sum.inl h ∉ L.observers c := by
    simpa only [not_exists] using hhyper
  right
  by_contra htwo
  have heq (C D : LargeBody M.graph) (hC : Sum.inr C ∈ L.observers c)
      (hD : Sum.inr D ∈ L.observers c) : C = D := by
    by_contra hCD
    exact htwo ⟨C,D,hCD,hC,hD⟩
  by_cases hlarge : ∃ C : LargeBody M.graph, Sum.inr C ∈ L.observers c
  · obtain ⟨D,hD⟩ := hlarge
    apply L.not_unobserved_except_one_body hgen hp hpin c D.val hnohyper
    intro C hCD hC
    exact hCD (congrArg Subtype.val (heq C D hC hD))
  · obtain ⟨v,hv⟩ := c.exists_rep
    apply L.not_unobserved_except_one_body hgen hp hpin c v.pin.left hnohyper
    intro C _ hC
    exact hlarge ⟨C,hC⟩

theorem SoftScalarSystem.every_component_observed
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hpin : PairPinGraph.UniversalPinGeneric (Body M.graph) p) :
    ∀ c : L.graph.ConnectedComponent, (L.observers c).Nonempty := by
  intro c
  rcases L.component_observer_alternative hgen hp hpin c with ⟨h,hh⟩ | ⟨C,D,hCD,hC,hD⟩
  · exact ⟨Sum.inl h,hh⟩
  · exact ⟨Sum.inr C,hC⟩

/-- A component with exactly one observer has a hypervertex observer. -/
theorem SoftScalarSystem.sole_observer_is_hypervertex
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hpin : PairPinGraph.UniversalPinGeneric (Body M.graph) p)
    (c : L.graph.ConnectedComponent) (hc : (L.observers c).card = 1) :
    ∃ h : Hypervertex M.graph, L.observers c = {Sum.inl h} := by
  rcases L.component_observer_alternative hgen hp hpin c with hh | ⟨C,D,hCD,hC,hD⟩
  · obtain ⟨h,hh⟩ := hh
    exact ⟨h,Finset.eq_singleton_iff_unique_mem.mpr ⟨hh,
      fun x hx => Finset.card_le_one_iff.mp (by omega) hx hh⟩⟩
  · have heq := Finset.card_le_one_iff.mp (by omega : (L.observers c).card ≤ 1) hC hD
    exact False.elim (hCD (Sum.inr.inj heq))

/-- All actual pins in a solely observed component belong to two
bodies of order four; this is the paper's type-A conclusion. -/
theorem SoftScalarSystem.sole_observer_all_tetrahedra
    (L : SoftScalarSystem M p) (c : L.graph.ConnectedComponent)
    (h : Hypervertex M.graph) (hc : L.observers c = {Sum.inl h})
    (v : SoftPointPin M.graph) (hv : L.graph.connectedComponentMk v = c)
    (C : Body M.graph) (hvC : v.val ∈ C.val) : C.val.card = 4 := by
  have hmin := C.property.1
  by_contra hfour
  have hbig : 5 ≤ C.val.card := by omega
  have hseen : Sum.inr (⟨C,hbig⟩ : LargeBody M.graph) ∈ L.observers c :=
    (L.large_mem_observers c ⟨C,hbig⟩).mpr
      ⟨v.val,(L.mem_vertices c v.val).mpr ⟨v.property,hv⟩,hvC⟩
  simpa only [hc,Finset.mem_singleton,Sum.inr_ne_inl] using hseen

/-- The actual span U of all point-force scalar functionals. -/
def SoftScalarSystem.scalarSpan (L : SoftScalarSystem M p) :
    Submodule ℝ (Module.Dual ℝ (StressSpace (maskedGraph M.graph Finset.univ) p)) :=
  Submodule.span ℝ (Set.range L.scalar)

/-- The actual edge-coordinate dual space at the hypervertex star. -/
def SoftScalarSystem.hyperStarSpan (L : SoftScalarSystem M p) (h : Hypervertex M.graph) :
    Submodule ℝ (Module.Dual ℝ (StressSpace (maskedGraph M.graph Finset.univ) p)) :=
  Submodule.span ℝ (Set.range (stressEdgeFunctional M.graph p h.val))

def SoftScalarSystem.hyperCredit (L : SoftScalarSystem M p) (h : Hypervertex M.graph) : ℕ :=
  Module.finrank ℝ ↥(L.scalarSpan ⊓ L.hyperStarSpan h :
    Submodule ℝ (Module.Dual ℝ (StressSpace (maskedGraph M.graph Finset.univ) p)))

def SoftScalarSystem.largeRank (L : SoftScalarSystem M p) (C : LargeBody M.graph) : ℕ :=
  LinearCover.observerRank (K := ℝ) L.scalar (L.seed (Sum.inr C))

/-- Every scalar observed at h lies both in U and in the span of
actual bar-coordinate functionals at h. -/
theorem SoftScalarSystem.hyper_seed_span_le
    (L : SoftScalarSystem M p) (hp : GeneralPosition.InGeneralPosition p)
    (h : Hypervertex M.graph) :
    Submodule.span ℝ (L.scalar '' (L.seed (Sum.inl h) : Set (SoftPointPin M.graph))) ≤
      L.scalarSpan ⊓ L.hyperStarSpan h := by
  apply Submodule.span_le.mpr
  rintro x ⟨v,hv,rfl⟩
  obtain ⟨C,hC,hvC,hhC,he⟩ := (Finset.mem_filter.mp hv).2
  have hline := span_eq_of_nonzero_functional_kernel
    (L.scalar v) (stressEdgeFunctional M.graph p v.val h.val)
    (L.scalar_ne_zero v) he
    (L.scalar_kernel_le_edge_kernel hp v C hC hvC h.val hhC)
  constructor
  · exact Submodule.subset_span ⟨v,rfl⟩
  · have hm : L.scalar v ∈ ℝ ∙ stressEdgeFunctional M.graph p v.val h.val := by
      rw [← hline]
      exact Submodule.subset_span (Set.mem_singleton _)
    apply Submodule.span_mono (show
      {stressEdgeFunctional M.graph p v.val h.val} ⊆
        Set.range (stressEdgeFunctional M.graph p h.val) from ?_) hm
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    exact ⟨v.val,(stressEdgeFunctional_symm _ _ _ _).trans hz.symm⟩

theorem SoftScalarSystem.hyper_observer_rank_le
    (L : SoftScalarSystem M p) (hp : GeneralPosition.InGeneralPosition p)
    (h : Hypervertex M.graph) :
    LinearCover.observerRank (K := ℝ) L.scalar (L.seed (Sum.inl h)) ≤ L.hyperCredit h :=
  Submodule.finrank_mono (L.hyper_seed_span_le hp h)

/-- Proposition 6.6 for the actual stress code and actual observers.
The exceptional count is exactly the number of components with one
observer; the preceding theorem proves that observer is a hypervertex. -/
theorem SoftScalarSystem.proposition_six_six
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hpin : PairPinGraph.UniversalPinGeneric (Body M.graph) p) :
    2 * Module.finrank ℝ L.scalarSpan ≤
      (∑ h : Hypervertex M.graph, L.hyperCredit h) +
      (∑ C : LargeBody M.graph, L.largeRank C) +
      ObserverCover.exceptionalCount L.graph L.seed := by
  have h := ObserverCover.rank_bound_with_exceptional_components
    L.graph L.scalar L.seed (L.edge_identifies_scalars hp)
    (L.every_component_observed hgen hp hpin)
  rw [Fintype.sum_sum_type] at h
  change 2 * Module.finrank ℝ L.scalarSpan ≤ _ at h
  apply h.trans
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  exact Finset.sum_le_sum (fun h _ => L.hyper_observer_rank_le hp h)

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0007

section BundleSource0008
/- Source: Papers/RigidityHingePrefix.lean -/






@[expose] public section

/-!
# Omitted hinge partners carry no prefix force

The compatible body-load space on a vertex prefix uses only coordinates
of that prefix. Its actual load vectors therefore transport unchanged
when an omitted vertex is moved. Varying an omitted hinge partner on
the open set of ordinary generic placements forces the retained hinge
force to lie on an open family of different lines, hence to vanish.
This supplies the omitted-partner argument in Lemmas 6.3 and 7.1
without any assumed coefficient-field descent.
-/

noncomputable section
namespace Papers.Rigidity

open BarJoint Matrix
open scoped Classical Matrix BigOperators Topology

/-- A fixed vector parallel to every line from a fixed point to a
nonempty open set is zero. -/
theorem force_eq_zero_of_parallel_on_open
    (a F : Vec3) (O : Set Vec3) (hO : IsOpen O) (hne : O.Nonempty)
    (hline : ∀ q ∈ O, F ∈ Submodule.span ℝ {a - q}) : F = 0 := by
  have hcross (q : Vec3) (hq : q ∈ O) : F ⨯₃ (a - q) = 0 := by
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hline q hq)
    rw [← hc]
    simp [map_smul]
  obtain ⟨q₀,hq₀⟩ := hne
  let U : Set Vec3 := {x | x + q₀ ∈ O}
  have hU : IsOpen U := hO.preimage (continuous_id.add continuous_const)
  have hzero : (0 : Vec3) ∈ U := by simpa only [U, Set.mem_setOf_eq, zero_add] using hq₀
  have hsub : U ⊆ ((crossProduct F).ker : Set Vec3) := by
    intro x hx
    change F ⨯₃ x = 0
    calc
      F ⨯₃ x = F ⨯₃ ((a - q₀) - (a - (x + q₀))) := by congr 1 <;> abel
      _ = 0 := by rw [map_sub, hcross q₀ hq₀, hcross (x + q₀) hx, sub_self]
  have htop : (crossProduct F).ker = ⊤ :=
    (crossProduct F).ker.eq_top_of_nonempty_interior'
      ⟨0,(hU.subset_interior_iff.mpr hsub) hzero⟩
  have hmap : crossProduct F = 0 := LinearMap.ker_eq_top.mp htop
  by_contra hF
  have hr := finrank_range_crossProduct F hF
  rw [hmap, LinearMap.range_zero] at hr
  norm_num at hr

namespace BodyLoads

variable {V : Type} [Fintype V]

/-- Balance only depends on positions where the actual load is supported. -/
theorem balanced_load_placement_congr
    (p q : Placement V 3) (T : Finset V) (F : V → Vec3)
    (hF : F ∈ balancedLoads p) (hT : ∀ w, w ∉ T → F w = 0)
    (hpq : ∀ w ∈ T, p w = q w) : F ∈ balancedLoads q := by
  rw [mem_balancedLoads_iff] at hF ⊢
  refine ⟨hF.1, ?_⟩
  calc
    (∑ w : V, q w ⨯₃ F w) = ∑ w : V, p w ⨯₃ F w := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : w ∈ T
      · rw [hpq w hw]
      · rw [hT w hw, map_zero, map_zero]
    _ = 0 := hF.2

/-- Identity on the load coordinates transports the literal compatible
prefix-load space between placements agreeing on that prefix. -/
def transportCompatibleLoadsOn
    (G : SimpleGraph V) (p q : Placement V 3) (T : Finset V)
    (hpq : ∀ w ∈ T, p w = q w) :
    compatibleBodyLoads G p T →ₗ[ℝ] compatibleBodyLoads G q T where
  toFun F := ⟨fun C => ⟨(F.val C).val,
    balanced_load_placement_congr p q T (F.val C).val (F.val C).property.1
      (fun w hw => (F.val C).property.2 w
        (fun hm => hw (Finset.mem_inter.mp hm).2)) hpq,
    (F.val C).property.2⟩, by
      rw [mem_compatibleBodyLoads_iff]
      exact (mem_compatibleBodyLoads_iff G p T F.val).mp F.property⟩
  map_add' F H := by
    apply Subtype.ext
    funext C
    apply Subtype.ext
    rfl
  map_smul' c F := by
    apply Subtype.ext
    funext C
    apply Subtype.ext
    rfl

@[simp] theorem transportCompatibleLoadsOn_apply
    (G : SimpleGraph V) (p q : Placement V 3) (T : Finset V)
    (hpq : ∀ w ∈ T, p w = q w)
    (F : compatibleBodyLoads G p T) (C : Body G) (w : V) :
    ((transportCompatibleLoadsOn G p q T hpq F).val C).val w = (F.val C).val w := rfl

/-- If the hinge partner is absent from a prefix, every compatible
prefix body load is zero at the retained two-body hinge vertex. -/
theorem TwoBodyPin.Hinge.prefix_load_zero_of_partner_not_mem
    (M : MinimalCounterexample V) {v : V} {Q : TwoBodyPin M.graph v}
    (H : Q.Hinge) (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V)
    (hpartner : H.partner ∉ T) (F : compatibleBodyLoads M.graph p T) :
    ∀ C : Body M.graph, (F.val C).val v = 0 := by
  obtain ⟨O,hO,hbase,hwindow⟩ :=
    VertexPin.exists_open_generic_general_pin_window p H.partner hgen hp
  have hleft : (F.val Q.left).val v = 0 := by
    apply force_eq_zero_of_parallel_on_open (p v) _ O hO ⟨p H.partner,hbase⟩
    intro q hq
    let p' := VertexPin.replacePlacement p H.partner q
    have hagree : ∀ w ∈ T, p w = p' w := by
      intro w hw
      have hne : w ≠ H.partner := by intro he; exact hpartner (he ▸ hw)
      simp only [p', VertexPin.replacePlacement, if_neg hne]
    let F' := transportCompatibleLoadsOn M.graph p p' T hagree F
    let A := includeCompatibleLoads M.graph p' T Finset.univ (Finset.subset_univ T) F'
    have hmem : Q.loadProjection p' A ∈ (Q.loadProjection p').range := ⟨A,rfl⟩
    rw [(H.rank_and_range M p' (hwindow q hq).1 (hwindow q hq).2).2] at hmem
    change (F.val Q.left).val v ∈ Submodule.span ℝ {p' v - p' H.partner} at hmem
    simpa only [p', VertexPin.replacePlacement, if_neg H.distinct, if_pos rfl, ite_true] using hmem
  let A := includeCompatibleLoads M.graph p T Finset.univ (Finset.subset_univ T) F
  intro C
  by_cases hvC : v ∈ C.val
  · rcases Q.exhaustive C hvC with hC | hC
    · subst C
      exact hleft
    · subst C
      have hright := Q.load_right_eq_neg_left p A
      change (F.val Q.right).val v = -(F.val Q.left).val v at hright
      rw [hright, hleft, neg_zero]
  · exact (F.val C).property.2 v (fun hm => hvC (Finset.mem_inter.mp hm).1)

/-- A full compatible load vanishing at the partner also vanishes at
this two-body hinge. This is the paired-endpoint step in Lemma 6.3. -/
theorem TwoBodyPin.Hinge.load_zero_of_partner_zero
    (M : MinimalCounterexample V) {v : V} {Q : TwoBodyPin M.graph v}
    (H : Q.Hinge) (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (F : compatibleBodyLoads M.graph p Finset.univ)
    (hpartner : ∀ C : Body M.graph, (F.val C).val H.partner = 0) :
    ∀ C : Body M.graph, (F.val C).val v = 0 := by
  let A : compatibleBodyLoads M.graph p (Finset.univ.erase H.partner) :=
    ⟨fun C => ⟨(F.val C).val, (F.val C).property.1, by
      intro w hw
      by_cases he : w = H.partner
      · subst w
        exact hpartner C
      · apply (F.val C).property.2 w
        intro hm
        exact hw (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hm).1,
          Finset.mem_erase.mpr ⟨he,Finset.mem_univ w⟩⟩)⟩, by
      rw [mem_compatibleBodyLoads_iff]
      exact (mem_compatibleBodyLoads_iff M.graph p Finset.univ F.val).mp F.property⟩
  exact H.prefix_load_zero_of_partner_not_mem M p hgen hp
    (Finset.univ.erase H.partner) (Finset.notMem_erase _ _) A

end BodyLoads
end Papers.Rigidity

end
end
end BundleSource0008

section BundleSource0009
/- Source: Papers/RigidityHingeElimination.lean -/




@[expose] public section

/-!
# Simultaneous elimination of all two-body hinge loads

This is Lemma 6.3 for the literal compatible-load and duplicate-load
spaces. A finite induction uses the omitted-partner result: if a hinge
partner has already been normalized, the new hinge is already zero.
Otherwise its duplicate edge mode changes none of the previous zeros.
No combinatorial disjointness assumption is required.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

theorem eliminate_hinge_loads_on_finset
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (S : Finset V)
    (hS : ∀ v ∈ S, ∃ Q : TwoBodyPin M.graph v, Nonempty Q.Hinge)
    (F : compatibleBodyLoads M.graph p Finset.univ) :
    ∃ A : compatibleBodyLoads M.graph p Finset.univ,
      F - A ∈ duplicateCompatibleLoads M.graph p Finset.univ ∧
      ∀ v ∈ S, ∀ C : Body M.graph, (A.val C).val v = 0 := by
  revert hS
  induction S using Finset.induction_on with
  | empty =>
      intro hS
      refine ⟨F, ?_, ?_⟩
      · have hzero : F - F = (0 : compatibleBodyLoads M.graph p Finset.univ) := sub_self F
        exact hzero.symm ▸ (duplicateCompatibleLoads M.graph p Finset.univ).zero_mem
      · simp
  | @insert v S hv ih =>
      intro hS
      obtain ⟨Q,⟨H⟩⟩ := hS v (Finset.mem_insert_self v S)
      obtain ⟨A,hFA,hkill⟩ := ih
        (fun w hw => hS w (Finset.mem_insert_of_mem hw))
      by_cases hvzero : ∀ C : Body M.graph, (A.val C).val v = 0
      · refine ⟨A,hFA,?_⟩
        intro w hw C
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hvzero C
        · exact hkill w hw C
      · have hpartner : H.partner ∉ S := by
          intro hw
          exact hvzero (H.load_zero_of_partner_zero M p hgen hp A (hkill H.partner hw))
        obtain ⟨c,hvkill,hkeep⟩ := H.eliminate_load M p hgen hp A
        refine ⟨A - c • H.mode p, ?_, ?_⟩
        · have heq : F - (A - c • H.mode p) = (F - A) + c • H.mode p := by abel
          rw [heq]
          exact (duplicateCompatibleLoads M.graph p Finset.univ).add_mem hFA
            ((duplicateCompatibleLoads M.graph p Finset.univ).smul_mem c (H.mode_mem_duplicates p))
        · intro w hw C
          by_cases hwv : w = v
          · subst w
            exact congrFun hvkill C
          · have hwS : w ∈ S := (Finset.mem_insert.mp hw).resolve_left hwv
            have hwp : w ≠ H.partner := by intro he; exact hpartner (he ▸ hwS)
            rw [hkeep w hwv hwp C, hkill w hwS C]

/-- Every actual compatible load can be adjusted by actual duplicate
edge modes to kill all two-body hinge vertices simultaneously. -/
theorem exists_hinge_normalized_load
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (F : compatibleBodyLoads M.graph p Finset.univ) :
    ∃ A : compatibleBodyLoads M.graph p Finset.univ,
      F - A ∈ duplicateCompatibleLoads M.graph p Finset.univ ∧
      ∀ (v : V) (Q : TwoBodyPin M.graph v) (_ : Q.Hinge),
        ∀ C : Body M.graph, (A.val C).val v = 0 := by
  let S := Finset.univ.filter fun v => ∃ Q : TwoBodyPin M.graph v, Nonempty Q.Hinge
  obtain ⟨A,hA,hkill⟩ := eliminate_hinge_loads_on_finset M p hgen hp S
    (fun v hv => (Finset.mem_filter.mp hv).2) F
  refine ⟨A,hA,?_⟩
  intro v Q H C
  exact hkill v (Finset.mem_filter.mpr ⟨Finset.mem_univ v,Q,⟨H⟩⟩) C

/-- Lemma 6.3, including preservation of every actual point-pin force.
Soft point pins are included without requiring a finite virtual center. -/
theorem hinge_normalization_preserves_point_loads
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (F : compatibleBodyLoads M.graph p Finset.univ) :
    ∃ A : compatibleBodyLoads M.graph p Finset.univ,
      F - A ∈ duplicateCompatibleLoads M.graph p Finset.univ ∧
      (∀ (v : V) (Q : TwoBodyPin M.graph v) (_ : Q.Hinge),
        ∀ C : Body M.graph, (A.val C).val v = 0) ∧
      ∀ (v : V) (Q : TwoBodyPin M.graph v), Q.IsPoint →
        ∀ C : Body M.graph, (A.val C).val v = (F.val C).val v := by
  obtain ⟨A,hA,hkill⟩ := exists_hinge_normalized_load M p hgen hp F
  refine ⟨A,hA,hkill,?_⟩
  intro v Q hQ C
  have hz := hQ.duplicates_zero M.covered p (F - A).val hA C
  change (F.val C).val v - (A.val C).val v = 0 at hz
  exact (sub_eq_zero.mp hz).symm

/-- Changing an actual compatible load by a duplicate load can be
lifted to copied coefficients without changing its ordinary stress.
This is the concrete adjustment behind the quotient isomorphism. -/
theorem exists_copied_adjustment_of_duplicate_difference
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (a : compatibleCopiedCoefficients G p T)
    (A : compatibleBodyLoads G p T)
    (hA : copiedToLoads G p T a - A ∈ duplicateCompatibleLoads G p T) :
    ∃ b : compatibleCopiedCoefficients G p T,
      copiedToStress G p T b = copiedToStress G p T a ∧
      copiedToLoads G p T b = A := by
  rw [← kernel_stress_image_eq_duplicates G p T] at hA
  obtain ⟨d,hd,hload⟩ := hA
  refine ⟨a - d,?_,?_⟩
  · rw [map_sub,LinearMap.mem_ker.mp hd,sub_zero]
  · rw [map_sub,hload]
    abel

/-- Every actual copied stress has a representative of the same ordinary
stress whose loads vanish at all two-body hinge vertices. -/
theorem exists_hinge_normalized_copied_coefficients
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (a : compatibleCopiedCoefficients M.graph p Finset.univ) :
    ∃ b : compatibleCopiedCoefficients M.graph p Finset.univ,
      copiedToStress M.graph p Finset.univ b = copiedToStress M.graph p Finset.univ a ∧
      ∀ (v : V) (Q : TwoBodyPin M.graph v) (_ : Q.Hinge),
        ∀ C : Body M.graph,
          ((copiedToLoads M.graph p Finset.univ b).val C).val v = 0 := by
  obtain ⟨A,hA,hkill⟩ := exists_hinge_normalized_load M p hgen hp
    (copiedToLoads M.graph p Finset.univ a)
  obtain ⟨b,hstress,hload⟩ := exists_copied_adjustment_of_duplicate_difference
    M.graph p Finset.univ a A hA
  exact ⟨b,hstress,by simpa only [hload] using hkill⟩

theorem normalized_load_zero_at_nonsoft_nonhyper
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (A : compatibleBodyLoads M.graph p Finset.univ)
    (hhinge : ∀ (v : V) (Q : TwoBodyPin M.graph v) (_ : Q.Hinge),
      ∀ C : Body M.graph, (A.val C).val v = 0)
    (v : V) (hsoft : ¬ IsSoftPointPin M.graph v) (hhyper : ¬ IsHypervertex M.graph v) :
    ∀ C : Body M.graph, (A.val C).val v = 0 := by
  obtain ⟨Q⟩ := nonempty_twoBodyPin_of_not_hypervertex M v hhyper
  rcases Q.point_or_hinge with hQ | hHingeExists
  · have hδ : deletionRankDrop M.graph v ≠ 5 := fun h => hsoft ⟨Q,hQ,h⟩
    have hz : Q.loadProjection p A = 0 := by
      rw [Q.loadProjection_eq_zero_of_drop_ne_five M p hgen hp hδ,LinearMap.zero_apply]
    have hk : A ∈ (vertexLoadProjection M.graph p v).ker := by
      rw [← Q.ker_loadProjection p,LinearMap.mem_ker]
      exact hz
    intro C
    exact congrFun (LinearMap.mem_ker.mp hk) C
  · exact hhinge v Q (Classical.choice hHingeExists)

/-- A normalized body with no soft point pin and at most one
hypervertex has zero load everywhere. Balance kills the possibly
remaining force at that one vertex. No local-stress claim is assumed. -/
theorem normalized_load_zero_on_body_with_at_most_one_hypervertex
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (A : compatibleBodyLoads M.graph p Finset.univ)
    (hhinge : ∀ (v : V) (Q : TwoBodyPin M.graph v) (_ : Q.Hinge),
      ∀ C : Body M.graph, (A.val C).val v = 0)
    (C : Body M.graph) (h : V)
    (hsoft : ∀ v ∈ C.val, ¬ IsSoftPointPin M.graph v)
    (hhyper : ∀ v ∈ C.val, IsHypervertex M.graph v → v = h) :
    (A.val C).val = 0 := by
  have haway (w : V) (hwh : w ≠ h) : (A.val C).val w = 0 := by
    by_cases hwC : w ∈ C.val
    · exact normalized_load_zero_at_nonsoft_nonhyper M p hgen hp A hhinge w
        (hsoft w hwC) (fun hw => hwh (hhyper w hwC hw)) C
    · exact compatible_load_zero_outside_body M.graph p A C w hwC
  have hsum := ((mem_balancedLoads_iff p (A.val C).val).mp (A.val C).property.1).1
  have heq : (∑ w : V, (A.val C).val w) = (A.val C).val h := by
    apply Finset.sum_eq_single h
    · intro w _ hwh
      exact haway w hwh
    · simp
  have hh : (A.val C).val h = 0 := heq.symm.trans hsum
  funext w
  by_cases hwh : w = h
  · simpa only [hwh,Pi.zero_apply] using hh
  · exact haway w hwh

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0009

section BundleSource0010
/- Source: Papers/RigidityCoefficientRank.lean -/






@[expose] public section

/-!
# The dimension of a coefficient-defined twist space

The span of any family of six-coordinate twists has the same dimension
over its coefficient field as its real scalar extension.  This is the
field-of-definition bridge in Lemma 3.4.  The statement compares ordinary
submodule spans and uses the injectivity of a field's algebra map into
the real numbers; it contains no rank or independence assumption.
-/

namespace Papers.Rigidity

noncomputable section

open Matrix
open scoped Matrix

/-- Six twist coordinates as one finite coordinate vector. -/
def twistCoordinateEquiv (K : Type*) [Field K] :
    CoefficientTwist K ≃ₗ[K] ((Fin 3 ⊕ Fin 3) → K) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin 3) (Fin 3) K K).symm

theorem finrank_coefficientTwistSpan {K I : Type*} [Field K] [Algebra K ℝ]
    (X : I → CoefficientTwist K) :
    Module.finrank ℝ (coefficientTwistSpan X) =
      Module.finrank K (Submodule.span K (Set.range X)) := by
  let eK := twistCoordinateEquiv K
  let eR := twistCoordinateEquiv ℝ
  have hK : Module.finrank K (Submodule.span K (Set.range X)) =
      Module.finrank K (Submodule.span K (Set.range fun i => eK (X i))) := by
    have h := (Submodule.equivMapOfInjective eK.toLinearMap eK.injective
      (Submodule.span K (Set.range X))).finrank_eq
    have hs : (Submodule.span K (Set.range X)).map eK.toLinearMap =
        Submodule.span K (Set.range fun i => eK (X i)) :=
      (Submodule.map_span eK.toLinearMap (Set.range X)).trans
        (congrArg (Submodule.span K) (Set.range_comp' (fun x => eK x) X).symm)
    exact h.trans (congrArg
      (fun W : Submodule K ((Fin 3 ⊕ Fin 3) → K) => Module.finrank K W) hs)
  have hR : Module.finrank ℝ (coefficientTwistSpan X) =
      Module.finrank ℝ (Submodule.span ℝ
        (Set.range fun i => eR (realTwist (X i)))) := by
    have h := (Submodule.equivMapOfInjective eR.toLinearMap eR.injective
      (Submodule.span ℝ (Set.range fun i => realTwist (X i)))).finrank_eq
    have hs : (Submodule.span ℝ (Set.range fun i => realTwist (X i))).map eR.toLinearMap =
        Submodule.span ℝ (Set.range fun i => eR (realTwist (X i))) :=
      (Submodule.map_span eR.toLinearMap (Set.range fun i => realTwist (X i))).trans
        (congrArg (Submodule.span ℝ)
          (Set.range_comp' (fun x => eR x) (fun i => realTwist (X i))).symm)
    exact h.trans (congrArg
      (fun W : Submodule ℝ ((Fin 3 ⊕ Fin 3) → ℝ) => Module.finrank ℝ W) hs)
  have hmap : (fun i => RB31E2E.FiniteFamilyBaseChange.mapVector (K := ℝ) (eK (X i))) =
      (fun i => eR (realTwist (X i))) := by
    funext i j
    cases j <;> rfl
  have hbase := RB31E2E.FiniteFamilyBaseChange.finrank_span_range_mapVector
    (K := ℝ) (fun i => eK (X i))
  rw [hmap] at hbase
  exact hR.trans (hbase.symm.trans hK.symm)

/-- A homogeneous system with finitely many coordinates has a nonzero
solution over the coefficient field whenever it has one over a field
extension.  The family of equations itself may be infinite. -/
theorem exists_nonzero_kernel_over_coefficient_field
    {K L I J : Type*} [Field K] [Field L] [Algebra K L] [Fintype J]
    (a : I → J → K) (x : J → L) (hx : x ≠ 0)
    (hax : ∀ i, (fun j => algebraMap K L (a i j)) ⬝ᵥ x = 0) :
    ∃ y : J → K, y ≠ 0 ∧ ∀ i, a i ⬝ᵥ y = 0 := by
  classical
  let UK := Submodule.span K (Set.range a)
  let aL : I → J → L := fun i j => algebraMap K L (a i j)
  let UL := Submodule.span L (Set.range aL)
  have hUL : UL ≠ ⊤ := by
    have hle : UL ≤ (dotProductBilin L L x).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change x ⬝ᵥ aL i = 0
      exact (dotProduct_comm x (aL i)).trans (hax i)
    intro htop
    apply hx
    ext j
    have hj : Pi.single j (1 : L) ∈ UL := by rw [htop]; trivial
    have hz := hle hj
    change x ⬝ᵥ Pi.single j (1 : L) = 0 at hz
    simpa using hz
  have hbase : Module.finrank K UK = Module.finrank L UL :=
    RB31E2E.FiniteFamilyBaseChange.finrank_span_range_mapVector (K := L) a
  have hUK : UK ≠ ⊤ := by
    intro htop
    apply hUL
    apply Submodule.eq_of_le_of_finrank_eq le_top
    calc
      Module.finrank L UL = Module.finrank K UK := hbase.symm
      _ = Module.finrank K (⊤ : Submodule K (J → K)) :=
        congrArg (fun W : Submodule K (J → K) => Module.finrank K W) htop
      _ = Fintype.card J :=
        (finrank_top K (J → K)).trans (Module.finrank_fintype_fun_eq_card K)
      _ = Module.finrank L (⊤ : Submodule L (J → L)) := by simp
  obtain ⟨f, hf, hzero⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hUK) inferInstance
  let y := (dotProductEquiv K J).symm f
  have hy : y ≠ 0 := by
    intro hy
    have h := (dotProductEquiv K J).apply_symm_apply f
    rw [show (dotProductEquiv K J).symm f = 0 from hy, map_zero] at h
    exact hf h.symm
  refine ⟨y, hy, ?_⟩
  intro i
  have hz : f (a i) ∈ UK.map f :=
    Submodule.mem_map.mpr ⟨a i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  rw [hzero, Submodule.mem_bot] at hz
  have he : (dotProductEquiv K J) y = f :=
    (dotProductEquiv K J).apply_symm_apply f
  have hi := congrArg (fun g : Module.Dual K (J → K) => g (a i)) he
  change y ⬝ᵥ a i = f (a i) at hi
  exact (dotProduct_comm (a i) y).trans (hi.trans hz)

end

end Papers.Rigidity

end
end BundleSource0010

section BundleSource0011
/- Source: Papers/RigidityAlternatingForms.lean -/



@[expose] public section

/-!
# Explicit four-dimensional alternating coordinates for Euclidean twists

All matrix and contraction formulas are proved from the literal entries.
-/

namespace Papers.Rigidity

open Matrix
open scoped Matrix

abbrev HomogeneousPoint := Vec3 × ℝ

def homogeneousVector (q : HomogeneousPoint) : Fin 4 → ℝ :=
  ![q.1 0, q.1 1, q.1 2, q.2]

/-- The standard homogeneous-coordinate identification is linear. -/
def homogeneousVectorLinear : HomogeneousPoint →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun := homogeneousVector
  map_add' q r := by
    ext i
    fin_cases i <;> rfl
  map_smul' c q := by
    ext i
    fin_cases i <;> rfl

theorem homogeneousVectorLinear_injective : Function.Injective homogeneousVectorLinear := by
  intro q r h
  apply Prod.ext
  · ext i
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 1
    · exact congrFun h 2
  · exact congrFun h 3

/-- The alternating matrix representing an actual Euclidean twist. -/
def twistMatrix (X : Twist) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -X.1 2, X.1 1, X.2 0;
     X.1 2, 0, -X.1 0, X.2 1;
     -X.1 1, X.1 0, 0, X.2 2;
     -X.2 0, -X.2 1, -X.2 2, 0]

theorem twistMatrix_transpose (X : Twist) : (twistMatrix X)ᵀ = -twistMatrix X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twistMatrix]

/-- Every alternating form is represented by exactly one six-coordinate twist. -/
theorem existsUnique_twistMatrix
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : Mᵀ = -M) :
    ∃! X : Twist, M = twistMatrix X := by
  have he (i j : Fin 4) : M j i = -M i j := by
    simpa using congrFun (congrFun hM i) j
  have h00 := he 0 0
  have h11 := he 1 1
  have h22 := he 2 2
  have h33 := he 3 3
  have h01 := he 0 1
  have h02 := he 0 2
  have h03 := he 0 3
  have h12 := he 1 2
  have h13 := he 1 3
  have h23 := he 2 3
  refine ⟨(![-M 1 2, M 0 2, -M 0 1], ![M 0 3, M 1 3, M 2 3]), ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [twistMatrix] <;> linarith
  · intro X hX
    have hω0 := congrFun (congrFun hX 1) 2
    have hω1 := congrFun (congrFun hX 0) 2
    have hω2 := congrFun (congrFun hX 0) 1
    have ht0 := congrFun (congrFun hX 0) 3
    have ht1 := congrFun (congrFun hX 1) 3
    have ht2 := congrFun (congrFun hX 2) 3
    simp [twistMatrix] at hω0 hω1 hω2 ht0 ht1 ht2
    apply Prod.ext
    · ext i
      fin_cases i <;> simp <;> linarith
    · ext i
      fin_cases i <;> simp <;> linarith

/-- The full vector space of alternating four-by-four real matrices. -/
def alternatingMatrixSpace : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) where
  carrier := {M | Mᵀ = -M}
  zero_mem' := by simp
  add_mem' := by
    intro M N hM hN
    simp only [Set.mem_setOf_eq] at hM hN ⊢
    rw [Matrix.transpose_add, hM, hN, neg_add]
  smul_mem' := by
    intro c M hM
    simp only [Set.mem_setOf_eq] at hM ⊢
    rw [Matrix.transpose_smul, hM, smul_neg]

def twistMatrixLinear : Twist →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℝ where
  toFun := twistMatrix
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twistMatrix] <;> ring
  map_smul' c X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twistMatrix]

def twistInAlternatingMatrices : Twist →ₗ[ℝ] alternatingMatrixSpace :=
  twistMatrixLinear.codRestrict alternatingMatrixSpace twistMatrix_transpose

theorem twistInAlternatingMatrices_bijective : Function.Bijective twistInAlternatingMatrices := by
  constructor
  · intro X Y hXY
    have h : twistMatrix X = twistMatrix Y := congrArg Subtype.val hXY
    have h01 := congrFun (congrFun h 0) 1
    have h02 := congrFun (congrFun h 0) 2
    have h12 := congrFun (congrFun h 1) 2
    have h03 := congrFun (congrFun h 0) 3
    have h13 := congrFun (congrFun h 1) 3
    have h23 := congrFun (congrFun h 2) 3
    simp [twistMatrix] at h01 h02 h12 h03 h13 h23
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [h01, h02, h12]
    · ext i
      fin_cases i <;> simp [h03, h13, h23]
  · intro M
    obtain ⟨X, hX, _⟩ := existsUnique_twistMatrix M.val M.property
    exact ⟨X, Subtype.ext hX.symm⟩

/-- A genuine linear equivalence, so dimension and linear subspaces transport
between twists and all alternating forms without losing mathematical content. -/
noncomputable def twistAlternatingEquiv : Twist ≃ₗ[ℝ] alternatingMatrixSpace :=
  LinearEquiv.ofBijective twistInAlternatingMatrices twistInAlternatingMatrices_bijective

theorem finrank_alternatingMatrixSpace : Module.finrank ℝ alternatingMatrixSpace = 6 := by
  rw [← twistAlternatingEquiv.finrank_eq, finrank_twist]

/-- Contraction of the alternating form with a homogeneous point. -/
def homogeneousEvaluation (q : HomogeneousPoint) : Twist →ₗ[ℝ] HomogeneousPoint :=
  ((q.2 • LinearMap.snd ℝ Vec3 Vec3) +
    ((crossProduct (R := ℝ)).flip q.1).comp (LinearMap.fst ℝ Vec3 Vec3)).prod
    (-((dotProductBilin ℝ ℝ q.1).comp (LinearMap.snd ℝ Vec3 Vec3)))

@[simp] theorem homogeneousEvaluation_apply (q : HomogeneousPoint) (X : Twist) :
    homogeneousEvaluation q X = (q.2 • X.2 + X.1 ⨯₃ q.1, -(q.1 ⬝ᵥ X.2)) := by
  simp [homogeneousEvaluation]

theorem twistMatrix_mulVec (q : HomogeneousPoint) (X : Twist) :
    twistMatrix X *ᵥ homogeneousVector q = homogeneousVector (homogeneousEvaluation q X) := by
  ext i
  fin_cases i <;>
    simp [twistMatrix, homogeneousVector, homogeneousEvaluation_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, cross_apply,
      Matrix.vecHead, Matrix.vecTail, smul_eq_mul] <;> ring

def homogeneousCenterSpace (q : HomogeneousPoint) : Submodule ℝ Twist :=
  (homogeneousEvaluation q).ker

theorem homogeneousCenterSpace_finite (a : Vec3) :
    homogeneousCenterSpace (a, 1) = finiteCenterSpace a := by
  ext X
  constructor
  · intro hX
    have ht := congrArg Prod.fst hX
    simpa [homogeneousEvaluation_apply, finiteCenterSpace, LinearMap.mem_ker] using ht
  · intro hX
    have he : X.2 + X.1 ⨯₃ a = 0 := hX
    have ht : X.2 = -(X.1 ⨯₃ a) := eq_neg_of_add_eq_zero_left he
    change homogeneousEvaluation (a, 1) X = 0
    apply Prod.ext
    · simpa using he
    · simp [homogeneousEvaluation_apply, ht]

theorem homogeneousCenterSpace_infinite (d : Vec3) :
    homogeneousCenterSpace (d, 0) = infiniteCenterSpace d := by
  ext X
  simp [homogeneousCenterSpace, LinearMap.mem_ker, homogeneousEvaluation_apply,
    infiniteCenterSpace, Prod.ext_iff, dotProduct_comm]

theorem homogeneousCenterSpace_normalize (q : HomogeneousPoint) (hs : q.2 ≠ 0) :
    homogeneousCenterSpace q = finiteCenterSpace (q.2⁻¹ • q.1) := by
  ext X
  constructor
  · intro hX
    have ht : q.2 • X.2 + X.1 ⨯₃ q.1 = 0 := congrArg Prod.fst hX
    have he : q.2 • (X.2 + X.1 ⨯₃ (q.2⁻¹ • q.1)) = 0 := by
      rw [smul_add, map_smul, smul_smul, mul_inv_cancel₀ hs, one_smul]
      exact ht
    exact (smul_eq_zero.mp he).resolve_left hs
  · intro hX
    have he : X.2 + X.1 ⨯₃ (q.2⁻¹ • q.1) = 0 := hX
    have ht : X.2 = -(X.1 ⨯₃ (q.2⁻¹ • q.1)) := eq_neg_of_add_eq_zero_left he
    change homogeneousEvaluation q X = 0
    apply Prod.ext
    · change q.2 • X.2 + X.1 ⨯₃ q.1 = 0
      have h := congrArg (fun v : Vec3 => q.2 • v) he
      simpa only [smul_add, map_smul, smul_smul, mul_inv_cancel₀ hs, one_smul,
        smul_zero] using h
    · simp [homogeneousEvaluation_apply, ht]

/-- The center space is literally the kernel of contraction of its
alternating matrices with the stated nonprojectivized homogeneous point. -/
theorem mem_homogeneousCenterSpace_iff_matrix_kernel
    (q : HomogeneousPoint) (X : Twist) :
    X ∈ homogeneousCenterSpace q ↔ twistMatrix X *ᵥ homogeneousVector q = 0 := by
  rw [homogeneousCenterSpace, LinearMap.mem_ker, twistMatrix_mulVec]
  constructor
  · intro h
    rw [h]
    exact map_zero homogeneousVectorLinear
  · intro h
    apply homogeneousVectorLinear_injective
    exact h.trans (map_zero homogeneousVectorLinear).symm

/-- The fourth component of an alternating contraction at `(p,1)` is
determined by the three ordinary velocity components. -/
def pinVelocityGraph (p : Vec3) : Vec3 →ₗ[ℝ] HomogeneousPoint :=
  (LinearMap.id : Vec3 →ₗ[ℝ] Vec3).prod (-(dotProductBilin ℝ ℝ p))

theorem pinVelocityGraph_injective (p : Vec3) : Function.Injective (pinVelocityGraph p) := by
  intro x y h
  exact congrArg Prod.fst h

theorem homogeneousEvaluation_finite_eq_graph (p : Vec3) :
    homogeneousEvaluation (p, 1) = (pinVelocityGraph p).comp (evaluateTwist p) := by
  apply LinearMap.ext
  intro X
  apply Prod.ext
  · simp [homogeneousEvaluation_apply, pinVelocityGraph, evaluateTwist_apply]
  · simp [homogeneousEvaluation_apply, pinVelocityGraph, evaluateTwist_apply,
      dotProduct_add]

/-- Restricting to the affine chart loses no contraction rank. -/
theorem homogeneousEvaluation_finite_rank (W : Submodule ℝ Twist) (p : Vec3) :
    Module.finrank ℝ ((homogeneousEvaluation (p, 1)).comp W.subtype).range =
      Module.finrank ℝ (restrictEvaluation W p).range := by
  rw [homogeneousEvaluation_finite_eq_graph, LinearMap.comp_assoc,
    LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective (pinVelocityGraph p)
    (pinVelocityGraph_injective p) (restrictEvaluation W p).range).finrank_eq.symm

/-- Literal four-coordinate matrix contraction on a space of alternating
forms, expressed through the proved twist/alternating linear equivalence. -/
def matrixPinContraction (W : Submodule ℝ Twist) (p : Vec3) :
    W →ₗ[ℝ] (Fin 4 → ℝ) :=
  homogeneousVectorLinear.comp ((homogeneousEvaluation (p, 1)).comp W.subtype)

theorem matrixPinContraction_apply (W : Submodule ℝ Twist) (p : Vec3) (X : W) :
    matrixPinContraction W p X = twistMatrix X.val *ᵥ homogeneousVector (p, 1) :=
  (twistMatrix_mulVec (p, 1) X.val).symm

/-- The three-velocity rank hypothesis is exactly the paper's
four-coordinate alternating-contraction rank hypothesis. -/
theorem matrixPinContraction_rank (W : Submodule ℝ Twist) (p : Vec3) :
    Module.finrank ℝ (matrixPinContraction W p).range =
      Module.finrank ℝ (restrictEvaluation W p).range := by
  rw [matrixPinContraction, LinearMap.range_comp]
  rw [← (Submodule.equivMapOfInjective homogeneousVectorLinear
    homogeneousVectorLinear_injective
    ((homogeneousEvaluation (p, 1)).comp W.subtype).range).finrank_eq]
  exact homogeneousEvaluation_finite_rank W p

/-- The ordinary Pfaffian of a four-by-four alternating matrix in the
ordered basis `0,1,2,3`. -/
def pfaffianFour (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  M 0 1 * M 2 3 - M 0 2 * M 1 3 + M 0 3 * M 1 2

/-- The sparse null-difference equation used by Zheng is the Pfaffian
in twist coordinates, up to the harmless sign fixed by the basis order. -/
theorem pfaffianFour_twistMatrix (X : Twist) :
    pfaffianFour (twistMatrix X) = -(X.1 ⬝ᵥ X.2) := by
  simp [pfaffianFour, twistMatrix, dotProduct, Fin.sum_univ_succ]
  ring

/-- Compatibility at an actual point forces the relative Pfaffian to vanish. -/
theorem pfaffianFour_eq_zero_of_evaluateTwist_eq_zero (X : Twist) (p : Vec3)
    (h : evaluateTwist p X = 0) : pfaffianFour (twistMatrix X) = 0 := by
  have ht : X.2 = -(X.1 ⨯₃ p) := eq_neg_of_add_eq_zero_left h
  rw [pfaffianFour_twistMatrix, ht]
  simp

end Papers.Rigidity

end
end BundleSource0011

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined07/block_0011/Consolidated/RigidityCombined07.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined07/checkpoint_0011.json"
