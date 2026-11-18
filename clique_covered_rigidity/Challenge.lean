module
public import Mathlib

@[expose] public section
/-!
# Six-connected K4-covered graphs are rigid in three dimensions

This statement records manuscript Theorem 1.1, both parts of Corollary 1.2,
the sharpness assertion, and all three clauses of Theorem 5.1. Generic rigidity
means maximum rank of the actual real bar-joint rigidity operator. The pair-pin
motion space is the actual compatibility kernel modulo common Euclidean twists;
its combinatorial defect is a maximum over every partition of the body set.
All custom definitions below are copied with their original semantics from the
substantive development at e0696fddcd3d10b5d6461e62e9b2f02c4195be37.
-/
noncomputable section
open Matrix
open scoped BigOperators Matrix Classical
namespace Papers.Rigidity.BarJoint

/-- A point in real coordinate dimension d. -/
abbrev Point (d : ℕ) := Fin d → ℝ

/-- A placement of the vertices in real coordinate dimension d. -/
abbrev Placement (V : Type) (d : ℕ) := V → Point d

/-- An infinitesimal velocity assignment in real coordinate dimension d. -/
abbrev Velocity (V : Type) (d : ℕ) := V → Point d

/-- The linearized squared-length constraint at an ordered pair of vertices. -/
def edgeConstraint {V : Type} {d : ℕ}
    (p : Placement V d) (u : Velocity V d) (v w : V) : ℝ :=
  ∑ i : Fin d, (p v i - p w i) * (u v i - u w i)

/-- One bar constraint, as a real linear functional of the velocity. -/
theorem edgeConstraint_map_add {V : Type} {d : ℕ}
    (p : Placement V d) (v w : V) (u z : Velocity V d) :
    edgeConstraint p (u + z) v w = edgeConstraint p u v w + edgeConstraint p z v w := by sorry

theorem edgeConstraint_map_smul {V : Type} {d : ℕ}
    (p : Placement V d) (v w : V) (c : ℝ) (u : Velocity V d) :
    edgeConstraint p (c • u) v w = (RingHom.id ℝ) c • edgeConstraint p u v w := by sorry

def edgeFunctional {V : Type} {d : ℕ}
    (p : Placement V d) (v w : V) : Velocity V d →ₗ[ℝ] ℝ where
  toFun u := edgeConstraint p u v w
  map_add' := edgeConstraint_map_add p v w
  map_smul' := edgeConstraint_map_smul p v w

/-- The real bar-joint rigidity operator on all ordered pairs, zero on nonedges. -/
noncomputable def rigidityOperator {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) :
    Velocity V d →ₗ[ℝ] (V × V → ℝ) := by
  classical
  exact LinearMap.pi fun vw ↦
    if G.Adj vw.1 vw.2 then edgeFunctional p vw.1 vw.2 else 0

/-- The rank of the actual rigidity operator at this placement. -/
noncomputable def rigidityRank {V : Type} [Fintype V] {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) : ℕ :=
  Module.finrank ℝ (LinearMap.range (rigidityOperator G p))

/-- Existence of a real placement at which the specified rank occurs. -/
def RankIsAttained {V : Type} [Fintype V] (G : SimpleGraph V) (d r : ℕ) : Prop :=
  ∃ p : Placement V d, rigidityRank G p = r

/-- The greatest rank attained by a real placement, bounded by velocity dimension. -/
noncomputable def genericRigidityRank {V : Type} [Fintype V] (G : SimpleGraph V)
    (d : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (RankIsAttained G d)
    (Module.finrank ℝ (Velocity V d))

/-- Equality of generic rank with the complete graph on the same vertices. -/
def IsGenericallyRigidInDimension {V : Type} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  genericRigidityRank G d =
    genericRigidityRank (SimpleGraph.completeGraph V) d

/-- Generic infinitesimal rigidity in dimension three. -/
def IsGenericallyRigidInR3 {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  IsGenericallyRigidInDimension G 3

end Papers.Rigidity.BarJoint

namespace Papers.Rigidity
open BarJoint

/-- Vertex connectivity k, including order strictly greater than k. -/
def VertexConnected {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce ((S : Set V)ᶜ)).Connected

/-- Every edge lies in a complete subgraph on four vertices. -/
def K4Covered {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ v w, G.Adj v w →
    ∃ S : Finset V, S.card = 4 ∧ v ∈ S ∧ w ∈ S ∧ G.IsClique (S : Set V)

/-- Every edge lies in a generically rigid subgraph of order at least four. -/
def RigidSubgraphCovered {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ v w, G.Adj v w → ∃ S : Finset V, 4 ≤ S.card ∧
    ∃ (hv : v ∈ S) (hw : w ∈ S) (H : SimpleGraph {x : V // x ∈ S}),
      H ≤ G.induce (S : Set V) ∧ H.Adj ⟨v, hv⟩ ⟨w, hw⟩ ∧
        IsGenericallyRigidInR3 H

/-- Complete each member of a family of vertex sets on the same ambient vertices. -/
theorem clusterCompletion_symm {V I : Type} (C : I → Finset V) :
    Std.Symm (fun v w : V => v ≠ w ∧ ∃ i, v ∈ C i ∧ w ∈ C i) := by sorry

theorem clusterCompletion_loopless {V I : Type} (C : I → Finset V) :
    Std.Irrefl (fun v w : V => v ≠ w ∧ ∃ i, v ∈ C i ∧ w ∈ C i) := by sorry

def clusterCompletion {V I : Type} (C : I → Finset V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ i, v ∈ C i ∧ w ∈ C i
  symm := clusterCompletion_symm C
  loopless := clusterCompletion_loopless C

/-- All pairs of vertices in this set belong to the ambient rigidity closure. -/
def RigidCluster {V : Type} [Fintype V] (G : SimpleGraph V) (S : Finset V) : Prop :=
  genericRigidityRank (G ⊔ clusterCompletion (fun _ : Unit => S)) 3 =
    genericRigidityRank G 3

theorem sixConnected_k4Covered_rigid
    {V : Type} [Fintype V] (G : SimpleGraph V)
    (hconn : VertexConnected G 6) (hcover : K4Covered G) :
    IsGenericallyRigidInR3 G := by
  sorry

theorem sixConnected_rigidSubgraphCovered_rigid
    {V : Type} [Fintype V] (G : SimpleGraph V)
    (hconn : VertexConnected G 6) (hcover : RigidSubgraphCovered G) :
    IsGenericallyRigidInR3 G := by
  sorry

theorem rigidCluster_completion_sixConnected_rigid
    {V I : Type} [Fintype V] (G : SimpleGraph V) (C : I → Finset V)
    (hC : ∀ i, 4 ≤ (C i).card ∧ RigidCluster G (C i))
    (hconn : VertexConnected (clusterCompletion C) 6) : IsGenericallyRigidInR3 G := by
  sorry

theorem fiveConnected_k4Covered_flexible_exists :
    ∃ (V : Type) (hV : Fintype V) (G : SimpleGraph V),
      @VertexConnected V hV G 5 ∧ K4Covered G ∧
        ¬ @BarJoint.IsGenericallyRigidInR3 V hV G := by
  sorry

/-- Three-dimensional coordinate vectors over the indicated field. -/
abbrev Vec3 := Fin 3 → ℝ

/-- Angular velocity and translational velocity of a Euclidean infinitesimal motion. -/
abbrev Twist := Vec3 × Vec3

/-- Velocity at point p under the specified Euclidean infinitesimal motion. -/
def evaluateTwist (p : Vec3) : Twist →ₗ[ℝ] Vec3 :=
  LinearMap.snd ℝ Vec3 Vec3 +
    ((crossProduct (R := ℝ)).flip p).comp (LinearMap.fst ℝ Vec3 Vec3)

/-- A loopless occurrence-labelled graph of bodies and pins. -/
structure PairPinGraph (B E : Type) where
  left : E → B
  right : E → B
  loopless : ∀ e, left e ≠ right e

namespace PairPinGraph
theorem realIdentityCompTriple :
    RingHomCompTriple (RingHom.id ℝ) (RingHom.id ℝ) (RingHom.id ℝ) := by sorry

variable {B E : Type}

/-- Three coordinate rows per pin equating velocities of its two bodies. -/
def compatibilityOperator (J : PairPinGraph B E) (p : E → Vec3) :
    (B → Twist) →ₗ[ℝ] (E → Vec3) :=
  letI : RingHomCompTriple (RingHom.id ℝ) (RingHom.id ℝ) (RingHom.id ℝ) := realIdentityCompTriple
  LinearMap.pi fun e =>
    (evaluateTwist (p e)).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : B => Twist) (J.left e) -
        LinearMap.proj (R := ℝ) (φ := fun _ : B => Twist) (J.right e))

/-- Rank of the real compatibility operator at the specified pin coordinates. -/
noncomputable def pinRank [Fintype B] [Fintype E]
    (J : PairPinGraph B E) (p : E → Vec3) : ℕ :=
  Module.finrank ℝ (compatibilityOperator J p).range

/-- The greatest compatibility rank attained at real pin coordinates. -/
noncomputable def genericPinRank [Fintype B] [Fintype E]
    (J : PairPinGraph B E) : ℕ := by
  classical
  exact Nat.findGreatest (fun r => ∃ p : E → Vec3, pinRank J p = r)
    (6 * Fintype.card B)

/-- Assign the same Euclidean infinitesimal motion to every body. -/
def commonTwistMap : Twist →ₗ[ℝ] (B → Twist) :=
  LinearMap.pi fun _ => LinearMap.id

theorem commonTwist_mem_ker (J : PairPinGraph B E) (p : E → Vec3) (X : Twist) :
    commonTwistMap X ∈ (compatibilityOperator J p).ker := by sorry

/-- The common Euclidean motions as elements of the compatibility kernel. -/
def commonTwistInKernel (J : PairPinGraph B E) (p : E → Vec3) :
    Twist →ₗ[ℝ] (compatibilityOperator J p).ker :=
  commonTwistMap.codRestrict _ (commonTwist_mem_ker J p)

/-- The actual compatibility kernel modulo its subspace of common twists. -/
abbrev RelativeMotionSpace (J : PairPinGraph B E) (p : E → Vec3) :=
  (compatibilityOperator J p).ker ⧸ (commonTwistInKernel J p).range

/-- Rank capacity of a body pair with zero, one, two, or at least three pins: 0,3,5,6. -/
def pinCapacity : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 5
  | _ => 6

/-- Number of pin occurrences between two labelled partition blocks. -/
noncomputable def multiplicity [Fintype E]
    (J : PairPinGraph B E) {t : ℕ} (π : B → Fin t) (i j : Fin t) : ℕ := by
  classical
  exact (Finset.univ.filter fun e =>
    (π (J.left e) = i ∧ π (J.right e) = j) ∨
    (π (J.left e) = j ∧ π (J.right e) = i)).card

/-- Sum of pair capacities over all distinct pairs of partition blocks. -/
noncomputable def partitionCapacity [Fintype E]
    (J : PairPinGraph B E) {t : ℕ} (π : B → Fin t) : ℕ :=
  ∑ i : Fin t, ∑ j ∈ Finset.univ.filter (i < ·), pinCapacity (multiplicity J π i j)

/-- Six times the number of nonempty blocks minus one, less the partition capacity. -/
noncomputable def labelledPartitionDefect [Fintype B] [Fintype E]
    (J : PairPinGraph B E) {t : ℕ} (π : B → Fin t) : ℤ :=
  6 * (((Finset.univ.image π).card : ℤ) - 1) - (partitionCapacity J π : ℤ)

/-- Maximum integer defect over every partition of the finite body set. -/
theorem partitionDefectSet_nonempty [Fintype B] [Fintype E]
    (J : PairPinGraph B E) :
    (Finset.univ.image (fun π : B → Fin (Fintype.card B) => labelledPartitionDefect J π)).Nonempty := by sorry

noncomputable def maxPartitionDefect [Fintype B] [Fintype E]
    (J : PairPinGraph B E) : ℤ :=
  (Finset.univ.image (fun π : B → Fin (Fintype.card B) => labelledPartitionDefect J π)).max'
    (partitionDefectSet_nonempty J)

/-- The integer defect for the partition into singleton bodies. -/
noncomputable def singletonPartitionDefect [Fintype B] [Fintype E]
    (J : PairPinGraph B E) : ℤ :=
  labelledPartitionDefect J (Fintype.equivFin B)

/-- No parallel pin occurrences, as injectivity of the unordered endpoint pair. -/
def IsSimple (J : PairPinGraph B E) : Prop :=
  Function.Injective (fun e => s(J.left e, J.right e))

/-- One literal coordinate row of a pin compatibility equation. -/
def pinRow (J : PairPinGraph B E) (p : E → Vec3) (a : E × Fin 3) :
    (B → Twist) →ₗ[ℝ] ℝ :=
  letI : RingHomCompTriple (RingHom.id ℝ) (RingHom.id ℝ) (RingHom.id ℝ) := realIdentityCompTriple
  (LinearMap.proj a.2).comp ((LinearMap.proj a.1).comp (compatibilityOperator J p))

/-- Distinct bodies have distinct twists in some actual compatible motion. -/
def NoMergedAt (J : PairPinGraph B E) (p : E → Vec3) : Prop :=
  ∀ u v : B, u ≠ v → ∃ X : B → Twist,
    X ∈ (compatibilityOperator J p).ker ∧ X u ≠ X v

end PairPinGraph
end Papers.Rigidity

namespace RB31E2E
/-- Three-dimensional coordinate vectors over the indicated field. -/
abbrev Vec3 (k : Type*) := Fin 3 → k
namespace GroundedTwistPolynomial
/-- One variable for each coordinate of each pin occurrence. -/
abbrev PinVariable (E : Type*) := E × Fin 3

/-- Encode concrete pins as the assignment of all their coordinate variables. -/
def assignmentOfPins {k E : Type*} (p : E → Vec3 k) : PinVariable E → k :=
  fun ei ↦ p ei.1 ei.2

end GroundedTwistPolynomial
end RB31E2E

namespace Papers.Rigidity.PairPinGraph
open RB31E2E.GroundedTwistPolynomial
variable {B E : Type} [Fintype B] [Fintype E] [Nonempty B]

theorem defect_theorem_at_algebraicallyGeneric_pins
    (J : PairPinGraph B E) (p : E → Vec3)
    (hp : AlgebraicIndependent ℚ (assignmentOfPins p)) :
    (Module.finrank ℝ (RelativeMotionSpace J p) : ℤ) = maxPartitionDefect J ∧
      (NoMergedAt J p →
        (Module.finrank ℝ (RelativeMotionSpace J p) : ℤ) = singletonPartitionDefect J ∧
          (IsSimple J → LinearIndependent ℝ (pinRow J p))) := by
  sorry

end Papers.Rigidity.PairPinGraph
