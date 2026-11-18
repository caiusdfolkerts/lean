module
public import normal_projective

/-! Original substantive proofs under their original fully qualified names. -/

namespace PalomarNormal
attribute [local instance] RCLike.toInnerProductSpaceReal
open NormalProjective NormalProjective.CanonicalModel
open NormalProjective.CanonicalModel.Realization NormalProjective.CyclicCube
open NormalProjective.RootedGeometry NormalProjective.UnitNormalization
/-- Exact labelled unit-normal and support data of the standard cube inequalities. -/
theorem referenceCube_data (n : ℕ) :
    (referenceCube n).normal =
      (fun i => unitRow ((rootedData (RankObstruction.cyclicMatrix n 0)).1 i)) ∧
    (referenceCube n).support =
      (fun i => (rootedData (RankObstruction.cyclicMatrix n 0)).2 i /
        length ((rootedData (RankObstruction.cyclicMatrix n 0)).1 i)) := by
  exact ⟨rfl, rfl⟩
/-- Exact labelled normalization of -x_i<=0 and x_i+epsilon*x_(i+1)<=1. -/
theorem cyclicRealization_data {n : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (CyclicCube.realization (n := n) hε0 hε1).val.normal =
      (fun i => unitRow ((rootedData (RankObstruction.cyclicMatrix n ε)).1 i)) ∧
    (CyclicCube.realization (n := n) hε0 hε1).val.support =
      (fun i => (rootedData (RankObstruction.cyclicMatrix n ε)).2 i /
        length ((rootedData (RankObstruction.cyclicMatrix n ε)).1 i)) := by
  exact ⟨rfl, rfl⟩
/-- Literal total length k, permitting every induced endpoint facet labelling. -/
theorem geometricLength_iff {n : ℕ} (P : Realization (referenceCube n)) (k : ℕ) :
    CubeTargetLabels.GeometricLength P k ↔
      ∃ Q : Realization (referenceCube n), ∃ p q : ℕ,
        Q.carrier = Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) ∧
          PNWord P Q p q ∧ p + q = k := by
  rfl
/-- Distance is uniquely fixed as the least literal geometric word length. -/
theorem geometricPNDistance_isLeast {n : ℕ} (hn : 1 ≤ n)
    (P : Realization (referenceCube n)) :
    IsLeast {k : ℕ | CubeTargetLabels.GeometricLength P k}
      (CubeTargetLabels.geometricPNDistance hn P) := by
  classical
  refine ⟨CubeTargetLabels.geometricPNDistance_spec hn P, ?_⟩
  intro k hk
  exact Nat.find_min' (CubeTargetLabels.geometricLength_exists hn P) hk
end PalomarNormal
