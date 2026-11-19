module
public import normal_projective
public import Cor7SourcePolarBridge
@[expose] public section
noncomputable section

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

namespace PalomarNormalCorollary7
abbrev Space (d : ℕ) := Fin d → ℝ
abbrev Label (d : ℕ) := Fin d ⊕ Fin d
/-- The actual convex hull of all the supplied paired points. -/
def hull {d : ℕ} (v : Label d → Space d) : Set (Space d) :=
  convexHull ℝ (Set.range v)
/-- No subset contains both labels from a prescribed opposite pair. -/
def PairFree {d : ℕ} (S : Finset (Label d)) : Prop :=
  ∀ i : Fin d, ¬(Sum.inl i ∈ S ∧ Sum.inr i ∈ S)
/-- A nonempty proper exposed face of the actual convex body. -/
def ProperExposedFace {d : ℕ} (K F : Set (Space d)) : Prop :=
  F.Nonempty ∧ F ≠ K ∧
    ∃ (ℓ : Space d →ₗ[ℝ] ℝ) (a : ℝ), ℓ ≠ 0 ∧
      (∀ x ∈ K, ℓ x ≤ a) ∧ F = {x ∈ K | ℓ x = a}
/-- The exact labelled crosspolytope conclusion: all and only the displayed
vertices, with every proper face choosing at most one point from each pair. -/
def LabelledCrosspolytope {d : ℕ} (v : Label d → Space d) : Prop :=
  Function.Injective v ∧ (hull v).extremePoints ℝ = Set.range v ∧
    ∀ F : Set (Space d), ProperExposedFace (hull v) F ↔
      ∃ S : Finset (Label d), S.Nonempty ∧ PairFree S ∧
        F = convexHull ℝ (v '' (S : Set (Label d)))
/-- Corollary7, with literal full dimensionality and open paired segments.
The dimension-zero case is retained; its hypotheses are inconsistent. -/
theorem paired_segment_crosspolytope (d : ℕ) (v : Label d → Space d)
    (hfull : (interior (hull v)).Nonempty)
    (hpair : ∀ i : Fin d,
      (openSegment ℝ (v (Sum.inl i)) (v (Sum.inr i)) ∩ interior (hull v)).Nonempty) :
    LabelledCrosspolytope v := by
  classical
  cases d with
  | zero =>
    have he : hull v = ∅ := by
      simp only [hull,Set.range_eq_empty v,convexHull_empty]
    rw [he,interior_empty] at hfull
    obtain ⟨x,hx⟩ := hfull
    exact hx.elim
  | succ n =>
    refine ⟨PalomarNormalCorollary7Bridge.paired_labels_injective n v hfull hpair,
      PalomarNormalCorollary7Bridge.paired_extremePoints n v hfull hpair,?_⟩
    intro F
    constructor
    · rintro ⟨hneF,hproper,ℓ,a,hℓ,hvalid,hF⟩
      let S : Finset (Label (n+1)) := Finset.univ.filter (fun i => ℓ (v i) = a)
      have hmem (i : Label (n+1)) : i ∈ S ↔ ℓ (v i) = a := by
        simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
      have hSset : (S : Set (Label (n+1))) = {i | ℓ (v i) = a} := by
        ext i
        exact hmem i
      have hv (i : Label (n+1)) : ℓ (v i) ≤ a :=
        hvalid _ (subset_convexHull ℝ _ ⟨i,rfl⟩)
      have heq : F = convexHull ℝ (v '' (S : Set (Label (n+1)))) := by
        rw [hF,hSset]
        exact PalomarNormalCorollary7Exposure.hull_support_level v ℓ a hv
      have hne : S.Nonempty := by
        by_contra hnone
        have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
        have hzero : F = ∅ := by
          simpa only [hS,Finset.coe_empty,Set.image_empty,convexHull_empty] using heq
        exact hneF.ne_empty hzero
      refine ⟨S,hne,?_,heq⟩
      intro i hi
      have hleft : ℓ (v (Sum.inl i)) = a := (hmem _).mp hi.1
      have hright : ℓ (v (Sum.inr i)) = a := (hmem _).mp hi.2
      obtain ⟨z,hseg,hz⟩ := hpair i
      have hcont : ℓ.toContinuousLinearMap ≠ 0 := by
        intro hh
        apply hℓ
        apply LinearMap.ext
        intro x
        exact congrArg (fun f : Space (n+1) →L[ℝ] ℝ => f x) hh
      have hstrict := NormalProjective.interior_lt_support (hull v)
        ℓ.toContinuousLinearMap hcont a hvalid hz
      rw [openSegment_eq_image] at hseg
      obtain ⟨t,ht,rfl⟩ := hseg
      change ℓ ((1-t) • v (Sum.inl i) + t • v (Sum.inr i)) < a at hstrict
      simp only [map_add,map_smul,smul_eq_mul,hleft,hright] at hstrict
      nlinarith
    · rintro ⟨S,hne,hfree,rfl⟩
      obtain ⟨ℓ,a,hℓ,hle,heq⟩ :=
        PalomarNormalCorollary7Bridge.pairfree_support n v hfull hpair S hne hfree
      have hvalid : ∀ x ∈ hull v, ℓ x ≤ a := by
        apply convexHull_min _ (convex_halfSpace_le ℓ.toLinearMap.isLinear a)
        rintro x ⟨i,rfl⟩
        exact hle i
      have hSset : (S : Set (Label (n+1))) = {i | ℓ (v i) = a} := by
        ext i
        exact (heq i).symm
      have hlevel : {x ∈ hull v | ℓ x = a} =
          convexHull ℝ (v '' (S : Set (Label (n+1)))) := by
        rw [hSset]
        exact PalomarNormalCorollary7Exposure.hull_support_level v ℓ.toLinearMap a hle
      have hnonempty : (convexHull ℝ (v '' (S : Set (Label (n+1))))).Nonempty := by
        obtain ⟨i,hi⟩ := hne
        exact ⟨v i,subset_convexHull ℝ _ ⟨i,hi,rfl⟩⟩
      have hproper : convexHull ℝ (v '' (S : Set (Label (n+1)))) ≠ hull v := by
        intro hwhole
        obtain ⟨i,hi⟩ := hne
        have hm : ∃ j : Label (n+1), j ∉ S := by
          cases i with
          | inl k => exact ⟨Sum.inr k,fun hk => hfree k ⟨hi,hk⟩⟩
          | inr k => exact ⟨Sum.inl k,fun hk => hfree k ⟨hk,hi⟩⟩
        obtain ⟨j,hj⟩ := hm
        have hjK : v j ∈ hull v := subset_convexHull ℝ _ ⟨j,rfl⟩
        have hjF : v j ∈ {x ∈ hull v | ℓ x = a} := by
          rw [hlevel,hwhole]
          exact hjK
        exact hj ((heq j).mp hjF.2)
      refine ⟨hnonempty,hproper,ℓ.toLinearMap,a,?_,hvalid,hlevel.symm⟩
      intro hh
      apply hℓ
      apply ContinuousLinearMap.ext
      intro x
      exact congrArg (fun f : Space (n+1) →ₗ[ℝ] ℝ => f x) hh
end PalomarNormalCorollary7
