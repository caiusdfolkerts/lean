module

public import Recovery.Unimodular.NativePort.A3Enumeration
public import Unimodular.FanRayTransport
public import Unimodular.HellerRootLattice

@[expose] public section

set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
open TauCeti.Toric

namespace Unimodular.LiteralRootCoordinates
open Heller.TypeA TypeAFanGeometry

/-- The literal real zero-sum hyperplane containing the paper's lattice. -/
def realSumMap (n : ℕ) : Ambient (n + 1) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum]

abbrev RootSpace (n : ℕ) := LinearMap.ker (realSumMap n)

/-- Integral roots are embedded by their actual coordinatewise real casts. -/
def rootEmbedding (n : ℕ) : RootLattice n →+ RootSpace n where
  toFun z := ⟨embed z.val, by
    have hz := z.property
    change (∑ i, z.val i) = 0 at hz
    change (∑ i, ((z.val i : ℤ) : ℝ)) = 0
    exact_mod_cast hz⟩
  map_zero' := by apply Subtype.ext; ext i; simp [embed]
  map_add' z w := by apply Subtype.ext; ext i; simp [embed]

/-- The real coordinate equivalence has exactly the same leading coordinate
as the integral equivalence: minus the sum of the remaining coordinates. -/
def realCoordinateEquiv (n : ℕ) : Ambient n ≃ₗ[ℝ] RootSpace n where
  toFun x := ⟨Fin.cons (-(∑ i, x i)) x, by
    change (∑ i, Fin.cons (-(∑ j, x j)) x i) = 0
    rw [Fin.sum_univ_succ]
    simp⟩
  invFun x := fun i => x.val i.succ
  left_inv x := by ext i; rfl
  right_inv x := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h := x.property
      change (∑ k, x.val k) = 0 at h
      rw [Fin.sum_univ_succ] at h
      change -(∑ k : Fin n, x.val k.succ) = x.val 0
      linarith
    · rfl
  map_add' x y := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Finset.sum_add_distrib, add_comm]
    · rfl
  map_smul' a x := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Finset.mul_sum, mul_neg]
    · rfl

/-- Commutativity is proved for every lattice vector, not just the roots. -/
theorem coordinateCompatibility (n : ℕ) (z : Lattice n) :
    realCoordinateEquiv n (FanBridge.standardEmbedding n z) =
      rootEmbedding n (coordinateEquiv n z) := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [realCoordinateEquiv, rootEmbedding, coordinateEquiv,
      FanBridge.standardEmbedding, embed]
  · rfl

theorem rootEmbedding_isIntegralLattice (n : ℕ) :
    IsIntegralLattice (rootEmbedding n) :=
  (isIntegralLattice_congr (coordinateEquiv n).toAddEquiv
    (realCoordinateEquiv n) (coordinateCompatibility n)).mp
      (FanBridge.standardEmbedding_isIntegralLattice n)

/-- The existing edge labels enumerate literal differences e_i-e_j. -/
def literalRootFamily (n : ℕ) (e : Edge n) : RootLattice n :=
  root (vertexIndex e.val.1) (vertexIndex e.val.2)

theorem coordinate_rootFamily (n : ℕ) (e : Edge n) :
    coordinateEquiv n (rootFamily n e) = literalRootFamily n e :=
  coordinateEquiv_difference e.val.1 e.val.2

/-- All nonzero oriented roots occur, with no root omitted or added. -/
theorem range_literalRootFamily (n : ℕ) :
    Set.range (literalRootFamily n) = roots n := by
  ext z
  constructor
  · rintro ⟨e,rfl⟩
    exact ⟨vertexIndex e.val.1,vertexIndex e.val.2,
      fun h => e.property (vertexIndex_bijective.1 h),rfl⟩
  · rintro ⟨i,j,hij,rfl⟩
    obtain ⟨p,rfl⟩ := vertexIndex_bijective.2 i
    obtain ⟨q,rfl⟩ := vertexIndex_bijective.2 j
    exact ⟨⟨(p,q),fun h => hij (congrArg vertexIndex h)⟩,rfl⟩

/-- Literal paper ray condition on the real zero-sum hyperplane. -/
def HasLiteralRays {n : ℕ} (Φ : Fan (rootEmbedding n)) : Prop :=
  ∀ R : PointedCone ℝ (RootSpace n),
    (R ∈ Φ.cones ∧ Module.finrank ℝ (Submodule.span ℝ (R : Set (RootSpace n))) = 1) ↔
      ∃ i j : Fin (n + 1), i ≠ j ∧
        R = AllowedBlocks.ray (rootEmbedding n (root i j))

theorem hasLiteralRays_iff {n : ℕ} (Φ : Fan (rootEmbedding n)) :
    HasLiteralRays Φ ↔ AllowedBlocks.HasRays (rootEmbedding n) (literalRootFamily n) Φ := by
  unfold HasLiteralRays AllowedBlocks.HasRays
  apply forall_congr'
  intro R
  apply iff_congr Iff.rfl
  constructor
  · rintro ⟨i,j,hij,he⟩
    obtain ⟨p,rfl⟩ := vertexIndex_bijective.2 i
    obtain ⟨q,rfl⟩ := vertexIndex_bijective.2 j
    exact ⟨⟨(p,q),fun h => hij (congrArg vertexIndex h)⟩,he⟩
  · rintro ⟨e,he⟩
    exact ⟨vertexIndex e.val.1,vertexIndex e.val.2,
      fun h => e.property (vertexIndex_bijective.1 h),he⟩

/-- Genuine bijection on entire finite fans under the proved compatible
integral and real coordinate changes. -/
def allFansEquiv (n : ℕ) :
    Fan (FanBridge.standardEmbedding n) ≃ Fan (rootEmbedding n) :=
  FanTransport.fansEquiv (coordinateEquiv n).toAddEquiv
    (realCoordinateEquiv n) (coordinateCompatibility n)

theorem allFansEquiv_complete_iff {n : ℕ} (Φ : Fan (FanBridge.standardEmbedding n)) :
    (allFansEquiv n Φ).IsComplete ↔ Φ.IsComplete :=
  FanTransport.transport_complete_iff (coordinateEquiv n).toAddEquiv
    (realCoordinateEquiv n) (coordinateCompatibility n) Φ

theorem allFansEquiv_regular_iff {n : ℕ} (Φ : Fan (FanBridge.standardEmbedding n)) :
    (allFansEquiv n Φ).IsRegular ↔ Φ.IsRegular :=
  FanTransport.transport_regular_iff (coordinateEquiv n).toAddEquiv
    (realCoordinateEquiv n) (coordinateCompatibility n) Φ

theorem allFansEquiv_rays_iff {n : ℕ} (Φ : Fan (FanBridge.standardEmbedding n)) :
    HasLiteralRays (allFansEquiv n Φ) ↔
      AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ := by
  rw [hasLiteralRays_iff]
  apply FanTransport.hasRays_equiv_iff
    (FanTransport.equivalence (coordinateEquiv n).toAddEquiv
      (realCoordinateEquiv n) (coordinateCompatibility n) Φ)
  intro e
  change realCoordinateEquiv n (FanBridge.standardEmbedding n (rootFamily n e)) =
    rootEmbedding n (literalRootFamily n e)
  rw [coordinateCompatibility,coordinate_rootFamily]

def completeRootFansEquiv (n : ℕ) :
    {Φ : Fan (FanBridge.standardEmbedding n) // Φ.IsComplete ∧
      AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ} ≃
    {Φ : Fan (rootEmbedding n) // Φ.IsComplete ∧ HasLiteralRays Φ} :=
  Equiv.subtypeEquiv (allFansEquiv n) (fun Φ =>
    ((allFansEquiv_complete_iff Φ).and (allFansEquiv_rays_iff Φ)).symm)

def regularCompleteRootFansEquiv (n : ℕ) :
    {Φ : Fan (FanBridge.standardEmbedding n) // Φ.IsComplete ∧
      AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ ∧ Φ.IsRegular} ≃
    {Φ : Fan (rootEmbedding n) // Φ.IsComplete ∧ HasLiteralRays Φ ∧ Φ.IsRegular} :=
  Equiv.subtypeEquiv (allFansEquiv n) (fun Φ =>
    ((allFansEquiv_complete_iff Φ).and
      ((allFansEquiv_rays_iff Φ).and (allFansEquiv_regular_iff Φ))).symm)

/-- Exactly 729 actual complete fans on the twelve literal zero-sum roots.
No quotient by relabelling, simplicity, smoothness or projectivity is imposed. -/
theorem a3_literal_complete_fan_count :
    Nat.card {Φ : Fan (rootEmbedding 3) // Φ.IsComplete ∧ HasLiteralRays Φ} = 729 := by
  rw [← Nat.card_congr (completeRootFansEquiv 3)]
  exact A3FanChoices.a3_complete_fan_count

/-- Exactly 64 of those actual fans are regular in their zero-sum lattice. -/
theorem a3_literal_regular_complete_fan_count :
    Nat.card {Φ : Fan (rootEmbedding 3) // Φ.IsComplete ∧ HasLiteralRays Φ ∧ Φ.IsRegular} = 64 := by
  rw [← Nat.card_congr (regularCompleteRootFansEquiv 3)]
  exact A3RegularFanCount.a3_regular_complete_fan_count_explicit

#print axioms coordinateCompatibility
#print axioms rootEmbedding_isIntegralLattice
#print axioms range_literalRootFamily
#print axioms completeRootFansEquiv
#print axioms regularCompleteRootFansEquiv
#print axioms a3_literal_complete_fan_count
#print axioms a3_literal_regular_complete_fan_count

end Unimodular.LiteralRootCoordinates
end
