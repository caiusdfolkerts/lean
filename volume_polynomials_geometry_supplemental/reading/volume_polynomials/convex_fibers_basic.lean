module

public import VolumePolynomials.BodyOperations
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

set_option autoImplicit false
noncomputable section

/-! Actual compact convex fibers in a product and their set-valued concavity. -/

open Set Metric MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def FiberConcave {U : Type*} [AddCommMonoid U] [Module ℝ U]
    (Z : Set U) (K : U → ConvexBody E) : Prop :=
  Convex ℝ Z ∧ ∀ x ∈ Z, ∀ y ∈ Z, ∀ a b : ℝ,
    0 ≤ a → 0 ≤ b → a + b = 1 →
      ((a • K x + b • K y : ConvexBody E) : Set E) ⊆ K (a • x + b • y)

end VolumePolynomials

namespace VolumePolynomials.ConvexFibers

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

def projection (C : ConvexBody (E × U)) : Set U := Prod.snd '' (C : Set (E × U))

def fiberSet (C : ConvexBody (E × U)) (y : U) : Set E := {x | (x, y) ∈ C}

theorem projection_compact (C : ConvexBody (E × U)) : IsCompact (projection C) :=
  C.isCompact.image continuous_snd

theorem projection_convex (C : ConvexBody (E × U)) : Convex ℝ (projection C) :=
  C.convex.linear_image (LinearMap.snd ℝ E U)

theorem fiberSet_nonempty_iff (C : ConvexBody (E × U)) (y : U) :
    (fiberSet C y).Nonempty ↔ y ∈ projection C := by
  first
  | constructor
    · rintro ⟨x, hx⟩
      exact ⟨(x, y), hx, rfl⟩
    · rintro ⟨⟨x, z⟩, hx, hzy⟩
      change z = y at hzy
      subst z
      exact ⟨x, hx⟩

theorem fiberSet_compact (C : ConvexBody (E × U)) (y : U) : IsCompact (fiberSet C y) := by
  first
  | have heq : fiberSet C y = Prod.fst '' ((C : Set (E × U)) ∩ Prod.snd ⁻¹' {y}) := by
      first
      | ext x
        constructor
        · intro hx
          exact ⟨(x, y), ⟨hx, rfl⟩, rfl⟩
        · rintro ⟨⟨u, v⟩, ⟨huv, hv⟩, hux⟩
          have hvy : v = y := hv
          subst v
          change u = x at hux
          subst u
          exact huv
    rw [heq]
    exact (C.isCompact.inter_right (isClosed_singleton.preimage continuous_snd)).image continuous_fst

theorem fiberSet_convex (C : ConvexBody (E × U)) (y : U) : Convex ℝ (fiberSet C y) := by
  first
  | intro x hx z hz a b ha hb hab
    have h := C.convex hx hz ha hb hab
    have hy : a • y + b • y = y := by rw [← add_smul, hab, one_smul]
    change (a • x + b • z, y) ∈ (C : Set (E × U))
    simpa only [Prod.smul_mk, Prod.mk_add_mk, hy] using h

def fiberBody (C : ConvexBody (E × U)) (y : U) : ConvexBody E := by
  classical
  exact if h : y ∈ projection C then
    ⟨fiberSet C y, fiberSet_convex C y, fiberSet_compact C y,
      Iff.mpr (fiberSet_nonempty_iff C y) h⟩
  else 0

theorem coe_fiberBody (C : ConvexBody (E × U)) {y : U} (hy : y ∈ projection C) :
    (fiberBody C y : Set E) = fiberSet C y := by
  first
  | rw [fiberBody, dif_pos hy]
    rfl

theorem fiberBody_concave (C : ConvexBody (E × U)) :
    FiberConcave (projection C) (fiberBody C) := by
  first
  | refine ⟨projection_convex C, ?_⟩
    intro y hy z hz a b ha hb hab x hx
    rcases hx with ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
    rw [coe_fiberBody C hy] at hu
    rw [coe_fiberBody C hz] at hv
    rw [coe_fiberBody C (projection_convex C hy hz ha hb hab)]
    exact C.convex hu hv ha hb hab

theorem fibers_uniformly_bounded (C : ConvexBody (E × U)) :
    ∃ R : ℝ, ∀ y ∈ projection C,
      (fiberBody C y : Set E) ⊆ closedBall 0 R := by
  first
  | obtain ⟨R, hR⟩ := C.isCompact.isBounded.exists_norm_le
    refine ⟨R, ?_⟩
    intro y hy x hx
    rw [coe_fiberBody C hy] at hx
    have h := (norm_fst_le (x, y)).trans (hR _ hx)
    simpa only [mem_closedBall, dist_zero_right] using h

end VolumePolynomials.ConvexFibers
