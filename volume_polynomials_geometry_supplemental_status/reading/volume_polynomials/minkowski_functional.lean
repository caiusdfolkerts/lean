module

public import VolumePolynomials.ConvexFibersBasic

public import VolumePolynomials.BodyTopology
public import VolumePolynomials.BodyContinuity
public import Mathlib.MeasureTheory.Integral.Average

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# Continuous monotone Minkowski functionals

Support values and directional widths are examples. The construction of
Minkowski averages will preserve all such functionals simultaneously.
-/

open Set Metric MeasureTheory
open scoped Pointwise

namespace VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Blaschke compactness for bodies in a fixed compact set, with no
requirement that the individual bodies contain the origin. -/
theorem isCompact_bodies_subset_compact {C : Set E} (hC : IsCompact C) :
    IsCompact {K : ConvexBody E | (K : Set E) ⊆ C} := by
  first
  | have hr : IsClosed (Set.range (bodyToNonemptyCompacts (E := E))) := by
      first
      | rw [range_bodyToNonemptyCompacts]
        exact isClosed_compacts_convex
    have hbase := TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact hC
    have hc : IsCompact {K : TopologicalSpace.NonemptyCompacts E |
        (K : Set E) ⊆ C ∧ Convex ℝ (K : Set E)} :=
      hbase.inter_right isClosed_compacts_convex
    have h := isometry_bodyToNonemptyCompacts.isUniformInducing.isInducing.isCompact_preimage hr hc
    convert h using 1
    ext K
    simp only [mem_ofPred_eq, mem_preimage, coe_bodyToNonemptyCompacts]
    exact ⟨fun hK => ⟨hK, K.convex⟩, fun hK => hK.1⟩

namespace BodySupport

theorem continuous_support (f : E →L[ℝ] ℝ) :
    Continuous (fun K : ConvexBody E => support K f) := by
  first
  | apply LipschitzWith.continuous (K := ‖f‖₊)
    apply LipschitzWith.of_dist_le_mul
    intro K L
    have hKL := support_le_add_norm_mul_dist K L f
    have hLK := support_le_add_norm_mul_dist L K f
    rw [dist_comm L K] at hLK
    rw [Real.dist_eq, coe_nnnorm, abs_le]
    constructor <;> linarith

theorem support_add (K L : ConvexBody E) (f : E →L[ℝ] ℝ) :
    support (K + L) f = support K f + support L f := by
  first
  | apply le_antisymm
    · apply support_le
      rintro _ ⟨x, hx, y, hy, rfl⟩
      rw [map_add]
      exact add_le_add (le_support K f hx) (le_support L f hy)
    · obtain ⟨x, hx, hfx⟩ := exists_support K f
      obtain ⟨y, hy, hfy⟩ := exists_support L f
      simpa only [map_add, hfx, hfy] using
        le_support (K + L) f (Set.add_mem_add hx hy)

theorem support_smul (K : ConvexBody E) (f : E →L[ℝ] ℝ)
    {r : ℝ} (hr : 0 ≤ r) : support (r • K) f = r * support K f := by
  first
  | apply le_antisymm
    · apply support_le
      rintro _ ⟨x, hx, rfl⟩
      simp only [map_smul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (le_support K f hx) hr
    · obtain ⟨x, hx, hfx⟩ := exists_support K f
      simpa only [map_smul, smul_eq_mul, hfx] using
        le_support (r • K) f (smul_mem_smul_set hx)

theorem support_mono {K L : ConvexBody E} (h : (K : Set E) ⊆ L)
    (f : E →L[ℝ] ℝ) : support K f ≤ support L f :=
  support_le K f (fun _ hx => le_support L f (h hx))

end BodySupport

structure MinkowskiFunctional (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ConvexBody E → ℝ
  continuous_toFun : Continuous toFun
  monotone : ∀ {K L : ConvexBody E}, (K : Set E) ⊆ L → toFun K ≤ toFun L
  map_add : ∀ K L, toFun (K + L) = toFun K + toFun L
  map_nonneg_smul : ∀ r : ℝ, 0 ≤ r → ∀ K, toFun (r • K) = r * toFun K

instance : CoeFun (MinkowskiFunctional E) (fun _ => ConvexBody E → ℝ) :=
  ⟨MinkowskiFunctional.toFun⟩

namespace MinkowskiFunctional

def support (f : E →L[ℝ] ℝ) : MinkowskiFunctional E where
  toFun K := BodySupport.support K f
  continuous_toFun := BodySupport.continuous_support f
  monotone h := BodySupport.support_mono h f
  map_add K L := BodySupport.support_add K L f
  map_nonneg_smul _ hr K := BodySupport.support_smul K f hr

def add (f g : MinkowskiFunctional E) : MinkowskiFunctional E where
  toFun K := f K + g K
  continuous_toFun := f.continuous_toFun.add g.continuous_toFun
  monotone h := add_le_add (f.monotone h) (g.monotone h)
  map_add K L := by rw [f.map_add, g.map_add]; ring
  map_nonneg_smul r hr K := by rw [f.map_nonneg_smul r hr, g.map_nonneg_smul r hr]; ring

def width (f : E →L[ℝ] ℝ) : MinkowskiFunctional E := add (support f) (support (-f))

theorem map_convex_combination (φ : MinkowskiFunctional E)
    (K L : ConvexBody E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    φ (a • K + b • L) = a * φ K + b * φ L := by
  first
  | rw [φ.map_add, φ.map_nonneg_smul a ha, φ.map_nonneg_smul b hb]

/-- Equality of all monotone Minkowski functionals implies equality of the
actual bodies, because support values are among the functionals. -/
theorem separating {K L : ConvexBody E} (h : ∀ φ : MinkowskiFunctional E, φ K = φ L) :
    K = L := by
  first
  | apply SetLike.coe_injective
    ext x
    change x ∈ K ↔ x ∈ L
    rw [BodySupport.mem_iff_le_support K, BodySupport.mem_iff_le_support L]
    have hs : ∀ f : E →L[ℝ] ℝ, BodySupport.support K f = BodySupport.support L f :=
      fun f => h (support f)
    simp only [hs]

end MinkowskiFunctional

/-- Concavity of a body-valued family means literal set containment. -/
theorem FiberConcave.functional_concave {U : Type*} [AddCommMonoid U] [Module ℝ U]
    {Z : Set U} {K : U → ConvexBody E} (hK : FiberConcave Z K)
    (φ : MinkowskiFunctional E) : ConcaveOn ℝ Z (fun y => φ (K y)) := by
  first
  | refine ⟨hK.1, ?_⟩
    intro x hx y hy a b ha hb hab
    rw [smul_eq_mul, smul_eq_mul, ← φ.map_convex_combination _ _ ha hb]
    exact φ.monotone (hK.2 x hx y hy a b ha hb hab)

end VolumePolynomials
