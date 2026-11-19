module

public import verified.main
import all verified.main
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-!
# The minimal face of a finite homogeneous inequality cone

This optional extension identifies the ordinary minimal convex face through a
point with the tight-inequality face. Its linear span and affine direction space
are exactly the complete tight kernel. The assertion of minimality quantifies
over all convex extreme subsets, using Mathlib's `Convex` and `IsExtreme`.
-/

noncomputable section

namespace GraphicalZonotopes.Polyhedral

variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]

/-- The actual solution set of the homogeneous linear inequalities. -/
def nonnegativeCone (A : I → E →ₗ[ℝ] ℝ) : Set E := {x | Nonnegative A x}

/-- The part of the cone on which every inequality tight at `y` remains tight. -/
def tightFace (A : I → E →ₗ[ℝ] ℝ) (y : E) : Set E :=
  {x | Nonnegative A x ∧ x ∈ tightKernel A y}

theorem self_mem_tightFace {A : I → E →ₗ[ℝ] ℝ} {y : E}
    (hy : Nonnegative A y) : y ∈ tightFace A y :=
  ⟨hy, self_mem_tightKernel A y⟩

theorem zero_mem_tightFace (A : I → E →ₗ[ℝ] ℝ) (y : E) :
    (0 : E) ∈ tightFace A y :=
  ⟨by intro i; simp, (tightKernel A y).zero_mem⟩

theorem tightFace_convex (A : I → E →ₗ[ℝ] ℝ) (y : E) :
    Convex ℝ (tightFace A y) := by
  apply convex_iff_add_mem.mpr
  intro u hu v hv a b ha hb _hab
  refine ⟨?_, (tightKernel A y).add_mem
    ((tightKernel A y).smul_mem a hu.2) ((tightKernel A y).smul_mem b hv.2)⟩
  intro i
  simp only [map_add, map_smul, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hu.1 i)) (mul_nonneg hb (hv.1 i))

theorem tightFace_isExtreme (A : I → E →ₗ[ℝ] ℝ) (y : E) :
    IsExtreme ℝ (nonnegativeCone A) (tightFace A y) := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  rintro u hu v hv z hz ⟨a, b, ha, hb, _hab, habz⟩
  refine ⟨hu, ?_⟩
  intro i hi
  have hz0 : A i z = 0 := hz.2 i hi
  have hrow := congrArg (A i) habz
  simp only [map_add, map_smul, smul_eq_mul] at hrow
  have hv0 : 0 ≤ b * A i v := mul_nonneg hb.le (hv i)
  have hu0 : a * A i u = 0 :=
    le_antisymm (by linarith) (mul_nonneg ha.le (hu i))
  exact (mul_eq_zero.mp hu0).resolve_left (ne_of_gt ha)

/-- Every extreme subset of the cone containing `y` contains the tight face.

The finite-inequality perturbation lemma puts `y` in an open segment from any
point of the tight face to another point of the cone. The defining property of
an extreme subset then forces that first endpoint into the subset.
-/
theorem tightFace_subset_of_isExtreme {A : I → E →ₗ[ℝ] ℝ} {y : E}
    (hy : Nonnegative A y) {F : Set E}
    (hF : IsExtreme ℝ (nonnegativeCone A) F) (hyF : y ∈ F) :
    tightFace A y ⊆ F := by
  intro v hv
  obtain ⟨ε, hε, _hp, hm⟩ := exists_two_sided_perturbation hy hv.2
  let r : ℝ := 1 + ε
  have hr : 0 < r := by dsimp [r]; linarith
  let w : E := r • y - ε • v
  have hw : Nonnegative A w := by
    intro i
    dsimp [w]
    simp only [map_sub, map_smul, smul_eq_mul]
    have hmi := hm i
    simp only [map_sub, map_smul, smul_eq_mul] at hmi
    have hrest : 0 ≤ (r - 1 / 2) * A i y :=
      mul_nonneg (by dsimp [r]; linarith) (hy i)
    linarith
  have hsum : ε * r⁻¹ + r⁻¹ = 1 := by
    calc
      ε * r⁻¹ + r⁻¹ = (ε + 1) * r⁻¹ := by ring
      _ = 1 := by simpa [r, add_comm] using mul_inv_cancel₀ (ne_of_gt hr)
  have hcomb : (ε * r⁻¹) • v + r⁻¹ • w = y := by
    calc
      (ε * r⁻¹) • v + r⁻¹ • w =
          (r⁻¹ * r) • y + (ε * r⁻¹ - r⁻¹ * ε) • v := by dsimp [w]; module
      _ = y := by rw [inv_mul_cancel₀ (ne_of_gt hr)]; simp [mul_comm]
  exact hF.left_mem_of_mem_openSegment hv.1 hw hyF
    ⟨ε * r⁻¹, r⁻¹, mul_pos hε (inv_pos.mpr hr), inv_pos.mpr hr, hsum, hcomb⟩

/-- The tight face is the least ordinary convex face of the cone containing `y`.
No pointedness or finite-dimensionality hypothesis is needed. -/
theorem tightFace_isLeast {A : I → E →ₗ[ℝ] ℝ} {y : E}
    (hy : Nonnegative A y) :
    IsLeast {F : Set E | Convex ℝ F ∧ IsExtreme ℝ (nonnegativeCone A) F ∧ y ∈ F}
      (tightFace A y) := by
  refine ⟨⟨tightFace_convex A y, tightFace_isExtreme A y, self_mem_tightFace hy⟩, ?_⟩
  intro F hF
  exact tightFace_subset_of_isExtreme hy hF.2.1 hF.2.2

theorem span_tightFace_eq_tightKernel {A : I → E →ₗ[ℝ] ℝ} {y : E}
    (hy : Nonnegative A y) :
    Submodule.span ℝ (tightFace A y) = tightKernel A y := by
  refine le_antisymm (Submodule.span_le.mpr (fun _ hx => hx.2)) ?_
  intro v hv
  obtain ⟨ε, hε, hp, _hm⟩ := exists_two_sided_perturbation hy hv
  have hyF : y ∈ tightFace A y := self_mem_tightFace hy
  have hpF : (1 / 2 : ℝ) • y + ε • v ∈ tightFace A y :=
    ⟨hp, (tightKernel A y).add_mem
      ((tightKernel A y).smul_mem (1 / 2 : ℝ) (self_mem_tightKernel A y))
      ((tightKernel A y).smul_mem ε hv)⟩
  have hvε : ε • v ∈ Submodule.span ℝ (tightFace A y) := by
    have h := (Submodule.span ℝ (tightFace A y)).sub_mem
      (Submodule.subset_span hpF)
      ((Submodule.span ℝ (tightFace A y)).smul_mem (1 / 2 : ℝ)
        (Submodule.subset_span hyF))
    simpa only [add_sub_cancel_left] using h
  have h := (Submodule.span ℝ (tightFace A y)).smul_mem ε⁻¹ hvε
  simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hε), one_smul] using h

theorem vectorSpan_tightFace_eq_tightKernel {A : I → E →ₗ[ℝ] ℝ} {y : E}
    (hy : Nonnegative A y) : vectorSpan ℝ (tightFace A y) = tightKernel A y := by
  rw [vectorSpan_eq_span_vsub_set_right ℝ (zero_mem_tightFace A y)]
  simpa only [vsub_eq_sub, sub_zero, Set.image_id'] using span_tightFace_eq_tightKernel hy

/-- Literal minimal-face and complete-kernel correspondence for the finite
inequality cone underlying Lemma 2.2 of the paper. -/
theorem minimal_face_tight_kernel {A : I → E →ₗ[ℝ] ℝ} {y : E}
    (hy : Nonnegative A y) :
    IsLeast {F : Set E | Convex ℝ F ∧ IsExtreme ℝ (nonnegativeCone A) F ∧ y ∈ F}
        (tightFace A y) ∧
      Submodule.span ℝ (tightFace A y) = tightKernel A y ∧
      vectorSpan ℝ (tightFace A y) = tightKernel A y :=
  ⟨tightFace_isLeast hy, span_tightFace_eq_tightKernel hy,
    vectorSpan_tightFace_eq_tightKernel hy⟩

theorem extremeRay_iff_minimal_face_span {A : I → E →ₗ[ℝ] ℝ}
    (hA : Pointed A) {y : E} (hy : Nonnegative A y) (hne : y ≠ 0) :
    ExtremeRay A y ↔ Submodule.span ℝ (tightFace A y) = Submodule.span ℝ {y} := by
  rw [span_tightFace_eq_tightKernel hy]
  exact extremeRay_iff_tightKernel hA hy hne

/-- The dimension-one criterion for the actual minimal convex face. -/
theorem extremeRay_iff_minimal_face_finrank {A : I → E →ₗ[ℝ] ℝ}
    (hA : Pointed A) {y : E} (hy : Nonnegative A y) (hne : y ≠ 0) :
    ExtremeRay A y ↔ Module.finrank ℝ (vectorSpan ℝ (tightFace A y)) = 1 := by
  rw [vectorSpan_tightFace_eq_tightKernel hy]
  constructor
  · intro he
    rw [he.tightKernel_eq_span]
    exact finrank_span_singleton hne
  · intro hd
    exact extremeRay_of_tightKernel hA hy hne
      (eq_span_singleton_of_mem_of_finrank_eq_one hd (self_mem_tightKernel A y) hne)

end GraphicalZonotopes.Polyhedral
