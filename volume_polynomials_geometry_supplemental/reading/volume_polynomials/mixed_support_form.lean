module

public import VolumePolynomials.SupportTypeCone
public import VolumePolynomials.MixedVolumeMultilinear
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Matrix.Mul

@[expose] public section
set_option autoImplicit false

/-!
# The actual mixed-volume form on all support vectors

On the open cone of a fixed simple support type, support addition is actual
Minkowski addition. The proved mixed-volume laws therefore extend uniquely to
an ordinary symmetric bilinear form on every real height vector. Its matrix
is defined by evaluation on the ordinary coordinate basis. No geometric
inequality or sign condition is part of this construction.
-/

noncomputable section
open Set MeasureTheory Module LinearMap Matrix
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Classical in
/-- A harmless total extension of the genuine support-body map. Every use in
the bilinear extension evaluates this map at an element of the support cone. -/
def bodyAtHeight (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h : ι → ℝ) : ConvexBody E :=
  if hh : h ∈ typeCone l h₀ hp hc then coneBody l h₀ hp hc ⟨h, hh⟩ else 0

theorem bodyAtHeight_eq (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {h : ι → ℝ} (hh : h ∈ typeCone l h₀ hp hc) :
    bodyAtHeight l h₀ hp hc h = coneBody l h₀ hp hc ⟨h, hh⟩ := by
  first
  | simp only [bodyAtHeight, dif_pos hh]

theorem coe_bodyAtHeight (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {h : ι → ℝ} (hh : h ∈ typeCone l h₀ hp hc) :
    (bodyAtHeight l h₀ hp hc h : Set E) = body l h := by
  first
  | rw [bodyAtHeight_eq l h₀ hp hc hh]
    rfl

theorem bodyAtHeight_add (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {h k : ι → ℝ} (hh : h ∈ typeCone l h₀ hp hc)
    (hk : k ∈ typeCone l h₀ hp hc) :
    bodyAtHeight l h₀ hp hc (h + k) =
      bodyAtHeight l h₀ hp hc h + bodyAtHeight l h₀ hp hc k := by
  first
  | rw [bodyAtHeight_eq l h₀ hp hc ((typeCone l h₀ hp hc).add_mem hh hk),
      bodyAtHeight_eq l h₀ hp hc hh, bodyAtHeight_eq l h₀ hp hc hk]
    exact coneBody_add l h₀ hp hc ⟨h, hh⟩ ⟨k, hk⟩

theorem bodyAtHeight_smul (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {h : ι → ℝ} (hh : h ∈ typeCone l h₀ hp hc) {r : ℝ} (hr : 0 < r) :
    bodyAtHeight l h₀ hp hc (r • h) = r • bodyAtHeight l h₀ hp hc h := by
  first
  | rw [bodyAtHeight_eq l h₀ hp hc ((typeCone l h₀ hp hc).smul_mem hr hh),
      bodyAtHeight_eq l h₀ hp hc hh]
    exact coneBody_smul l h₀ hp hc ⟨h, hh⟩ hr

variable [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem mixedVolume_cons_cons_swap {d : ℕ} (A B : ConvexBody E)
    (K : Fin d → ConvexBody E) :
    mixedVolume μ (Fin.cons A (Fin.cons B K)) =
      mixedVolume μ (Fin.cons B (Fin.cons A K)) := by
  first
  | have he := mixedVolume_reindex μ (Fin.cons A (Fin.cons B K))
      (Equiv.swap (0 : Fin (d + 2)) 1)
    change mixedVolume μ ((Matrix.vecCons A (Matrix.vecCons B K)) ∘
      Equiv.swap 0 1) = _ at he
    rw [Matrix.cons_cons_comp_swap_zero_one] at he
    exact he.symm

theorem mixedVolume_cons_add {d : ℕ} (A B : ConvexBody E)
    (K : Fin d → ConvexBody E) :
    mixedVolume μ (Fin.cons (A + B) K) =
      mixedVolume μ (Fin.cons A K) + mixedVolume μ (Fin.cons B K) := by
  first
  | simpa only [Fin.update_cons_zero] using
      mixedVolume_add μ (Fin.cons A K) 0 A B

theorem mixedVolume_cons_smul {d : ℕ} (A : ConvexBody E)
    (K : Fin d → ConvexBody E) {r : ℝ} (hr : 0 ≤ r) :
    mixedVolume μ (Fin.cons (r • A) K) = r * mixedVolume μ (Fin.cons A K) := by
  first
  | simpa only [Fin.update_cons_zero] using
      mixedVolume_smul μ (Fin.cons A K) 0 A hr

def mixedSupportValue (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) (x y : ι → ℝ) : ℝ :=
  mixedVolume μ (Fin.cons (bodyAtHeight l h₀ hp hc x)
    (Fin.cons (bodyAtHeight l h₀ hp hc y) K))

theorem mixedSupportValue_symmetric (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) (x y : ι → ℝ) :
    mixedSupportValue μ l h₀ hp hc K x y = mixedSupportValue μ l h₀ hp hc K y x :=
  mixedVolume_cons_cons_swap μ _ _ K

theorem mixedSupportValue_additive_left (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) (y : ι → ℝ) :
    OpenConeExtension.AdditiveOn (typeCone l h₀ hp hc)
      (fun x => mixedSupportValue μ l h₀ hp hc K x y) := by
  first
  | intro a ha b hb
    unfold mixedSupportValue
    dsimp only
    rw [bodyAtHeight_add l h₀ hp hc ha hb, mixedVolume_cons_add]

theorem mixedSupportValue_homogeneous_left (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) (y : ι → ℝ) :
    OpenConeExtension.PositiveHomogeneousOn (typeCone l h₀ hp hc)
      (fun x => mixedSupportValue μ l h₀ hp hc K x y) := by
  first
  | intro r hr x hx
    unfold mixedSupportValue
    dsimp only
    rw [bodyAtHeight_smul l h₀ hp hc hx hr, mixedVolume_cons_smul μ _ _ hr.le]

theorem mixedSupportValue_additive_right (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) (x : ι → ℝ) :
    OpenConeExtension.AdditiveOn (typeCone l h₀ hp hc)
      (mixedSupportValue μ l h₀ hp hc K x) := by
  first
  | intro a ha b hb
    simpa only [mixedSupportValue_symmetric μ l h₀ hp hc K x] using
      mixedSupportValue_additive_left μ l h₀ hp hc K x a ha b hb

theorem mixedSupportValue_homogeneous_right (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) (x : ι → ℝ) :
    OpenConeExtension.PositiveHomogeneousOn (typeCone l h₀ hp hc)
      (mixedSupportValue μ l h₀ hp hc K x) := by
  first
  | intro r hr y hy
    simpa only [mixedSupportValue_symmetric μ l h₀ hp hc K x] using
      mixedSupportValue_homogeneous_left μ l h₀ hp hc K x r hr y hy

/-- The full symmetric bilinear form, defined from the actual mixed volumes
of genuine compact convex bodies through their open support cone. -/
def mixedSupportForm (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) : LinearMap.BilinForm ℝ (ι → ℝ) :=
  OpenConeExtension.bilinearExtension (typeCone l h₀ hp hc)
    (typeCone_isOpen l h₀ hp hc) (typeCone_nonempty l h₀ hg hp hc)
    (mixedSupportValue μ l h₀ hp hc K)
    (fun y _ => mixedSupportValue_additive_left μ l h₀ hp hc K y)
    (fun y _ => mixedSupportValue_homogeneous_left μ l h₀ hp hc K y)
    (fun x _ => mixedSupportValue_additive_right μ l h₀ hp hc K x)
    (fun x _ => mixedSupportValue_homogeneous_right μ l h₀ hp hc K x)

theorem mixedSupportForm_eq_value (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) {x y : ι → ℝ}
    (hx : x ∈ typeCone l h₀ hp hc) (hy : y ∈ typeCone l h₀ hp hc) :
    mixedSupportForm μ l h₀ hg hp hc K x y = mixedSupportValue μ l h₀ hp hc K x y :=
  OpenConeExtension.bilinearExtensionValue_eq _ _ _ _
    (fun z _ => mixedSupportValue_additive_left μ l h₀ hp hc K z)
    (fun z _ => mixedSupportValue_additive_right μ l h₀ hp hc K z) hx hy

theorem mixedSupportForm_eq (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) {x y : ι → ℝ}
    (hx : x ∈ typeCone l h₀ hp hc) (hy : y ∈ typeCone l h₀ hp hc) :
    mixedSupportForm μ l h₀ hg hp hc K x y =
      mixedVolume μ (Fin.cons (coneBody l h₀ hp hc ⟨x, hx⟩)
        (Fin.cons (coneBody l h₀ hp hc ⟨y, hy⟩) K)) := by
  first
  | change OpenConeExtension.bilinearExtensionValue _ _ _ _ x y = _
    rw [OpenConeExtension.bilinearExtensionValue_eq _ _ _ _
      (fun z _ => mixedSupportValue_additive_left μ l h₀ hp hc K z)
      (fun z _ => mixedSupportValue_additive_right μ l h₀ hp hc K z) hx hy]
    simp only [mixedSupportValue, bodyAtHeight_eq l h₀ hp hc hx,
      bodyAtHeight_eq l h₀ hp hc hy]

theorem mixedSupportForm_symmetric (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) (x y : ι → ℝ) :
    mixedSupportForm μ l h₀ hg hp hc K x y =
      mixedSupportForm μ l h₀ hg hp hc K y x :=
  OpenConeExtension.bilinearExtensionValue_symmetric _ _ _ _
    (fun x _ y _ => mixedSupportValue_symmetric μ l h₀ hp hc K x y) x y

def mixedSupportMatrix (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) : Matrix ι ι ℝ :=
  fun i j => mixedSupportForm μ l h₀ hg hp hc K (Pi.single i 1) (Pi.single j 1)

theorem mixedSupportMatrix_symmetric (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) :
    ∀ i j, mixedSupportMatrix μ l h₀ hg hp hc K i j =
      mixedSupportMatrix μ l h₀ hg hp hc K j i :=
  fun i j => mixedSupportForm_symmetric μ l h₀ hg hp hc K _ _

theorem mixedSupportForm_eq_dotProduct (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {d : ℕ} (K : Fin d → ConvexBody E) (x y : ι → ℝ) :
    mixedSupportForm μ l h₀ hg hp hc K x y =
      x ⬝ᵥ (mixedSupportMatrix μ l h₀ hg hp hc K *ᵥ y) := by
  first
  | let B := mixedSupportForm μ l h₀ hg hp hc K
    change B x y = _
    calc
      B x y = B (∑ i, x i • Pi.single i 1) (∑ j, y j • Pi.single j 1) := by
        rw [← pi_eq_sum_univ' x, ← pi_eq_sum_univ' y]
      _ = ∑ i, x i * ∑ j, y j * B (Pi.single i 1) (Pi.single j 1) := by
        simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
          smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = x ⬝ᵥ (mixedSupportMatrix μ l h₀ hg hp hc K *ᵥ y) := by
        simp only [dotProduct, mulVec, mixedSupportMatrix]
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        exact mul_comm _ _

end VolumePolynomials.PolyhedralSupport
