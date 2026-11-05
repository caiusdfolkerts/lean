module
public import VolumePolynomials.ProjectionAlexandrovFenchel
public import VolumeVerification.AFPairingEquality
public import VolumeVerification.PositiveHollowKernel
@[expose] public section
set_option autoImplicit false

/-!
# Equality of all actual mixed-volume pairings

This is the algebraic half of Lemma 4.1 of the projection-volume paper.
The mixed volume is the coefficient of the actual Haar-volume polynomial
defined by the recovered VolumePolynomials project.  The conclusion does
not assert the separate Shenfeld–van Handel support-function rigidity.
-/
namespace VolumePolynomials
open MeasureTheory Module
open scoped Pointwise BigOperators Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem mixedVolume_equal_pairings_of_AF_equality {n : ℕ}
    (hdim : finrank ℝ E = n + 2) (K : Fin n → ConvexBody E)
    (A B : ConvexBody E) (a : ℝ) (ha : 0 < a)
    (hAA : mixedVolume μ (Fin.cons A (Fin.cons A K)) = a)
    (hAB : mixedVolume μ (Fin.cons A (Fin.cons B K)) = a)
    (hBB : mixedVolume μ (Fin.cons B (Fin.cons B K)) = a) :
    ∀ T : ConvexBody E,
      mixedVolume μ (Fin.cons A (Fin.cons T K)) =
        mixedVolume μ (Fin.cons B (Fin.cons T K)) := by
  let q : ConvexBody E → ConvexBody E → ℝ :=
    fun X Y => mixedVolume μ (Fin.cons X (Fin.cons Y K))
  apply VolumeVerification.AFPairingEquality.equality_of_equal_positive_pairings
    q (fun X Y => PolyhedralSupport.mixedVolume_cons_cons_swap μ X Y K)
    (fun X Y T => PolyhedralSupport.mixedVolume_cons_add μ X Y (Fin.cons T K))
    (fun r hr X T => PolyhedralSupport.mixedVolume_cons_smul μ X (Fin.cons T K) hr)
    (fun X Y => mixedVolume_alexandrovFenchel μ hdim K X Y)
    A B a ha hAA hAB hBB

theorem mixedVolume_cons_zero {n : ℕ} (K : Fin n → ConvexBody E) :
    mixedVolume μ (Fin.cons (0 : ConvexBody E) K) = 0 := by
  simpa only [Fin.update_cons_zero] using
    mixedVolume_zero_arg μ (Fin.cons (0 : ConvexBody E) K) 0

theorem mixedVolume_cons_sum {ι : Type*} [DecidableEq ι] {n : ℕ}
    (s : Finset ι) (A : ι → ConvexBody E) (K : Fin n → ConvexBody E) :
    mixedVolume μ (Fin.cons (∑ i ∈ s, A i) K) =
      ∑ i ∈ s, mixedVolume μ (Fin.cons (A i) K) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, mixedVolume_cons_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, PolyhedralSupport.mixedVolume_cons_add, ih,
        Finset.sum_insert hi]

theorem mixedVolume_weighted_sum_pairing {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (K : Fin n → ConvexBody E) (S : ι → ConvexBody E)
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    mixedVolume μ (Fin.cons (∑ i, x i • S i) (Fin.cons (∑ j, y j • S j) K)) =
      ∑ i, ∑ j, x i * y j * mixedVolume μ (Fin.cons (S i) (Fin.cons (S j) K)) := by
  rw [mixedVolume_cons_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [PolyhedralSupport.mixedVolume_cons_smul μ _ _ (hx i),
    PolyhedralSupport.mixedVolume_cons_cons_swap, mixedVolume_cons_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [PolyhedralSupport.mixedVolume_cons_smul μ _ _ (hy j),
    PolyhedralSupport.mixedVolume_cons_cons_swap]
  ring

theorem scaled_mixedVolume_weighted_sum_pairing
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (K : Fin n → ConvexBody E) (S : ι → ConvexBody E)
    (P : Matrix ι ι ℝ) (c : ℝ)
    (hP : ∀ i j, P i j =
      c * mixedVolume μ (Fin.cons (S i) (Fin.cons (S j) K)))
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    c * mixedVolume μ
      (Fin.cons (∑ i, x i • S i) (Fin.cons (∑ j, y j • S j) K)) =
      x ⬝ᵥ (P *ᵥ y) := by
  rw [mixedVolume_weighted_sum_pairing μ K S x y hx hy]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hP]
  ring

/-- The actual Minkowski sums with the positive and negative kernel
coefficients satisfy precisely the positive equality hypotheses of AF.
This includes lower-dimensional comparison bodies and dependent marked
segments; the only normalization requirement is `0 < c`. -/
theorem mixedVolume_kernel_zonotopes_equal_positive
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    {n : ℕ} (K : Fin n → ConvexBody E) (S : ι → ConvexBody E)
    (P : Matrix ι ι ℝ) (c : ℝ) (hc : 0 < c)
    (hP : ∀ i j, P i j =
      c * mixedVolume μ (Fin.cons (S i) (Fin.cons (S j) K)))
    (hsymm : ∀ i j, P i j = P j i)
    (hdiag : ∀ i, P i i = 0) (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (w : ι → ℝ) (hw : P *ᵥ w = 0) (hne : w ≠ 0) :
    let A := ∑ i, VolumeVerification.PositiveHollowKernel.positivePart w i • S i
    let B := ∑ i, VolumeVerification.PositiveHollowKernel.negativePart w i • S i
    ∃ a : ℝ, 0 < a ∧
      mixedVolume μ (Fin.cons A (Fin.cons A K)) = a ∧
      mixedVolume μ (Fin.cons A (Fin.cons B K)) = a ∧
      mixedVolume μ (Fin.cons B (Fin.cons B K)) = a := by
  dsimp only
  let x := VolumeVerification.PositiveHollowKernel.positivePart w
  let y := VolumeVerification.PositiveHollowKernel.negativePart w
  have hx : ∀ i, 0 ≤ x i := fun i => le_max_right _ _
  have hy : ∀ i, 0 ≤ y i := fun i => le_max_right _ _
  obtain ⟨a, ha, hxx, hxy, hyy⟩ :=
    VolumeVerification.PositiveHollowKernel.parts_equal_positive_pairings
      P hsymm hdiag hpos w hw hne
  have h₁ := scaled_mixedVolume_weighted_sum_pairing μ K S P c hP x x hx hx
  have h₂ := scaled_mixedVolume_weighted_sum_pairing μ K S P c hP x y hx hy
  have h₃ := scaled_mixedVolume_weighted_sum_pairing μ K S P c hP y y hy hy
  rw [show x ⬝ᵥ (P *ᵥ x) = a from hxx] at h₁
  rw [show x ⬝ᵥ (P *ᵥ y) = a from hxy] at h₂
  rw [show y ⬝ᵥ (P *ᵥ y) = a from hyy] at h₃
  refine ⟨a / c, div_pos ha hc, ?_, ?_, ?_⟩
  · apply (eq_div_iff hc.ne').mpr
    simpa only [mul_comm] using h₁
  · apply (eq_div_iff hc.ne').mpr
    simpa only [mul_comm] using h₂
  · apply (eq_div_iff hc.ne').mpr
    simpa only [mul_comm] using h₃

end VolumePolynomials
