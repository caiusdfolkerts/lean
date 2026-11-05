module

public import Projection.MixedArea
public import VolumePolynomials.ProjectionPairingEquality
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic.Ring

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped BigOperators Pointwise Matrix

namespace RankThreeProjection
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- The measure-equality half of Lemma 4.1, for the actual mixed area measures.
This uses the proved AF inequality and the proved density of support differences;
it makes no assertion about the separate support-function rigidity theorem. -/
theorem mixedAreaMeasure_eq_of_positive_AF_equality {d : ℕ}
    (K : Fin d → ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (A B : ConvexBody E) (a : ℝ) (ha : 0 < a)
    (hAA : mixedVolume μ (Fin.cons A (Fin.cons A K)) = a)
    (hAB : mixedVolume μ (Fin.cons A (Fin.cons B K)) = a)
    (hBB : mixedVolume μ (Fin.cons B (Fin.cons B K)) = a) :
    mixedAreaMeasure μ (Fin.cons A K) hdim =
      mixedAreaMeasure μ (Fin.cons B K) hdim := by
  have heq := mixedVolume_equal_pairings_of_AF_equality μ hdim K A B a ha hAA hAB hBB
  apply measure_eq_of_support_integrals
  intro T
  rw [mixedAreaMeasure_integral, mixedAreaMeasure_integral,
    PolyhedralSupport.mixedVolume_cons_cons_swap μ T A K,
    PolyhedralSupport.mixedVolume_cons_cons_swap μ T B K, heq T]

/-- Minkowski linearity of the actual area measure in a marked body. -/
theorem mixedAreaMeasure_weighted_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (K : Fin d → ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (S : ι → ConvexBody E) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    mixedAreaMeasure μ (Fin.cons (∑ i, x i • S i) K) hdim =
      ∑ i, ENNReal.ofReal (x i) • mixedAreaMeasure μ (Fin.cons (S i) K) hdim := by
  letI : ∀ i, IsFiniteMeasure
      (ENNReal.ofReal (x i) • mixedAreaMeasure μ (Fin.cons (S i) K) hdim) :=
    fun i => Measure.smul_finite _ ENNReal.ofReal_ne_top
  apply measure_eq_of_support_integrals
  intro A
  rw [mixedAreaMeasure_integral,
    PolyhedralSupport.mixedVolume_cons_cons_swap μ A _ K,
    mixedVolume_cons_sum, Finset.mul_sum,
    integral_finsetSum_measure (f := fun u : NormalSphere E => supportContinuous A u) (fun i _ =>
      (BoundedContinuousFunction.mkOfCompact (supportContinuous A)).integrable _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [PolyhedralSupport.mixedVolume_cons_smul μ _ _ (hx i),
    integral_smul_measure, ENNReal.toReal_ofReal (hx i), smul_eq_mul,
    mixedAreaMeasure_integral,
    PolyhedralSupport.mixedVolume_cons_cons_swap μ (S i) A K]
  ring

private theorem real_weighted_sum {X : Type*} [MeasurableSpace X]
    {ι : Type*} [Fintype ι] (ν : ι → Measure X) [∀ i, IsFiniteMeasure (ν i)]
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (s : Set X) :
    (∑ i, ENNReal.ofReal (x i) • ν i).real s = ∑ i, x i * (ν i).real s := by
  letI : ∀ i, IsFiniteMeasure (ENNReal.ofReal (x i) • ν i) :=
    fun i => Measure.smul_finite _ ENNReal.ofReal_ne_top
  rw [Measure.real, Measure.finsetSum_apply,
    ENNReal.toReal_sum (fun i _ => measure_ne_top _ s)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hx i)]
  rfl

/-- Every kernel vector of an actual positive hollow mixed-volume matrix gives
an identity of signed area measures, including on arbitrary measurable sets.
The positive and negative bodies are genuine Minkowski sums. -/
theorem mixedAreaMeasure_kernel_relation
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    {d : ℕ} (K : Fin d → ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (S : ι → ConvexBody E) (P : Matrix ι ι ℝ) (c : ℝ) (hc : 0 < c)
    (hP : ∀ i j, P i j =
      c * mixedVolume μ (Fin.cons (S i) (Fin.cons (S j) K)))
    (hsymm : ∀ i j, P i j = P j i)
    (hdiag : ∀ i, P i i = 0) (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (w : ι → ℝ) (hw : P *ᵥ w = 0) (s : Set (NormalSphere E)) :
    ∑ i, w i * (mixedAreaMeasure μ (Fin.cons (S i) K) hdim).real s = 0 := by
  by_cases hne : w = 0
  · subst w
    simp
  let x := VolumeVerification.PositiveHollowKernel.positivePart w
  let y := VolumeVerification.PositiveHollowKernel.negativePart w
  have hx : ∀ i, 0 ≤ x i := fun i => le_max_right _ _
  have hy : ∀ i, 0 ≤ y i := fun i => le_max_right _ _
  obtain ⟨a, ha, hAA, hAB, hBB⟩ :=
    mixedVolume_kernel_zonotopes_equal_positive μ K S P c hc hP hsymm hdiag hpos w hw hne
  have heq := mixedAreaMeasure_eq_of_positive_AF_equality μ K hdim
    (∑ i, x i • S i) (∑ i, y i • S i) a ha hAA hAB hBB
  rw [mixedAreaMeasure_weighted_sum μ K hdim S x hx,
    mixedAreaMeasure_weighted_sum μ K hdim S y hy] at heq
  have hr := congrArg (fun ν : Measure (NormalSphere E) => ν.real s) heq
  rw [real_weighted_sum _ x hx, real_weighted_sum _ y hy] at hr
  have hparts : ∀ i, w i = x i - y i := by
    intro i
    exact (congrFun
      (VolumeVerification.PositiveHollowKernel.positivePart_sub_negativePart w) i).symm
  simp_rw [hparts, sub_mul]
  rw [Finset.sum_sub_distrib, hr, sub_self]

end RankThreeProjection
