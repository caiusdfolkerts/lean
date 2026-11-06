module

public import wishart.verified.real_remainder05
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/- Generated ordinary proof stage. See audit/staged_real_remainder/RealRemainder06/manifest.json. -/

@[expose] public section

section CanonicalSource50
/- Source: Wishart/OuterFunctionClosure.lean -/



/-! # Domain and covariance-scale properties of the outer functions -/

noncomputable section

open Filter Set Topology

namespace WishartVerification

theorem GeometricallyLogConvex.monotoneOn {f : ℝ → ℝ} (hf : GeometricallyLogConvex f) :
    MonotoneOn f (Ioi 0) := by
  intro x hx y hy hxy
  rw [← exp_log_profile_eq hf hx, ← exp_log_profile_eq hf hy]
  exact Real.exp_le_exp.mpr (hf.monotone_log (Real.log_le_log hx hxy))

theorem GeometricallyLogConvex.continuousOn {f : ℝ → ℝ} (hf : GeometricallyLogConvex f) :
    ContinuousOn f (Ioi 0) := by
  have hcont : Continuous (fun s => Real.log (f (Real.exp s))) := by
    simpa only [interior_univ, continuousOn_univ] using hf.convex_log.continuousOn_interior
  intro x hx
  have hcom : ContinuousAt
      (fun y => Real.exp (Real.log (f (Real.exp (Real.log y))))) x :=
    Real.continuous_exp.continuousAt.comp
      (hcont.continuousAt.comp (Real.continuousAt_log hx.ne'))
  have heq : f =ᶠ[𝓝 x] (fun y => Real.exp (Real.log (f (Real.exp (Real.log y))))) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (exp_log_profile_eq hf hy).symm
  exact ((continuousAt_congr heq).mpr hcom).continuousWithinAt

/-- Positive covariance determinant factors are absorbed into the outer
function without changing its mathematical class. -/
theorem GeometricallyLogConvex.scale_argument {f : ℝ → ℝ}
    (hf : GeometricallyLogConvex f) {c : ℝ} (hc : 0 < c) :
    GeometricallyLogConvex (fun x => f (c * x)) := by
  have hlog (s : ℝ) : Real.log (f (c * Real.exp s)) =
      Real.log (f (Real.exp (s + Real.log c))) := by
    rw [Real.exp_add, Real.exp_log hc, mul_comm]
  refine ⟨fun x hx => hf.positive _ (mul_pos hc hx), ?_, ?_⟩
  · refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul, hlog]
    have h := hf.convex_log.2 (mem_univ (x + Real.log c))
      (mem_univ (y + Real.log c)) ha hb hab
    simp only [smul_eq_mul] at h
    have hid : a * (x + Real.log c) + b * (y + Real.log c) =
        a * x + b * y + Real.log c := by
      calc
        _ = a * x + b * y + (a + b) * Real.log c := by ring
        _ = _ := by rw [hab, one_mul]
    simpa only [hid] using h
  · intro x y hxy
    change Real.log (f (c * Real.exp x)) ≤ Real.log (f (c * Real.exp y))
    rw [hlog, hlog]
    exact hf.monotone_log (by linarith)

end WishartVerification
end
end CanonicalSource50

section CanonicalSource51
/- Source: Wishart/OuterExpectationLimits.lean -/



/-!
# Passing selected-factor inequalities to the full outer class

The independent-copy representation turns the product of two expectations
into one nonnegative integral. Both sides then pass by monotone convergence,
including infinite expectations, without an indeterminate limit argument.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators ENNReal

namespace WishartVerification

def positiveOuterExtension (f : ℝ → ℝ) : ℝ → ℝ :=
  (Ioi (0 : ℝ)).piecewise f (fun _ => 1)

theorem measurable_positiveOuterExtension {f : ℝ → ℝ} (hf : GeometricallyLogConvex f) :
    Measurable (positiveOuterExtension f) :=
  hf.continuousOn.measurable_piecewise continuous_const.continuousOn measurableSet_Ioi

theorem positiveOuterExtension_eq {f : ℝ → ℝ} {x : ℝ} (hx : 0 < x) :
    positiveOuterExtension f x = f x := Set.piecewise_eq_of_mem _ _ _ hx

theorem aemeasurable_geometric_outer_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : ℝ → ℝ} (hf : GeometricallyLogConvex f)
    {d : Ω → ℝ} (hd : Measurable d) (hpos : ∀ᵐ z ∂μ, 0 < d z) :
    AEMeasurable (fun z => f (d z)) μ := by
  apply ((measurable_positiveOuterExtension hf).comp hd).aemeasurable.congr
  exact hpos.mono fun z hz => positiveOuterExtension_eq hz


/-- An internal limit theorem. Its finite-test premise is supplied in the
matrix application by the actual radial comparison and Haar association. -/
theorem geometric_outer_selected_split_of_finite_splits
    {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (μ : Measure Ω) [SFinite μ]
    (d₀ : Ω → ℝ) (d : Ω → κ → ℝ)
    (hd₀m : Measurable d₀) (hdm : Measurable d)
    (hd₀pos : ∀ᵐ z ∂μ, 0 < d₀ z) (hdpos : ∀ᵐ z ∂μ, ∀ i, 0 < d z i)
    (hfinite : ∀ n : ℕ, ∀ a₀ b₀ : Fin (n + 1) → ℝ,
      ∀ a b : κ → Fin (n + 1) → ℝ,
      (∀ j, 0 ≤ a₀ j) → (∀ i j, 0 ≤ a i j) →
      (∫⁻ z, ENNReal.ofReal (finiteMaximum (fun j => Real.exp (b₀ j) * d₀ z ^ (a₀ j))) ∂μ) *
        (∫⁻ z, ENNReal.ofReal (finiteOuterTest a b (d z)) ∂μ) ≤
        ∫⁻ z, ENNReal.ofReal (finiteMaximum (fun j => Real.exp (b₀ j) * d₀ z ^ (a₀ j)) *
          finiteOuterTest a b (d z)) ∂μ)
    (f₀ : ℝ → ℝ) (f : κ → ℝ → ℝ)
    (hf₀ : GeometricallyLogConvex f₀) (hf : ∀ i, GeometricallyLogConvex (f i)) :
    (∫⁻ z, ENNReal.ofReal (f₀ (d₀ z)) ∂μ) *
      (∫⁻ z, ENNReal.ofReal (∏ i, f i (d z i)) ∂μ) ≤
      ∫⁻ z, ENNReal.ofReal (f₀ (d₀ z) * ∏ i, f i (d z i)) ∂μ := by
  classical
  let left : Ω × Ω → Option κ → ℝ := fun z i =>
    Option.elim i (d₀ z.1) (fun j => d z.2 j)
  let right : Ω → Option κ → ℝ := fun z i =>
    Option.elim i (d₀ z) (fun j => d z j)
  let functions : Option κ → ℝ → ℝ := fun i => Option.elim i f₀ f
  have hlm : Measurable left := by
    apply measurable_pi_iff.mpr
    intro i
    cases i with
    | none => exact hd₀m.comp measurable_fst
    | some i => exact ((measurable_pi_iff.mp hdm) i).comp measurable_snd
  have hrm : Measurable right := by
    apply measurable_pi_iff.mpr
    intro i
    cases i with
    | none => exact hd₀m
    | some i => exact (measurable_pi_iff.mp hdm) i
  have hlpos : ∀ᵐ z ∂μ.prod μ, ∀ i, 0 < left z i := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hd₀pos,
      Measure.quasiMeasurePreserving_snd.ae hdpos] with z hz₀ hz i
    cases i with
    | none => exact hz₀
    | some i => exact hz i
  have hrpos : ∀ᵐ z ∂μ, ∀ i, 0 < right z i := by
    filter_upwards [hd₀pos, hdpos] with z hz₀ hz i
    cases i with
    | none => exact hz₀
    | some i => exact hz i
  have hfuns : ∀ i, GeometricallyLogConvex (functions i) := by
    intro i
    cases i with
    | none => exact hf₀
    | some i => exact hf i
  have hcompare := geometric_outer_comparison_of_finite_comparisons
    (μ.prod μ) μ left right hlm hrm hlpos hrpos (by
      intro n a b ha
      have hselm : Measurable (fun z => finiteMaximum
          (fun j : Fin (n + 1) => Real.exp (b none j) * d₀ z ^ (a none j))) :=
        measurable_finiteMaximum _ fun j =>
          measurable_const.mul (hd₀m.pow_const _)
      have hrestm : Measurable (fun z => finiteOuterTest (a ∘ some) (b ∘ some) (d z)) :=
        (continuous_finiteOuterTest _ _ (fun i j => ha (some i) j)).measurable.comp hdm
      have hselpos : ∀ᵐ z ∂μ, 0 ≤ finiteMaximum
          (fun j : Fin (n + 1) => Real.exp (b none j) * d₀ z ^ (a none j)) :=
        hd₀pos.mono fun z hz => finiteMaximum_nonneg fun j =>
          mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hz.le _)
      simp only [finiteOuterTest, Fintype.prod_option, left, right, Option.elim_none,
        Option.elim_some]
      have h := hfinite n (a none) (b none) (a ∘ some) (b ∘ some) (ha none)
        (fun i j => ha (some i) j)
      rw [← lintegral_independent_real_product hselm.aemeasurable
        hrestm.aemeasurable hselpos] at h
      simpa only [finiteOuterTest, Function.comp_apply] using h) functions hfuns
  have hf₀m := aemeasurable_geometric_outer_comp hf₀ hd₀m hd₀pos
  have hfm : AEMeasurable (fun z => ∏ i, f i (d z i)) μ := by
    apply Finset.aemeasurable_fun_prod
    intro i hi
    exact aemeasurable_geometric_outer_comp (hf i) ((measurable_pi_iff.mp hdm) i)
      (hdpos.mono fun z hz => hz i)
  simp only [Fintype.prod_option, functions, left, right, Option.elim_none,
    Option.elim_some] at hcompare
  rw [lintegral_independent_real_product hf₀m hfm
    (hd₀pos.mono fun z hz => (hf₀.positive _ hz).le)] at hcompare
  exact hcompare

end WishartVerification
end
end CanonicalSource51

section CanonicalSource52
/- Source: Wishart/GeometricSelectedSplit.lean -/



/-!
# The geometric outer-function selected split

This theorem concerns the actual nonsingular real-shape Wishart law. Every
compression has full column rank, the shifts are the manuscript's proportional
covariance shifts, and the exact minimum-rank threshold is retained. The final
expectations are nonnegative extended integrals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

def shiftedCompressionDeterminant {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (Q : Matrix (Fin p) (Fin q) ℝ)
    (c : ℝ) (X : SymmetricMatrix p) : ℝ :=
  (Qᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * Q + c • compressionScale Sigma Q).det

theorem measurable_shiftedCompressionDeterminant {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (Q : Matrix (Fin p) (Fin q) ℝ) (c : ℝ) :
    Measurable (shiftedCompressionDeterminant Sigma Q c) := by
  unfold shiftedCompressionDeterminant
  fun_prop

theorem shiftedCompressionDeterminant_pos {p q : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q) {c : ℝ} (hc : 0 ≤ c)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    0 < shiftedCompressionDeterminant Sigma Q c X :=
  ((compressionScale_posDef hX Q hQ).add_posSemidef
    ((compressionScale_posDef hSigma Q hQ).posSemidef.smul hc)).det_pos

set_option backward.isDefEq.respectTransparency false in
theorem allFiniteMoments_shiftedCompressionDeterminant {p q : ℕ} {n : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (Q : Matrix (Fin p) (Fin q) ℝ) (c : ℝ) :
    HasAllFiniteMoments (shiftedCompressionDeterminant Sigma Q c)
      (nonsingularWishartMeasure n Sigma) := by
  change HasAllFiniteMoments
    (fun X : WishartVerification.SymmetricMatrix p =>
      (Qᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * Q + c • compressionScale Sigma Q).det)
    (nonsingularWishartMeasure n Sigma)
  simpa only [add_comm] using
    allFiniteMoments_wishart_affine_compression_det hSigma hn (c • compressionScale Sigma Q) Q

theorem regularizedCompression_zero_shift_det {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (Q : Matrix (Fin p) (Fin q) ℝ)
    (c : ℝ) (X : SymmetricMatrix p) :
    (regularizedCompression 0 (c • compressionScale Sigma Q) Q X).det =
      shiftedCompressionDeterminant Sigma Q c X := by
  simp only [regularizedCompression, compressionCLM_apply, shiftedCompressionDeterminant,
    zero_smul, zero_add, add_zero, add_comm]

/-- Internal limit assembly for actual full-rank compressions. Every use below
supplies the finite comparisons by a proved matrix theorem. -/
theorem compression_geometric_split_of_finite {p q : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q) (hc : 0 ≤ c)
    {κ : Type*} [Fintype κ]
    (k : κ → ℕ) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hM : ∀ i, (M i).rank = k i) (d : κ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (f₀ : ℝ → ℝ) (f : κ → ℝ → ℝ)
    (hf₀ : GeometricallyLogConvex f₀) (hf : ∀ i, GeometricallyLogConvex (f i))
    (hfinite : ∀ l : ℕ, ∀ a₀ b₀ : Fin (l + 1) → ℝ,
      ∀ a b : κ → Fin (l + 1) → ℝ,
      (∀ j, 0 ≤ a₀ j) → (∀ i j, 0 ≤ a i j) →
      (∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X ∂nonsingularWishartMeasure n Sigma) *
        (∫ X, affineMaximumProduct 0 k
          (fun i => d i • compressionScale Sigma (M i)) M a b X
          ∂nonsingularWishartMeasure n Sigma) ≤
        ∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X *
          affineMaximumProduct 0 k (fun i => d i • compressionScale Sigma (M i)) M a b X
          ∂nonsingularWishartMeasure n Sigma) :
    (∫⁻ X, ENNReal.ofReal (f₀ (shiftedCompressionDeterminant Sigma Q c X))
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ i, f i (shiftedCompressionDeterminant Sigma (M i) (d i) X))
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (f₀ (shiftedCompressionDeterminant Sigma Q c X) *
        ∏ i, f i (shiftedCompressionDeterminant Sigma (M i) (d i) X))
        ∂nonsingularWishartMeasure n Sigma := by
  classical
  let μ := nonsingularWishartMeasure n Sigma
  letI := isProbabilityMeasure_nonsingularWishartMeasure hSigma hn
  let B := fun i => d i • compressionScale Sigma (M i)
  have hB : ∀ i, (B i).PosSemidef := fun i =>
    (compressionScale_posDef hSigma (M i) (hM i)).posSemidef.smul (hd i)
  have h₀pos : ∀ᵐ X ∂μ, 0 < shiftedCompressionDeterminant Sigma Q c X :=
    (ae_posDef_nonsingularWishartMeasure n Sigma).mono fun X hX =>
      shiftedCompressionDeterminant_pos hSigma Q hQ hc hX
  have hpos : ∀ᵐ X ∂μ, ∀ i,
      0 < shiftedCompressionDeterminant Sigma (M i) (d i) X :=
    (ae_posDef_nonsingularWishartMeasure n Sigma).mono fun X hX i =>
      shiftedCompressionDeterminant_pos hSigma (M i) (hM i) (hd i) hX
  apply geometric_outer_selected_split_of_finite_splits μ
    (shiftedCompressionDeterminant Sigma Q c)
    (fun X i => shiftedCompressionDeterminant Sigma (M i) (d i) X)
    (measurable_shiftedCompressionDeterminant Sigma Q c)
    (measurable_pi_iff.mpr fun i => measurable_shiftedCompressionDeterminant Sigma (M i) (d i))
    h₀pos hpos _ f₀ f hf₀ hf
  intro l a₀ b₀ a b ha₀ ha
  let selected := finiteCompressionDetTest Sigma Q c a₀ b₀
  let remaining := affineMaximumProduct 0 k B M a b
  have hsm : HasAllFiniteMoments selected μ :=
    hasAllFiniteMoments_finiteMaximum _ fun j =>
      ((allFiniteMoments_shiftedCompressionDeterminant hSigma hn Q c).rpow (ha₀ j)).const_mul
        (Real.exp (b₀ j))
  have hrm : HasAllFiniteMoments remaining μ :=
    allFiniteMoments_affineMaximumProduct_of_entries 0 k B M a b ha
      (fun X : SymmetricMatrix p => X)
      (fun i j => allFiniteMoments_wishart_entry (α := n) (Sigma := Sigma) i j)
  have hsp : ∀ᵐ X ∂μ, 0 ≤ selected X :=
    h₀pos.mono fun X hX => finiteMaximum_nonneg fun j =>
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hX.le _)
  have hrp : ∀ᵐ X ∂μ, 0 ≤ remaining X :=
    (ae_posDef_nonsingularWishartMeasure n Sigma).mono fun X hX =>
      affineMaximumProduct_zero_nonneg k B M a b hB hX.posSemidef
  have heq (X : SymmetricMatrix p) : remaining X =
      finiteOuterTest a b (fun i => shiftedCompressionDeterminant Sigma (M i) (d i) X) := by
    simp only [remaining, affineMaximumProduct, finiteOuterTest, B,
      regularizedCompression_zero_shift_det]
  have hcomp := hfinite l a₀ b₀ a b ha₀ ha
  have hreal := ENNReal.ofReal_le_ofReal hcomp
  rw [ENNReal.ofReal_mul (integral_nonneg_of_ae hsp),
    ofReal_integral_eq_lintegral_ofReal hsm.integrable hsp,
    ofReal_integral_eq_lintegral_ofReal hrm.integrable hrp,
    ofReal_integral_eq_lintegral_ofReal (hsm.mul hrm).integrable
      (by filter_upwards [hsp, hrp] with X hs hr; exact mul_nonneg hs hr)] at hreal
  change (∫⁻ X, ENNReal.ofReal (selected X) ∂μ) *
      (∫⁻ X, ENNReal.ofReal (remaining X) ∂μ) ≤
      ∫⁻ X, ENNReal.ofReal (selected X * remaining X) ∂μ at hreal
  simpa only [heq, selected, finiteCompressionDetTest, shiftedCompressionDetPower,
    shiftedCompressionDeterminant] using hreal

/-- The selected-factor assertion of Theorem 5.1 under its exact shape
threshold, for the full stated class of geometrically log-convex functions.
There is no integrability or polynomial-growth assumption on those functions. -/
theorem compression_geometric_selected_split {p q : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q) (hc : 0 ≤ c)
    {κ : Type*} [Fintype κ]
    (k : κ → ℕ) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hM : ∀ i, (M i).rank = k i) (d : κ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (f₀ : ℝ → ℝ) (f : κ → ℝ → ℝ)
    (hf₀ : GeometricallyLogConvex f₀) (hf : ∀ i, GeometricallyLogConvex (f i))
    (hsize : ∀ i, min ((q : ℝ) + k i) ((p : ℝ) + 1) ≤ n) :
    (∫⁻ X, ENNReal.ofReal (f₀ (shiftedCompressionDeterminant Sigma Q c X))
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ i, f i (shiftedCompressionDeterminant Sigma (M i) (d i) X))
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (f₀ (shiftedCompressionDeterminant Sigma Q c X) *
        ∏ i, f i (shiftedCompressionDeterminant Sigma (M i) (d i) X))
        ∂nonsingularWishartMeasure n Sigma := by
  apply compression_geometric_split_of_finite hSigma hn Q hQ hc k M hM d hd f₀ f hf₀ hf
  intro l a₀ b₀ a b ha₀ ha
  exact compression_finiteOuter_selected_split hSigma hn Q hQ hc a₀ b₀ ha₀ k
    (fun i => d i • compressionScale Sigma (M i)) M a b
    (fun i => (compressionScale_posDef hSigma (M i) (hM i)).posSemidef.smul (hd i))
    ha hsize

end Wishart
end
end CanonicalSource52

section CanonicalSource53
/- Source: Wishart/GeometricFullRankSplit.lean -/



/-! # The unrestricted full-rank part of Theorem 5.1 -/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

theorem fullRank_finiteOuter_split {p : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (Q : Matrix (Fin p) (Fin p) ℝ) (hQ : Q.rank = p) (hc : 0 ≤ c)
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (a₀ b₀ : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j)
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j) :
    (∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, affineMaximumProduct 0 k B M a b X ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X * affineMaximumProduct 0 k B M a b X
        ∂nonsingularWishartMeasure n Sigma := by
  let N := compressionNormalization hSigma Q hQ
  let b₀' : ι → ℝ := fun j => b₀ j + Real.log (compressionScale Sigma Q).det * a₀ j
  let M' := fun i => N.ambientᵀ * M i
  have hblock (Y : SymmetricMatrix p) : principalSymmetricBlock (Fin.castAdd 0) Y = Y := by
    apply Subtype.ext
    ext i j
    rfl
  have htransform (f : SymmetricMatrix p → ℝ) (hf : Measurable f) :
      (∫ X, f X ∂nonsingularWishartMeasure n Sigma) =
        ∫ Y, f (Matrix.symmetricCongruenceLinearMap N.ambient Y)
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [← map_compressionNormalization n N,
      integral_map (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
        hf.aestronglyMeasurable]
  have hs (Y : SymmetricMatrix p) (hY : (Y : Matrix (Fin p) (Fin p) ℝ).PosDef) :
      finiteCompressionDetTest Sigma Q c a₀ b₀ (Matrix.symmetricCongruenceLinearMap N.ambient Y) =
        finiteShiftedDetTest c a₀ b₀' Y := by
    simpa only [hblock] using
      compressionNormalization_finiteOuter (m := 0) hSigma Q hQ N hc a₀ b₀ Y hY.posSemidef
  have hselected :
      (∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X ∂nonsingularWishartMeasure n Sigma) =
        ∫ Y, finiteShiftedDetTest c a₀ b₀' Y
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [htransform _ (measurable_finiteCompressionDetTest Sigma Q c a₀ b₀)]
    apply integral_congr_ae
    exact (ae_posDef_nonsingularWishartMeasure n 1).mono hs
  have hremaining :
      (∫ X, affineMaximumProduct 0 k B M a b X ∂nonsingularWishartMeasure n Sigma) =
        ∫ Y, affineMaximumProduct 0 k B M' a b Y
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [htransform _ (continuous_affineMaximumProduct 0 k B M a b ha).measurable]
    simp only [affineMaximumProduct_congruence, M']
  have hjoint :
      (∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X * affineMaximumProduct 0 k B M a b X
        ∂nonsingularWishartMeasure n Sigma) =
        ∫ Y, finiteShiftedDetTest c a₀ b₀' Y * affineMaximumProduct 0 k B M' a b Y
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [htransform _ ((measurable_finiteCompressionDetTest Sigma Q c a₀ b₀).fun_mul
      (continuous_affineMaximumProduct 0 k B M a b ha).measurable)]
    apply integral_congr_ae
    filter_upwards [ae_posDef_nonsingularWishartMeasure n
      (1 : Matrix (Fin p) (Fin p) ℝ)] with Y hY
    rw [hs Y hY, affineMaximumProduct_congruence]
  rw [hselected, hremaining, hjoint]
  exact fullRank_finiteOuter_split_identity hn hc a₀ b₀' ha₀ k B M' a b hB ha

/-- Every full-rank factor in Theorem 5.1 splits throughout `n > p−1`.
The remaining family may overlap arbitrarily, and all expectations may be
infinite. -/
theorem compression_geometric_fullRank_split {p : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (Q : Matrix (Fin p) (Fin p) ℝ) (hQ : Q.rank = p) (hc : 0 ≤ c)
    {κ : Type*} [Fintype κ]
    (k : κ → ℕ) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hM : ∀ i, (M i).rank = k i) (d : κ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (f₀ : ℝ → ℝ) (f : κ → ℝ → ℝ)
    (hf₀ : GeometricallyLogConvex f₀) (hf : ∀ i, GeometricallyLogConvex (f i)) :
    (∫⁻ X, ENNReal.ofReal (f₀ (shiftedCompressionDeterminant Sigma Q c X))
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ i, f i (shiftedCompressionDeterminant Sigma (M i) (d i) X))
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (f₀ (shiftedCompressionDeterminant Sigma Q c X) *
        ∏ i, f i (shiftedCompressionDeterminant Sigma (M i) (d i) X))
        ∂nonsingularWishartMeasure n Sigma := by
  apply compression_geometric_split_of_finite hSigma hn Q hQ hc k M hM d hd f₀ f hf₀ hf
  intro l a₀ b₀ a b ha₀ ha
  exact fullRank_finiteOuter_split hSigma hn Q hQ hc a₀ b₀ ha₀ k
    (fun i => d i • compressionScale Sigma (M i)) M a b
    (fun i => (compressionScale_posDef hSigma (M i) (hM i)).posSemidef.smul (hd i)) ha

end Wishart
end
end CanonicalSource53

section CanonicalSource54
/- Source: Wishart/OuterPairComparison.lean -/



/-! # The unrestricted two-factor comparison for finite outer approximations -/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def finiteMonomialTest (a b : ι → ℝ) (x : ℝ) : ℝ :=
  finiteMaximum (fun j => Real.exp (b j) * x ^ (a j))

theorem measurable_finiteMonomialTest (a b : ι → ℝ) : Measurable (finiteMonomialTest a b) :=
  measurable_finiteMaximum _ fun j => measurable_const.mul (measurable_id.pow_const _)

theorem monotoneOn_finiteMonomialTest (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) :
    MonotoneOn (finiteMonomialTest a b) (Set.Ici 0) := by
  intro x hx y hy hxy
  exact finiteMaximum_mono fun j => mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hx hxy (ha j)) (Real.exp_pos _).le

theorem allFiniteMoments_finiteMonomialTest
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {d : Ω → ℝ} (hd : HasAllFiniteMoments d μ)
    (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) :
    HasAllFiniteMoments (fun z => finiteMonomialTest a b (d z)) μ :=
  hasAllFiniteMoments_finiteMaximum _ fun j => (hd.rpow (ha j)).const_mul (Real.exp (b j))

theorem affineMaximumProduct_unit {p k : ℕ}
    (E : Matrix (Fin k) (Fin k) ℝ) (M : Matrix (Fin p) (Fin k) ℝ)
    (a b : ι → ℝ) (X : SymmetricMatrix p) :
    affineMaximumProduct 0 (fun _ : Unit => k) (fun _ => E) (fun _ => M)
      (fun _ => a) (fun _ => b) X = finiteMonomialTest a b (compressedDeterminant E M X) := by
  simp only [affineMaximumProduct, Fintype.prod_unique, regularizedCompression,
    compressionCLM_apply, zero_smul, add_zero, finiteMonomialTest, compressedDeterminant]

theorem affineMaximumProduct_unit_fun {p k : ℕ}
    (E : Matrix (Fin k) (Fin k) ℝ) (M : Matrix (Fin p) (Fin k) ℝ)
    (a b : ι → ℝ) :
    affineMaximumProduct 0 (fun _ : Unit => k) (fun _ => E) (fun _ => M)
      (fun _ => a) (fun _ => b) =
      fun X => finiteMonomialTest a b (compressedDeterminant E M X) := by
  funext X
  exact affineMaximumProduct_unit E M a b X

theorem monotoneOn_linearShiftedRows_compressedDet_finiteOuter
    {q m p k : ℕ} {ν : ℝ} (hν : (m : ℝ) - 1 < ν)
    (L : Matrix (Fin p) (Fin m) ℝ)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin p) (Fin k) ℝ) (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j)
    (v : Fin q → EuclideanSpace ℝ (Fin p)) :
    MonotoneOn (fun lam : Fin q → ℝ => ∫ x,
      finiteMonomialTest a b (compressedDeterminant E M (linearShiftedRowsSym L v lam x))
        ∂gaussianResidualMeasure q 1 (nonsingularWishartMeasure ν 1))
      (Set.Ici (0 : Fin q → ℝ)) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin m) (Fin m) ℝ)) Matrix.PosDef.one hν
  apply monotoneOn_nonnegative_pi_of_update
  intro lam c
  apply monotoneOn_linearShiftedRows_compressedDet_coordinate_of_integrable hν L hE M
    (measurable_finiteMonomialTest a b) (monotoneOn_finiteMonomialTest a b ha) v lam c
  intro t
  exact (allFiniteMoments_finiteMonomialTest
    (allFiniteMoments_linearShiftedRows_compressedDet hν L E M v (Function.update lam c t))
    a b ha).integrable

theorem monotoneOn_fullSpectralConditionalMoment_singleFiniteOuter
    {q m k : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin (q + m)) (Fin k) ℝ) (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) :
    MonotoneOn (fun lam => fullSpectralConditionalMoment n C K
      (fun X => finiteMonomialTest a b (compressedDeterminant E M X)) lam O)
      (Set.Ici (0 : Fin q → ℝ)) := by
  have hν : (m : ℝ) - 1 < n - q := by push_cast at hn; linarith
  have hgm : Measurable (fun X : SymmetricMatrix (q + m) =>
      finiteMonomialTest a b (compressedDeterminant E M X)) := by
    simpa only [Function.comp_def] using
      (measurable_finiteMonomialTest a b).comp (measurable_compressedDeterminant E M)
  intro lam hlam lam' hlam' hle
  dsimp only
  rw [fullSpectralConditionalMoment_standardNoise n hC K O lam hgm,
    fullSpectralConditionalMoment_standardNoise n hC K O lam' hgm]
  exact monotoneOn_linearShiftedRows_compressedDet_finiteOuter hν
    (regressionNoiseInjection q m * CFC.sqrt C) hE M a b ha (fullSpectralRegressionDirections K O)
      hlam hlam' hle

theorem monotoneOn_fullRegressionSpectralAverage_singleFiniteOuter
    {q m k : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin (q + m)) (Fin k) ℝ) (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) :
    MonotoneOn (fullRegressionSpectralAverage n C K
      (fun X => finiteMonomialTest a b (compressedDeterminant E M X)))
      (Spectral.positiveChamber q) := by
  apply parameterAverageOn_monotoneOn
  · intro lam hlam
    simpa only [affineMaximumProduct_unit_fun, haarFullRegressionIntegrand] using
      integrable_haar_fullSpectralConditionalMoment_finiteOuter hn hC K
        (fun _ : Unit => k) (fun _ => E) (fun _ => M) (fun _ => a) (fun _ => b)
        (fun _ => ha) lam
  · intro lam hlam lam' hlam' hle
    exact Filter.Eventually.of_forall fun O =>
      monotoneOn_fullSpectralConditionalMoment_singleFiniteOuter hn hC K ↑O hE M a b ha
        (fun i => (hlam.2 i).le) (fun i => (hlam'.2 i).le) hle

theorem compression_finiteOuter_pair {p q k : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q) (hc : 0 ≤ c)
    (a₀ b₀ a b : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j) (ha : ∀ j, 0 ≤ a j)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef) (M : Matrix (Fin p) (Fin k) ℝ) :
    (∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, finiteMonomialTest a b (compressedDeterminant E M X)
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X *
        finiteMonomialTest a b (compressedDeterminant E M X) ∂nonsingularWishartMeasure n Sigma := by
  have hqp : q ≤ p := (compressionNormalization hSigma Q hQ).q_le
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hqp
  have h := compression_finiteOuter_split_of_whitened_split hSigma hn Q hQ hc a₀ b₀ ha₀
    (fun _ : Unit => k) (fun _ => E) (fun _ => M) (fun _ => a) (fun _ => b)
    (fun _ => hE) (fun _ => ha) (by
      apply identity_leading_finiteOuter_split_of_spectral_monotone hn hc _ _ ha₀
        (fun _ : Unit => k) (fun _ => E) _ (fun _ => a) (fun _ => b)
        (fun _ => hE) (fun _ => ha)
      simpa only [affineMaximumProduct_unit_fun] using
        monotoneOn_fullRegressionSpectralAverage_singleFiniteOuter hn Matrix.PosDef.one
          (0 : Matrix (Fin q) (Fin m) ℝ) hE
          ((compressionNormalization hSigma Q hQ).ambientᵀ * M) a b ha)
  simpa only [affineMaximumProduct_unit] using h

end Wishart
end
end CanonicalSource54

section CanonicalSource55
/- Source: Wishart/GeometricPairSplit.lean -/



/-! # Unrestricted geometric outer functions on two overlapping compressions -/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

theorem compression_geometric_pair {p q k : ℕ} {n c d : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q)
    (M : Matrix (Fin p) (Fin k) ℝ) (hM : M.rank = k)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (f g : ℝ → ℝ) (hf : GeometricallyLogConvex f) (hg : GeometricallyLogConvex g) :
    (∫⁻ X, ENNReal.ofReal (f (shiftedCompressionDeterminant Sigma Q c X))
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (g (shiftedCompressionDeterminant Sigma M d X))
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (f (shiftedCompressionDeterminant Sigma Q c X) *
        g (shiftedCompressionDeterminant Sigma M d X))
        ∂nonsingularWishartMeasure n Sigma := by
  have h := compression_geometric_split_of_finite hSigma hn Q hQ hc
    (fun _ : Unit => k) (fun _ => M) (fun _ => hM) (fun _ => d) (fun _ => hd)
    f (fun _ => g) hf (fun _ => hg) (by
      intro l a₀ b₀ a b ha₀ ha
      have hpair := compression_finiteOuter_pair hSigma hn Q hQ hc
        a₀ b₀ (a ()) (b ()) ha₀ (ha ())
        ((compressionScale_posDef hSigma M hM).posSemidef.smul hd) M
      simpa only [affineMaximumProduct, Fintype.prod_unique, regularizedCompression,
        compressionCLM_apply, zero_smul, add_zero, finiteMonomialTest, compressedDeterminant]
        using hpair)
  simpa only [Fintype.prod_unique] using h

end Wishart
end
end CanonicalSource55

section CanonicalSource56
/- Source: Wishart/RankIteration.lean -/



/-!
# The largest-plus-third-largest rank condition

The finite iteration removes constant and full-rank factors first, then selects
a factor of smallest remaining rank. The last pair uses the unrestricted pair
comparison. A permutation-invariant condition on triples is proved equivalent
to the manuscript's largest-plus-third-largest condition after descending sort.
-/

noncomputable section

open scoped Classical

namespace WishartVerification.MomentAssembly

variable {ι : Type*} [DecidableEq ι]

theorem product_singletons_le_of_exists_split (m : Finset ι → ℝ)
    (hempty : m ∅ = 1) (hpos : ∀ i, 0 ≤ m {i})
    (hsplit : ∀ J : Finset ι, J.Nonempty →
      ∃ i ∈ J, m {i} * m (J.erase i) ≤ m J) (J : Finset ι) :
    (∏ i ∈ J, m {i}) ≤ m J := by
  induction J using Finset.strongInductionOn with
  | _ J ih =>
      by_cases hJ : J.Nonempty
      · obtain ⟨i, hi, hs⟩ := hsplit J hJ
        rw [← Finset.mul_prod_erase J (fun i => m {i}) hi]
        exact (mul_le_mul_of_nonneg_left
          (ih (J.erase i) (Finset.erase_ssubset hi)) (hpos i)).trans hs
      · have hzero : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
        simp [hzero, hempty]

/-- For any three distinct active proper factors, the sum of the smallest
rank and either other rank meets the selected-factor threshold. -/
def rankTripleThreshold (rank : ι → ℕ) (A : Finset ι) (p : ℕ) (n : ℝ) : Prop :=
  ∀ i ∈ A, ∀ j ∈ A, ∀ k ∈ A,
    i ≠ j → i ≠ k → j ≠ k → rank i ≤ rank j → rank i ≤ rank k →
      min ((rank i : ℝ) + rank j) ((p : ℝ) + 1) ≤ n

theorem rankTripleThreshold_of_card_le_two (rank : ι → ℕ) (A : Finset ι)
    (p : ℕ) (n : ℝ) (hA : A.card ≤ 2) : rankTripleThreshold rank A p n := by
  intro i hi j hj k hk hij hik hjk _ _
  have hsub : ({i, j, k} : Finset ι) ⊆ A := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> assumption
  have hcard : ({i, j, k} : Finset ι).card = 3 := by simp [hij, hik, hjk]
  have hle := Finset.card_le_card hsub
  omega

/-- All combinatorial choices in the rank-ordered factorization are justified
here. The analytic split inputs are explicit and are instantiated separately. -/
theorem product_singletons_le_by_rank (m : Finset ι → ℝ)
    (rank : ι → ℕ) (A : Finset ι) (p : ℕ) (n : ℝ)
    (hempty : m ∅ = 1) (hpos : ∀ i, 0 ≤ m {i})
    (houtside : ∀ J i, i ∈ J → i ∉ A → m {i} * m (J.erase i) ≤ m J)
    (hpair : ∀ J i, i ∈ J → J.card ≤ 2 → m {i} * m (J.erase i) ≤ m J)
    (hrank : ∀ J i, i ∈ J → J ⊆ A →
      (∀ j ∈ J.erase i, min ((rank i : ℝ) + rank j) ((p : ℝ) + 1) ≤ n) →
      m {i} * m (J.erase i) ≤ m J)
    (hthreshold : rankTripleThreshold rank A p n) (J : Finset ι) :
    (∏ i ∈ J, m {i}) ≤ m J := by
  apply product_singletons_le_of_exists_split m hempty hpos _ J
  intro S hS
  by_cases hout : ∃ i ∈ S, i ∉ A
  · obtain ⟨i, hi, hiA⟩ := hout
    exact ⟨i, hi, houtside S i hi hiA⟩
  have hSA : S ⊆ A := by
    intro i hi
    by_contra hiA
    exact hout ⟨i, hi, hiA⟩
  by_cases hsmall : S.card ≤ 2
  · obtain ⟨i, hi⟩ := hS
    exact ⟨i, hi, hpair S i hi hsmall⟩
  obtain ⟨i, hi, hmin⟩ := S.exists_min_image rank hS
  refine ⟨i, hi, hrank S i hi hSA ?_⟩
  intro j hj
  have hjS := Finset.mem_of_mem_erase hj
  have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
  have hex : ∃ k ∈ S, k ≠ i ∧ k ≠ j := by
    by_contra hnone
    have hsub : S ⊆ ({i, j} : Finset ι) := by
      intro k hk
      by_cases hki : k = i
      · simp [hki]
      · have hkj : k = j := by
          by_contra hkj
          exact hnone ⟨k, hk, hki, hkj⟩
        simp [hkj]
    exact hsmall ((Finset.card_le_card hsub).trans Finset.card_le_two)
  obtain ⟨k, hk, hki, hkj⟩ := hex
  exact hthreshold i (hSA hi) j (hSA hjS) k (hSA hk)
    hij hki.symm hkj.symm (hmin j hjS) (hmin k hk)

theorem rankTripleThreshold_equiv {κ : Type*} [Fintype κ] [DecidableEq κ]
    (rank : ι → ℕ) (A : Finset ι) (e : κ ≃ A) (p : ℕ) (n : ℝ) :
    rankTripleThreshold rank A p n ↔
      rankTripleThreshold (fun i => rank (e i)) Finset.univ p n := by
  constructor
  · intro h i _ j _ k _ hij hik hjk hrij hrik
    apply h (e i) (e i).property (e j) (e j).property (e k) (e k).property
    · intro heq
      exact hij (e.injective (Subtype.ext heq))
    · intro heq
      exact hik (e.injective (Subtype.ext heq))
    · intro heq
      exact hjk (e.injective (Subtype.ext heq))
    · exact hrij
    · exact hrik
  · intro h i hi j hj k hk hij hik hjk hrij hrik
    have hne (a b : A) (hab : (a : ι) ≠ b) : e.symm a ≠ e.symm b := by
      intro heq
      exact hab (congrArg Subtype.val (e.symm.injective heq))
    have h' := h (e.symm ⟨i, hi⟩) (Finset.mem_univ _)
      (e.symm ⟨j, hj⟩) (Finset.mem_univ _) (e.symm ⟨k, hk⟩) (Finset.mem_univ _)
      (hne _ _ hij) (hne _ _ hik) (hne _ _ hjk)
      (by simpa only [Equiv.apply_symm_apply] using hrij)
      (by simpa only [Equiv.apply_symm_apply] using hrik)
    simpa only [Equiv.apply_symm_apply] using h'

def descendingRankEquiv (rank : ι → ℕ) (A : Finset ι) :
    Fin (Fintype.card A) ≃ A :=
  (Tuple.sortDesc (fun i => rank ((Fintype.equivFin A).symm i))).trans
    (Fintype.equivFin A).symm

def descendingRanks (rank : ι → ℕ) (A : Finset ι) : Fin (Fintype.card A) → ℕ :=
  fun i => rank (descendingRankEquiv rank A i)

theorem antitone_descendingRanks (rank : ι → ℕ) (A : Finset ι) :
    Antitone (descendingRanks rank A) :=
  Tuple.antitone_sortDesc (fun i => rank ((Fintype.equivFin A).symm i))

theorem rankTripleThreshold_iff_largest_third {d : ℕ} (hd : 3 ≤ d)
    (rank : Fin d → ℕ) (hsorted : Antitone rank) (p : ℕ) (n : ℝ) :
    rankTripleThreshold rank Finset.univ p n ↔
      min ((rank ⟨0, by omega⟩ : ℝ) + rank ⟨2, by omega⟩) ((p : ℝ) + 1) ≤ n := by
  constructor
  · intro h
    have h' := h ⟨2, by omega⟩ (Finset.mem_univ _)
      ⟨0, by omega⟩ (Finset.mem_univ _) ⟨1, by omega⟩ (Finset.mem_univ _)
      (by intro heq; have hv : (2 : ℕ) = 0 := congrArg Fin.val heq; omega)
      (by intro heq; have hv : (2 : ℕ) = 1 := congrArg Fin.val heq; omega)
      (by intro heq; have hv : (0 : ℕ) = 1 := congrArg Fin.val heq; omega)
      (hsorted (by change (0 : ℕ) ≤ 2; decide))
      (hsorted (by change (1 : ℕ) ≤ 2; decide))
    simpa only [add_comm] using h'
  · intro h i _ j _ k _ hij hik hjk hrij hrik
    have hijv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hikv : i.val ≠ k.val := fun h => hik (Fin.ext h)
    have hjkv : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    have hindices : 2 ≤ i.val ∨ 2 ≤ j.val ∨ 2 ≤ k.val := by omega
    have hi3 : rank i ≤ rank ⟨2, by omega⟩ := by
      rcases hindices with hi | hj | hk
      · exact hsorted hi
      · exact hrij.trans (hsorted hj)
      · exact hrik.trans (hsorted hk)
    have hj1 : rank j ≤ rank ⟨0, by omega⟩ := hsorted (Nat.zero_le _)
    have hsum : (rank i : ℝ) + rank j ≤
        (rank ⟨0, by omega⟩ : ℝ) + rank ⟨2, by omega⟩ := by
      have hi3' : (rank i : ℝ) ≤ rank ⟨2, by omega⟩ := Nat.cast_le.mpr hi3
      have hj1' : (rank j : ℝ) ≤ rank ⟨0, by omega⟩ := Nat.cast_le.mpr hj1
      linarith
    exact (min_le_min_right _ hsum).trans h

/-- The condition is vacuous when at most two active proper factors remain;
otherwise it reads precisely `n ≥ min(k_(1)+k_(3), p+1)` in descending order. -/
def orderedRankThreshold (rank : ι → ℕ) (A : Finset ι) (p : ℕ) (n : ℝ) : Prop :=
  ∀ h : 3 ≤ Fintype.card A,
    min ((descendingRanks rank A ⟨0, by omega⟩ : ℝ) +
      descendingRanks rank A ⟨2, by omega⟩) ((p : ℝ) + 1) ≤ n

theorem orderedRankThreshold_iff (rank : ι → ℕ) (A : Finset ι) (p : ℕ) (n : ℝ) :
    orderedRankThreshold rank A p n ↔ rankTripleThreshold rank A p n := by
  rw [rankTripleThreshold_equiv rank A (descendingRankEquiv rank A) p n]
  change orderedRankThreshold rank A p n ↔
    rankTripleThreshold (descendingRanks rank A) Finset.univ p n
  by_cases hd : 3 ≤ Fintype.card A
  · rw [rankTripleThreshold_iff_largest_third hd _ (antitone_descendingRanks rank A)]
    exact ⟨fun h => h hd, fun h _ => h⟩
  · constructor
    · intro _
      apply rankTripleThreshold_of_card_le_two
      simpa only [Finset.card_univ, Fintype.card_fin] using (show Fintype.card A ≤ 2 by omega)
    · intro _ h
      exact (hd h).elim

end WishartVerification.MomentAssembly
end
end CanonicalSource56

section CanonicalSource57
/- Source: Wishart/ExtendedRankIteration.lean -/



/-! # Finite rank iteration for extended nonnegative expectations

The same finite combinatorial argument is valid in ENNReal, including infinite
moments. No subtraction, division, or cancellation of an infinite quantity occurs.
-/

noncomputable section

open scoped Classical ENNReal BigOperators

namespace WishartVerification.MomentAssembly

variable {ι : Type*} [DecidableEq ι]

theorem extended_product_singletons_le_of_exists_split (m : Finset ι → ℝ≥0∞)
    (hempty : m ∅ = 1) (hpos : ∀ i, 0 ≤ m {i})
    (hsplit : ∀ J : Finset ι, J.Nonempty →
      ∃ i ∈ J, m {i} * m (J.erase i) ≤ m J) (J : Finset ι) :
    (∏ i ∈ J, m {i}) ≤ m J := by
  induction J using Finset.strongInductionOn with
  | _ J ih =>
      by_cases hJ : J.Nonempty
      · obtain ⟨i, hi, hs⟩ := hsplit J hJ
        rw [← Finset.mul_prod_erase J (fun i => m {i}) hi]
        exact (mul_le_mul_of_nonneg_left
          (ih (J.erase i) (Finset.erase_ssubset hi)) (hpos i)).trans hs
      · have hzero : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
        simp [hzero, hempty]

theorem extended_product_singletons_le_by_rank (m : Finset ι → ℝ≥0∞)
    (rank : ι → ℕ) (A : Finset ι) (p : ℕ) (n : ℝ)
    (hempty : m ∅ = 1) (hpos : ∀ i, 0 ≤ m {i})
    (houtside : ∀ J i, i ∈ J → i ∉ A → m {i} * m (J.erase i) ≤ m J)
    (hpair : ∀ J i, i ∈ J → J.card ≤ 2 → m {i} * m (J.erase i) ≤ m J)
    (hrank : ∀ J i, i ∈ J → J ⊆ A →
      (∀ j ∈ J.erase i, min ((rank i : ℝ) + rank j) ((p : ℝ) + 1) ≤ n) →
      m {i} * m (J.erase i) ≤ m J)
    (hthreshold : rankTripleThreshold rank A p n) (J : Finset ι) :
    (∏ i ∈ J, m {i}) ≤ m J := by
  apply extended_product_singletons_le_of_exists_split m hempty hpos _ J
  intro S hS
  by_cases hout : ∃ i ∈ S, i ∉ A
  · obtain ⟨i, hi, hiA⟩ := hout
    exact ⟨i, hi, houtside S i hi hiA⟩
  have hSA : S ⊆ A := by
    intro i hi
    by_contra hiA
    exact hout ⟨i, hi, hiA⟩
  by_cases hsmall : S.card ≤ 2
  · obtain ⟨i, hi⟩ := hS
    exact ⟨i, hi, hpair S i hi hsmall⟩
  obtain ⟨i, hi, hmin⟩ := S.exists_min_image rank hS
  refine ⟨i, hi, hrank S i hi hSA ?_⟩
  intro j hj
  have hjS := Finset.mem_of_mem_erase hj
  have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
  have hex : ∃ k ∈ S, k ≠ i ∧ k ≠ j := by
    by_contra hnone
    have hsub : S ⊆ ({i, j} : Finset ι) := by
      intro k hk
      by_cases hki : k = i
      · simp [hki]
      · have hkj : k = j := by
          by_contra hkj
          exact hnone ⟨k, hk, hki, hkj⟩
        simp [hkj]
    exact hsmall ((Finset.card_le_card hsub).trans Finset.card_le_two)
  obtain ⟨k, hk, hki, hkj⟩ := hex
  exact hthreshold i (hSA hi) j (hSA hjS) k (hSA hk)
    hij hki.symm hkj.symm (hmin j hjS) (hmin k hk)


end WishartVerification.MomentAssembly
end
end CanonicalSource57

section CanonicalSource58
/- Source: Wishart/GeometricCompressionProducts.lean -/



/-!
# The full geometric determinant product inequality

The factors, their constant-value test, and their extended expectations are
literal functions of positive definite matrices. Constant and full-rank factors
are removed before sorting the remaining ranks. The rank iteration uses only
multiplication and order in ENNReal, so infinite moments require no cancellation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification WishartVerification.MomentAssembly
open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

structure GeometricCompressionFamily (p : ℕ) (ι : Type*) where
  size : ι → ℕ
  matrix : ∀ i, Matrix (Fin p) (Fin (size i)) ℝ
  full_rank : ∀ i, (matrix i).rank = size i
  shift : ι → ℝ
  shift_nonneg : ∀ i, 0 ≤ shift i
  outer : ι → ℝ → ℝ
  geometric : ∀ i, GeometricallyLogConvex (outer i)

namespace GeometricCompressionFamily

variable {p : ℕ} {ι : Type*} [DecidableEq ι]
variable (F : GeometricCompressionFamily p ι) (Sigma : Matrix (Fin p) (Fin p) ℝ)

def factor (i : ι) (X : SymmetricMatrix p) : ℝ :=
  F.outer i (shiftedCompressionDeterminant Sigma (F.matrix i) (F.shift i) X)

def subproduct (J : Finset ι) (X : SymmetricMatrix p) : ℝ :=
  ∏ i ∈ J, F.factor Sigma i X

def moment (n : ℝ) (J : Finset ι) : ℝ≥0∞ :=
  ∫⁻ X, ENNReal.ofReal (F.subproduct Sigma J X) ∂nonsingularWishartMeasure n Sigma

/-- Constancy is tested on the entire positive definite cone, the actual support
of the nonsingular law. It is not a premise about an unknown conditional moment. -/
def ConstantFactor (i : ι) : Prop :=
  ∃ c : ℝ, ∀ X : SymmetricMatrix p,
    (X : Matrix (Fin p) (Fin p) ℝ).PosDef → F.factor Sigma i X = c

def activeProper [Fintype ι] : Finset ι :=
  Finset.univ.filter (fun i => F.size i < p ∧ ¬ F.ConstantFactor Sigma i)

theorem size_le (i : ι) : F.size i ≤ p := by
  rw [← F.full_rank i]
  exact (F.matrix i).rank_le_height

theorem factor_pos (hSigma : Sigma.PosDef) (i : ι) {X : SymmetricMatrix p}
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef) : 0 < F.factor Sigma i X :=
  (F.geometric i).positive _
    (shiftedCompressionDeterminant_pos hSigma (F.matrix i) (F.full_rank i)
      (F.shift_nonneg i) hX)

theorem subproduct_pos (hSigma : Sigma.PosDef) (J : Finset ι) {X : SymmetricMatrix p}
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef) : 0 < F.subproduct Sigma J X :=
  Finset.prod_pos (fun i _ => F.factor_pos Sigma hSigma i hX)

theorem aemeasurable_factor {n : ℝ} (hSigma : Sigma.PosDef) (i : ι) :
    AEMeasurable (F.factor Sigma i) (nonsingularWishartMeasure n Sigma) := by
  apply aemeasurable_geometric_outer_comp (F.geometric i)
    (measurable_shiftedCompressionDeterminant Sigma (F.matrix i) (F.shift i))
  exact (ae_posDef_nonsingularWishartMeasure n Sigma).mono fun X hX =>
    shiftedCompressionDeterminant_pos hSigma (F.matrix i) (F.full_rank i)
      (F.shift_nonneg i) hX

theorem aemeasurable_subproduct {n : ℝ} (hSigma : Sigma.PosDef) (J : Finset ι) :
    AEMeasurable (F.subproduct Sigma J) (nonsingularWishartMeasure n Sigma) :=
  Finset.aemeasurable_fun_prod J (fun i _ => F.aemeasurable_factor Sigma hSigma i)

@[simp] theorem moment_singleton (n : ℝ) (i : ι) :
    F.moment Sigma n {i} =
      ∫⁻ X, ENNReal.ofReal (F.factor Sigma i X) ∂nonsingularWishartMeasure n Sigma := by
  simp only [moment, subproduct, Finset.prod_singleton]

theorem moment_empty {n : ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n) :
    F.moment Sigma n ∅ = 1 := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hSigma hn
  simp only [moment, subproduct, Finset.prod_empty, ENNReal.ofReal_one,
    lintegral_const, measure_univ, mul_one]

theorem moment_split (n : ℝ) (J : Finset ι) (i : ι) (hi : i ∈ J) :
    F.moment Sigma n J =
      ∫⁻ X, ENNReal.ofReal (F.factor Sigma i X * F.subproduct Sigma (J.erase i) X)
        ∂nonsingularWishartMeasure n Sigma := by
  apply lintegral_congr_ae
  filter_upwards with X
  congr 1
  exact (Finset.mul_prod_erase J (fun i => F.factor Sigma i X) hi).symm

theorem moment_constant_split {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (J : Finset ι) (i : ι) (hi : i ∈ J) (hconst : F.ConstantFactor Sigma i) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) = F.moment Sigma n J := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hSigma hn
  obtain ⟨c, hc⟩ := hconst
  have hcpos : 0 < c := by
    rw [← hc ⟨Sigma, hSigma.isHermitian.isSelfAdjoint⟩ hSigma]
    exact F.factor_pos Sigma hSigma i hSigma
  have hcae : ∀ᵐ X ∂nonsingularWishartMeasure n Sigma, F.factor Sigma i X = c :=
    (ae_posDef_nonsingularWishartMeasure n Sigma).mono fun X hX => hc X hX
  have hsingle : F.moment Sigma n {i} = ENNReal.ofReal c := by
    rw [F.moment_singleton]
    calc
      (∫⁻ X, ENNReal.ofReal (F.factor Sigma i X) ∂nonsingularWishartMeasure n Sigma) =
          ∫⁻ _X, ENNReal.ofReal c ∂nonsingularWishartMeasure n Sigma :=
        lintegral_congr_ae (hcae.mono fun X hX => congrArg ENNReal.ofReal hX)
      _ = _ := by simp only [lintegral_const, measure_univ, mul_one]
  rw [hsingle, F.moment_split Sigma n J i hi]
  calc
    ENNReal.ofReal c * F.moment Sigma n (J.erase i) =
        ∫⁻ X, ENNReal.ofReal c * ENNReal.ofReal (F.subproduct Sigma (J.erase i) X)
          ∂nonsingularWishartMeasure n Sigma :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hcae] with X hX
      rw [hX, ENNReal.ofReal_mul hcpos.le]

theorem moment_selected_split {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (J : Finset ι) (i : ι) (hi : i ∈ J)
    (hsize : ∀ j ∈ J.erase i,
      min ((F.size i : ℝ) + F.size j) ((p : ℝ) + 1) ≤ n) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J := by
  have h := compression_geometric_selected_split hSigma hn
    (F.matrix i) (F.full_rank i) (F.shift_nonneg i)
    (fun j : J.erase i => F.size j) (fun j => F.matrix j) (fun j => F.full_rank j)
    (fun j => F.shift j) (fun j => F.shift_nonneg j)
    (F.outer i) (fun j => F.outer j) (F.geometric i) (fun j => F.geometric j)
    (fun j => hsize j j.property)
  change (∫⁻ X, ENNReal.ofReal (F.factor Sigma i X) ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ j : J.erase i, F.factor Sigma (j : ι) X)
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (F.factor Sigma i X *
        ∏ j : J.erase i, F.factor Sigma (j : ι) X) ∂nonsingularWishartMeasure n Sigma at h
  rw [F.moment_singleton, F.moment_split Sigma n J i hi]
  have hprod (X : SymmetricMatrix p) :
      (∏ j : J.erase i, F.factor Sigma (j : ι) X) =
        F.subproduct Sigma (J.erase i) X :=
    Finset.prod_coe_sort (J.erase i) (fun j => F.factor Sigma j X)
  simp_rw [hprod] at h
  simpa only [moment] using h

theorem moment_full_rank_split {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (J : Finset ι) (i : ι) (hi : i ∈ J) (hfull : F.size i = p) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J := by
  have hsplit (q : ℕ) (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q) (hqp : q = p) :
      (∫⁻ X, ENNReal.ofReal (F.outer i (shiftedCompressionDeterminant Sigma Q (F.shift i) X))
        ∂nonsingularWishartMeasure n Sigma) * F.moment Sigma n (J.erase i) ≤
        ∫⁻ X, ENNReal.ofReal (F.outer i (shiftedCompressionDeterminant Sigma Q (F.shift i) X) *
          F.subproduct Sigma (J.erase i) X) ∂nonsingularWishartMeasure n Sigma := by
    subst q
    have h := compression_geometric_fullRank_split hSigma hn Q hQ (F.shift_nonneg i)
      (fun j : J.erase i => F.size j) (fun j => F.matrix j) (fun j => F.full_rank j)
      (fun j => F.shift j) (fun j => F.shift_nonneg j)
      (F.outer i) (fun j => F.outer j) (F.geometric i) (fun j => F.geometric j)
    change (∫⁻ X, ENNReal.ofReal
        (F.outer i (shiftedCompressionDeterminant Sigma Q (F.shift i) X))
        ∂nonsingularWishartMeasure n Sigma) *
        (∫⁻ X, ENNReal.ofReal (∏ j : J.erase i, F.factor Sigma (j : ι) X)
          ∂nonsingularWishartMeasure n Sigma) ≤
        ∫⁻ X, ENNReal.ofReal
          (F.outer i (shiftedCompressionDeterminant Sigma Q (F.shift i) X) *
            ∏ j : J.erase i, F.factor Sigma (j : ι) X)
          ∂nonsingularWishartMeasure n Sigma at h
    have hprod (X : SymmetricMatrix p) :
        (∏ j : J.erase i, F.factor Sigma (j : ι) X) =
          F.subproduct Sigma (J.erase i) X :=
      Finset.prod_coe_sort (J.erase i) (fun j => F.factor Sigma j X)
    simp_rw [hprod] at h
    simpa only [moment] using h
  rw [F.moment_singleton, F.moment_split Sigma n J i hi]
  exact hsplit (F.size i) (F.matrix i) (F.full_rank i) hfull

theorem moment_pair_split {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (J : Finset ι) (i : ι) (hi : i ∈ J) (hsmall : J.card ≤ 2) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J := by
  have hcard : (J.erase i).card ≤ 1 := by rw [Finset.card_erase_of_mem hi]; omega
  by_cases hrest : J.erase i = ∅
  · have hJ : J = {i} := by
      have h := Finset.insert_erase hi
      rw [hrest, Finset.insert_empty] at h
      exact h.symm
    rw [hrest, hJ, F.moment_empty Sigma hSigma hn, mul_one]
  · have hcard' : (J.erase i).card = 1 := by
      have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hrest)
      omega
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard'
    have h := compression_geometric_pair hSigma hn
      (F.matrix i) (F.full_rank i) (F.matrix j) (F.full_rank j)
      (F.shift_nonneg i) (F.shift_nonneg j)
      (F.outer i) (F.outer j) (F.geometric i) (F.geometric j)
    rw [F.moment_singleton, F.moment_split Sigma n J i hi, hj, F.moment_singleton]
    simpa only [factor, subproduct, Finset.prod_singleton] using h

theorem moment_split_outside_activeProper [Fintype ι] {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (J : Finset ι) (i : ι) (hi : i ∈ J) (hinactive : i ∉ F.activeProper Sigma) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J := by
  by_cases hc : F.ConstantFactor Sigma i
  · exact (F.moment_constant_split Sigma hSigma hn J i hi hc).le
  have hfull : F.size i = p := by
    have hle := F.size_le i
    by_contra hne
    have hklt : F.size i < p := lt_of_le_of_ne hle hne
    exact hinactive (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hklt, hc⟩)
  exact F.moment_full_rank_split Sigma hSigma hn J i hi hfull

/-- A reusable form permits any retained set containing every nonconstant proper
factor. Its outside-set hypothesis concerns only literal pointwise constancy or
matrix rank; it is not an unproved analytic comparison. -/
theorem product_moments_le_of_rank_test {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (A : Finset ι) (houtside : ∀ i, i ∉ A → F.size i = p ∨ F.ConstantFactor Sigma i)
    (hsize : orderedRankThreshold F.size A p n) (J : Finset ι) :
    (∏ i ∈ J, F.moment Sigma n {i}) ≤ F.moment Sigma n J := by
  apply extended_product_singletons_le_by_rank (F.moment Sigma n) F.size A p n
    (F.moment_empty Sigma hSigma hn) (fun _ => zero_le) _
    (F.moment_pair_split Sigma hSigma hn)
    (fun S i hi _ hs => F.moment_selected_split Sigma hSigma hn S i hi hs)
    ((orderedRankThreshold_iff F.size A p n).mp hsize) J
  intro S i hi hiA
  rcases houtside i hiA with hfull | hc
  · exact F.moment_full_rank_split Sigma hSigma hn S i hi hfull
  · exact (F.moment_constant_split Sigma hSigma hn S i hi hc).le

/-- The full product assertion of Theorem 5.1 for the entire geometric outer
class, with exactly the sorted largest-plus-third-largest retained-rank test. -/
theorem product_moments_le [Fintype ι] {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (hsize : orderedRankThreshold F.size (F.activeProper Sigma) p n) (J : Finset ι) :
    (∏ i ∈ J, F.moment Sigma n {i}) ≤ F.moment Sigma n J := by
  apply extended_product_singletons_le_by_rank (F.moment Sigma n) F.size
    (F.activeProper Sigma) p n (F.moment_empty Sigma hSigma hn) (fun _ => zero_le)
    (F.moment_split_outside_activeProper Sigma hSigma hn)
    (F.moment_pair_split Sigma hSigma hn)
    (fun S i hi _ hs => F.moment_selected_split Sigma hSigma hn S i hi hs)
    ((orderedRankThreshold_iff F.size (F.activeProper Sigma) p n).mp hsize) J

theorem product_integrals_le_integral_product [Fintype ι] {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (hsize : orderedRankThreshold F.size (F.activeProper Sigma) p n) :
    (∏ i, ∫⁻ X, ENNReal.ofReal (F.factor Sigma i X) ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (∏ i, F.factor Sigma i X) ∂nonsingularWishartMeasure n Sigma := by
  simpa only [moment_singleton, moment, subproduct, Finset.prod_singleton] using
    F.product_moments_le Sigma hSigma hn hsize Finset.univ

end GeometricCompressionFamily

end Wishart
end
end CanonicalSource58

section CanonicalSource59
/- Source: Wishart/PrekopaLeindler.lean -/
/-
Copyright (c) 2024 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in
LICENSES/AsymptoticStatistics-APACHE-2.0.txt.

Adapted from https://github.com/junwei-lu/Lean-Asymptotic-Statistical-Theory,
commit 8e7f22c88cc3280e898005b6445d94c581dd8b4d,
AsymptoticStatistics/ForMathlib/PrekopaLeindler.lean.
Local modifications: Lean 4.36 module/public import declarations; namespace;
updated stale proof-status comments. Further compatibility changes, if any,
are recorded in audit/prekopa_source.json and version control.
-/


/-!
Asymptotic Statistics — Prékopa-Leindler inequality.

The functional generalisation of Brunn-Minkowski. Foundational tool for
log-concave measure theory; the route by which we prove Anderson's lemma
(`ForMathlib/Anderson.lean`) for multivariate Gaussian shifts.

Mathlib has neither Prékopa-Leindler nor Brunn-Minkowski directly. We build
the 1D form first, then n-dim by induction over Fubini (each marginal is
log-concave by 1D PL applied fibre-wise).

The proof of `prekopaLeindler_1d` is assembled from explicit proved sublemmas,
including one-dimensional Brunn–Minkowski. All definitions and proof terms
below are retained from the pinned upstream source, apart from the documented
namespace and module-system adaptations.
-/


open MeasureTheory Set
open scoped ENNReal NNReal Pointwise Topology

namespace Wishart.PrekopaLeindler

/-! ## 1D Prékopa-Leindler — sub-helpers

The 1D PL proof factors as four steps, exposed as named sub-helpers so each
step is locally identifiable:

1. **Level-set inclusion** (`prekopaLeindler_1d_levelInclusion`): for `α > 0`,
   `t • {f > α} + (1-t) • {g > α} ⊆ {h > α}`, via the pointwise hypothesis
   on `h` and the trivial identity `α^t · α^(1-t) = α`.

2. **1D Brunn-Minkowski** (`oneDim_brunn_minkowski_le`): for
   nonempty measurable `A, B ⊆ ℝ` with `A + B ⊆ C` measurable,
   `volume A + volume B ≤ volume C`.

3. **Level-measure bound** (`prekopaLeindler_1d_levelMeasureBound`):
   combines (1) + (2) + smul-set scaling
   (`Measure.addHaar_smul_of_nonneg` with `finrank ℝ ℝ = 1`) to give
   `t · m({f>α}) + (1-t) · m({g>α}) ≤ m({h>α})` for `α > 0`.

4. **Integral assembly**: layer-cake on ENNReal-valued functions
   (`lintegral_eq_lintegral_meas_lt_ennreal`, reducible from Mathlib's
   ℝ-valued form via truncation + MCT) plus weighted AM-GM lifted to ENNReal
   (`ennreal_geom_mean_le_arith_mean2_weighted`, lifted from
   `Real.geom_mean_le_arith_mean2_weighted`).
-/

/-- **Level-set inclusion (1D PL).**

For `t ∈ (0, 1)` and finite `α > 0`, if `f, g, h : ℝ → ℝ≥0∞` satisfy the PL
pointwise hypothesis, then for `x ∈ {f > α}` and `y ∈ {g > α}`:
  `h(t x + (1-t) y) ≥ f(x)^t · g(y)^(1-t) > α^t · α^(1-t) = α`.

Equivalently:
  `t • {x | α < f x} + (1-t) • {y | α < g y} ⊆ {z | α < h z}`. -/
private theorem prekopaLeindler_1d_levelInclusion
    {f g h : ℝ → ℝ≥0∞}
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    {α : ℝ≥0∞} (hα_pos : 0 < α) (hα_top : α ≠ ⊤) :
    t • {x | α < f x} + (1 - t) • {y | α < g y} ⊆ {z | α < h z} := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  rintro z hz
  rw [Set.mem_add] at hz
  obtain ⟨_, hu, _, hv, rfl⟩ := hz
  rw [Set.mem_smul_set] at hu hv
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨y, hy, rfl⟩ := hv
  -- `hx : α < f x`, `hy : α < g y`. Goal: `α < h (t * x + (1 - t) * y)`.
  simp only [smul_eq_mul, Set.mem_setOf_eq] at hx hy ⊢
  -- Step 1: `α = α ^ t * α ^ (1 - t)` (using `α ∈ (0, ∞)`).
  have h_alpha_split : α = α ^ t * α ^ (1 - t) := by
    rw [← ENNReal.rpow_add t (1 - t) hα_pos.ne' hα_top]
    have ht_one : t + (1 - t) = (1 : ℝ) := by ring
    rw [ht_one, ENNReal.rpow_one]
  -- Step 2: `α ^ t < f(x) ^ t` and `α ^ (1-t) < g(y) ^ (1-t)`.
  have h1 : α ^ t < f x ^ t := ENNReal.rpow_lt_rpow hx ht_pos
  have h2 : α ^ (1 - t) < g y ^ (1 - t) := ENNReal.rpow_lt_rpow hy h1t_pos
  -- Step 3: multiply.
  have h3 : α ^ t * α ^ (1 - t) < f x ^ t * g y ^ (1 - t) := ENNReal.mul_lt_mul h1 h2
  -- Step 4: chain with the PL hypothesis at (x, y).
  calc α = α ^ t * α ^ (1 - t) := h_alpha_split
    _ < f x ^ t * g y ^ (1 - t) := h3
    _ ≤ h (t * x + (1 - t) * y) := h_le x y

/-- **1D Brunn-Minkowski (compact case).**

For nonempty compact `K_A, K_B ⊆ ℝ`:
$$\text{vol}(K_A) + \text{vol}(K_B) \le \text{vol}(K_A + K_B).$$

**Proof**: let `a := sSup K_A` and `b := sInf K_B` (attained on compact). Then
`K_A ⊆ Iic a` and `K_B ⊆ Ici b`. Define translates `U := K_A + {b}` and
`V := {a} + K_B`. Both `U, V ⊆ K_A + K_B` (using `b ∈ K_B`, `a ∈ K_A`). Then:
- `U ⊆ Iic (a + b)`, `V ⊆ Ici (a + b)`, so `U ∩ V ⊆ {a + b}`, hence
  `vol(U ∩ V) = 0` (Lebesgue is non-atomic).
- `vol U = vol K_A`, `vol V = vol K_B` by translation invariance.
- `vol(U ∪ V) + vol(U ∩ V) = vol U + vol V`, so `vol(U ∪ V) = vol U + vol V`.
- `U ∪ V ⊆ K_A + K_B`, hence `vol(K_A + K_B) ≥ vol(U ∪ V) = vol K_A + vol K_B`.
-/
private lemma oneDim_brunn_minkowski_compact_le
    {K_A K_B : Set ℝ}
    (hA_compact : IsCompact K_A) (hB_compact : IsCompact K_B)
    (hA_ne : K_A.Nonempty) (hB_ne : K_B.Nonempty) :
    volume K_A + volume K_B ≤ volume (K_A + K_B) := by
  -- `a := sup K_A`, `b := inf K_B`, both attained on compact.
  set a := sSup K_A with ha_def
  set b := sInf K_B with hb_def
  have ha_mem : a ∈ K_A := hA_compact.sSup_mem hA_ne
  have hb_mem : b ∈ K_B := hB_compact.sInf_mem hB_ne
  have hA_le_a : ∀ x ∈ K_A, x ≤ a :=
    fun x hx => le_csSup hA_compact.bddAbove hx
  have hB_ge_b : ∀ y ∈ K_B, b ≤ y :=
    fun y hy => csInf_le hB_compact.bddBelow hy
  -- Translates: `U := K_A + {b}`, `V := {a} + K_B`.
  set U : Set ℝ := K_A + {b} with hU_def
  set V : Set ℝ := {a} + K_B with hV_def
  -- Both `U, V ⊆ K_A + K_B`.
  have hU_sub_AB : U ⊆ K_A + K_B := by
    rintro _ ⟨x, hx, _, rfl, rfl⟩
    exact ⟨x, hx, b, hb_mem, rfl⟩
  have hV_sub_AB : V ⊆ K_A + K_B := by
    rintro _ ⟨_, rfl, y, hy, rfl⟩
    exact ⟨a, ha_mem, y, hy, rfl⟩
  -- `vol U = vol K_A` via translation invariance.
  have hU_vol : volume U = volume K_A := by
    rw [hU_def, Set.add_singleton, Set.image_add_right]
    exact MeasureTheory.measure_preimage_add_right volume (-b) K_A
  -- `vol V = vol K_B`.
  have hV_vol : volume V = volume K_B := by
    rw [hV_def, Set.singleton_add, Set.image_add_left]
    exact MeasureTheory.measure_preimage_add volume (-a) K_B
  -- `U ⊆ Iic (a + b)`.
  have hU_sub_Iic : U ⊆ Set.Iic (a + b) := by
    rintro _ ⟨x, hx, _, rfl, rfl⟩
    have := hA_le_a x hx
    simp only [Set.mem_Iic]
    linarith
  -- `V ⊆ Ici (a + b)`.
  have hV_sub_Ici : V ⊆ Set.Ici (a + b) := by
    rintro _ ⟨_, rfl, y, hy, rfl⟩
    have := hB_ge_b y hy
    simp only [Set.mem_Ici]
    linarith
  -- `U ∩ V ⊆ {a + b}`.
  have h_inter_sub : U ∩ V ⊆ {a + b} := by
    rintro z ⟨hzU, hzV⟩
    have h1 := hU_sub_Iic hzU
    have h2 := hV_sub_Ici hzV
    simp only [Set.mem_Iic] at h1
    simp only [Set.mem_Ici] at h2
    simp only [Set.mem_singleton_iff]
    linarith
  -- `vol(U ∩ V) ≤ vol{a+b} = 0`.
  have h_inter_zero : volume (U ∩ V) = 0 := by
    apply le_antisymm _ zero_le
    calc volume (U ∩ V)
        ≤ volume ({a + b} : Set ℝ) := MeasureTheory.measure_mono h_inter_sub
      _ = 0 := MeasureTheory.measure_singleton (a + b)
  -- `vol(U ∪ V) + vol(U ∩ V) = vol U + vol V` (inclusion-exclusion).
  -- Need `MeasurableSet V`. `V = {a} + K_B`, where `K_B` compact (so closed,
  -- measurable) and `{a}` measurable, but the Minkowski sum need not be.
  -- Workaround: `V = (· + a) '' K_B` (after rewriting via singleton + comm),
  -- which is the image of compact `K_B` under continuous `(· + a)`, hence
  -- compact, hence closed, hence measurable.
  have hV_meas : MeasurableSet V := by
    rw [hV_def, Set.singleton_add, Set.image_add_left]
    exact (hB_compact.measurableSet).preimage (measurable_const_add (-a))
  have h_inc_excl : volume (U ∪ V) + volume (U ∩ V) = volume U + volume V :=
    MeasureTheory.measure_union_add_inter U hV_meas
  -- `vol(U ∪ V) ≤ vol(K_A + K_B)` via monotonicity.
  have h_union_sub : U ∪ V ⊆ K_A + K_B := Set.union_subset hU_sub_AB hV_sub_AB
  have h_union_le : volume (U ∪ V) ≤ volume (K_A + K_B) :=
    MeasureTheory.measure_mono h_union_sub
  -- Assemble: `vol K_A + vol K_B = vol U + vol V = vol(U∪V) + vol(U∩V)
  --            = vol(U∪V) + 0 ≤ vol(K_A + K_B)`.
  calc volume K_A + volume K_B
      = volume U + volume V := by rw [hU_vol, hV_vol]
    _ = volume (U ∪ V) + volume (U ∩ V) := h_inc_excl.symm
    _ = volume (U ∪ V) + 0 := by rw [h_inter_zero]
    _ = volume (U ∪ V) := add_zero _
    _ ≤ volume (K_A + K_B) := h_union_le

/-- **1D Brunn-Minkowski (outer-measure form, sufficient for PL).**

For nonempty Lebesgue-measurable `A, B ⊆ ℝ` and any measurable `C ⊇ A + B`:
$$\text{vol}(A) + \text{vol}(B) \le \text{vol}(C).$$

**Proof**: reduce to compact via inner regularity. For any `ε > 0`, find
compact `K_A ⊆ A, K_B ⊆ B` with `vol A < vol K_A + ε / 2,
vol B < vol K_B + ε / 2`. Then `K_A + K_B ⊆ A + B ⊆ C`, and by the compact
case, `vol K_A + vol K_B ≤ vol(K_A + K_B) ≤ vol C`. Hence
`vol A + vol B ≤ vol K_A + ε/2 + vol K_B + ε/2 ≤ vol C + ε`. Take `ε → 0`.

The `vol A = ⊤` case is handled separately (then `vol K_A → ⊤`, so
`vol C = ⊤`). -/
private theorem oneDim_brunn_minkowski_le
    {A B C : Set ℝ}
    (hA_meas : MeasurableSet A) (hB_meas : MeasurableSet B)
    (_hC_meas : MeasurableSet C)
    (hA_ne : A.Nonempty) (hB_ne : B.Nonempty)
    (hAB_sub : A + B ⊆ C) :
    volume A + volume B ≤ volume C := by
  -- Pre-step: trivial case `vol A = 0`.
  -- Then `{a₀} + B ⊆ A + B ⊆ C` gives `vol B ≤ vol C`, hence the bound.
  by_cases hA_zero : volume A = 0
  · obtain ⟨a₀, ha₀⟩ := hA_ne
    have h_aB_sub_C : ({a₀} : Set ℝ) + B ⊆ C := fun z ⟨_, rfl, y, hy, hyz⟩ =>
      hAB_sub ⟨a₀, ha₀, y, hy, hyz⟩
    have h_aB_eq : volume (({a₀} : Set ℝ) + B) = volume B := by
      rw [Set.singleton_add, Set.image_add_left]
      exact MeasureTheory.measure_preimage_add volume (-a₀) B
    rw [hA_zero, zero_add]
    calc volume B = volume (({a₀} : Set ℝ) + B) := h_aB_eq.symm
      _ ≤ volume C := MeasureTheory.measure_mono h_aB_sub_C
  -- Pre-step: trivial case `vol B = 0`. Symmetric.
  by_cases hB_zero : volume B = 0
  · obtain ⟨b₀, hb₀⟩ := hB_ne
    have h_Ab_sub_C : A + ({b₀} : Set ℝ) ⊆ C := fun z ⟨x, hx, _, rfl, hxz⟩ =>
      hAB_sub ⟨x, hx, b₀, hb₀, hxz⟩
    have h_Ab_eq : volume (A + ({b₀} : Set ℝ)) = volume A := by
      rw [Set.add_singleton, Set.image_add_right]
      exact MeasureTheory.measure_preimage_add_right volume (-b₀) A
    rw [hB_zero, add_zero]
    calc volume A = volume (A + ({b₀} : Set ℝ)) := h_Ab_eq.symm
      _ ≤ volume C := MeasureTheory.measure_mono h_Ab_sub_C
  -- Edge case `vol A = ⊤`: show `vol C = ⊤` via inner regularity.
  -- For each compact `K_A ⊆ A`, `K_A + {b₀} ⊆ A + B ⊆ C` with same volume,
  -- so `vol C ≥ ⨆ K compact ⊆ A, vol K = vol A = ⊤`.
  by_cases hA_top : volume A = ⊤
  · obtain ⟨b₀, hb₀⟩ := hB_ne
    suffices h_C_top : volume C = ⊤ by
      rw [hA_top, h_C_top]; exact le_top
    apply top_le_iff.mp
    have h_inner :
        volume A = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), volume K :=
      MeasureTheory.Measure.InnerRegularWRT.measure_eq_iSup
        MeasureTheory.Measure.InnerRegular.innerRegular hA_meas
    calc (⊤ : ℝ≥0∞)
        = volume A := hA_top.symm
      _ = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), volume K := h_inner
      _ ≤ volume C := by
          refine iSup_le fun K_A => iSup_le fun hK_A_sub => iSup_le fun _ => ?_
          have h_KA_b0_sub : K_A + ({b₀} : Set ℝ) ⊆ C :=
            fun z ⟨x, hx, _, rfl, hxz⟩ => hAB_sub ⟨x, hK_A_sub hx, b₀, hb₀, hxz⟩
          have h_KA_b0_eq : volume (K_A + ({b₀} : Set ℝ)) = volume K_A := by
            rw [Set.add_singleton, Set.image_add_right]
            exact MeasureTheory.measure_preimage_add_right volume (-b₀) K_A
          calc volume K_A
              = volume (K_A + ({b₀} : Set ℝ)) := h_KA_b0_eq.symm
            _ ≤ volume C := MeasureTheory.measure_mono h_KA_b0_sub
  -- Symmetric to vol A = ⊤ case.
  by_cases hB_top : volume B = ⊤
  · obtain ⟨a₀, ha₀⟩ := hA_ne
    suffices h_C_top : volume C = ⊤ by
      rw [hB_top, h_C_top]; exact le_top
    apply top_le_iff.mp
    have h_inner :
        volume B = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ B), ⨆ (_ : IsCompact K), volume K :=
      MeasureTheory.Measure.InnerRegularWRT.measure_eq_iSup
        MeasureTheory.Measure.InnerRegular.innerRegular hB_meas
    calc (⊤ : ℝ≥0∞)
        = volume B := hB_top.symm
      _ = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ B), ⨆ (_ : IsCompact K), volume K := h_inner
      _ ≤ volume C := by
          refine iSup_le fun K_B => iSup_le fun hK_B_sub => iSup_le fun _ => ?_
          have h_a0_KB_sub : ({a₀} : Set ℝ) + K_B ⊆ C :=
            fun z ⟨_, rfl, y, hy, hyz⟩ => hAB_sub ⟨a₀, ha₀, y, hK_B_sub hy, hyz⟩
          have h_a0_KB_eq : volume (({a₀} : Set ℝ) + K_B) = volume K_B := by
            rw [Set.singleton_add, Set.image_add_left]
            exact MeasureTheory.measure_preimage_add volume (-a₀) K_B
          calc volume K_B
              = volume (({a₀} : Set ℝ) + K_B) := h_a0_KB_eq.symm
            _ ≤ volume C := MeasureTheory.measure_mono h_a0_KB_sub
  -- Both finite, both nonzero. Use ε-approximation.
  -- Key: with vol A > 0 and vol A < ⊤, can pick K_A nonempty (vol K_A > 0).
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _hC_top
  -- Pick δ small enough that `vol K_A + δ < vol A` is impossible (so K_A
  -- nonempty automatic). Concretely: δ := min(ε/2, vol A / 2, vol B / 2).
  -- Simpler: just take δ := ε/2 and handle empty K_A by direct bound.
  set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / 2 with hδ_def
  have hδ_pos : (0 : ℝ≥0∞) < δ := by
    rw [hδ_def]
    refine ENNReal.div_pos ?_ (by norm_num)
    exact_mod_cast hε.ne'
  have hδ_ne : δ ≠ 0 := hδ_pos.ne'
  have hδ_le : δ ≤ ε := by
    rw [hδ_def]; exact ENNReal.half_le_self
  -- Inner regularity for A and B.
  obtain ⟨K_A, hK_A_sub, hK_A_compact, hK_A_lt⟩ :=
    hA_meas.exists_isCompact_lt_add hA_top hδ_ne
  obtain ⟨K_B, hK_B_sub, hK_B_compact, hK_B_lt⟩ :=
    hB_meas.exists_isCompact_lt_add hB_top hδ_ne
  -- Empty K_A case: handle via vol A < δ ≤ ε bound.
  rcases K_A.eq_empty_or_nonempty with hKA_empty | hKA_ne
  · -- `vol K_A = 0`, so `vol A < δ`. Combined with `vol B ≤ vol C` gives the bound.
    rw [hKA_empty, MeasureTheory.measure_empty, zero_add] at hK_A_lt
    -- vol A < δ ≤ ε
    have hA_le_ε : volume A ≤ (ε : ℝ≥0∞) := le_trans hK_A_lt.le hδ_le
    -- vol B ≤ vol C: pick a₀ ∈ A, {a₀} + B ⊆ C, measure-preserving.
    obtain ⟨a₀, ha₀⟩ := hA_ne
    have h_aB_sub_C : ({a₀} : Set ℝ) + B ⊆ C := fun z ⟨_, rfl, y, hy, hyz⟩ =>
      hAB_sub ⟨a₀, ha₀, y, hy, hyz⟩
    have h_aB_eq : volume (({a₀} : Set ℝ) + B) = volume B := by
      rw [Set.singleton_add, Set.image_add_left]
      exact MeasureTheory.measure_preimage_add volume (-a₀) B
    have hB_le_C : volume B ≤ volume C := by
      rw [← h_aB_eq]; exact MeasureTheory.measure_mono h_aB_sub_C
    calc volume A + volume B ≤ (ε : ℝ≥0∞) + volume C := add_le_add hA_le_ε hB_le_C
      _ = volume C + (ε : ℝ≥0∞) := add_comm _ _
  rcases K_B.eq_empty_or_nonempty with hKB_empty | hKB_ne
  · -- Symmetric to the empty K_A case.
    rw [hKB_empty, MeasureTheory.measure_empty, zero_add] at hK_B_lt
    have hB_le_ε : volume B ≤ (ε : ℝ≥0∞) := le_trans hK_B_lt.le hδ_le
    obtain ⟨b₀, hb₀⟩ := hB_ne
    have h_Ab_sub_C : A + ({b₀} : Set ℝ) ⊆ C := fun z ⟨x, hx, _, rfl, hxz⟩ =>
      hAB_sub ⟨x, hx, b₀, hb₀, hxz⟩
    have h_Ab_eq : volume (A + ({b₀} : Set ℝ)) = volume A := by
      rw [Set.add_singleton, Set.image_add_right]
      exact MeasureTheory.measure_preimage_add_right volume (-b₀) A
    have hA_le_C : volume A ≤ volume C := by
      rw [← h_Ab_eq]; exact MeasureTheory.measure_mono h_Ab_sub_C
    exact add_le_add hA_le_C hB_le_ε
  · -- Generic case: both K_A, K_B nonempty.
    have hKAB_sub : K_A + K_B ⊆ C :=
      fun z ⟨x, hx, y, hy, hxyz⟩ =>
        hAB_sub ⟨x, hK_A_sub hx, y, hK_B_sub hy, hxyz⟩
    have h_compact_bm := oneDim_brunn_minkowski_compact_le
      hK_A_compact hK_B_compact hKA_ne hKB_ne
    have h_KAKB_le_C : volume (K_A + K_B) ≤ volume C :=
      MeasureTheory.measure_mono hKAB_sub
    -- `vol A + vol B ≤ (vol K_A + δ) + (vol K_B + δ) ≤ vol C + 2δ ≤ vol C + ε`.
    have h_2δ_le_ε : (2 : ℝ≥0∞) * δ ≤ (ε : ℝ≥0∞) := by
      rw [hδ_def]; exact ENNReal.mul_div_le
    calc volume A + volume B
        ≤ (volume K_A + δ) + (volume K_B + δ) := by gcongr
      _ = (volume K_A + volume K_B) + (δ + δ) := by ring
      _ = (volume K_A + volume K_B) + 2 * δ := by ring
      _ ≤ volume C + 2 * δ := by
          gcongr
          exact le_trans h_compact_bm h_KAKB_le_C
      _ ≤ volume C + (ε : ℝ≥0∞) := by gcongr

/-- **Level-measure bound (1D PL, both level sets nonempty).**

For `α ∈ (0, ∞)` with both `A_α := {x | α < f x}` and `B_α := {y | α < g y}`
nonempty:
$$t \cdot \text{vol}(A_\alpha) + (1-t) \cdot \text{vol}(B_\alpha)
  \;\le\; \text{vol}(\{z \mid \alpha < h(z)\}).$$

Combines `prekopaLeindler_1d_levelInclusion` (set inclusion) +
`oneDim_brunn_minkowski_le` (BM measure inequality) +
`Measure.addHaar_smul_of_nonneg` (smul scaling: `vol(c • s) = ofReal(c) * vol(s)`
for `c ≥ 0` since `finrank ℝ ℝ = 1`).

Note: requires both level sets nonempty (positive measure). The case where
one is empty (i.e., `α ≥ ess-sup` of one of `f, g`) is handled by reduction
to `ess-sup f = ess-sup g` via prior rescaling of `f, g, h` — currently
folded into the assembly's general edge-case bookkeeping. -/
private theorem prekopaLeindler_1d_levelMeasureBound
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    {α : ℝ≥0∞} (hα_pos : 0 < α) (hα_top : α ≠ ⊤)
    (hA_ne : ({x | α < f x} : Set ℝ).Nonempty)
    (hB_ne : ({y | α < g y} : Set ℝ).Nonempty) :
    ENNReal.ofReal t * volume {x | α < f x}
      + ENNReal.ofReal (1 - t) * volume {y | α < g y}
      ≤ volume {z | α < h z} := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  set A : Set ℝ := {x | α < f x} with hA_def
  set B : Set ℝ := {y | α < g y} with hB_def
  set C : Set ℝ := {z | α < h z} with hC_def
  -- Level sets are measurable via `f, g, h` measurable + `Ioi α` measurable.
  have hA_meas : MeasurableSet A := hf_meas measurableSet_Ioi
  have hB_meas : MeasurableSet B := hg_meas measurableSet_Ioi
  have hC_meas : MeasurableSet C := hh_meas measurableSet_Ioi
  -- Inclusion: `t • A + (1 - t) • B ⊆ C` from level-set inclusion helper.
  have h_incl : t • A + (1 - t) • B ⊆ C :=
    prekopaLeindler_1d_levelInclusion ht_pos ht_lt h_le hα_pos hα_top
  -- Smul-set measurability (uses `t ≠ 0`).
  have htA_meas : MeasurableSet (t • A) :=
    hA_meas.const_smul_of_ne_zero ht_pos.ne'
  have h1tB_meas : MeasurableSet ((1 - t) • B) :=
    hB_meas.const_smul_of_ne_zero h1t_pos.ne'
  -- Smul-set nonempty.
  have htA_ne : (t • A).Nonempty := Set.smul_set_nonempty.mpr hA_ne
  have h1tB_ne : ((1 - t) • B).Nonempty := Set.smul_set_nonempty.mpr hB_ne
  -- 1D BM applied to `t • A`, `(1-t) • B`, `C`.
  have h_bm : volume (t • A) + volume ((1 - t) • B) ≤ volume C :=
    oneDim_brunn_minkowski_le htA_meas h1tB_meas hC_meas htA_ne h1tB_ne h_incl
  -- Smul-set measure scaling: `vol(c • S) = ofReal c * vol(S)` for `c ≥ 0`,
  -- since `finrank ℝ ℝ = 1`.
  have h_finrank : Module.finrank ℝ ℝ = 1 := CommSemiring.finrank_self ℝ
  have h_smul_t : volume (t • A) = ENNReal.ofReal t * volume A := by
    rw [Measure.addHaar_smul_of_nonneg volume ht_pos.le A, h_finrank, pow_one]
  have h_smul_1t : volume ((1 - t) • B) = ENNReal.ofReal (1 - t) * volume B := by
    rw [Measure.addHaar_smul_of_nonneg volume h1t_pos.le B, h_finrank, pow_one]
  rw [← h_smul_t, ← h_smul_1t]
  exact h_bm

/-- **Layer-cake for ENNReal-valued lintegral.**

For measurable `f : ℝ → ℝ≥0∞`,
$$\int^- f \, d\lambda
  \;=\; \int^-_{\alpha \in (0, \infty)} \lambda(\{x \mid \alpha < f(x)\})
  \, d\alpha.$$

Mathlib has this for `f : α → ℝ` (`MeasureTheory.lintegral_eq_lintegral_meas_lt`)
but not directly for ENNReal-valued `f`. Derived here via truncation
`f_n := f ⊓ n` + monotone convergence on both sides + Mathlib's ℝ-valued
form applied to `f_n.toReal` per `n`. -/
private theorem lintegral_eq_lintegral_meas_lt_ennreal
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < f x} := by
  -- Truncation: `fN n x := f x ⊓ n` is bounded, monotone in `n`, sup = `f`.
  set fN : ℕ → ℝ → ℝ≥0∞ := fun n x => f x ⊓ (n : ℝ≥0∞) with hfN_def
  have hfN_meas : ∀ n, Measurable (fN n) :=
    fun n => hf.inf measurable_const
  have hfN_lt_top : ∀ n x, fN n x ≠ ⊤ :=
    fun n x => ne_top_of_le_ne_top ENNReal.coe_ne_top inf_le_right
  have hfN_mono : Monotone fN := by
    intro m n hmn x
    exact inf_le_inf_left _ (by exact_mod_cast hmn)
  have hfN_iSup_eq : ∀ x, ⨆ n, fN n x = f x := fun x => by
    simp only [fN]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  -- LHS via MCT.
  have hLHS : ∫⁻ x, f x = ⨆ n, ∫⁻ x, fN n x := by
    rw [← MeasureTheory.lintegral_iSup hfN_meas hfN_mono]
    exact MeasureTheory.lintegral_congr fun x => (hfN_iSup_eq x).symm
  -- For each `n`, layer cake on `fN n` via Mathlib's ℝ-version + transfer
  -- `ENNReal.ofReal ((fN n x).toReal) = fN n x` (using `fN n x ≠ ⊤`).
  have h_per_n : ∀ n, ∫⁻ x, fN n x =
      ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < fN n x} := by
    intro n
    have h_eq : ∫⁻ x, fN n x = ∫⁻ x, ENNReal.ofReal ((fN n x).toReal) :=
      MeasureTheory.lintegral_congr fun x => (ENNReal.ofReal_toReal (hfN_lt_top n x)).symm
    rw [h_eq, MeasureTheory.lintegral_eq_lintegral_meas_lt volume
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
        ((hfN_meas n).ennreal_toReal.aemeasurable)]
    -- Goal: `∫⁻ α in Ioi 0, vol {x | α < (fN n x).toReal}
    --      = ∫⁻ α in Ioi 0, vol {x | ENNReal.ofReal α < fN n x}`.
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
    intro α hα
    have hα_nn : (0 : ℝ) ≤ α := le_of_lt hα
    change volume {x | α < (fN n x).toReal}
        = volume {x | ENNReal.ofReal α < fN n x}
    congr 1
    ext x
    simp only [Set.mem_setOf_eq]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα_nn).mpr h
      rwa [ENNReal.ofReal_toReal (hfN_lt_top n x)] at this
    · have h' : ENNReal.ofReal α < ENNReal.ofReal ((fN n x).toReal) := by
        rwa [ENNReal.ofReal_toReal (hfN_lt_top n x)]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα_nn).mp h'
  -- RHS: rewrite `vol{ofReal α < f x}` as `⨆ n vol{ofReal α < fN n x}` via
  -- `Monotone.measure_iUnion` + `⋃ n {ofReal α < fN n x} = {ofReal α < f x}`,
  -- then swap iSup with `∫⁻ α` via MCT.
  have h_set_mono : ∀ α : ℝ,
      Monotone fun n : ℕ => {x | ENNReal.ofReal α < fN n x} := by
    intro α m n hmn x hx
    exact lt_of_lt_of_le hx (hfN_mono hmn x)
  have h_set_iUnion : ∀ α : ℝ,
      ⋃ n : ℕ, {x | ENNReal.ofReal α < fN n x}
        = {x | ENNReal.ofReal α < f x} := by
    intro α
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨fun ⟨n, hn⟩ => lt_of_lt_of_le hn (le_trans inf_le_left le_rfl), ?_⟩
    intro hx
    rw [← hfN_iSup_eq x] at hx
    exact lt_iSup_iff.mp hx
  -- Measurability of `α ↦ vol {ofReal α < fN n x}`: use Tonelli's
  -- measurability lemma `measurable_measure_prodMk_left`.
  have h_meas_vol : ∀ n,
      Measurable fun α : ℝ => volume {x | ENNReal.ofReal α < fN n x} := by
    intro n
    -- The set `{(α, x) | ofReal α < fN n x}` is measurable in `ℝ × ℝ`.
    have h_set_meas : MeasurableSet
        {p : ℝ × ℝ | ENNReal.ofReal p.1 < fN n p.2} :=
      measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        ((hfN_meas n).comp measurable_snd)
    -- Apply `measurable_measure_prodMk_left` to volume on `ℝ` (sfinite).
    exact measurable_measure_prodMk_left h_set_meas
  have hRHS : ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < f x}
        = ⨆ n, ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < fN n x} := by
    rw [show (fun α => volume {x | ENNReal.ofReal α < f x})
          = fun α => ⨆ n, volume {x | ENNReal.ofReal α < fN n x} from
        funext fun α => by rw [← h_set_iUnion α,
          (h_set_mono α).measure_iUnion]]
    exact MeasureTheory.lintegral_iSup (fun n => h_meas_vol n)
      (fun m n hmn α => MeasureTheory.measure_mono (h_set_mono α hmn))
  rw [hLHS, hRHS]
  exact iSup_congr h_per_n

/-- **ENNReal weighted AM-GM (2-form).**

For `t ∈ (0, 1)` and `a, b : ℝ≥0∞`:
$$a^t \cdot b^{1-t} \;\le\; t \cdot a + (1-t) \cdot b.$$

Lifted from `Real.geom_mean_le_arith_mean2_weighted` via `toReal`/`ofReal`,
with `⊤` edge cases handled by absorbing into RHS. -/
private theorem ennreal_geom_mean_le_arith_mean2_weighted
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (a b : ℝ≥0∞) :
    a ^ t * b ^ (1 - t) ≤ ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  by_cases ha : a = ⊤
  · subst ha
    have h_rhs : ENNReal.ofReal t * ⊤ + ENNReal.ofReal (1 - t) * b = ⊤ := by
      have : ENNReal.ofReal t ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero]; linarith
      simp [ENNReal.mul_top this]
    rw [h_rhs]; exact le_top
  by_cases hb : b = ⊤
  · subst hb
    have h_rhs : ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * ⊤ = ⊤ := by
      have : ENNReal.ofReal (1 - t) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero]; linarith
      simp [ENNReal.mul_top this]
    rw [h_rhs]; exact le_top
  -- Both finite; lift to Real.
  set A : ℝ := a.toReal with hA_def
  set B : ℝ := b.toReal with hB_def
  have hA_nn : (0 : ℝ) ≤ A := ENNReal.toReal_nonneg
  have hB_nn : (0 : ℝ) ≤ B := ENNReal.toReal_nonneg
  have hofa : ENNReal.ofReal A = a := ENNReal.ofReal_toReal ha
  have hofb : ENNReal.ofReal B = b := ENNReal.ofReal_toReal hb
  have h_real : A ^ t * B ^ (1 - t) ≤ t * A + (1 - t) * B :=
    Real.geom_mean_le_arith_mean2_weighted ht_pos.le h1t_pos.le hA_nn hB_nn
      (by linarith)
  have hAt_nn : (0 : ℝ) ≤ A ^ t := Real.rpow_nonneg hA_nn t
  have hBt_nn : (0 : ℝ) ≤ B ^ (1 - t) := Real.rpow_nonneg hB_nn (1 - t)
  calc a ^ t * b ^ (1 - t)
      = ENNReal.ofReal A ^ t * ENNReal.ofReal B ^ (1 - t) := by rw [hofa, hofb]
    _ = ENNReal.ofReal (A ^ t) * ENNReal.ofReal (B ^ (1 - t)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hA_nn ht_pos.le,
            ENNReal.ofReal_rpow_of_nonneg hB_nn h1t_pos.le]
    _ = ENNReal.ofReal (A ^ t * B ^ (1 - t)) := by
        rw [← ENNReal.ofReal_mul hAt_nn]
    _ ≤ ENNReal.ofReal (t * A + (1 - t) * B) := ENNReal.ofReal_le_ofReal h_real
    _ = ENNReal.ofReal (t * A) + ENNReal.ofReal ((1 - t) * B) :=
        ENNReal.ofReal_add (mul_nonneg ht_pos.le hA_nn)
          (mul_nonneg h1t_pos.le hB_nn)
    _ = ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b := by
        rw [ENNReal.ofReal_mul ht_pos.le, ENNReal.ofReal_mul h1t_pos.le,
            hofa, hofb]

/-- **Arithmetic-bound assembly (1D PL, ess-sup-aligned form).**

Under the PL pointwise hypothesis AND `essSup f = essSup g`:
$$t \cdot \int f \;+\; (1-t) \cdot \int g \;\le\; \int h.$$

The `essSup` alignment hypothesis is necessary for the pointwise level-measure
bound to apply at every `α`: for `α < essSup f = essSup g`, both level sets
have positive measure (hence non-empty); for `α ≥ essSup f = essSup g`, both
have null measure, so the LHS pointwise contribution is 0.

The unconditional `prekopaLeindler_1d` reduces to this conditional form by
rescaling `f → c•f, h → c^t•h` (with `c := essSup g / essSup f`) which
preserves both PL hypothesis and conclusion while equalizing ess-sups. -/
private theorem prekopaLeindler_1d_arithBound
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    (h_ess_eq : essSup f volume = essSup g volume) :
    ENNReal.ofReal t * (∫⁻ x, f x) + ENNReal.ofReal (1 - t) * (∫⁻ y, g y)
      ≤ ∫⁻ z, h z := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  set M : ℝ≥0∞ := essSup f volume with hM_def
  -- Helper: for `β < M`, the level set `{φ > β}` has positive measure when
  -- `essSup φ = M`. Standard via `essSup_le_of_ae_le` contrapositive.
  have h_pos_meas : ∀ {φ : ℝ → ℝ≥0∞}, essSup φ volume = M →
      ∀ {β : ℝ≥0∞}, β < M → 0 < volume {x | β < φ x} := by
    intro φ hφ_ess β hβ
    by_contra h_neg
    rw [not_lt, nonpos_iff_eq_zero] at h_neg
    have h_ae : φ ≤ᵐ[volume] fun _ => β := by
      rw [Filter.EventuallyLE, MeasureTheory.ae_iff]
      simpa using h_neg
    have : essSup φ volume ≤ β := essSup_le_of_ae_le β h_ae
    rw [hφ_ess] at this
    exact absurd this (not_le.mpr hβ)
  -- Helper: for `β ≥ M`, the level set `{φ > β}` has null measure.
  have h_null_meas : ∀ {φ : ℝ → ℝ≥0∞}, essSup φ volume = M →
      ∀ {β : ℝ≥0∞}, M ≤ β → volume {x | β < φ x} = 0 := by
    intro φ hφ_ess β hβ
    have h_essSup_le : essSup φ volume ≤ β := hφ_ess.trans_le hβ
    -- {φ > β} ⊆ {φ > essSup φ}, latter null by `meas_essSup_lt`.
    have h_sub : {x | β < φ x} ⊆ {x | essSup φ volume < φ x} :=
      fun x hx => lt_of_le_of_lt h_essSup_le hx
    refine le_antisymm ?_ zero_le
    calc volume {x | β < φ x}
        ≤ volume {x | essSup φ volume < φ x} := MeasureTheory.measure_mono h_sub
      _ = 0 := meas_essSup_lt
  -- Named integrand functions (with explicit measurability):
  let volF : ℝ → ℝ≥0∞ := fun α => volume {x | ENNReal.ofReal α < f x}
  let volG : ℝ → ℝ≥0∞ := fun α => volume {y | ENNReal.ofReal α < g y}
  let volH : ℝ → ℝ≥0∞ := fun α => volume {z | ENNReal.ofReal α < h z}
  have hvolF_meas : Measurable volF :=
    measurable_measure_prodMk_left
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        (hf_meas.comp measurable_snd))
  have hvolG_meas : Measurable volG :=
    measurable_measure_prodMk_left
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        (hg_meas.comp measurable_snd))
  -- Pointwise bound on `volF, volG, volH`.
  have h_pointwise : ∀ α : ℝ, 0 < α →
      ENNReal.ofReal t * volF α + ENNReal.ofReal (1 - t) * volG α ≤ volH α := by
    intro α hα
    have hα_pos_e : (0 : ℝ≥0∞) < ENNReal.ofReal α :=
      ENNReal.ofReal_pos.mpr hα
    have hα_top : ENNReal.ofReal α ≠ ⊤ := ENNReal.ofReal_ne_top
    by_cases hαM : ENNReal.ofReal α < M
    · -- `α < M`: both level sets positive-measure ⇒ non-empty.
      have hA_pos : 0 < volume {x | ENNReal.ofReal α < f x} :=
        h_pos_meas hM_def.symm hαM
      have hB_pos : 0 < volume {y | ENNReal.ofReal α < g y} :=
        h_pos_meas (h_ess_eq.symm.trans hM_def.symm) hαM
      have hA_ne : ({x | ENNReal.ofReal α < f x} : Set ℝ).Nonempty :=
        MeasureTheory.nonempty_of_measure_ne_zero hA_pos.ne'
      have hB_ne : ({y | ENNReal.ofReal α < g y} : Set ℝ).Nonempty :=
        MeasureTheory.nonempty_of_measure_ne_zero hB_pos.ne'
      exact prekopaLeindler_1d_levelMeasureBound hf_meas hg_meas hh_meas
        ht_pos ht_lt h_le hα_pos_e hα_top hA_ne hB_ne
    · -- `α ≥ M`: both level sets null, LHS = 0.
      rw [not_lt] at hαM
      have hf_null : volF α = 0 := h_null_meas hM_def.symm hαM
      have hg_null : volG α = 0 := h_null_meas (h_ess_eq.symm.trans hM_def.symm) hαM
      change ENNReal.ofReal t * volF α + ENNReal.ofReal (1 - t) * volG α ≤ volH α
      rw [hf_null, hg_null, mul_zero, mul_zero, zero_add]
      exact zero_le
  -- Layer cake.
  rw [lintegral_eq_lintegral_meas_lt_ennreal hf_meas,
      lintegral_eq_lintegral_meas_lt_ennreal hg_meas,
      lintegral_eq_lintegral_meas_lt_ennreal hh_meas]
  -- Reshape to use volF/volG/volH names.
  change ENNReal.ofReal t * (∫⁻ α in Ioi (0:ℝ), volF α)
       + ENNReal.ofReal (1 - t) * (∫⁻ α in Ioi (0:ℝ), volG α)
       ≤ ∫⁻ α in Ioi (0:ℝ), volH α
  -- Pull constants inside.
  rw [← MeasureTheory.lintegral_const_mul _ hvolF_meas,
      ← MeasureTheory.lintegral_const_mul _ hvolG_meas]
  -- Combine sums.
  rw [← MeasureTheory.lintegral_add_left (hvolF_meas.const_mul _)]
  -- Apply pointwise bound.
  exact MeasureTheory.setLIntegral_mono'
    measurableSet_Ioi (fun α hα => h_pointwise α hα)

/-- **Prékopa-Leindler 1D — bounded-ess-sup helper.**

Same statement as `prekopaLeindler_1d` but with `essSup f, essSup g ≠ ⊤`.
Body: trivial 0-cases + main rescaling case. The unconditional
`prekopaLeindler_1d` reduces to this via truncation + monotone convergence. -/
private theorem prekopaLeindler_1d_essBdd
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    (hMf_top : essSup f volume ≠ ⊤) (hMg_top : essSup g volume ≠ ⊤) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  set Mf := essSup f volume with hMf_def
  set Mg := essSup g volume with hMg_def
  -- Trivial case `essSup f = 0` ⇒ `f = 0 a.e.` ⇒ `∫f = 0` ⇒ LHS = 0.
  by_cases hMf_zero : Mf = 0
  · have hf_int_zero : ∫⁻ x, f x = 0 := by
      rw [MeasureTheory.lintegral_eq_zero_iff hf_meas]
      filter_upwards [ENNReal.ae_le_essSup f] with x hx
      rw [← hMf_def, hMf_zero] at hx
      exact le_antisymm hx zero_le
    rw [hf_int_zero, ENNReal.zero_rpow_of_pos ht_pos, zero_mul]
    exact zero_le
  -- Symmetric: `essSup g = 0`.
  by_cases hMg_zero : Mg = 0
  · have hg_int_zero : ∫⁻ y, g y = 0 := by
      rw [MeasureTheory.lintegral_eq_zero_iff hg_meas]
      filter_upwards [ENNReal.ae_le_essSup g] with y hy
      rw [← hMg_def, hMg_zero] at hy
      exact le_antisymm hy zero_le
    rw [hg_int_zero, ENNReal.zero_rpow_of_pos h1t_pos, mul_zero]
    exact zero_le
  -- Main case: `Mf, Mg ∈ (0, ⊤)`. Rescale `f → c•f, h → c^t•h` with
  -- `c := Mg / Mf` (so `essSup (c•f) = c · Mf = Mg`).
  set c : ℝ≥0∞ := Mg / Mf with hc_def
  have hc_pos : (0 : ℝ≥0∞) < c := ENNReal.div_pos hMg_zero hMf_top
  have hc_top : c ≠ ⊤ := by
    rw [hc_def]
    exact (ENNReal.div_lt_top hMg_top hMf_zero).ne
  have hcMf_eq_Mg : c * Mf = Mg := by
    rw [hc_def, ENNReal.div_mul_cancel hMf_zero hMf_top]
  -- Define rescaled `f', h'`.
  set f' : ℝ → ℝ≥0∞ := fun x => c * f x with hf'_def
  set h' : ℝ → ℝ≥0∞ := fun z => c ^ t * h z with hh'_def
  have hf'_meas : Measurable f' := hf_meas.const_mul c
  have hh'_meas : Measurable h' := hh_meas.const_mul (c ^ t)
  -- `essSup f' = c * Mf = Mg = essSup g`.
  have hf'_essSup : essSup f' volume = Mg := by
    change essSup (fun x => c * f x) volume = Mg
    rw [ENNReal.essSup_const_mul, hcMf_eq_Mg]
  -- PL hypothesis for `(f', g, h')`.
  have h_le' : ∀ x y : ℝ,
      f' x ^ t * g y ^ (1 - t) ≤ h' (t * x + (1 - t) * y) := by
    intro x y
    change (c * f x) ^ t * g y ^ (1 - t) ≤ c ^ t * h (t * x + (1 - t) * y)
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht_pos.le, mul_assoc]
    gcongr
    exact h_le x y
  -- Apply `arithBound` + AM-GM to `(f', g, h')`.
  have h_amgm := ennreal_geom_mean_le_arith_mean2_weighted ht_pos ht_lt
    (∫⁻ x, f' x) (∫⁻ y, g y)
  have h_arith := prekopaLeindler_1d_arithBound hf'_meas hg_meas hh'_meas
    ht_pos ht_lt h_le' (hf'_essSup.trans hMg_def.symm)
  have h_pl_rescaled :
      (∫⁻ x, f' x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h' z :=
    le_trans h_amgm h_arith
  -- Translate: `∫f' = c · ∫f`, `∫h' = c^t · ∫h`. Cancel `c^t`.
  rw [show ∫⁻ x, f' x = c * ∫⁻ x, f x from
        MeasureTheory.lintegral_const_mul c hf_meas,
      show ∫⁻ z, h' z = c ^ t * ∫⁻ z, h z from
        MeasureTheory.lintegral_const_mul (c ^ t) hh_meas,
      ENNReal.mul_rpow_of_nonneg _ _ ht_pos.le, mul_assoc] at h_pl_rescaled
  -- Now `h_pl_rescaled : c^t * ((∫f)^t * (∫g)^(1-t)) ≤ c^t * ∫h`.
  have hct_ne_zero : c ^ t ≠ 0 := (ENNReal.rpow_pos hc_pos hc_top).ne'
  have hct_ne_top : c ^ t ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg ht_pos.le hc_top).ne
  -- `mul_le_mul_iff_left` gives the form `a * c ≤ b * c ↔ a ≤ b`. Convert via mul_comm.
  rw [mul_comm (c ^ t) _, mul_comm (c ^ t) _] at h_pl_rescaled
  exact (ENNReal.mul_le_mul_iff_left hct_ne_zero hct_ne_top).mp h_pl_rescaled

theorem prekopaLeindler_1d
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  -- Truncate `f, g`: `f_n := f ⊓ n, g_n := g ⊓ n`. Both `essSup ≤ n < ⊤`.
  set fN : ℕ → ℝ → ℝ≥0∞ := fun n x => f x ⊓ (n : ℝ≥0∞) with hfN_def
  set gN : ℕ → ℝ → ℝ≥0∞ := fun n y => g y ⊓ (n : ℝ≥0∞) with hgN_def
  have hfN_meas : ∀ n, Measurable (fN n) := fun n => hf_meas.inf measurable_const
  have hgN_meas : ∀ n, Measurable (gN n) := fun n => hg_meas.inf measurable_const
  have hfN_essSup_top : ∀ n, essSup (fN n) volume ≠ ⊤ := fun n => by
    have h_le_n : essSup (fN n) volume ≤ (n : ℝ≥0∞) :=
      essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun _ => inf_le_right)
    exact ne_of_lt (lt_of_le_of_lt h_le_n ENNReal.coe_lt_top)
  have hgN_essSup_top : ∀ n, essSup (gN n) volume ≠ ⊤ := fun n => by
    have h_le_n : essSup (gN n) volume ≤ (n : ℝ≥0∞) :=
      essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun _ => inf_le_right)
    exact ne_of_lt (lt_of_le_of_lt h_le_n ENNReal.coe_lt_top)
  -- PL hypothesis for `(fN n, gN m, h)` (any n, m): truncation only weakens.
  have h_le_N : ∀ n m, ∀ x y : ℝ,
      fN n x ^ t * gN m y ^ (1 - t) ≤ h (t * x + (1 - t) * y) := by
    intro n m x y
    calc fN n x ^ t * gN m y ^ (1 - t)
        ≤ f x ^ t * g y ^ (1 - t) := by
          gcongr <;> exact inf_le_left
      _ ≤ h (t * x + (1 - t) * y) := h_le x y
  -- Per-(n, m): apply bdd helper.
  have h_per_nm : ∀ n m,
      (∫⁻ x, fN n x) ^ t * (∫⁻ y, gN m y) ^ (1 - t) ≤ ∫⁻ z, h z := fun n m =>
    prekopaLeindler_1d_essBdd (hfN_meas n) (hgN_meas m) hh_meas ht_pos ht_lt
      (h_le_N n m) (hfN_essSup_top n) (hgN_essSup_top m)
  -- Monotone in n: `∫fN n ↑ ∫f` (MCT). Similarly gN.
  have hfN_mono : Monotone fun n => ∫⁻ x, fN n x := by
    intro n m hnm
    apply MeasureTheory.lintegral_mono
    intro x; exact inf_le_inf_left _ (by exact_mod_cast hnm)
  have hgN_mono : Monotone fun m => ∫⁻ y, gN m y := by
    intro n m hnm
    apply MeasureTheory.lintegral_mono
    intro y; exact inf_le_inf_left _ (by exact_mod_cast hnm)
  have hfN_iSup : ⨆ n, ∫⁻ x, fN n x = ∫⁻ x, f x := by
    rw [← MeasureTheory.lintegral_iSup hfN_meas (fun n m hnm x =>
      inf_le_inf_left _ (by exact_mod_cast hnm))]
    apply MeasureTheory.lintegral_congr
    intro x
    simp only [fN]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hgN_iSup : ⨆ m, ∫⁻ y, gN m y = ∫⁻ y, g y := by
    rw [← MeasureTheory.lintegral_iSup hgN_meas (fun n m hnm y =>
      inf_le_inf_left _ (by exact_mod_cast hnm))]
    apply MeasureTheory.lintegral_congr
    intro y
    simp only [gN]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  -- Conclude: `(∫f)^t * (∫g)^(1-t) ≤ ∫h` via iSup commute with rpow + mul.
  -- `(∫f)^t = (⨆ n, ∫fN n)^t = ⨆ n, (∫fN n)^t` (rpow continuous + monotone).
  -- Similarly for g.
  -- `(⨆ n, A_n) * (⨆ m, B_m) = ⨆ n, ⨆ m, A_n * B_m ≤ ⨆ k, A_k * B_k ≤ ∫h`.
  -- Helper: `(⨆ a_n)^p = ⨆ a_n^p` for monotone `a_n` and `p ≥ 0`.
  -- Via `tendsto_atTop_iSup` + `continuous_rpow_const` + `tendsto_nhds_unique`.
  have h_rpow_iSup : ∀ (a : ℕ → ℝ≥0∞) (p : ℝ), 0 ≤ p → Monotone a →
      (⨆ n, a n) ^ p = ⨆ n, a n ^ p := by
    intro a p hp ha_mono
    have h_tendsto : Filter.Tendsto a Filter.atTop (𝓝 (⨆ n, a n)) :=
      tendsto_atTop_iSup ha_mono
    have h_tendsto_pow : Filter.Tendsto (fun n => a n ^ p) Filter.atTop
        (𝓝 ((⨆ n, a n) ^ p)) :=
      (ENNReal.continuous_rpow_const.tendsto _).comp h_tendsto
    have ha_pow_mono : Monotone (fun n => a n ^ p) := fun n m hnm =>
      ENNReal.rpow_le_rpow (ha_mono hnm) hp
    exact tendsto_nhds_unique h_tendsto_pow (tendsto_atTop_iSup ha_pow_mono)
  rw [← hfN_iSup, ← hgN_iSup]
  -- Push rpow inside iSup.
  rw [h_rpow_iSup _ t ht_pos.le hfN_mono,
      h_rpow_iSup _ (1 - t) h1t_pos.le hgN_mono]
  -- `(⨆ n, A_n) * (⨆ m, B_m) = ⨆ n, ⨆ m, A_n * B_m`.
  rw [ENNReal.iSup_mul]
  refine iSup_le fun n => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun m => ?_
  -- Goal: `(∫fN n)^t * (∫gN m)^(1-t) ≤ ∫h`. Use `h_per_nm n m`.
  exact h_per_nm n m

/-- **Prékopa-Leindler inequality (finite-dimensional form).**

For nonneg measurable `f, g, h : (ι → ℝ) → ℝ≥0∞` (with `ι` finite) and
`t ∈ (0, 1)` such that
$h(t \cdot x + (1-t) \cdot y) \ge f(x)^t \cdot g(y)^{1-t}$
for all `x, y : ι → ℝ`, we have
$$\int h \;\ge\; \left(\int f\right)^t \cdot \left(\int g\right)^{1-t}$$
where all integrals are with respect to the Pi product Lebesgue measure on
`ι → ℝ` (available as `volume` via `MeasureTheory.MeasureSpace.pi`).

The statement uses `ι → ℝ` rather than `EuclideanSpace ℝ ι` because only the
former has a default `MeasureSpace` instance (by Mathlib design — `PiLp` is a
type synonym chosen *not* to inherit the Pi measure to avoid ambiguity with
Haar measure). For the `anderson_lemma_set` application, transfer via
`PiLp.volume_preserving_toLp` / `EuclideanSpace.equiv`.

**Proof sketch (deferred)**: induction on `Fintype.card ι`.
* Base (`card ι = 0`): `ι → ℝ` is a singleton (`dirac`), both sides reduce to
  evaluation at the unique point; the PL hypothesis at that point is the
  conclusion.
* Step: pick an element `i : ι` (possible since induction is on cardinality),
  split `(ι → ℝ) ≃ᵐ ℝ × ((ι \ {i}) → ℝ)` via `MeasurableEquiv.piSplitAt` or
  `MeasurableEquiv.piFinSuccAbove`. By Fubini, rewrite each integral as a
  double integral: outer over the `i`-th coordinate, inner over the remaining
  `card ι - 1` coordinates. Apply the inductive (smaller-dim) PL to the
  inner integrals fibre-wise (for fixed first-coordinate values `(u, v)`, the
  functions `f(u, ·), g(v, ·), h((tu + (1-t)v), ·)` satisfy the PL hypothesis
  with parameter `t`); the marginalised integrals are log-concave in the
  outer variable by exactly this inductive step. Close with 1D PL on the outer
  variable.

This is the form directly consumed by `anderson_lemma_set` in
`ForMathlib/Anderson.lean`: apply with `f(x) := ρ(x) · 𝟙_{C-y}(x)`,
`g(x) := ρ(x) · 𝟙_{C+y}(x)`, `h(x) := ρ(x) · 𝟙_C(x)` (where `ρ` is the
Gaussian density, in `(ι → ℝ)`-coordinates) and `t = 1/2`; the pointwise
hypothesis follows from log-concavity of `ρ` and midpoint-convexity of `C`. -/
theorem prekopaLeindler.{u}
    {ι : Type u} [Fintype ι]
    {f g h : (ι → ℝ) → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ι → ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  -- Generalise over the index type κ and over `(f, g, h, s)` so we can run
  -- `Fintype.induction_empty_option` (the predicate must be `(κ : Type u) →
  -- [Fintype κ] → Prop`, sharing the universe of `ι`).
  suffices H : ∀ (κ : Type u) [Fintype κ] (f g h : (κ → ℝ) → ℝ≥0∞),
      Measurable f → Measurable g → Measurable h →
      ∀ {s : ℝ}, 0 < s → s < 1 →
      (∀ x y : κ → ℝ, f x ^ s * g y ^ (1 - s) ≤ h (s • x + (1 - s) • y)) →
      (∫⁻ x, f x) ^ s * (∫⁻ y, g y) ^ (1 - s) ≤ ∫⁻ z, h z by
    exact H ι f g h hf_meas hg_meas hh_meas ht_pos ht_lt h_le
  intro κ _Fκ
  refine Fintype.induction_empty_option
    (P := fun κ [Fintype κ] => ∀ (f g h : (κ → ℝ) → ℝ≥0∞),
      Measurable f → Measurable g → Measurable h →
      ∀ {s : ℝ}, 0 < s → s < 1 →
      (∀ x y : κ → ℝ, f x ^ s * g y ^ (1 - s) ≤ h (s • x + (1 - s) • y)) →
      (∫⁻ x, f x) ^ s * (∫⁻ y, g y) ^ (1 - s) ≤ ∫⁻ z, h z) ?_ ?_ ?_ κ
  · -- `of_equiv`: transport along an `Equiv α ≃ β`. Pull `(f, g, h)` back
    -- through `(piCongrLeft (fun _ : α => ℝ) e.symm).symm : (α → ℝ) ≃ᵐ (β → ℝ)`,
    -- whose value `ψ.symm x b = x (e.symm b)` is `rfl`-apply.
    intro α β _Fβ e IH f g h hf hg hh s hs hs1 hle
    letI : Fintype α := Fintype.ofEquiv β e.symm
    set ψ : (β → ℝ) ≃ᵐ (α → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ : α => ℝ) e.symm with hψ_def
    -- `ψ.symm` preserves affine combinations (componentwise).
    have hψ_smul : ∀ x y : α → ℝ,
        ψ.symm (s • x + (1 - s) • y) = s • ψ.symm x + (1 - s) • ψ.symm y := fun _ _ => rfl
    -- Volume transfer: `(volume_α).map ψ.symm = volume_β`.
    have h_vol_fwd : (volume : Measure (β → ℝ)).map ψ = (volume : Measure (α → ℝ)) := by
      conv_lhs => rw [MeasureTheory.volume_pi]
      conv_rhs => rw [MeasureTheory.volume_pi]
      exact MeasureTheory.Measure.pi_map_piCongrLeft e.symm (fun _ : α => volume)
    have h_vol : (volume : Measure (α → ℝ)).map ψ.symm = (volume : Measure (β → ℝ)) := by
      rw [← h_vol_fwd, MeasurableEquiv.map_symm_map]
    -- Pull `(f, g, h)` back to `(α → ℝ)`.
    have hf' : Measurable (f ∘ ψ.symm) := hf.comp ψ.symm.measurable
    have hg' : Measurable (g ∘ ψ.symm) := hg.comp ψ.symm.measurable
    have hh' : Measurable (h ∘ ψ.symm) := hh.comp ψ.symm.measurable
    have hle' : ∀ x y : α → ℝ,
        (f ∘ ψ.symm) x ^ s * (g ∘ ψ.symm) y ^ (1 - s)
        ≤ (h ∘ ψ.symm) (s • x + (1 - s) • y) := by
      intro x y
      change f (ψ.symm x) ^ s * g (ψ.symm y) ^ (1 - s) ≤ h (ψ.symm (s • x + (1 - s) • y))
      rw [hψ_smul x y]
      exact hle (ψ.symm x) (ψ.symm y)
    -- Translate β-side integrals back to α-side via `lintegral_map`.
    have hf_int : ∫⁻ y, f y = ∫⁻ x, f (ψ.symm x) := by
      conv_lhs => rw [show (volume : Measure (β → ℝ))
          = (volume : Measure (α → ℝ)).map ψ.symm from h_vol.symm]
      exact MeasureTheory.lintegral_map hf ψ.symm.measurable
    have hg_int : ∫⁻ y, g y = ∫⁻ x, g (ψ.symm x) := by
      conv_lhs => rw [show (volume : Measure (β → ℝ))
          = (volume : Measure (α → ℝ)).map ψ.symm from h_vol.symm]
      exact MeasureTheory.lintegral_map hg ψ.symm.measurable
    have hh_int : ∫⁻ y, h y = ∫⁻ x, h (ψ.symm x) := by
      conv_lhs => rw [show (volume : Measure (β → ℝ))
          = (volume : Measure (α → ℝ)).map ψ.symm from h_vol.symm]
      exact MeasureTheory.lintegral_map hh ψ.symm.measurable
    rw [hf_int, hg_int, hh_int]
    exact IH (f ∘ ψ.symm) (g ∘ ψ.symm) (h ∘ ψ.symm) hf' hg' hh' hs hs1 hle'
  · -- `h_empty`: `PEmpty → ℝ` is a singleton. Volume is Dirac at the unique
    -- point; all integrals reduce to evaluation, the conclusion is the PL
    -- hypothesis at that point.
    intro f g h hf_meas hg_meas hh_meas s hs_pos hs_lt h_le
    have h_volume : (volume : Measure (PEmpty → ℝ))
        = Measure.dirac (fun a : PEmpty => isEmptyElim a) :=
      Measure.volume_pi_eq_dirac _
    rw [h_volume, lintegral_dirac' _ hf_meas, lintegral_dirac' _ hg_meas,
        lintegral_dirac' _ hh_meas]
    have h_pl := h_le (fun a => isEmptyElim a) (fun a => isEmptyElim a)
    have h_smul : s • (fun a : PEmpty => isEmptyElim a : PEmpty → ℝ)
                  + (1 - s) • (fun a : PEmpty => isEmptyElim a : PEmpty → ℝ)
                = (fun a : PEmpty => isEmptyElim a : PEmpty → ℝ) := by
      funext a; exact isEmptyElim a
    rwa [h_smul] at h_pl
  · -- `h_option`: `P α ⇒ P (Option α)`. Split the index off the `none`-coord
    -- via `MeasurableEquiv.piOptionEquivProd`, push integrals through Fubini
    -- to land outer-on-ℝ + inner-on-(α → ℝ); apply IH fibrewise to obtain the
    -- 1D PL hypothesis on the marginalised integrals; close with
    -- `prekopaLeindler_1d`.
    intro α _Fα IH f g h hf hg hh s hs hs1 hle
    let E : ((i : Option α) → ℝ) ≃ᵐ ((i : α) → ℝ) × ℝ :=
      MeasurableEquiv.piOptionEquivProd (fun _ : Option α => ℝ)
    -- `E.symm` is `rfl`-apply at `none` (gives `u`) and `some a` (gives `x' a`).
    have hE_none : ∀ (x' : α → ℝ) (u : ℝ),
        E.symm (x', u) none = u := fun _ _ => rfl
    have hE_some : ∀ (x' : α → ℝ) (u : ℝ) (a : α),
        E.symm (x', u) (some a) = x' a := fun _ _ _ => rfl
    -- `E.symm` preserves affine combinations (verified at each `Option` case).
    have hE_smul : ∀ (x' y' : α → ℝ) (u v : ℝ),
        s • E.symm (x', u) + (1 - s) • E.symm (y', v)
        = E.symm (s • x' + (1 - s) • y', s * u + (1 - s) * v) := by
      intro x' y' u v
      funext i
      cases i with
      | none =>
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        change s * u + (1 - s) * v = s * u + (1 - s) * v
        rfl
      | some a =>
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        change s * x' a + (1 - s) * y' a = s * x' a + (1 - s) * y' a
        rfl
    -- Volume transfer: `(volume_α.prod volume_ℝ).map E.symm = volume_OptionAlpha`.
    have h_vol : ((volume : Measure (α → ℝ)).prod (volume : Measure ℝ)).map E.symm
        = (volume : Measure (Option α → ℝ)) := by
      conv_rhs => rw [MeasureTheory.volume_pi]
      conv_lhs => rw [show (volume : Measure (α → ℝ))
          = MeasureTheory.Measure.pi (fun _ : α => volume) from MeasureTheory.volume_pi]
      exact MeasureTheory.Measure.pi_map_piOptionEquivProd
        (fun _ : Option α => volume)
    -- Marginalised functions on ℝ.
    set F : ℝ → ℝ≥0∞ := fun u => ∫⁻ x' : α → ℝ, f (E.symm (x', u)) with hF_def
    set G : ℝ → ℝ≥0∞ := fun v => ∫⁻ y' : α → ℝ, g (E.symm (y', v)) with hG_def
    set H_marg : ℝ → ℝ≥0∞ := fun w => ∫⁻ z' : α → ℝ, h (E.symm (z', w)) with hH_def
    -- Measurability of `f ∘ E.symm`, `g ∘ E.symm`, `h ∘ E.symm`.
    have hf_comp : Measurable (fun p : (α → ℝ) × ℝ => f (E.symm p)) :=
      hf.comp E.symm.measurable
    have hg_comp : Measurable (fun p : (α → ℝ) × ℝ => g (E.symm p)) :=
      hg.comp E.symm.measurable
    have hh_comp : Measurable (fun p : (α → ℝ) × ℝ => h (E.symm p)) :=
      hh.comp E.symm.measurable
    have hF_meas : Measurable F := Measurable.lintegral_prod_left' hf_comp
    have hG_meas : Measurable G := Measurable.lintegral_prod_left' hg_comp
    have hH_marg_meas : Measurable H_marg := Measurable.lintegral_prod_left' hh_comp
    -- 1D PL hypothesis on `(F, G, H_marg)` via IH at each `(u, v) ∈ ℝ × ℝ`.
    have h_FGH_le : ∀ u v : ℝ,
        F u ^ s * G v ^ (1 - s) ≤ H_marg (s * u + (1 - s) * v) := by
      intro u v
      have hf_slice : Measurable (fun x' : α → ℝ => f (E.symm (x', u))) :=
        hf.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have hg_slice : Measurable (fun y' : α → ℝ => g (E.symm (y', v))) :=
        hg.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have hh_slice : Measurable (fun z' : α → ℝ =>
          h (E.symm (z', s * u + (1 - s) * v))) :=
        hh.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have h_slice_le : ∀ x' y' : α → ℝ,
          f (E.symm (x', u)) ^ s * g (E.symm (y', v)) ^ (1 - s)
          ≤ h (E.symm (s • x' + (1 - s) • y', s * u + (1 - s) * v)) := by
        intro x' y'
        have h_pl := hle (E.symm (x', u)) (E.symm (y', v))
        rw [hE_smul] at h_pl
        exact h_pl
      exact IH _ _ _ hf_slice hg_slice hh_slice hs hs1 h_slice_le
    -- Apply 1D PL.
    have h_1d := prekopaLeindler_1d hF_meas hG_meas hH_marg_meas hs hs1 h_FGH_le
    -- Translate full Option-α integrals back via `h_vol` + Fubini.
    have h_int_split : ∀ (k : (Option α → ℝ) → ℝ≥0∞), Measurable k →
        ∫⁻ z, k z = ∫⁻ u : ℝ, ∫⁻ x' : α → ℝ, k (E.symm (x', u)) := by
      intro k hk
      conv_lhs => rw [show (volume : Measure (Option α → ℝ))
          = ((volume : Measure (α → ℝ)).prod (volume : Measure ℝ)).map E.symm
        from h_vol.symm]
      rw [MeasureTheory.lintegral_map hk E.symm.measurable]
      exact MeasureTheory.lintegral_prod_symm' _ (hk.comp E.symm.measurable)
    rw [h_int_split f hf, h_int_split g hg, h_int_split h hh]
    exact h_1d

end Wishart.PrekopaLeindler
end CanonicalSource59
