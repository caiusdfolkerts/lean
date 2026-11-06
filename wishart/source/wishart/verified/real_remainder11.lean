module

public import wishart.verified.real_remainder10

/- Generated ordinary proof stage. See audit/staged_real_remainder/RealRemainder11/manifest.json. -/

@[expose] public section

section CanonicalSource100
/- Source: Wishart/BoundaryMonomialApproximation.lean -/



/-!
# Supporting monomials that retain the value at zero

The usual positive-domain supporting lines can lose a nonzero boundary value.
When that value is positive, this construction adds its constant supporting
line. When it is zero, every supporting monomial already vanishes at zero.
The resulting finite maxima increase to the actual function on the entire
nonnegative half-line, including the singular boundary.
-/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped Classical BigOperators ENNReal
namespace WishartVerification

theorem monomial_minorant_of_log_minorant {f : ℝ → ℝ}
    (hf : GeometricallyLogConvex f) {a b : ℝ}
    (hab : ∀ s, a * s + b ≤ Real.log (f (Real.exp s)))
    {x : ℝ} (hx : 0 < x) : Real.exp b * x ^ a ≤ f x := by
  rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
  have heq : b + Real.log x * a = a * Real.log x + b := by ring
  rw [heq, ← exp_log_profile_eq hf hx]
  exact Real.exp_le_exp.mpr (hab (Real.log x))

theorem monomial_minorant_at_zero {f : ℝ → ℝ}
    (hf : GeometricOuterOnNonnegative f) {a b : ℝ} (ha : 0 ≤ a)
    (hab : ∀ s, a * s + b ≤ Real.log (f (Real.exp s))) :
    Real.exp b * (0 : ℝ) ^ a ≤ f 0 := by
  let x (l : ℕ) : ℝ := 1 / ((l : ℝ) + 1)
  have hxpos : ∀ l, 0 < x l := fun l => by dsimp [x]; positivity
  have hx : Tendsto x atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hleft : Tendsto (fun l => Real.exp b * (x l) ^ a) atTop
      (𝓝 (Real.exp b * (0 : ℝ) ^ a)) :=
    (continuous_const.mul (Real.continuous_rpow_const ha)).continuousAt.tendsto.comp hx
  have hright : Tendsto (fun l => f (x l)) atTop (𝓝 (f 0)) :=
    hf.continuous_zero.tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hx, Filter.Eventually.of_forall fun l => (hxpos l).le⟩)
  exact le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall fun l =>
    monomial_minorant_of_log_minorant hf.geometric hab (hxpos l))

theorem finiteMonomialMaximum_mono_index (a b : ℕ → ℝ) (x : ℝ) :
    Monotone (fun n => finiteMaximum (fun j : Fin (n + 1) => Real.exp (b j) * x ^ (a j))) := by
  intro n m hnm
  apply finiteMaximum_le
  intro j
  let k : Fin (m + 1) := ⟨j, lt_of_lt_of_le j.isLt (Nat.add_le_add_right hnm 1)⟩
  exact le_finiteMaximum (fun j : Fin (m + 1) => Real.exp (b j) * x ^ (a j)) k

/-- The finite maxima now converge at every nonnegative argument and are
bounded by the original function there. The first monomial recovers its exact
value at zero. -/
theorem geometric_boundary_monomial_approximants {f : ℝ → ℝ}
    (hf : GeometricOuterOnNonnegative f) :
    ∃ a b : ℕ → ℝ, (∀ i, 0 ≤ a i) ∧
      (∀ i x, 0 ≤ x → Real.exp (b i) * x ^ (a i) ≤ f x) ∧
      (∀ x, 0 ≤ x → Tendsto
        (fun n => finiteMaximum (fun j : Fin (n + 1) => Real.exp (b j) * x ^ (a j)))
        atTop (𝓝 (f x))) := by
  obtain ⟨a, b, ha, hle, hsup⟩ := exists_nonnegative_affine_minorants
    hf.geometric.convex_log hf.geometric.monotone_log
  have build (A B : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i)
      (hle' : ∀ i s, A i * s + B i ≤ Real.log (f (Real.exp s)))
      (hsup' : ∀ s, (⨆ i, A i * s + B i) = Real.log (f (Real.exp s)))
      (hfirst : Real.exp (B 0) * (0 : ℝ) ^ (A 0) = f 0) :
      (∀ i x, 0 ≤ x → Real.exp (B i) * x ^ (A i) ≤ f x) ∧
      (∀ x, 0 ≤ x → Tendsto
        (fun n => finiteMaximum (fun j : Fin (n + 1) => Real.exp (B j) * x ^ (A j)))
        atTop (𝓝 (f x))) := by
    have hbound (i : ℕ) (x : ℝ) (hx : 0 ≤ x) : Real.exp (B i) * x ^ (A i) ≤ f x := by
      rcases hx.eq_or_lt with hx0 | hxpos
      · subst x
        exact monomial_minorant_at_zero hf (hA i) (hle' i)
      · exact monomial_minorant_of_log_minorant hf.geometric (hle' i) hxpos
    refine ⟨hbound, ?_⟩
    intro x hx
    rcases hx.eq_or_lt with hx0 | hxpos
    · subst x
      have heq (n : ℕ) : finiteMaximum
          (fun j : Fin (n + 1) => Real.exp (B j) * (0 : ℝ) ^ (A j)) = f 0 := by
        apply le_antisymm (finiteMaximum_le fun j : Fin (n + 1) => hbound j 0 le_rfl)
        rw [← hfirst]
        exact le_finiteMaximum (fun j : Fin (n + 1) => Real.exp (B j) * (0 : ℝ) ^ (A j))
          ⟨0, Nat.succ_pos n⟩
      simp only [heq]
      exact tendsto_const_nhds
    · have hlim := Real.continuous_exp.continuousAt.tendsto.comp
        (affinePartialMaximum_tendsto hle' hsup' (Real.log x))
      simpa only [finiteMonomialMaximum_eq_exp_affineMaximum A B _ hxpos,
        Function.comp_def, exp_log_profile_eq hf.geometric hxpos] using hlim
  by_cases hf0 : 0 < f 0
  · let A : ℕ → ℝ := fun i => if i = 0 then 0 else a (i - 1)
    let B : ℕ → ℝ := fun i => if i = 0 then Real.log (f 0) else b (i - 1)
    have hA (i : ℕ) : 0 ≤ A i := by
      by_cases hi : i = 0
      · simp only [A, hi, if_pos rfl, le_refl]
      · simpa only [A, if_neg hi] using ha (i - 1)
    have hnew (i : ℕ) (s : ℝ) : A i * s + B i ≤ Real.log (f (Real.exp s)) := by
      by_cases hi : i = 0
      · simp only [A, B, hi, if_pos rfl, zero_mul, zero_add]
        exact Real.log_le_log hf0 (hf.zero_le_value (Real.exp_pos s))
      · simpa only [A, B, if_neg hi] using hle (i - 1) s
    have hsupnew (s : ℝ) : (⨆ i, A i * s + B i) = Real.log (f (Real.exp s)) := by
      apply le_antisymm (ciSup_le (fun i => hnew i s))
      rw [← hsup s]
      apply ciSup_le
      intro i
      have hb : BddAbove (Set.range (fun j => A j * s + B j)) :=
        ⟨Real.log (f (Real.exp s)), by rintro _ ⟨j, rfl⟩; exact hnew j s⟩
      have heq : A (i + 1) * s + B (i + 1) = a i * s + b i := by
        simp only [A, B, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
      rw [← heq]
      exact le_ciSup hb (i + 1)
    have hfirst : Real.exp (B 0) * (0 : ℝ) ^ (A 0) = f 0 := by
      simp only [A, B, if_pos rfl, Real.rpow_zero, mul_one, Real.exp_log hf0]
    exact ⟨A, B, hA, build A B hA hnew hsupnew hfirst⟩
  · have hfzero : f 0 = 0 := le_antisymm (le_of_not_gt hf0) hf.zero_nonneg
    have hfirst : Real.exp (b 0) * (0 : ℝ) ^ (a 0) = f 0 := by
      apply le_antisymm (monomial_minorant_at_zero hf (ha 0) (hle 0))
      rw [hfzero]
      exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg le_rfl _)
    exact ⟨a, b, ha, build a b ha hle hsup hfirst⟩

end WishartVerification
end
end CanonicalSource100

section CanonicalSource101
/- Source: Wishart/BoundaryOuterLimits.lean -/



/-!
# Nonnegative expectation limits with the exact boundary values

The additional constant supporting line makes the finite monomial maxima
valid on every rank stratum. Both sides of each split are passed to their
limits by monotone convergence, using independent copies for the product of
expectations. No finite-moment premise or decreasing-limit interchange enters.
-/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped Classical BigOperators ENNReal
namespace WishartVerification
variable {κ : Type*} [Fintype κ]

theorem supportingOuterProduct_nonneg_of_nonneg (a b : κ → ℕ → ℝ) (n : ℕ)
    {d : κ → ℝ} (hd : ∀ i, 0 ≤ d i) : 0 ≤ supportingOuterProduct a b n d := by
  apply Finset.prod_nonneg
  intro i hi
  exact finiteMaximum_nonneg fun j =>
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (hd i) _)

theorem supportingOuterProduct_mono_index_of_nonneg (a b : κ → ℕ → ℝ)
    {d : κ → ℝ} (hd : ∀ i, 0 ≤ d i) :
    Monotone (fun n => supportingOuterProduct a b n d) := by
  intro n m hnm
  apply Finset.prod_le_prod₀
  · intro i hi
    exact finiteMaximum_nonneg fun j =>
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (hd i) _)
  · intro i hi
    exact finiteMonomialMaximum_mono_index (a i) (b i) (d i) hnm

theorem supportingOuterProduct_tendsto_of_nonneg (a b : κ → ℕ → ℝ)
    (f : κ → ℝ → ℝ)
    (hlimit : ∀ i x, 0 ≤ x → Tendsto
      (fun n => finiteMaximum (fun j : Fin (n + 1) => Real.exp (b i j) * x ^ (a i j)))
      atTop (𝓝 (f i x))) {d : κ → ℝ} (hd : ∀ i, 0 ≤ d i) :
    Tendsto (fun n => supportingOuterProduct a b n d) atTop (𝓝 (∏ i, f i (d i))) :=
  tendsto_finsetProd _ (fun i _ => hlimit i (d i) (hd i))

theorem supportingOuterProduct_lintegral_tendsto_of_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a b : κ → ℕ → ℝ) (ha : ∀ i n, 0 ≤ a i n) (f : κ → ℝ → ℝ)
    (hlimit : ∀ i x, 0 ≤ x → Tendsto
      (fun n => finiteMaximum (fun j : Fin (n + 1) => Real.exp (b i j) * x ^ (a i j)))
      atTop (𝓝 (f i x)))
    (d : Ω → κ → ℝ) (hdm : Measurable d) (hdpos : ∀ᵐ z ∂μ, ∀ i, 0 ≤ d z i) :
    Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (supportingOuterProduct a b n (d z)) ∂μ) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (∏ i, f i (d z i)) ∂μ)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    exact ((continuous_finiteOuterTest
      (fun i (j : Fin (n + 1)) => a i j) (fun i (j : Fin (n + 1)) => b i j)
      (fun i j => ha i j)).measurable.comp hdm).ennreal_ofReal.aemeasurable
  · filter_upwards [hdpos] with z hz
    intro n m hnm
    exact ENNReal.ofReal_le_ofReal (supportingOuterProduct_mono_index_of_nonneg a b hz hnm)
  · filter_upwards [hdpos] with z hz
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (supportingOuterProduct_tendsto_of_nonneg a b f hlimit hz)

theorem boundary_geometric_outer_comparison_of_finite_comparisons
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) (d : Ω → κ → ℝ) (e : Ξ → κ → ℝ)
    (hdm : Measurable d) (hem : Measurable e)
    (hdpos : ∀ᵐ z ∂μ, ∀ i, 0 ≤ d z i) (hepos : ∀ᵐ z ∂ν, ∀ i, 0 ≤ e z i)
    (hfinite : ∀ n : ℕ, ∀ a b : κ → Fin (n + 1) → ℝ,
      (∀ i j, 0 ≤ a i j) →
      (∫⁻ z, ENNReal.ofReal (finiteOuterTest a b (d z)) ∂μ) ≤
        ∫⁻ z, ENNReal.ofReal (finiteOuterTest a b (e z)) ∂ν)
    (f : κ → ℝ → ℝ) (hf : ∀ i, GeometricOuterOnNonnegative (f i)) :
    (∫⁻ z, ENNReal.ofReal (∏ i, f i (d z i)) ∂μ) ≤
      ∫⁻ z, ENNReal.ofReal (∏ i, f i (e z i)) ∂ν := by
  choose a b ha hbound hlimit using fun i => geometric_boundary_monomial_approximants (hf i)
  exact le_of_tendsto_of_tendsto
    (supportingOuterProduct_lintegral_tendsto_of_nonneg μ a b ha f hlimit d hdm hdpos)
    (supportingOuterProduct_lintegral_tendsto_of_nonneg ν a b ha f hlimit e hem hepos)
    (Filter.Eventually.of_forall fun n =>
      hfinite n (fun i j => a i j) (fun i j => b i j) (fun i j => ha i j))

/-- An internal limit theorem. Its finite-test premise is supplied in the
matrix application by the actual radial comparison and Haar association. -/
theorem boundary_geometric_outer_selected_split_of_finite_splits
    {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (μ : Measure Ω) [SFinite μ]
    (d₀ : Ω → ℝ) (d : Ω → κ → ℝ)
    (hd₀m : Measurable d₀) (hdm : Measurable d)
    (hd₀pos : ∀ᵐ z ∂μ, 0 ≤ d₀ z) (hdpos : ∀ᵐ z ∂μ, ∀ i, 0 ≤ d z i)
    (hfinite : ∀ n : ℕ, ∀ a₀ b₀ : Fin (n + 1) → ℝ,
      ∀ a b : κ → Fin (n + 1) → ℝ,
      (∀ j, 0 ≤ a₀ j) → (∀ i j, 0 ≤ a i j) →
      (∫⁻ z, ENNReal.ofReal (finiteMaximum (fun j => Real.exp (b₀ j) * d₀ z ^ (a₀ j))) ∂μ) *
        (∫⁻ z, ENNReal.ofReal (finiteOuterTest a b (d z)) ∂μ) ≤
        ∫⁻ z, ENNReal.ofReal (finiteMaximum (fun j => Real.exp (b₀ j) * d₀ z ^ (a₀ j)) *
          finiteOuterTest a b (d z)) ∂μ)
    (f₀ : ℝ → ℝ) (f : κ → ℝ → ℝ)
    (hf₀ : GeometricOuterOnNonnegative f₀) (hf : ∀ i, GeometricOuterOnNonnegative (f i)) :
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
  have hlpos : ∀ᵐ z ∂μ.prod μ, ∀ i, 0 ≤ left z i := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hd₀pos,
      Measure.quasiMeasurePreserving_snd.ae hdpos] with z hz₀ hz i
    cases i with
    | none => exact hz₀
    | some i => exact hz i
  have hrpos : ∀ᵐ z ∂μ, ∀ i, 0 ≤ right z i := by
    filter_upwards [hd₀pos, hdpos] with z hz₀ hz i
    cases i with
    | none => exact hz₀
    | some i => exact hz i
  have hfuns : ∀ i, GeometricOuterOnNonnegative (functions i) := by
    intro i
    cases i with
    | none => exact hf₀
    | some i => exact hf i
  have hcompare := boundary_geometric_outer_comparison_of_finite_comparisons
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
          mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hz _)
      have hind := lintegral_independent_real_product (μ := μ) (ν := μ)
        hselm.aemeasurable hrestm.aemeasurable hselpos
      dsimp only [finiteOuterTest, Function.comp_def] at hind
      simp only [finiteOuterTest, Fintype.prod_option, left, right, Option.elim_none,
        Option.elim_some]
      rw [hind]
      exact hfinite n (a none) (b none) (a ∘ some) (b ∘ some) (ha none)
        (fun i j => ha (some i) j)) functions hfuns
  have hf₀m := aemeasurable_geometric_outer_comp_nonnegative hf₀ hd₀m hd₀pos
  have hfm : AEMeasurable (fun z => ∏ i, f i (d z i)) μ := by
    apply Finset.aemeasurable_fun_prod
    intro i hi
    exact aemeasurable_geometric_outer_comp_nonnegative (hf i) ((measurable_pi_iff.mp hdm) i)
      (hdpos.mono fun z hz => hz i)
  simp only [Fintype.prod_option, functions, left, right, Option.elim_none,
    Option.elim_some] at hcompare
  rw [lintegral_independent_real_product hf₀m hfm
    (hd₀pos.mono fun z hz => hf₀.nonneg hz)] at hcompare
  exact hcompare

end WishartVerification
end
end CanonicalSource101

section CanonicalSource102
/- Source: Wishart/GramGeometricLimits.lean -/



/-!
# Geometric outer limits for the actual integer Gram law

The positive-domain limit is retained as an internal helper. The boundary
version uses a supporting constant when the assigned value at zero is positive,
so that monotone convergence also applies on every singular rank stratum.
Every application below supplies its finite comparisons by a matrix theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator
namespace Wishart

/-- Internal limit assembly for actual full-rank compressions. Every use below
supplies the finite comparisons by a proved matrix theorem. -/
theorem gram_compression_geometric_split_of_finite {p q : ℕ} (n : ℕ) {c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q) (hc : 0 ≤ c)
    (hselectedPositive : 0 < c ∨ q ≤ n)
    {κ : Type*} [Fintype κ]
    (k : κ → ℕ) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hM : ∀ i, (M i).rank = k i) (d : κ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hremainingPositive : ∀ i, 0 < d i ∨ k i ≤ n)
    (f₀ : ℝ → ℝ) (f : κ → ℝ → ℝ)
    (hf₀ : GeometricallyLogConvex f₀) (hf : ∀ i, GeometricallyLogConvex (f i))
    (hfinite : ∀ l : ℕ, ∀ a₀ b₀ : Fin (l + 1) → ℝ,
      ∀ a b : κ → Fin (l + 1) → ℝ,
      (∀ j, 0 ≤ a₀ j) → (∀ i j, 0 ≤ a i j) →
      (∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X ∂wishartGramMeasure n Sigma) *
        (∫ X, affineMaximumProduct 0 k
          (fun i => d i • compressionScale Sigma (M i)) M a b X
          ∂wishartGramMeasure n Sigma) ≤
        ∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X *
          affineMaximumProduct 0 k (fun i => d i • compressionScale Sigma (M i)) M a b X
          ∂wishartGramMeasure n Sigma) :
    (∫⁻ X, ENNReal.ofReal (f₀ (shiftedCompressionDeterminant Sigma Q c X))
      ∂wishartGramMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ i, f i (shiftedCompressionDeterminant Sigma (M i) (d i) X))
        ∂wishartGramMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (f₀ (shiftedCompressionDeterminant Sigma Q c X) *
        ∏ i, f i (shiftedCompressionDeterminant Sigma (M i) (d i) X))
        ∂wishartGramMeasure n Sigma := by
  classical
  let μ := wishartGramMeasure n Sigma
  let B := fun i => d i • compressionScale Sigma (M i)
  have hB : ∀ i, (B i).PosSemidef := fun i =>
    (compressionScale_posDef hSigma (M i) (hM i)).posSemidef.smul (hd i)
  have h₀pos : ∀ᵐ X ∂μ, 0 < shiftedCompressionDeterminant Sigma Q c X :=
    ae_shiftedCompressionDeterminant_pos_gram hSigma Q hQ hc hselectedPositive
  have hpos : ∀ᵐ X ∂μ, ∀ i,
      0 < shiftedCompressionDeterminant Sigma (M i) (d i) X := by
    rw [ae_all_iff]
    exact fun i => ae_shiftedCompressionDeterminant_pos_gram hSigma (M i) (hM i)
      (hd i) (hremainingPositive i)
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
      ((by
        change HasAllFiniteMoments (fun X : SymmetricMatrix p =>
          (Qᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * Q + c • compressionScale Sigma Q).det)
          (wishartGramMeasure n Sigma)
        simpa only [add_comm] using
          allFiniteMoments_gram_affine_compression_det n Sigma
            (c • compressionScale Sigma Q) Q :
        HasAllFiniteMoments (shiftedCompressionDeterminant Sigma Q c) μ).rpow (ha₀ j)).const_mul
        (Real.exp (b₀ j))
  have hrm : HasAllFiniteMoments remaining μ :=
    allFiniteMoments_affineMaximumProduct_of_entries 0 k B M a b ha
      (fun X : SymmetricMatrix p => X)
      (allFiniteMoments_gram_entry n Sigma)
  have hsp : ∀ᵐ X ∂μ, 0 ≤ selected X :=
    h₀pos.mono fun X hX => finiteMaximum_nonneg fun j =>
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hX.le _)
  have hrp : ∀ᵐ X ∂μ, 0 ≤ remaining X :=
    (ae_posSemidef_wishartGramMeasure n Sigma).mono fun X hX =>
      affineMaximumProduct_zero_nonneg k B M a b hB hX
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


/-- Internal limit assembly for actual full-rank compressions. Every use below
supplies the finite comparisons by a proved matrix theorem. -/
theorem gram_compression_boundary_split_of_finite {p q : ℕ} (n : ℕ) {c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q) (hc : 0 ≤ c)
    {κ : Type*} [Fintype κ]
    (k : κ → ℕ) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hM : ∀ i, (M i).rank = k i) (d : κ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (f₀ : ℝ → ℝ) (f : κ → ℝ → ℝ)
    (hf₀ : GeometricOuterOnNonnegative f₀) (hf : ∀ i, GeometricOuterOnNonnegative (f i))
    (hfinite : ∀ l : ℕ, ∀ a₀ b₀ : Fin (l + 1) → ℝ,
      ∀ a b : κ → Fin (l + 1) → ℝ,
      (∀ j, 0 ≤ a₀ j) → (∀ i j, 0 ≤ a i j) →
      (∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X ∂wishartGramMeasure n Sigma) *
        (∫ X, affineMaximumProduct 0 k
          (fun i => d i • compressionScale Sigma (M i)) M a b X
          ∂wishartGramMeasure n Sigma) ≤
        ∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X *
          affineMaximumProduct 0 k (fun i => d i • compressionScale Sigma (M i)) M a b X
          ∂wishartGramMeasure n Sigma) :
    (∫⁻ X, ENNReal.ofReal (f₀ (shiftedCompressionDeterminant Sigma Q c X))
      ∂wishartGramMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ i, f i (shiftedCompressionDeterminant Sigma (M i) (d i) X))
        ∂wishartGramMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (f₀ (shiftedCompressionDeterminant Sigma Q c X) *
        ∏ i, f i (shiftedCompressionDeterminant Sigma (M i) (d i) X))
        ∂wishartGramMeasure n Sigma := by
  classical
  let μ := wishartGramMeasure n Sigma
  let B := fun i => d i • compressionScale Sigma (M i)
  have hB : ∀ i, (B i).PosSemidef := fun i =>
    (compressionScale_posDef hSigma (M i) (hM i)).posSemidef.smul (hd i)
  have h₀pos : ∀ᵐ X ∂μ, 0 ≤ shiftedCompressionDeterminant Sigma Q c X := by
    filter_upwards [ae_posSemidef_wishartGramMeasure n Sigma] with X hX
    have hcomp := hX.conjTranspose_mul_mul_same Q
    have hscale := (compressionScale_posDef hSigma Q hQ).posSemidef.smul hc
    simpa only [shiftedCompressionDeterminant,
      Matrix.conjTranspose_eq_transpose_of_trivial] using (hcomp.add hscale).det_nonneg
  have hpos : ∀ᵐ X ∂μ, ∀ i,
      0 ≤ shiftedCompressionDeterminant Sigma (M i) (d i) X := by
    filter_upwards [ae_posSemidef_wishartGramMeasure n Sigma] with X hX i
    have hcomp := hX.conjTranspose_mul_mul_same (M i)
    simpa only [shiftedCompressionDeterminant, B,
      Matrix.conjTranspose_eq_transpose_of_trivial] using (hcomp.add (hB i)).det_nonneg
  apply boundary_geometric_outer_selected_split_of_finite_splits μ
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
      ((by
        change HasAllFiniteMoments (fun X : SymmetricMatrix p =>
          (Qᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * Q + c • compressionScale Sigma Q).det)
          (wishartGramMeasure n Sigma)
        simpa only [add_comm] using
          allFiniteMoments_gram_affine_compression_det n Sigma
            (c • compressionScale Sigma Q) Q :
        HasAllFiniteMoments (shiftedCompressionDeterminant Sigma Q c) μ).rpow (ha₀ j)).const_mul
        (Real.exp (b₀ j))
  have hrm : HasAllFiniteMoments remaining μ :=
    allFiniteMoments_affineMaximumProduct_of_entries 0 k B M a b ha
      (fun X : SymmetricMatrix p => X)
      (allFiniteMoments_gram_entry n Sigma)
  have hsp : ∀ᵐ X ∂μ, 0 ≤ selected X :=
    h₀pos.mono fun X hX => finiteMaximum_nonneg fun j =>
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hX _)
  have hrp : ∀ᵐ X ∂μ, 0 ≤ remaining X :=
    (ae_posSemidef_wishartGramMeasure n Sigma).mono fun X hX =>
      affineMaximumProduct_zero_nonneg k B M a b hB hX
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


end Wishart
end
end CanonicalSource102

section CanonicalSource103
/- Source: Wishart/GramRankIteration.lean -/



/-! # The uncapped rank test for singular integer Gram laws

This is the exact largest-plus-third-largest test of Corollary 5.4.  It has
no ambient-dimension cap. Constant/full-rank removal and the last pair are
explicit analytic inputs to the finite iteration, supplied by the Gram-law
applications.
-/

noncomputable section
open scoped Classical ENNReal BigOperators
namespace WishartVerification.MomentAssembly
variable {ι : Type*} [DecidableEq ι]

/-- For any three distinct active proper factors, the sum of the smallest
rank and either other rank meets the selected-factor threshold. -/
def gramRankTripleThreshold (rank : ι → ℕ) (A : Finset ι) (n : ℕ) : Prop :=
  ∀ i ∈ A, ∀ j ∈ A, ∀ k ∈ A,
    i ≠ j → i ≠ k → j ≠ k → rank i ≤ rank j → rank i ≤ rank k →
      rank i + rank j ≤ n

theorem gramRankTripleThreshold_of_card_le_two (rank : ι → ℕ) (A : Finset ι)
    (n : ℕ) (hA : A.card ≤ 2) : gramRankTripleThreshold rank A n := by
  intro i hi j hj k hk hij hik hjk _ _
  have hsub : ({i, j, k} : Finset ι) ⊆ A := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> assumption
  have hcard : ({i, j, k} : Finset ι).card = 3 := by simp [hij, hik, hjk]
  have hle := Finset.card_le_card hsub
  omega


theorem gramRankTripleThreshold_equiv {κ : Type*} [Fintype κ] [DecidableEq κ]
    (rank : ι → ℕ) (A : Finset ι) (e : κ ≃ A) (n : ℕ) :
    gramRankTripleThreshold rank A n ↔
      gramRankTripleThreshold (fun i => rank (e i)) Finset.univ n := by
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


theorem gramRankTripleThreshold_iff_largest_third {d : ℕ} (hd : 3 ≤ d)
    (rank : Fin d → ℕ) (hsorted : Antitone rank) (n : ℕ) :
    gramRankTripleThreshold rank Finset.univ n ↔
      rank ⟨0, by omega⟩ + rank ⟨2, by omega⟩ ≤ n := by
  constructor
  · intro h
    have h' := h ⟨2, by omega⟩ (Finset.mem_univ _)
      ⟨0, by omega⟩ (Finset.mem_univ _) ⟨1, by omega⟩ (Finset.mem_univ _)
      (by intro heq; have hv := congrArg Fin.val heq; change (2 : ℕ) = 0 at hv; omega)
      (by intro heq; have hv := congrArg Fin.val heq; change (2 : ℕ) = 1 at hv; omega)
      (by intro heq; have hv := congrArg Fin.val heq; change (0 : ℕ) = 1 at hv; omega)
      (hsorted (by change (0 : ℕ) ≤ 2; omega))
      (hsorted (by change (1 : ℕ) ≤ 2; omega))
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
    have hsum : rank i + rank j ≤ rank ⟨0, by omega⟩ + rank ⟨2, by omega⟩ := by omega
    exact hsum.trans h

/-- The condition is vacuous when at most two active proper factors remain;
otherwise it reads precisely `n ≥ k_(1)+k_(3)` in descending order. -/
def gramOrderedRankThreshold (rank : ι → ℕ) (A : Finset ι) (n : ℕ) : Prop :=
  ∀ h : 3 ≤ Fintype.card A,
    descendingRanks rank A ⟨0, by omega⟩ +
      descendingRanks rank A ⟨2, by omega⟩ ≤ n

theorem gramOrderedRankThreshold_iff (rank : ι → ℕ) (A : Finset ι) (n : ℕ) :
    gramOrderedRankThreshold rank A n ↔ gramRankTripleThreshold rank A n := by
  rw [gramRankTripleThreshold_equiv rank A (descendingRankEquiv rank A) n]
  change gramOrderedRankThreshold rank A n ↔
    gramRankTripleThreshold (descendingRanks rank A) Finset.univ n
  by_cases hd : 3 ≤ Fintype.card A
  · rw [gramRankTripleThreshold_iff_largest_third hd _ (antitone_descendingRanks rank A)]
    exact ⟨fun h => h hd, fun h _ => h⟩
  · constructor
    · intro _
      apply gramRankTripleThreshold_of_card_le_two
      simpa only [Finset.card_univ, Fintype.card_fin] using (show Fintype.card A ≤ 2 by omega)
    · intro _ h
      exact (hd h).elim

theorem extended_product_singletons_le_by_gram_rank (m : Finset ι → ℝ≥0∞)
    (rank : ι → ℕ) (A : Finset ι) (n : ℕ)
    (hempty : m ∅ = 1) (hpos : ∀ i, 0 ≤ m {i})
    (houtside : ∀ J i, i ∈ J → i ∉ A → m {i} * m (J.erase i) ≤ m J)
    (hpair : ∀ J i, i ∈ J → J.card ≤ 2 → m {i} * m (J.erase i) ≤ m J)
    (hrank : ∀ J i, i ∈ J → J ⊆ A →
      (∀ j ∈ J.erase i, rank i + rank j ≤ n) →
      m {i} * m (J.erase i) ≤ m J)
    (hthreshold : gramRankTripleThreshold rank A n) (J : Finset ι) :
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
end CanonicalSource103

section CanonicalSource104
/- Source: Wishart/GramGeometricFamily.lean -/



/-!
# Actual factors, constants, and retained ranks in Corollary 5.4

Constancy means almost-sure constancy under the actual integer Gaussian Gram
law. In particular an unshifted compression above the sample rank is constant
at the prescribed boundary value. The retained-rank condition removes exactly
these almost-sure constants and the full-rank factors, as in the manuscript.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability Matrix
open WishartVerification WishartVerification.MomentAssembly
open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator
namespace Wishart

structure GramGeometricCompressionFamily (p : ℕ) (ι : Type*) where
  size : ι → ℕ
  matrix : ∀ i, Matrix (Fin p) (Fin (size i)) ℝ
  full_rank : ∀ i, (matrix i).rank = size i
  shift : ι → ℝ
  shift_nonneg : ∀ i, 0 ≤ shift i
  outer : ι → ℝ → ℝ
  boundary : ∀ i, GeometricOuterOnNonnegative (outer i)

namespace GramGeometricCompressionFamily
variable {p : ℕ} {ι : Type*} [DecidableEq ι]
variable (F : GramGeometricCompressionFamily p ι) (Sigma : Matrix (Fin p) (Fin p) ℝ)

def factor (i : ι) (X : SymmetricMatrix p) : ℝ :=
  F.outer i (shiftedCompressionDeterminant Sigma (F.matrix i) (F.shift i) X)

def subproduct (J : Finset ι) (X : SymmetricMatrix p) : ℝ :=
  ∏ i ∈ J, F.factor Sigma i X

def moment (n : ℕ) (J : Finset ι) : ℝ≥0∞ :=
  ∫⁻ X, ENNReal.ofReal (F.subproduct Sigma J X) ∂wishartGramMeasure n Sigma

def AEConstantFactor (n : ℕ) (i : ι) : Prop :=
  ∃ c : ℝ, ∀ᵐ X ∂wishartGramMeasure n Sigma, F.factor Sigma i X = c

def activeProper [Fintype ι] (n : ℕ) : Finset ι :=
  Finset.univ.filter (fun i => F.size i < p ∧ ¬ F.AEConstantFactor Sigma n i)

theorem size_le (i : ι) : F.size i ≤ p := by
  rw [← F.full_rank i]
  exact (F.matrix i).rank_le_height

theorem determinant_nonneg (hSigma : Sigma.PosSemidef) (i : ι)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    0 ≤ shiftedCompressionDeterminant Sigma (F.matrix i) (F.shift i) X := by
  have hcomp : ((F.matrix i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * F.matrix i).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hX.conjTranspose_mul_mul_same (F.matrix i)
  have hscale : (compressionScale Sigma (F.matrix i)).PosSemidef := by
    simpa only [compressionScale, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hSigma.conjTranspose_mul_mul_same (F.matrix i)
  exact (hcomp.add (hscale.smul (F.shift_nonneg i))).det_nonneg

theorem factor_nonneg (hSigma : Sigma.PosSemidef) (i : ι)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    0 ≤ F.factor Sigma i X :=
  (F.boundary i).nonneg (F.determinant_nonneg Sigma hSigma i hX)

theorem subproduct_nonneg (hSigma : Sigma.PosSemidef) (J : Finset ι)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    0 ≤ F.subproduct Sigma J X :=
  Finset.prod_nonneg (fun i _ => F.factor_nonneg Sigma hSigma i hX)

theorem aemeasurable_factor (n : ℕ) (hSigma : Sigma.PosSemidef) (i : ι) :
    AEMeasurable (F.factor Sigma i) (wishartGramMeasure n Sigma) := by
  apply aemeasurable_geometric_outer_comp_nonnegative (F.boundary i)
    (measurable_shiftedCompressionDeterminant Sigma (F.matrix i) (F.shift i))
  exact (ae_posSemidef_wishartGramMeasure n Sigma).mono fun X hX =>
    F.determinant_nonneg Sigma hSigma i hX

theorem aemeasurable_subproduct (n : ℕ) (hSigma : Sigma.PosSemidef) (J : Finset ι) :
    AEMeasurable (F.subproduct Sigma J) (wishartGramMeasure n Sigma) :=
  Finset.aemeasurable_fun_prod J (fun i _ => F.aemeasurable_factor Sigma n hSigma i)

theorem aeConstant_of_unshifted_above_rank (n : ℕ) (hSigma : Sigma.PosSemidef)
    (i : ι) (hc : F.shift i = 0) (hrank : n < F.size i) :
    F.AEConstantFactor Sigma n i := by
  refine ⟨F.outer i 0, ?_⟩
  simpa only [factor, hc] using
    ae_outer_unshifted_gram_eq_const hSigma (F.matrix i) hrank (F.outer i)

theorem positive_det_of_not_aeConstant (n : ℕ) (hSigma : Sigma.PosDef)
    (i : ι) (hi : ¬ F.AEConstantFactor Sigma n i) : 0 < F.shift i ∨ F.size i ≤ n := by
  by_cases hc : F.shift i = 0
  · exact Or.inr (le_of_not_gt fun h => hi
      (F.aeConstant_of_unshifted_above_rank Sigma n hSigma.posSemidef i hc h))
  · exact Or.inl (lt_of_le_of_ne (F.shift_nonneg i) (Ne.symm hc))

@[simp] theorem moment_singleton (n : ℕ) (i : ι) :
    F.moment Sigma n {i} =
      ∫⁻ X, ENNReal.ofReal (F.factor Sigma i X) ∂wishartGramMeasure n Sigma := by
  simp only [moment, subproduct, Finset.prod_singleton]

@[simp] theorem moment_empty (n : ℕ) : F.moment Sigma n ∅ = 1 := by
  simp only [moment, subproduct, Finset.prod_empty, ENNReal.ofReal_one,
    lintegral_const, measure_univ, mul_one]

theorem moment_split (n : ℕ) (J : Finset ι) (i : ι) (hi : i ∈ J) :
    F.moment Sigma n J =
      ∫⁻ X, ENNReal.ofReal (F.factor Sigma i X * F.subproduct Sigma (J.erase i) X)
        ∂wishartGramMeasure n Sigma := by
  apply lintegral_congr_ae
  filter_upwards with X
  congr 1
  exact (Finset.mul_prod_erase J (fun i => F.factor Sigma i X) hi).symm

theorem moment_constant_split (n : ℕ) (hSigma : Sigma.PosSemidef)
    (J : Finset ι) (i : ι) (hi : i ∈ J) (hconst : F.AEConstantFactor Sigma n i) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) = F.moment Sigma n J := by
  obtain ⟨c, hcae⟩ := hconst
  have hc0 : 0 ≤ c := by
    obtain ⟨X, hX, heq⟩ := ((ae_posSemidef_wishartGramMeasure n Sigma).and hcae).exists
    rw [← heq]
    exact F.factor_nonneg Sigma hSigma i hX
  have hsingle : F.moment Sigma n {i} = ENNReal.ofReal c := by
    rw [F.moment_singleton]
    calc
      (∫⁻ X, ENNReal.ofReal (F.factor Sigma i X) ∂wishartGramMeasure n Sigma) =
          ∫⁻ _X, ENNReal.ofReal c ∂wishartGramMeasure n Sigma :=
        lintegral_congr_ae (hcae.mono fun X hX => congrArg ENNReal.ofReal hX)
      _ = _ := by simp only [lintegral_const, measure_univ, mul_one]
  rw [hsingle, F.moment_split Sigma n J i hi]
  calc
    ENNReal.ofReal c * F.moment Sigma n (J.erase i) =
        ∫⁻ X, ENNReal.ofReal c * ENNReal.ofReal (F.subproduct Sigma (J.erase i) X)
          ∂wishartGramMeasure n Sigma :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hcae] with X hX
      rw [hX, ENNReal.ofReal_mul hc0]

/-- The manuscript's identically-zero convention follows from the actual
almost-sure zero factor, including when another marginal expectation is infinite. -/
theorem moment_eq_zero_of_factor_ae_zero (n : ℕ) (J : Finset ι) (i : ι) (hi : i ∈ J)
    (hzero : ∀ᵐ X ∂wishartGramMeasure n Sigma, F.factor Sigma i X = 0) :
    F.moment Sigma n J = 0 := by
  rw [F.moment_split Sigma n J i hi]
  calc
    (∫⁻ X, ENNReal.ofReal (F.factor Sigma i X * F.subproduct Sigma (J.erase i) X)
        ∂wishartGramMeasure n Sigma) = ∫⁻ _X, (0 : ℝ≥0∞) ∂wishartGramMeasure n Sigma := by
      apply lintegral_congr_ae
      filter_upwards [hzero] with X hX
      simp only [hX, zero_mul, ENNReal.ofReal_zero]
    _ = 0 := lintegral_zero

end GramGeometricCompressionFamily
end Wishart
end
end CanonicalSource104

section CanonicalSource105
/- Source: Wishart/SingularGaussianMatrix.lean -/



/-!
# Rectangular Gaussian matrices and orthogonal Gram fibres

The source measure is the product of the actual independent standard normal
entries. Both rectangular Gram maps are identified with Gaussian Gram laws.
The orbit witnesses below are only pointwise; no measurable QR factor is
chosen. This is sufficient after integrating independent invariant noise.
-/

open Matrix MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped Classical Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

def gaussianMatrixMeasure (n p : ℕ) : Measure (Matrix (Fin n) (Fin p) ℝ) :=
  Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1

instance gaussianMatrixMeasure_isProbability (n p : ℕ) :
    IsProbabilityMeasure (gaussianMatrixMeasure n p) := by
  exact (inferInstance : IsProbabilityMeasure
    (Measure.pi (fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1)))

def gaussianMatrixCoordinates (n p : ℕ) :
    (Fin n × Fin p → ℝ) ≃ᵐ Matrix (Fin n) (Fin p) ℝ where
  toFun g := Matrix.of (fun i j => g (i, j))
  invFun A ij := A ij.1 ij.2
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable (fun g : Fin n × Fin p → ℝ => Matrix.of (fun i j => g (i, j)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun A : Matrix (Fin n) (Fin p) ℝ => fun ij : Fin n × Fin p => A ij.1 ij.2)
    fun_prop

theorem measurePreserving_gaussianMatrixCoordinates (n p : ℕ) :
    MeasurePreserving (gaussianMatrixCoordinates n p)
      (Measure.pi fun _ : Fin n × Fin p => gaussianReal 0 1)
      (gaussianMatrixMeasure n p) := by
  let e : (Fin n × Fin p) ≃ ((i : Fin n) × Fin p) :=
    (Equiv.sigmaEquivProd (Fin n) (Fin p)).symm
  have he := measurePreserving_piCongrLeft
    (fun _ : (i : Fin n) × Fin p => gaussianReal 0 1) e
  have hc := TauCeti.measurePreserving_piCurry
    (fun (_ : Fin n) (_ : Fin p) => gaussianReal 0 1)
  exact hc.comp he

theorem measurePreserving_gaussianMatrix_transpose (n p : ℕ) :
    MeasurePreserving (Matrix.transpose : Matrix (Fin n) (Fin p) ℝ → _)
      (gaussianMatrixMeasure n p) (gaussianMatrixMeasure p n) := by
  have h := (measurePreserving_rectangularGaussian_columns (q := p) (m := n)).comp
    (measurePreserving_gaussianMatrixCoordinates n p).symm
  change MeasurePreserving (Matrix.transpose : Matrix (Fin n) (Fin p) ℝ → _)
    (gaussianMatrixMeasure n p) (gaussianMatrixMeasure p n) at h
  exact h

theorem measurePreserving_gaussianMatrix_mul_right {n p : ℕ}
    (U : Matrix (Fin p) (Fin p) ℝ) (hU : U * Uᵀ = 1) :
    MeasurePreserving (fun A : Matrix (Fin n) (Fin p) ℝ => A * U)
      (gaussianMatrixMeasure n p) (gaussianMatrixMeasure n p) := by
  have hUt : Uᵀ * (Uᵀ)ᵀ = 1 := by
    simpa only [Matrix.transpose_transpose] using mul_eq_one_comm.mp hU
  have hrow : MeasurePreserving Uᵀ.mulVec
      (Measure.pi fun _ : Fin p => gaussianReal 0 1)
      (Measure.pi fun _ : Fin p => gaussianReal 0 1) :=
    ⟨by fun_prop, map_piGaussian_mulVec Uᵀ hUt⟩
  have h := measurePreserving_pi
    (fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1)
    (fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1)
    (fun _ => hrow)
  change MeasurePreserving
    (fun A : Matrix (Fin n) (Fin p) ℝ => Matrix.of (fun i => Uᵀ *ᵥ A i))
    (gaussianMatrixMeasure n p) (gaussianMatrixMeasure n p) at h
  have heq : (fun A : Matrix (Fin n) (Fin p) ℝ => Matrix.of (fun i => Uᵀ *ᵥ A i)) =
      fun A => A * U := by
    funext A
    ext i j
    simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  rw [heq] at h
  exact h

theorem measurePreserving_gaussianMatrix_mul_left {n p : ℕ}
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U * Uᵀ = 1) :
    MeasurePreserving (fun A : Matrix (Fin n) (Fin p) ℝ => U * A)
      (gaussianMatrixMeasure n p) (gaussianMatrixMeasure n p) := by
  have hUt : Uᵀ * (Uᵀ)ᵀ = 1 := by
    simpa only [Matrix.transpose_transpose] using mul_eq_one_comm.mp hU
  have h := (measurePreserving_gaussianMatrix_transpose p n).comp
    ((measurePreserving_gaussianMatrix_mul_right (n := p) Uᵀ hUt).comp
      (measurePreserving_gaussianMatrix_transpose n p))
  simpa only [Function.comp_def, Matrix.transpose_mul,
    Matrix.transpose_transpose] using h

def matrixGram {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ) : Spectral.Sym p :=
  ⟨Aᵀ * A, by
    change Matrix.IsHermitian (Aᵀ * A)
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.isHermitian_conjTranspose_mul_self A)⟩

@[simp] theorem coe_matrixGram {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ) :
    (matrixGram A : Matrix (Fin p) (Fin p) ℝ) = Aᵀ * A := rfl

@[fun_prop] theorem continuous_matrixGram (n p : ℕ) :
    Continuous (@matrixGram n p) := by
  exact (continuous_id.matrix_transpose.matrix_mul continuous_id).subtype_mk _

@[fun_prop] theorem measurable_matrixGram (n p : ℕ) :
    Measurable (@matrixGram n p) := (continuous_matrixGram n p).measurable

theorem matrixGram_eq_wishartGram {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ) :
    matrixGram A = wishartGram (fun i => WithLp.toLp 2 (A i)) := by
  apply Subtype.ext
  ext i j
  simp only [coe_matrixGram, Matrix.mul_apply, Matrix.transpose_apply,
    coe_wishartGram, Matrix.sum_apply, Matrix.vecMulVec_apply, WithLp.ofLp_toLp]

theorem map_matrixGram_gaussianMatrixMeasure (n p : ℕ) :
    (gaussianMatrixMeasure n p).map matrixGram =
      wishartGramMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
  have hstd : MeasurePreserving (WithLp.toLp 2 : (Fin p → ℝ) → EuclideanSpace ℝ (Fin p))
      (Measure.pi fun _ : Fin p => gaussianReal 0 1)
      (multivariateGaussian 0 (1 : Matrix (Fin p) (Fin p) ℝ)) := by
    refine ⟨by fun_prop, ?_⟩
    simpa only [PiLp.zero_apply] using
      (multivariateGaussian_one_eq_map_pi (0 : EuclideanSpace ℝ (Fin p))).symm
  have hrows := measurePreserving_pi
    (fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1)
    (fun _ : Fin n => multivariateGaussian 0 (1 : Matrix (Fin p) (Fin p) ℝ))
    (fun _ => hstd)
  rw [wishartGramMeasure_eq_map_pi, ← hrows.map_eq,
    Measure.map_map measurable_wishartGram (by fun_prop)]
  apply congrArg (fun f => (gaussianMatrixMeasure n p).map f)
  funext A
  exact matrixGram_eq_wishartGram A

/-- The dual Gram matrix exchanges the sample size and the column count. -/
theorem map_dualMatrixGram_gaussianMatrixMeasure (n p : ℕ) :
    (gaussianMatrixMeasure n p).map (fun A => matrixGram Aᵀ) =
      wishartGramMeasure p (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have h := map_matrixGram_gaussianMatrixMeasure p n
  rw [← (measurePreserving_gaussianMatrix_transpose n p).map_eq,
    Measure.map_map (measurable_matrixGram p n) (by fun_prop)] at h
  exact h

def initialRows {r p : ℕ} (h : r ≤ p) : Matrix (Fin r) (Fin p) ℝ :=
  (1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE h) id

theorem initialRows_mul_transpose {r p : ℕ} (h : r ≤ p) :
    initialRows h * (initialRows h)ᵀ = 1 := by
  have ht := Matrix.submatrix_one_mul_mul_submatrix_one (Fin.castLE h)
    (1 : Matrix (Fin p) (Fin p) ℝ)
  simpa only [initialRows, Matrix.transpose_submatrix, Matrix.transpose_one,
    Matrix.mul_one, Matrix.submatrix_one _ (Fin.castLE_injective h)] using ht

theorem initialRows_mul {r p k : ℕ} (h : r ≤ p)
    (A : Matrix (Fin p) (Fin k) ℝ) :
    initialRows h * A = A.submatrix (Fin.castLE h) id := by
  have hrefl : (⇑(Equiv.refl (Fin p)).symm : Fin p → Fin p) = id := rfl
  simpa only [initialRows, Equiv.coe_refl, hrefl, Function.id_comp] using
    Matrix.one_submatrix_mul (Fin.castLE h) (Equiv.refl (Fin p)) A

/-- A full-row-rank data matrix is in the right orthogonal orbit of its
positive square-root factor, padded with zero columns. -/
theorem exists_orthogonal_wideFactor {n p : ℕ} (h : n ≤ p)
    (A : Matrix (Fin n) (Fin p) ℝ) (hA : (A * Aᵀ).PosDef) :
    ∃ U : Matrix (Fin p) (Fin p) ℝ, U * Uᵀ = 1 ∧
      A = CFC.sqrt (A * Aᵀ) * initialRows h * U := by
  have hsqrt : (CFC.sqrt (A * Aᵀ)).det ≠ 0 :=
    fun hz => by
      have hd := congrArg Matrix.det
        (CFC.sqrt_mul_sqrt_self (A * Aᵀ) hA.posSemidef.nonneg)
      rw [Matrix.det_mul, hz, zero_mul] at hd
      exact hA.det_pos.ne' hd.symm
  have hsq : CFC.sqrt (A * Aᵀ) * (CFC.sqrt (A * Aᵀ))ᵀ = A * Aᵀ := by
    rw [matrix_sqrt_transpose, CFC.sqrt_mul_sqrt_self _ hA.posSemidef.nonneg]
  obtain ⟨U, hU, hAU⟩ :=
    Matrix.exists_mul_transpose_eq_one_and_eq_mul_submatrix_castLE A h hsqrt hsq
  exact ⟨U, hU, by simpa only [Matrix.mul_assoc, initialRows_mul] using hAU⟩

/-- The tall case is the transpose of the preceding full-row factorization. -/
theorem exists_orthogonal_tallFactor {n p : ℕ} (h : p ≤ n)
    (A : Matrix (Fin n) (Fin p) ℝ) (hA : (Aᵀ * A).PosDef) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, U * Uᵀ = 1 ∧
      A = U * (initialRows h)ᵀ * CFC.sqrt (Aᵀ * A) := by
  obtain ⟨U, hU, hAU⟩ := exists_orthogonal_wideFactor h Aᵀ
    (by simpa only [Matrix.transpose_transpose] using hA)
  refine ⟨Uᵀ, by simpa only [Matrix.transpose_transpose] using mul_eq_one_comm.mp hU, ?_⟩
  have ht := congrArg Matrix.transpose hAU
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
    matrix_sqrt_transpose, Matrix.mul_assoc] using ht

/-- Equal full-column-rank Gram matrices have data factors related by a row
rotation. The witnesses are pointwise and are never asserted measurable. -/
theorem exists_orthogonal_mul_of_tallGram_eq {n p : ℕ} (h : p ≤ n)
    (A B : Matrix (Fin n) (Fin p) ℝ) (hA : (Aᵀ * A).PosDef)
    (hgram : Aᵀ * A = Bᵀ * B) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, U * Uᵀ = 1 ∧ U * B = A := by
  obtain ⟨U, hU, hAU⟩ := exists_orthogonal_tallFactor h A hA
  obtain ⟨V, hV, hBV⟩ := exists_orthogonal_tallFactor h B (hgram ▸ hA)
  refine ⟨U * Vᵀ, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V,
      mul_eq_one_comm.mp hV, Matrix.one_mul, hU]
  · rw [hBV, ← hgram]
    simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V,
      mul_eq_one_comm.mp hV, Matrix.one_mul] using hAU.symm

/-- On a full-row-rank fibre the orthogonal comparison has an explicit
algebraic witness, so no matrix decomposition is required. -/
theorem exists_orthogonal_mul_of_wideGram_eq {n p : ℕ}
    (A B : Matrix (Fin n) (Fin p) ℝ) (hA : (A * Aᵀ).PosDef)
    (hgram : Aᵀ * A = Bᵀ * B) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, U * Uᵀ = 1 ∧ U * B = A := by
  let R := A * Aᵀ
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hRtr : Rᵀ = R := by simp only [R, Matrix.transpose_mul, Matrix.transpose_transpose]
  refine ⟨R⁻¹ * A * Bᵀ, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv, hRtr]
    calc
      R⁻¹ * A * Bᵀ * (B * (Aᵀ * R⁻¹)) =
          R⁻¹ * A * (Bᵀ * B) * Aᵀ * R⁻¹ := by simp only [Matrix.mul_assoc]
      _ = R⁻¹ * R * R * R⁻¹ := by rw [← hgram]; simp only [R, Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.nonsing_inv_mul _ hRu, Matrix.one_mul,
        Matrix.mul_nonsing_inv _ hRu]
  · calc
      R⁻¹ * A * Bᵀ * B = R⁻¹ * A * (Bᵀ * B) := by simp only [Matrix.mul_assoc]
      _ = R⁻¹ * R * A := by rw [← hgram]; simp only [R, Matrix.mul_assoc]
      _ = A := by rw [Matrix.nonsing_inv_mul _ hRu, Matrix.one_mul]

end Wishart
end
end CanonicalSource105

section CanonicalSource106
/- Source: Wishart/OrbitDisintegration.lean -/



/-!
# Orbit integration without measurable orbit witnesses

An almost-everywhere orbit representative suffices to reconstruct an invariant
law. The second theorem transports a product law after proving equality of its
individual noise fibres. These identities are used for singular Gaussian Gram
laws, where a measurable orthogonal completion would be unnecessary machinery.
-/

open MeasureTheory Function
open scoped ENNReal

namespace Wishart

theorem map_prod_orbit_representative_ae
    {G X Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (μ : Measure X) [SFinite μ]
    (act : G → X → X) (selector : X → Y) (repr : Y → X)
    (hact : Measurable (uncurry act))
    (hselector : Measurable selector) (hrepr : Measurable repr)
    (hmul : ∀ g h x, act (g * h) x = act g (act h x))
    (hinv : ∀ g, μ.map (act g) = μ)
    (horbit : ∀ᵐ x ∂μ, ∃ g, act g (repr (selector x)) = x) :
    (ν.prod (μ.map selector)).map (fun p => act p.1 (repr p.2)) = μ := by
  have hbuild : Measurable (fun p : G × Y => act p.1 (repr p.2)) :=
    hact.comp (measurable_fst.prodMk (hrepr.comp measurable_snd))
  apply Measure.ext_of_lintegral
  intro f hf
  have hfg : Measurable (fun p : G × X => f (act p.1 p.2)) := hf.comp hact
  have hfr : Measurable (fun p : G × Y => f (act p.1 (repr p.2))) :=
    hf.comp hbuild
  have havg : (fun x => ∫⁻ g, f (act g (repr (selector x))) ∂ν) =ᵐ[μ]
      (fun x => ∫⁻ g, f (act g x) ∂ν) := by
    filter_upwards [horbit] with x hx
    obtain ⟨h, hx⟩ := hx
    have hm : Measurable (fun g => f (act g (repr (selector x)))) :=
      hf.comp (hact.comp (measurable_id.prodMk measurable_const))
    calc
      (∫⁻ g, f (act g (repr (selector x))) ∂ν) =
          ∫⁻ g, f (act (g * h) (repr (selector x))) ∂ν :=
        ((measurePreserving_mul_right ν h).lintegral_comp hm).symm
      _ = ∫⁻ g, f (act g x) ∂ν := by simp only [hmul, hx]
  calc
    (∫⁻ x, f x ∂(ν.prod (μ.map selector)).map (fun p => act p.1 (repr p.2))) =
        ∫⁻ y, ∫⁻ g, f (act g (repr y)) ∂ν ∂μ.map selector := by
      rw [lintegral_map hf hbuild, lintegral_prod_symm _ hfr.aemeasurable]
    _ = ∫⁻ x, ∫⁻ g, f (act g (repr (selector x))) ∂ν ∂μ :=
      lintegral_map hfr.lintegral_prod_left hselector
    _ = ∫⁻ x, ∫⁻ g, f (act g x) ∂ν ∂μ := lintegral_congr_ae havg
    _ = ∫⁻ g, ∫⁻ x, f (act g x) ∂μ ∂ν :=
      (lintegral_lintegral_swap hfg.aemeasurable).symm
    _ = ∫⁻ g, ∫⁻ x, f x ∂μ ∂ν := by
      apply lintegral_congr
      intro g
      have hg : Measurable (act g) :=
        hact.comp (measurable_const.prodMk measurable_id)
      calc
        (∫⁻ x, f (act g x) ∂μ) = ∫⁻ x, f x ∂μ.map (act g) :=
          (lintegral_map hf hg).symm
        _ = ∫⁻ x, f x ∂μ := by rw [hinv g]
    _ = ∫⁻ x, f x ∂μ := by simp

/-- Pointwise equality of integrated noise fibres yields an equality of the
entire pushforward law. No conditional distribution is postulated. -/
theorem map_prod_eq_of_map_fibres
    {A B Z X : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure A) [SFinite μ] (ν : Measure Z) [SFinite ν]
    (T : A → B) (hT : Measurable T)
    (f : A × Z → X) (hf : Measurable f)
    (g : B × Z → X) (hg : Measurable g)
    (hfg : ∀ᵐ a ∂μ, ν.map (fun z => f (a, z)) =
      ν.map (fun z => g (T a, z))) :
    (μ.prod ν).map f = ((μ.map T).prod ν).map g := by
  apply Measure.ext_of_lintegral
  intro k hk
  rw [lintegral_map hk hf, lintegral_map hk hg]
  have hfk : Measurable (fun z : A × Z => k (f z)) := hk.comp hf
  have hgk : Measurable (fun z : B × Z => k (g z)) := hk.comp hg
  rw [lintegral_prod _ hfk.aemeasurable, lintegral_prod _ hgk.aemeasurable,
    lintegral_map hgk.lintegral_prod_right hT]
  apply lintegral_congr_ae
  filter_upwards [hfg] with a ha
  have hfa : Measurable (fun z => f (a, z)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  have hga : Measurable (fun z => g (T a, z)) :=
    hg.comp (measurable_const.prodMk measurable_id)
  rw [← lintegral_map hk hfa, ha, lintegral_map hk hga]

/-- The orbit label may be computed on a larger source space. In particular,
the positive eigenvalues of a singular Gram matrix can be read from its dual
Gram matrix without first constructing a spectral selector on the singular
matrix space. -/
theorem map_prod_orbit_image_ae
    {G A X Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (μ : Measure A) [SFinite μ]
    (F : A → X) (hF : Measurable F)
    (act : G → X → X) (selector : A → Y) (repr : Y → X)
    (hact : Measurable (uncurry act))
    (hselector : Measurable selector) (hrepr : Measurable repr)
    (hmul : ∀ g h x, act (g * h) x = act g (act h x))
    (hinv : ∀ g, (μ.map F).map (act g) = μ.map F)
    (horbit : ∀ᵐ a ∂μ, ∃ g, act g (repr (selector a)) = F a) :
    (ν.prod (μ.map selector)).map (fun p => act p.1 (repr p.2)) = μ.map F := by
  have hbuild : Measurable (fun p : G × Y => act p.1 (repr p.2)) :=
    hact.comp (measurable_fst.prodMk (hrepr.comp measurable_snd))
  apply Measure.ext_of_lintegral
  intro f hf
  have hfg : Measurable (fun p : G × A => f (act p.1 (F p.2))) :=
    hf.comp (hact.comp (measurable_fst.prodMk (hF.comp measurable_snd)))
  have hfr : Measurable (fun p : G × Y => f (act p.1 (repr p.2))) := hf.comp hbuild
  have havg : (fun a => ∫⁻ g, f (act g (repr (selector a))) ∂ν) =ᵐ[μ]
      (fun a => ∫⁻ g, f (act g (F a)) ∂ν) := by
    filter_upwards [horbit] with a ha
    obtain ⟨h, ha⟩ := ha
    have hm : Measurable (fun g => f (act g (repr (selector a)))) :=
      hf.comp (hact.comp (measurable_id.prodMk measurable_const))
    calc
      (∫⁻ g, f (act g (repr (selector a))) ∂ν) =
          ∫⁻ g, f (act (g * h) (repr (selector a))) ∂ν :=
        ((measurePreserving_mul_right ν h).lintegral_comp hm).symm
      _ = ∫⁻ g, f (act g (F a)) ∂ν := by simp only [hmul, ha]
  calc
    (∫⁻ x, f x ∂(ν.prod (μ.map selector)).map (fun p => act p.1 (repr p.2))) =
        ∫⁻ y, ∫⁻ g, f (act g (repr y)) ∂ν ∂μ.map selector := by
      rw [lintegral_map hf hbuild, lintegral_prod_symm _ hfr.aemeasurable]
    _ = ∫⁻ a, ∫⁻ g, f (act g (repr (selector a))) ∂ν ∂μ :=
      lintegral_map hfr.lintegral_prod_left hselector
    _ = ∫⁻ a, ∫⁻ g, f (act g (F a)) ∂ν ∂μ := lintegral_congr_ae havg
    _ = ∫⁻ g, ∫⁻ a, f (act g (F a)) ∂μ ∂ν :=
      (lintegral_lintegral_swap hfg.aemeasurable).symm
    _ = ∫⁻ g, ∫⁻ x, f x ∂μ.map F ∂ν := by
      apply lintegral_congr
      intro g
      have hg : Measurable (act g) :=
        hact.comp (measurable_const.prodMk measurable_id)
      calc
        (∫⁻ a, f (act g (F a)) ∂μ) = ∫⁻ x, f (act g x) ∂μ.map F :=
          (lintegral_map (hf.comp hg) hF).symm
        _ = ∫⁻ x, f x ∂(μ.map F).map (act g) :=
          (lintegral_map hf hg).symm
        _ = ∫⁻ x, f x ∂μ.map F := by rw [hinv g]
    _ = ∫⁻ x, f x ∂μ.map F := by simp

end Wishart
end CanonicalSource106

section CanonicalSource107
/- Source: Wishart/SingularGramSpectral.lean -/



/-!
# The complete positive-spectrum law of an integer Gaussian Gram matrix

For `n < p`, the dual Gram matrix has the nonsingular `W_n(p,I)` law.
Pointwise rectangular factorization and Haar averaging transfer its ascending
eigenvalues to the original `p × p` Gram matrix. Consequently the exact law is
an independent Haar frame around the positive Laguerre spectrum of dimension
`min n p`, with the remaining eigenvalues zero. This includes the singular
range and does not assume the spectral law as an input.
-/

open Matrix MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped Classical ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart.Spectral

def paddedSym {r p : ℕ} (h : r ≤ p) (S : Sym r) : Sym p :=
  Matrix.symmetricCongruenceLinearMap (initialRows h)ᵀ S

@[simp] theorem coe_paddedSym {r p : ℕ} (h : r ≤ p) (S : Sym r) :
    (paddedSym h S : Matrix (Fin p) (Fin p) ℝ) =
      (initialRows h)ᵀ * (S : Matrix (Fin r) (Fin r) ℝ) * initialRows h := by
  simp only [paddedSym, Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.transpose_transpose]

@[fun_prop] theorem continuous_paddedSym {r p : ℕ} (h : r ≤ p) :
    Continuous (paddedSym h) :=
  LinearMap.continuous_of_finiteDimensional _

@[simp] theorem initialRows_refl (p : ℕ) : initialRows (le_refl p) = 1 := by
  ext i j
  simp only [initialRows, Matrix.submatrix_apply, Fin.castLE_refl, id_eq]
  rfl

@[simp] theorem paddedSym_refl {p : ℕ} (S : Sym p) :
    paddedSym (le_refl p) S = S := by
  apply Subtype.ext
  simp only [coe_paddedSym, initialRows_refl, Matrix.transpose_one,
    Matrix.one_mul, Matrix.mul_one]

theorem map_conjugate_identity_gram {p : ℕ} (n : ℕ) (O : Orth p) :
    (wishartGramMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)).map (conjugate O) =
      wishartGramMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
  simpa only [conjugate, Matrix.mul_one, orth_mul_transpose O] using
    map_symmetricCongruenceLinearMap_wishartGramMeasure n
      (O : Matrix (Fin p) (Fin p) ℝ) Matrix.PosSemidef.one

/-- The positive spectrum read from the dual Gram matrix has an orthogonal
representative in the original ambient dimension. -/
theorem exists_conjugate_paddedSpectrum_gram {n p : ℕ} (h : n ≤ p)
    (A : Matrix (Fin n) (Fin p) ℝ) (hA : (A * Aᵀ).PosDef) :
    ∃ O : Orth p,
      conjugate O (paddedSym h (diagonalSym (ascendingSpectrum (matrixGram Aᵀ)))) =
        matrixGram A := by
  let R := A * Aᵀ
  obtain ⟨P, hP⟩ := exists_conjugate_diagonal_ascendingSpectrum (matrixGram Aᵀ)
  let D := Matrix.diagonal (ascendingSpectrum (matrixGram Aᵀ))
  have hPmat : (P : Matrix (Fin n) (Fin n) ℝ) * D *
      (P : Matrix (Fin n) (Fin n) ℝ)ᵀ = R := by
    simpa only [conjugate, Matrix.coe_symmetricCongruenceLinearMap_apply,
      diagonalSym, coe_matrixGram, Matrix.transpose_transpose, D, R] using
      congrArg Subtype.val hP
  let T := CFC.sqrt R * (P : Matrix (Fin n) (Fin n) ℝ)
  have hsq : CFC.sqrt R * CFC.sqrt R = R :=
    CFC.sqrt_mul_sqrt_self R hA.posSemidef.nonneg
  have hTT : T * Tᵀ = R := by
    change (CFC.sqrt R * (P : Matrix (Fin n) (Fin n) ℝ)) *
      (CFC.sqrt R * (P : Matrix (Fin n) (Fin n) ℝ))ᵀ = R
    rw [Matrix.transpose_mul, matrix_sqrt_transpose]
    calc
      CFC.sqrt R * (P : Matrix (Fin n) (Fin n) ℝ) *
          ((P : Matrix (Fin n) (Fin n) ℝ)ᵀ * CFC.sqrt R) =
        CFC.sqrt R * ((P : Matrix (Fin n) (Fin n) ℝ) *
          (P : Matrix (Fin n) (Fin n) ℝ)ᵀ) * CFC.sqrt R := by
            simp only [Matrix.mul_assoc]
      _ = R := by rw [orth_mul_transpose, Matrix.mul_one, hsq]
  have hTtT : Tᵀ * T = D := by
    change (CFC.sqrt R * (P : Matrix (Fin n) (Fin n) ℝ))ᵀ *
      (CFC.sqrt R * (P : Matrix (Fin n) (Fin n) ℝ)) = D
    rw [Matrix.transpose_mul, matrix_sqrt_transpose]
    calc
      (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * CFC.sqrt R *
          (CFC.sqrt R * (P : Matrix (Fin n) (Fin n) ℝ)) =
        (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * R *
          (P : Matrix (Fin n) (Fin n) ℝ) := by
            calc
              _ = (P : Matrix (Fin n) (Fin n) ℝ)ᵀ *
                  (CFC.sqrt R * CFC.sqrt R) * P := by simp only [Matrix.mul_assoc]
              _ = _ := by rw [hsq]
      _ = D := by
        calc
          (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * R *
              (P : Matrix (Fin n) (Fin n) ℝ) =
              ((P : Matrix (Fin n) (Fin n) ℝ)ᵀ * P) * D *
                ((P : Matrix (Fin n) (Fin n) ℝ)ᵀ * P) := by
                  rw [← hPmat]; simp only [Matrix.mul_assoc]
          _ = D := by rw [orth_transpose_mul, Matrix.one_mul, Matrix.mul_one]
  have hTdet : T.det ≠ 0 := by
    intro hz
    have hd := congrArg Matrix.det hTT
    rw [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul] at hd
    exact hA.det_pos.ne' hd.symm
  obtain ⟨Q, hQ, hAQ⟩ :=
    Matrix.exists_mul_transpose_eq_one_and_eq_mul_submatrix_castLE A h hTdet hTT
  have hAQ' : A = T * initialRows h * Q := by
    simpa only [Matrix.mul_assoc, initialRows_mul] using hAQ
  let O : Orth p := ⟨Qᵀ, (Matrix.mem_orthogonalGroup_iff' (Fin p) ℝ).mpr (by
    simpa only [Matrix.transpose_transpose] using hQ)⟩
  refine ⟨O, Subtype.ext ?_⟩
  simp only [conjugate, Matrix.coe_symmetricCongruenceLinearMap_apply,
    coe_paddedSym, diagonalSym, coe_matrixGram]
  change Qᵀ * ((initialRows h)ᵀ * D * initialRows h) * (Qᵀ)ᵀ = Aᵀ * A
  rw [Matrix.transpose_transpose, hAQ', Matrix.transpose_mul, Matrix.transpose_mul]
  calc
    Qᵀ * ((initialRows h)ᵀ * D * initialRows h) * Q =
        Qᵀ * (initialRows h)ᵀ * (Tᵀ * T) * initialRows h * Q := by
          rw [hTtT]; simp only [Matrix.mul_assoc]
    _ = Qᵀ * ((initialRows h)ᵀ * Tᵀ) * (T * initialRows h * Q) := by
      simp only [Matrix.mul_assoc]

theorem ae_dualGram_posDef {n p : ℕ} (h : n ≤ p) :
    ∀ᵐ A ∂gaussianMatrixMeasure n p, (A * Aᵀ).PosDef := by
  have hmap : MeasurePreserving (fun A : Matrix (Fin n) (Fin p) ℝ => matrixGram Aᵀ)
      (gaussianMatrixMeasure n p) (wishartGramMeasure p (1 : Matrix (Fin n) (Fin n) ℝ)) :=
    ⟨(measurable_matrixGram p n).comp (by fun_prop), map_dualMatrixGram_gaussianMatrixMeasure n p⟩
  have hae := hmap.quasiMeasurePreserving.ae
    (ae_posDef_wishartGramMeasure Matrix.PosDef.one h)
  simpa only [coe_matrixGram, Matrix.transpose_transpose] using hae

/-- Exact singular-range Haar--Laguerre law, with all zero eigenvalues retained
by the actual padded matrix. -/
theorem gram_haar_laguerre_representation_of_le {n p : ℕ} (h : n ≤ p) :
    ((haarProb (Orth p)).prod
      (WishartVerification.normalizedWeight volume (wishartEigenDensity n (p : ℝ)))).map
        (fun z => conjugate z.1 (paddedSym h (diagonalSym z.2))) =
      wishartGramMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
  have hp : (n : ℝ) - 1 < (p : ℝ) := by
    have hle : (n : ℝ) ≤ (p : ℝ) := by exact_mod_cast h
    linarith
  have hselector : Measurable (fun A : Matrix (Fin n) (Fin p) ℝ =>
      ascendingSpectrum (matrixGram Aᵀ)) :=
    (continuous_ascendingSpectrum n).measurable.comp
      ((measurable_matrixGram p n).comp (by fun_prop))
  have hlabel : (gaussianMatrixMeasure n p).map
      (fun A => ascendingSpectrum (matrixGram Aᵀ)) =
        WishartVerification.normalizedWeight volume (wishartEigenDensity n (p : ℝ)) := by
    change (gaussianMatrixMeasure n p).map
      (ascendingSpectrum ∘ (fun A : Matrix (Fin n) (Fin p) ℝ => matrixGram Aᵀ)) = _
    rw [← Measure.map_map (continuous_ascendingSpectrum n).measurable
      (show Measurable (fun A : Matrix (Fin n) (Fin p) ℝ => matrixGram Aᵀ) from
        (measurable_matrixGram p n).comp (by fun_prop)),
      map_dualMatrixGram_gaussianMatrixMeasure,
      wishartGramMeasure_eq_nonsingularWishartMeasure Matrix.PosDef.one h]
    exact (identityEigenLaw_normalized_density hp).2.2
  have hbuild := map_prod_orbit_image_ae (haarProb (Orth p))
    (gaussianMatrixMeasure n p) matrixGram (measurable_matrixGram n p)
    conjugate (fun A => ascendingSpectrum (matrixGram Aᵀ))
    (fun lam => paddedSym h (diagonalSym lam)) (continuous_conjugate p).measurable
    hselector ((continuous_paddedSym h).comp (continuous_diagonalSym n)).measurable
    conjugate_mul (fun O => by
      rw [map_matrixGram_gaussianMatrixMeasure]
      exact map_conjugate_identity_gram n O) (by
        filter_upwards [ae_dualGram_posDef h] with A hA
        exact exists_conjugate_paddedSpectrum_gram h A hA)
  simpa only [hlabel, map_matrixGram_gaussianMatrixMeasure] using hbuild

def positiveGramEigenLaw (n p : ℕ) : Measure (Fin (min n p) → ℝ) :=
  WishartVerification.normalizedWeight volume
    (wishartEigenDensity (min n p) (max n p : ℕ))

def positiveGramSpectralMatrix (n p : ℕ)
    (lam : Fin (min n p) → ℝ) (O : Orth p) : Sym p :=
  conjugate O (paddedSym (min_le_right n p) (diagonalSym lam))

theorem positiveGramEigenLaw_isProbability (n p : ℕ) :
    IsProbabilityMeasure (positiveGramEigenLaw n p) := by
  apply laguerreLaw_isProbability
  have hle : ((min n p : ℕ) : ℝ) ≤ (max n p : ℕ) := by
    exact_mod_cast (min_le_max : min n p ≤ max n p)
  linarith

theorem ae_positiveGramEigenLaw_mem_chamber (n p : ℕ) :
    ∀ᵐ lam ∂positiveGramEigenLaw n p, lam ∈ positiveChamber (min n p) := by
  apply ae_laguerreLaw_mem_chamber
  have hle : ((min n p : ℕ) : ℝ) ≤ (max n p : ℕ) := by
    exact_mod_cast (min_le_max : min n p ≤ max n p)
  linarith

/-- All dimensions and natural degrees, including both rectangular regimes.
The nonzero eigenvalue law is `W_min(n,p)(max(n,p),I)` and the frame is an
independent normalized Haar frame in the full ambient dimension. -/
theorem gram_haar_positive_spectrum_representation (n p : ℕ) :
    ((haarProb (Orth p)).prod (positiveGramEigenLaw n p)).map
      (fun z => positiveGramSpectralMatrix n p z.2 z.1) =
        wishartGramMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
  have aux (r : ℕ) (hrp : r ≤ p) (hr : r = min n p) :
      ((haarProb (Orth p)).prod
        (WishartVerification.normalizedWeight volume
          (wishartEigenDensity r (max n p : ℕ)))).map
        (fun z => conjugate z.1 (paddedSym hrp (diagonalSym z.2))) =
          wishartGramMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
    rcases le_total n p with h | h
    · have heq : r = n := hr.trans (min_eq_left h)
      clear hr
      subst r
      simpa only [max_eq_right h] using gram_haar_laguerre_representation_of_le h
    · have heq : r = p := hr.trans (min_eq_right h)
      clear hr
      subst r
      have hn : (p : ℝ) - 1 < (n : ℝ) := by
        have hle : (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
        linarith
      rw [wishartGramMeasure_eq_nonsingularWishartMeasure Matrix.PosDef.one h]
      simpa only [max_eq_left h, paddedSym_refl] using
        wishart_haar_laguerre_representation hn
  exact aux (min n p) (min_le_right n p) rfl

theorem gram_positive_spectrum_haar_representation (n p : ℕ) :
    ((positiveGramEigenLaw n p).prod (haarProb (Orth p))).map
      (fun z => positiveGramSpectralMatrix n p z.1 z.2) =
        wishartGramMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
  letI := positiveGramEigenLaw_isProbability n p
  have hm : Measurable (fun z : Orth p × (Fin (min n p) → ℝ) =>
      positiveGramSpectralMatrix n p z.2 z.1) := by
    unfold positiveGramSpectralMatrix
    exact (continuous_conjugate p).measurable.comp
      (measurable_fst.prodMk (((continuous_paddedSym _).comp
        (continuous_diagonalSym _)).measurable.comp measurable_snd))
  have h := gram_haar_positive_spectrum_representation n p
  rw [← Measure.prod_swap (μ := positiveGramEigenLaw n p) (ν := haarProb (Orth p)),
    Measure.map_map hm measurable_swap] at h
  exact h

end Wishart.Spectral
end
end CanonicalSource107

section CanonicalSource108
/- Source: Wishart/SingularGaussianSVD.lean -/



/-!
# Independent Haar factors for the actual rectangular Gaussian matrix law

The singular values are the square roots of the ascending Laguerre spectrum
of dimension `min n p` and shape `max n p`. Independent left and right Haar
frames reconstruct the full Gaussian data matrix. The proof uses only
pointwise singular-value factorizations, followed by invariant integration.
-/

open Matrix MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open Wishart.Spectral
open scoped Classical ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

def rectangularOrthogonalAction {n p : ℕ} (g : Orth n × Orth p)
    (A : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin n) (Fin p) ℝ :=
  (g.1 : Matrix (Fin n) (Fin n) ℝ) * A * (g.2 : Matrix (Fin p) (Fin p) ℝ)ᵀ

@[fun_prop] theorem measurable_rectangularOrthogonalAction (n p : ℕ) :
    Measurable (Function.uncurry (@rectangularOrthogonalAction n p)) := by
  unfold rectangularOrthogonalAction
  fun_prop

theorem rectangularOrthogonalAction_mul {n p : ℕ} (g h : Orth n × Orth p)
    (A : Matrix (Fin n) (Fin p) ℝ) :
    rectangularOrthogonalAction (g * h) A =
      rectangularOrthogonalAction g (rectangularOrthogonalAction h A) := by
  simp only [rectangularOrthogonalAction, Prod.fst_mul, Prod.snd_mul,
    Submonoid.coe_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem map_rectangularOrthogonalAction_gaussianMatrixMeasure {n p : ℕ}
    (g : Orth n × Orth p) :
    (gaussianMatrixMeasure n p).map (rectangularOrthogonalAction g) =
      gaussianMatrixMeasure n p := by
  have ht : (g.2 : Matrix (Fin p) (Fin p) ℝ)ᵀ *
      ((g.2 : Matrix (Fin p) (Fin p) ℝ)ᵀ)ᵀ = 1 := by
    simpa only [Matrix.transpose_transpose] using orth_transpose_mul g.2
  have hm := (measurePreserving_gaussianMatrix_mul_right
    (g.2 : Matrix (Fin p) (Fin p) ℝ)ᵀ ht).comp
      (measurePreserving_gaussianMatrix_mul_left
        (g.1 : Matrix (Fin n) (Fin n) ℝ) (orth_mul_transpose g.1))
  exact hm.map_eq

def rectangularDiagonalFactor (n p : ℕ) (lam : Fin (min n p) → ℝ) :
    Matrix (Fin n) (Fin p) ℝ :=
  (initialRows (min_le_left n p))ᵀ * Matrix.diagonal (fun i => Real.sqrt (lam i)) *
    initialRows (min_le_right n p)

@[fun_prop] theorem measurable_rectangularDiagonalFactor (n p : ℕ) :
    Measurable (rectangularDiagonalFactor n p) := by
  unfold rectangularDiagonalFactor
  fun_prop

/-- A rectangular full-row-rank matrix has a pointwise SVD with its specified
ascending dual-Gram spectrum, rather than an arbitrary enumeration. -/
theorem exists_wideSVD {n p : ℕ} (h : n ≤ p)
    (A : Matrix (Fin n) (Fin p) ℝ) (hA : (A * Aᵀ).PosDef) :
    ∃ g : Orth n × Orth p,
      rectangularOrthogonalAction g
        (Matrix.diagonal (fun i => Real.sqrt (ascendingSpectrum (matrixGram Aᵀ) i)) *
          initialRows h) = A := by
  let lam := ascendingSpectrum (matrixGram Aᵀ)
  have hlam : ∀ i, 0 ≤ lam i := by
    intro i
    exact (hA.eigenvalues_pos (ascendingIndexEquiv n i)).le
  obtain ⟨P, hP⟩ := exists_conjugate_diagonal_ascendingSpectrum (matrixGram Aᵀ)
  have hPmat : (P : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal lam *
      (P : Matrix (Fin n) (Fin n) ℝ)ᵀ = A * Aᵀ := by
    simpa only [conjugate, Matrix.coe_symmetricCongruenceLinearMap_apply,
      diagonalSym, coe_matrixGram, Matrix.transpose_transpose, lam] using
      congrArg Subtype.val hP
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => Real.sqrt (lam i))
  have hDD : D * D = Matrix.diagonal lam := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hlam i)
  let T := (P : Matrix (Fin n) (Fin n) ℝ) * D
  have hTT : T * Tᵀ = A * Aᵀ := by
    change ((P : Matrix (Fin n) (Fin n) ℝ) * D) *
      ((P : Matrix (Fin n) (Fin n) ℝ) * D)ᵀ = _
    rw [Matrix.transpose_mul, show Dᵀ = D from Matrix.diagonal_transpose _]
    calc
      (P : Matrix (Fin n) (Fin n) ℝ) * D *
          (D * (P : Matrix (Fin n) (Fin n) ℝ)ᵀ) =
        (P : Matrix (Fin n) (Fin n) ℝ) * (D * D) *
          (P : Matrix (Fin n) (Fin n) ℝ)ᵀ := by simp only [Matrix.mul_assoc]
      _ = A * Aᵀ := by rw [hDD, hPmat]
  have hTdet : T.det ≠ 0 := by
    intro hz
    have hd := congrArg Matrix.det hTT
    rw [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul] at hd
    exact hA.det_pos.ne' hd.symm
  obtain ⟨Q, hQ, hAQ⟩ :=
    Matrix.exists_mul_transpose_eq_one_and_eq_mul_submatrix_castLE A h hTdet hTT
  let V : Orth p := ⟨Qᵀ, (Matrix.mem_orthogonalGroup_iff' (Fin p) ℝ).mpr (by
    simpa only [Matrix.transpose_transpose] using hQ)⟩
  refine ⟨(P, V), ?_⟩
  change (P : Matrix (Fin n) (Fin n) ℝ) * (D * initialRows h) * (Qᵀ)ᵀ = A
  rw [Matrix.transpose_transpose]
  simpa only [T, Matrix.mul_assoc, initialRows_mul] using hAQ.symm

theorem exists_tallSVD {n p : ℕ} (h : p ≤ n)
    (A : Matrix (Fin n) (Fin p) ℝ) (hA : (Aᵀ * A).PosDef) :
    ∃ g : Orth n × Orth p,
      rectangularOrthogonalAction g
        ((initialRows h)ᵀ * Matrix.diagonal
          (fun i => Real.sqrt (ascendingSpectrum (matrixGram A) i))) = A := by
  obtain ⟨⟨P, Q⟩, hPQ⟩ := exists_wideSVD h Aᵀ
    (by simpa only [Matrix.transpose_transpose] using hA)
  refine ⟨(Q, P), ?_⟩
  have ht := congrArg Matrix.transpose hPQ
  simpa only [rectangularOrthogonalAction, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.diagonal_transpose, Matrix.mul_assoc] using ht

theorem gaussianMatrix_svd_law_of_le {n p : ℕ} (h : n ≤ p) :
    (((haarProb (Orth n)).prod (haarProb (Orth p))).prod
      (WishartVerification.normalizedWeight volume (wishartEigenDensity n (p : ℝ)))).map
        (fun z => rectangularOrthogonalAction z.1
          (Matrix.diagonal (fun i => Real.sqrt (z.2 i)) * initialRows h)) =
      gaussianMatrixMeasure n p := by
  have hp : (n : ℝ) - 1 < (p : ℝ) := by
    have hle : (n : ℝ) ≤ (p : ℝ) := by exact_mod_cast h
    linarith
  have hselector : Measurable (fun A : Matrix (Fin n) (Fin p) ℝ =>
      ascendingSpectrum (matrixGram Aᵀ)) :=
    (continuous_ascendingSpectrum n).measurable.comp
      ((measurable_matrixGram p n).comp (by fun_prop))
  have hlabel : (gaussianMatrixMeasure n p).map
      (fun A => ascendingSpectrum (matrixGram Aᵀ)) =
        WishartVerification.normalizedWeight volume (wishartEigenDensity n (p : ℝ)) := by
    change (gaussianMatrixMeasure n p).map
      (ascendingSpectrum ∘ (fun A : Matrix (Fin n) (Fin p) ℝ => matrixGram Aᵀ)) = _
    rw [← Measure.map_map (continuous_ascendingSpectrum n).measurable
      (show Measurable (fun A : Matrix (Fin n) (Fin p) ℝ => matrixGram Aᵀ) from
        (measurable_matrixGram p n).comp (by fun_prop)),
      map_dualMatrixGram_gaussianMatrixMeasure,
      wishartGramMeasure_eq_nonsingularWishartMeasure Matrix.PosDef.one h]
    exact (identityEigenLaw_normalized_density hp).2.2
  have hbuild := map_prod_orbit_representative_ae
    ((haarProb (Orth n)).prod (haarProb (Orth p))) (gaussianMatrixMeasure n p)
    rectangularOrthogonalAction (fun A => ascendingSpectrum (matrixGram Aᵀ))
    (fun lam => Matrix.diagonal (fun i => Real.sqrt (lam i)) * initialRows h)
    (measurable_rectangularOrthogonalAction n p) hselector (by fun_prop)
    rectangularOrthogonalAction_mul map_rectangularOrthogonalAction_gaussianMatrixMeasure (by
      filter_upwards [ae_dualGram_posDef h] with A hA
      exact exists_wideSVD h A hA)
  simpa only [hlabel] using hbuild

theorem gaussianMatrix_svd_law_of_ge {n p : ℕ} (h : p ≤ n) :
    (((haarProb (Orth n)).prod (haarProb (Orth p))).prod
      (WishartVerification.normalizedWeight volume (wishartEigenDensity p (n : ℝ)))).map
        (fun z => rectangularOrthogonalAction z.1
          ((initialRows h)ᵀ * Matrix.diagonal (fun i => Real.sqrt (z.2 i)))) =
      gaussianMatrixMeasure n p := by
  have hn : (p : ℝ) - 1 < (n : ℝ) := by
    have hle : (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    linarith
  have hselector : Measurable (fun A : Matrix (Fin n) (Fin p) ℝ =>
      ascendingSpectrum (matrixGram A)) :=
    (continuous_ascendingSpectrum p).measurable.comp (measurable_matrixGram n p)
  have hlabel : (gaussianMatrixMeasure n p).map
      (fun A => ascendingSpectrum (matrixGram A)) =
        WishartVerification.normalizedWeight volume (wishartEigenDensity p (n : ℝ)) := by
    change (gaussianMatrixMeasure n p).map
      (ascendingSpectrum ∘ (matrixGram : Matrix (Fin n) (Fin p) ℝ → Sym p)) = _
    rw [← Measure.map_map (continuous_ascendingSpectrum p).measurable
      (measurable_matrixGram n p), map_matrixGram_gaussianMatrixMeasure,
      wishartGramMeasure_eq_nonsingularWishartMeasure Matrix.PosDef.one h]
    exact (identityEigenLaw_normalized_density hn).2.2
  have hmap : MeasurePreserving (matrixGram : Matrix (Fin n) (Fin p) ℝ → Sym p)
      (gaussianMatrixMeasure n p) (wishartGramMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)) :=
    ⟨measurable_matrixGram n p, map_matrixGram_gaussianMatrixMeasure n p⟩
  have hae := hmap.quasiMeasurePreserving.ae
    (ae_posDef_wishartGramMeasure Matrix.PosDef.one h)
  have hbuild := map_prod_orbit_representative_ae
    ((haarProb (Orth n)).prod (haarProb (Orth p))) (gaussianMatrixMeasure n p)
    rectangularOrthogonalAction (fun A => ascendingSpectrum (matrixGram A))
    (fun lam => (initialRows h)ᵀ * Matrix.diagonal (fun i => Real.sqrt (lam i)))
    (measurable_rectangularOrthogonalAction n p) hselector (by fun_prop)
    rectangularOrthogonalAction_mul map_rectangularOrthogonalAction_gaussianMatrixMeasure (by
      filter_upwards [hae] with A hA
      exact exists_tallSVD h A hA)
  simpa only [hlabel] using hbuild

/-- Exact independent rectangular SVD for every natural shape. -/
theorem gaussianMatrix_svd_law (n p : ℕ) :
    (((haarProb (Orth n)).prod (haarProb (Orth p))).prod
      (positiveGramEigenLaw n p)).map
        (fun z => rectangularOrthogonalAction z.1 (rectangularDiagonalFactor n p z.2)) =
      gaussianMatrixMeasure n p := by
  have aux (r : ℕ) (hrn : r ≤ n) (hrp : r ≤ p) (hr : r = min n p) :
      (((haarProb (Orth n)).prod (haarProb (Orth p))).prod
        (WishartVerification.normalizedWeight volume (wishartEigenDensity r (max n p : ℕ)))).map
          (fun z => rectangularOrthogonalAction z.1
            ((initialRows hrn)ᵀ * Matrix.diagonal (fun i => Real.sqrt (z.2 i)) *
              initialRows hrp)) = gaussianMatrixMeasure n p := by
    rcases le_total n p with h | h
    · have heq : r = n := hr.trans (min_eq_left h)
      clear hr
      subst r
      simpa only [max_eq_right h, initialRows_refl, Matrix.transpose_one,
        Matrix.one_mul] using gaussianMatrix_svd_law_of_le h
    · have heq : r = p := hr.trans (min_eq_right h)
      clear hr
      subst r
      simpa only [max_eq_left h, initialRows_refl, Matrix.mul_one] using
        gaussianMatrix_svd_law_of_ge h
  exact aux (min n p) (min_le_left n p) (min_le_right n p) rfl

/-- Any measurable nonnegative row-rotation-invariant observable may be
integrated using just the independent right Haar frame and positive spectrum.
This is the form used after averaging the independent regression noise. -/
theorem lintegral_gaussianMatrix_of_rowInvariant {n p : ℕ}
    (H : Matrix (Fin n) (Fin p) ℝ → ℝ≥0∞) (hH : Measurable H)
    (hleft : ∀ U : Orth n, ∀ A : Matrix (Fin n) (Fin p) ℝ,
      H ((U : Matrix (Fin n) (Fin n) ℝ) * A) = H A) :
    (∫⁻ A, H A ∂gaussianMatrixMeasure n p) =
      ∫⁻ lam, ∫⁻ O : Orth p,
        H (rectangularDiagonalFactor n p lam * (O : Matrix (Fin p) (Fin p) ℝ)ᵀ)
          ∂haarProb (Orth p) ∂positiveGramEigenLaw n p := by
  letI := positiveGramEigenLaw_isProbability n p
  have hmodel : Measurable (fun z : (Orth n × Orth p) × (Fin (min n p) → ℝ) =>
      rectangularOrthogonalAction z.1 (rectangularDiagonalFactor n p z.2)) := by
    fun_prop
  calc
    (∫⁻ A, H A ∂gaussianMatrixMeasure n p) =
        ∫⁻ z, H (rectangularOrthogonalAction z.1 (rectangularDiagonalFactor n p z.2))
          ∂(((haarProb (Orth n)).prod (haarProb (Orth p))).prod
            (positiveGramEigenLaw n p)) := by
      rw [← gaussianMatrix_svd_law n p, lintegral_map hH hmodel]
    _ = ∫⁻ lam, ∫⁻ g : Orth n × Orth p,
        H (rectangularOrthogonalAction g (rectangularDiagonalFactor n p lam))
          ∂(haarProb (Orth n)).prod (haarProb (Orth p)) ∂positiveGramEigenLaw n p := by
      have hm : Measurable (fun z : (Orth n × Orth p) × (Fin (min n p) → ℝ) =>
          H (rectangularOrthogonalAction z.1 (rectangularDiagonalFactor n p z.2))) :=
        hH.comp hmodel
      exact lintegral_prod_symm _ hm.aemeasurable
    _ = ∫⁻ lam, ∫⁻ O : Orth p,
        H (rectangularDiagonalFactor n p lam * (O : Matrix (Fin p) (Fin p) ℝ)ᵀ)
          ∂haarProb (Orth p) ∂positiveGramEigenLaw n p := by
      apply lintegral_congr
      intro lam
      have hg : Measurable (fun g : Orth n × Orth p =>
          H (rectangularOrthogonalAction g (rectangularDiagonalFactor n p lam))) := by
        fun_prop
      rw [lintegral_prod_symm _ hg.aemeasurable]
      apply lintegral_congr
      intro O
      have heq : (fun U : Orth n =>
          H (rectangularOrthogonalAction (U, O) (rectangularDiagonalFactor n p lam))) =
          fun _ : Orth n => H (rectangularDiagonalFactor n p lam *
            (O : Matrix (Fin p) (Fin p) ℝ)ᵀ) := by
        funext U
        simpa only [rectangularOrthogonalAction, Matrix.mul_assoc] using
          hleft U (rectangularDiagonalFactor n p lam *
            (O : Matrix (Fin p) (Fin p) ℝ)ᵀ)
      rw [heq]
      simp

end Wishart
end
end CanonicalSource108

section CanonicalSource109
/- Source: Wishart/SingularGaussianRegression.lean -/



/-!
# Actual spectral regression at every natural sample size

The full source consists of independent positive eigenvalues, a full selected
Haar frame, and `n` Gaussian noise rows. Only `min n q` selected mean rows are
nonzero. The source law pushes forward to the actual `n`-row Gaussian Gram
law even when the selected or full Gram matrix is singular.
-/

open Matrix MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open Wishart.Spectral
open scoped Classical ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

def gaussianColumnJoin {n q m : ℕ}
    (x : Matrix (Fin n) (Fin q) ℝ × Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Fin n) (Fin (q + m)) ℝ :=
  fun i j => Sum.elim (x.1 i) (x.2 i) (finSumFinEquiv.symm j)

@[fun_prop] theorem measurable_gaussianColumnJoin (n q m : ℕ) :
    Measurable (@gaussianColumnJoin n q m) := by
  apply Matrix.measurable_iff.mpr
  intro i j
  unfold gaussianColumnJoin
  cases finSumFinEquiv.symm j <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop

theorem measurePreserving_gaussianColumnJoin (n q m : ℕ) :
    MeasurePreserving (@gaussianColumnJoin n q m)
      ((gaussianMatrixMeasure n q).prod (gaussianMatrixMeasure n m))
      (gaussianMatrixMeasure n (q + m)) := by
  let γq := Measure.pi fun _ : Fin q => gaussianReal 0 1
  let γm := Measure.pi fun _ : Fin m => gaussianReal 0 1
  have hsum := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin q ⊕ Fin m => gaussianReal 0 1)
  have hindex := measurePreserving_piCongrLeft
    (fun _ : Fin (q + m) => gaussianReal 0 1) finSumFinEquiv
  have hrow := hindex.comp hsum
  have hrows := measurePreserving_pi
    (fun _ : Fin n => γq.prod γm)
    (fun _ : Fin n => Measure.pi fun _ : Fin (q + m) => gaussianReal 0 1)
    (fun _ => hrow)
  have hsplit := measurePreserving_arrowProdEquivProdArrow
    (Fin q → ℝ) (Fin m → ℝ) (Fin n) (fun _ => γq) (fun _ => γm)
  convert hrows.comp hsplit.symm using 1 <;> try rfl
  apply heq_of_eq
  funext x i j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [gaussianColumnJoin, Equiv.symm_apply_apply, Function.comp_apply]
  change Sum.elim (x.1 i) (x.2 i) j =
    MeasurableEquiv.piCongrLeft (fun _ : Fin (q + m) => ℝ) finSumFinEquiv
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin q ⊕ Fin m => ℝ)).symm
        (x.1 i, x.2 i)) (finSumFinEquiv j)
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  cases j <;> rfl

@[simp] theorem gaussianColumnJoin_submatrix {n q m : ℕ}
    (A : Matrix (Fin n) (Fin q) ℝ) (G : Matrix (Fin n) (Fin m) ℝ) :
    (gaussianColumnJoin (A, G)).submatrix id finSumFinEquiv = Matrix.fromCols A G := by
  ext i j
  cases j <;> simp only [gaussianColumnJoin, Matrix.submatrix_apply, id_eq,
    Equiv.symm_apply_apply, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Sum.elim_inl, Sum.elim_inr]

theorem gaussianColumnJoin_mul_left {n q m : ℕ}
    (U : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin q) ℝ) (G : Matrix (Fin n) (Fin m) ℝ) :
    gaussianColumnJoin (U * A, U * G) = U * gaussianColumnJoin (A, G) := by
  ext i j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases j <;> simp only [gaussianColumnJoin, Equiv.symm_apply_apply,
    Sum.elim_inl, Sum.elim_inr, Matrix.mul_apply]

theorem matrixGram_mul_left {n p : ℕ}
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U * Uᵀ = 1)
    (A : Matrix (Fin n) (Fin p) ℝ) : matrixGram (U * A) = matrixGram A := by
  apply Subtype.ext
  rw [coe_matrixGram, coe_matrixGram, Matrix.transpose_mul]
  calc
    Aᵀ * Uᵀ * (U * A) = Aᵀ * (Uᵀ * U) * A := by simp only [Matrix.mul_assoc]
    _ = Aᵀ * A := by rw [mul_eq_one_comm.mp hU, Matrix.mul_one]

theorem matrixGram_mul_transpose {n p k : ℕ}
    (A : Matrix (Fin n) (Fin p) ℝ) (T : Matrix (Fin k) (Fin p) ℝ) :
    matrixGram (A * Tᵀ) = Matrix.symmetricCongruenceLinearMap T (matrixGram A) := by
  apply Subtype.ext
  simp only [coe_matrixGram, Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

def rawGaussianRegressionData {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (x : Matrix (Fin n) (Fin q) ℝ × Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Fin n) (Fin (q + m)) ℝ :=
  gaussianColumnJoin x * (regressionCovarianceFactor K (CFC.sqrt C))ᵀ

def rawGaussianRegressionGram {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (x : Matrix (Fin n) (Fin q) ℝ × Matrix (Fin n) (Fin m) ℝ) : Sym (q + m) :=
  Matrix.symmetricCongruenceLinearMap (regressionCovarianceFactor K (CFC.sqrt C))
    (matrixGram (gaussianColumnJoin x))

@[fun_prop] theorem measurable_rawGaussianRegressionGram {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ) :
    Measurable (rawGaussianRegressionGram (n := n) K C) :=
  (LinearMap.continuous_of_finiteDimensional _).measurable.comp
    ((measurable_matrixGram n (q + m)).comp (measurable_gaussianColumnJoin n q m))

theorem rawGaussianRegressionGram_eq_matrixGram {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (x : Matrix (Fin n) (Fin q) ℝ × Matrix (Fin n) (Fin m) ℝ) :
    rawGaussianRegressionGram K C x = matrixGram (rawGaussianRegressionData K C x) :=
  (matrixGram_mul_transpose _ _).symm

theorem rawGaussianRegressionData_submatrix {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (A : Matrix (Fin n) (Fin q) ℝ) (G : Matrix (Fin n) (Fin m) ℝ) :
    (rawGaussianRegressionData K C (A, G)).submatrix id finSumFinEquiv =
      Matrix.fromCols A (A * K + G * CFC.sqrt C) := by
  rw [rawGaussianRegressionData,
    Matrix.submatrix_mul _ _ id finSumFinEquiv finSumFinEquiv finSumFinEquiv.bijective,
    gaussianColumnJoin_submatrix, ← Matrix.transpose_submatrix,
    regressionCovarianceFactor_submatrix, Matrix.fromBlocks_transpose,
    Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_transpose,
    matrix_sqrt_transpose, Matrix.fromCols_mul_fromBlocks,
    Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem rawGaussianRegressionData_selected {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (A : Matrix (Fin n) (Fin q) ℝ) (G : Matrix (Fin n) (Fin m) ℝ)
    (i : Fin n) (j : Fin q) :
    rawGaussianRegressionData K C (A, G) i (Fin.castAdd m j) = A i j := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin q ⊕ Fin m) ℝ => M i (.inl j))
    (rawGaussianRegressionData_submatrix K C A G)
  simpa only [Matrix.submatrix_apply, id_eq, finSumFinEquiv_apply_left,
    Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Sum.elim_inl] using h

theorem rawGaussianRegressionGram_selected {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (A : Matrix (Fin n) (Fin q) ℝ) (G : Matrix (Fin n) (Fin m) ℝ) :
    regressionSelectedBlock (rawGaussianRegressionGram K C (A, G)) = matrixGram A := by
  apply Subtype.ext
  ext i j
  rw [rawGaussianRegressionGram_eq_matrixGram]
  change (∑ k : Fin n, rawGaussianRegressionData K C (A, G) k (Fin.castAdd m i) *
    rawGaussianRegressionData K C (A, G) k (Fin.castAdd m j)) = ∑ k : Fin n, A k i * A k j
  simp only [rawGaussianRegressionData_selected]

theorem map_rawGaussianRegressionGram {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosSemidef) :
    ((gaussianMatrixMeasure n q).prod (gaussianMatrixMeasure n m)).map
      (rawGaussianRegressionGram K C) = wishartGramMeasure n (regressionScale K C) := by
  have hgram : MeasurePreserving (matrixGram : Matrix (Fin n) (Fin (q + m)) ℝ → _)
      (gaussianMatrixMeasure n (q + m))
      (wishartGramMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) :=
    ⟨measurable_matrixGram n (q + m), map_matrixGram_gaussianMatrixMeasure n (q + m)⟩
  have hcong : MeasurePreserving
      (Matrix.symmetricCongruenceLinearMap (regressionCovarianceFactor K (CFC.sqrt C)))
      (wishartGramMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ))
      (wishartGramMeasure n (regressionScale K C)) := by
    refine ⟨(LinearMap.continuous_of_finiteDimensional _).measurable, ?_⟩
    simpa only [Matrix.mul_one, regressionCovarianceFactor_mul_transpose,
      matrix_sqrt_transpose, CFC.sqrt_mul_sqrt_self C hC.nonneg] using
      map_symmetricCongruenceLinearMap_wishartGramMeasure n
        (regressionCovarianceFactor K (CFC.sqrt C)) Matrix.PosSemidef.one
  exact (hcong.comp (hgram.comp (measurePreserving_gaussianColumnJoin n q m))).map_eq

theorem rawGaussianRegressionGram_rowRotation {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U * Uᵀ = 1)
    (A : Matrix (Fin n) (Fin q) ℝ) (G : Matrix (Fin n) (Fin m) ℝ) :
    rawGaussianRegressionGram K C (U * A, U * G) = rawGaussianRegressionGram K C (A, G) := by
  unfold rawGaussianRegressionGram
  rw [gaussianColumnJoin_mul_left, matrixGram_mul_left U hU]

theorem map_rawGaussianRegressionGram_noiseRotation {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U * Uᵀ = 1)
    (A : Matrix (Fin n) (Fin q) ℝ) :
    (gaussianMatrixMeasure n m).map (fun G => rawGaussianRegressionGram K C (U * A, G)) =
      (gaussianMatrixMeasure n m).map (fun G => rawGaussianRegressionGram K C (A, G)) := by
  have hmeas : Measurable (fun G => rawGaussianRegressionGram K C (U * A, G)) :=
    (measurable_rawGaussianRegressionGram K C).comp (measurable_const.prodMk measurable_id)
  have hrotate := (measurePreserving_gaussianMatrix_mul_left (p := m) U hU).map_eq
  calc
    _ = ((gaussianMatrixMeasure n m).map (fun G => U * G)).map
        (fun G => rawGaussianRegressionGram K C (U * A, G)) := by rw [hrotate]
    _ = _ := by
      rw [Measure.map_map hmeas (by fun_prop)]
      congr 1
      funext G
      exact rawGaussianRegressionGram_rowRotation K C U hU A G

def singularSpectralFactor (n q : ℕ) (lam : Fin (min n q) → ℝ) (O : Orth q) :
    Matrix (Fin n) (Fin q) ℝ :=
  rectangularDiagonalFactor n q lam * (O : Matrix (Fin q) (Fin q) ℝ)ᵀ

def singularRegressionSource (n q m : ℕ) :
    Measure ((Fin (min n q) → ℝ) × (Orth q × Matrix (Fin n) (Fin m) ℝ)) :=
  (positiveGramEigenLaw n q).prod ((haarProb (Orth q)).prod (gaussianMatrixMeasure n m))

instance singularRegressionSource_isProbability (n q m : ℕ) :
    IsProbabilityMeasure (singularRegressionSource n q m) := by
  letI := positiveGramEigenLaw_isProbability n q
  unfold singularRegressionSource
  infer_instance

def singularSpectralRegressionModel {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (z : (Fin (min n q) → ℝ) × (Orth q × Matrix (Fin n) (Fin m) ℝ)) : Sym (q + m) :=
  rawGaussianRegressionGram K C (singularSpectralFactor n q z.1 z.2.1, z.2.2)

@[fun_prop] theorem measurable_singularSpectralRegressionModel {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ) :
    Measurable (singularSpectralRegressionModel (n := n) K C) := by
  unfold singularSpectralRegressionModel singularSpectralFactor
  apply (measurable_rawGaussianRegressionGram K C).comp
  apply Measurable.prodMk
  · fun_prop
  · exact measurable_snd.comp measurable_snd

/-- The actual singular or nonsingular integer Gram law, with independent
positive Laguerre eigenvalues, a selected Haar frame, and Gaussian regression
noise. No rank or density assumption is imposed on the full matrix. -/
theorem map_singularSpectralRegressionModel {n q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosSemidef) :
    (singularRegressionSource n q m).map (singularSpectralRegressionModel K C) =
      wishartGramMeasure n (regressionScale K C) := by
  letI := positiveGramEigenLaw_isProbability n q
  apply Measure.ext_of_lintegral
  intro f hf
  let H : Matrix (Fin n) (Fin q) ℝ → ℝ≥0∞ :=
    fun A => ∫⁻ G, f (rawGaussianRegressionGram K C (A, G)) ∂gaussianMatrixMeasure n m
  have hraw : Measurable (fun x : Matrix (Fin n) (Fin q) ℝ × Matrix (Fin n) (Fin m) ℝ =>
      f (rawGaussianRegressionGram K C x)) := hf.comp (measurable_rawGaussianRegressionGram K C)
  have hH : Measurable H := hraw.lintegral_prod_right
  have hleft (U : Orth n) (A : Matrix (Fin n) (Fin q) ℝ) :
      H ((U : Matrix (Fin n) (Fin n) ℝ) * A) = H A := by
    have heq := map_rawGaussianRegressionGram_noiseRotation K C
      (U : Matrix (Fin n) (Fin n) ℝ) (orth_mul_transpose U) A
    have h1 : Measurable (fun G => rawGaussianRegressionGram K C
        ((U : Matrix (Fin n) (Fin n) ℝ) * A, G)) :=
      (measurable_rawGaussianRegressionGram K C).comp (measurable_const.prodMk measurable_id)
    have h2 : Measurable (fun G => rawGaussianRegressionGram K C (A, G)) :=
      (measurable_rawGaussianRegressionGram K C).comp (measurable_const.prodMk measurable_id)
    change (∫⁻ G, f (rawGaussianRegressionGram K C ((U : Matrix (Fin n) (Fin n) ℝ) * A, G)) ∂gaussianMatrixMeasure n m) = _
    rw [← lintegral_map hf h1, heq, lintegral_map hf h2]
  have hmodel : Measurable (fun z : (Fin (min n q) → ℝ) ×
      (Orth q × Matrix (Fin n) (Fin m) ℝ) => f (singularSpectralRegressionModel K C z)) :=
    hf.comp (measurable_singularSpectralRegressionModel (n := n) K C)
  calc
    (∫⁻ X, f X ∂(singularRegressionSource n q m).map (singularSpectralRegressionModel K C)) =
        ∫⁻ lam, ∫⁻ O : Orth q,
          H (rectangularDiagonalFactor n q lam * (O : Matrix (Fin q) (Fin q) ℝ)ᵀ)
            ∂haarProb (Orth q) ∂positiveGramEigenLaw n q := by
      rw [lintegral_map hf (measurable_singularSpectralRegressionModel K C)]
      unfold singularRegressionSource
      rw [lintegral_prod _ hmodel.aemeasurable]
      apply lintegral_congr
      intro lam
      have hmodel_lam : Measurable (fun z : Orth q × Matrix (Fin n) (Fin m) ℝ =>
          f (singularSpectralRegressionModel K C (lam, z))) :=
        hmodel.comp (measurable_const.prodMk measurable_id)
      rw [lintegral_prod _ hmodel_lam.aemeasurable]
      rfl
    _ = ∫⁻ A, H A ∂gaussianMatrixMeasure n q :=
      (lintegral_gaussianMatrix_of_rowInvariant H hH hleft).symm
    _ = ∫⁻ X, f X ∂wishartGramMeasure n (regressionScale K C) := by
      rw [← map_rawGaussianRegressionGram (n := n) K hC,
        lintegral_map hf (measurable_rawGaussianRegressionGram K C),
        lintegral_prod _ hraw.aemeasurable]

end Wishart
end
end CanonicalSource109
