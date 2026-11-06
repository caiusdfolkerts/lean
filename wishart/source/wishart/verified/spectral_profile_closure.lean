module

public import wishart.verified.field_residual08
public import wishart.verified.field_residual09

/- Source: Wishart/SpectralProfileClosure.lean -/

@[expose] public section

/-!
# The closure operations printed after Theorem 7.1

Products, nonnegative sums, and increasing geometrically log-convex outer
compositions are represented by actual convex monotone symmetric profiles.
Their boundary identities follow from the original regularized limit, so
they also hold on singular faces.  A sum with every coefficient zero is
recorded as the zero function, rather than assigned a fictitious finite
logarithmic profile.  Empty products are included.
-/

noncomputable section
open Set Filter Topology
open scoped Classical BigOperators

namespace Wishart.Spectral
open WishartVerification
variable {k : ℕ} {ι : Type*} [Fintype ι]

def productProfile (h : ι → (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) : ℝ :=
  ∑ i, h i x

theorem productProfile_properties (h : ι → (Fin k → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i))
    (hs : ∀ i, SymmetricProfile (h i)) :
    ConvexOn ℝ univ (productProfile h) ∧ Monotone (productProfile h) ∧
      SymmetricProfile (productProfile h) := by
  refine ⟨⟨convex_univ, ?_⟩, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      (hc i).2 hx hy ha hb hab
    simpa only [productProfile, smul_eq_mul, Finset.sum_add_distrib,
      Finset.mul_sum] using hh
  · intro x y hxy
    exact Finset.sum_le_sum fun i _ => hm i hxy
  · intro σ x
    exact Finset.sum_congr rfl fun i _ => hs i σ x

theorem spectralBoundaryValue_productProfile (h : ι → (Fin k → ℝ) → ℝ)
    (hm : ∀ i, Monotone (h i)) {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    spectralBoundaryValue (productProfile h) x =
      ∏ i, spectralBoundaryValue (h i) x := by
  have hmprod : Monotone (productProfile h) := fun u v huv =>
    Finset.sum_le_sum fun i _ => hm i huv
  have hlimit (s : Finset ι) :
      Tendsto (fun t => ∏ i ∈ s, spectralRegularization (h i) x t) atBot
        (𝓝 (∏ i ∈ s, spectralBoundaryValue (h i) x)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using tendsto_const_nhds
    | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using
        (spectralBoundaryValue_tendsto (hm i) hx).mul ih
  apply tendsto_nhds_unique (spectralBoundaryValue_tendsto hmprod hx)
  change Tendsto (fun t : ℝ => spectralRegularization (productProfile h) x t)
    atBot (𝓝 (∏ i, spectralBoundaryValue (h i) x))
  simpa only [spectralRegularization, productProfile, Real.exp_sum] using
    hlimit Finset.univ

def nonnegativeSumProfile (c : ι → ℝ) (h : ι → (Fin k → ℝ) → ℝ)
    (x : Fin k → ℝ) : ℝ := Real.log (weightedExponentialSum c h x)

theorem nonnegativeSumProfile_properties (c : ι → ℝ)
    (h : ι → (Fin k → ℝ) → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hpos : ∃ i, 0 < c i) (hh : ∀ i, ConvexOn ℝ univ (h i))
    (hm : ∀ i, Monotone (h i)) (hs : ∀ i, SymmetricProfile (h i)) :
    ConvexOn ℝ univ (nonnegativeSumProfile c h) ∧
      Monotone (nonnegativeSumProfile c h) ∧
      SymmetricProfile (nonnegativeSumProfile c h) := by
  refine ⟨convexOn_log_weightedExponentialSum c h hc hpos hh,
    monotone_log_weightedExponentialSum c h hc hpos hm, ?_⟩
  intro σ x
  unfold nonnegativeSumProfile weightedExponentialSum
  congr 1
  exact Finset.sum_congr rfl fun i _ => congrArg (fun t => c i * Real.exp t) (hs i σ x)

theorem spectralBoundaryValue_nonnegativeSumProfile (c : ι → ℝ)
    (h : ι → (Fin k → ℝ) → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hpos : ∃ i, 0 < c i) (hm : ∀ i, Monotone (h i))
    {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    spectralBoundaryValue (nonnegativeSumProfile c h) x =
      ∑ i, c i * spectralBoundaryValue (h i) x := by
  have hlimit (s : Finset ι) :
      Tendsto (fun t => ∑ i ∈ s, c i * spectralRegularization (h i) x t) atBot
        (𝓝 (∑ i ∈ s, c i * spectralBoundaryValue (h i) x)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using tendsto_const_nhds
    | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        (tendsto_const_nhds.mul (spectralBoundaryValue_tendsto (hm i) hx)).add ih
  apply tendsto_nhds_unique (spectralBoundaryValue_tendsto
    (monotone_log_weightedExponentialSum c h hc hpos hm) hx)
  apply (hlimit Finset.univ).congr'
  exact Filter.Eventually.of_forall fun t => by
    exact (Real.exp_log (weightedExponentialSum_pos c h hc hpos
      (fun i => Real.log (x i + Real.exp t)))).symm

/-- The degenerate coefficient case is part of the closure statement. -/
theorem nonnegativeSum_zero_or_profile (c : ι → ℝ)
    (h : ι → (Fin k → ℝ) → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hh : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i))
    (hs : ∀ i, SymmetricProfile (h i)) :
    (∀ x : Fin k → ℝ, ∑ i, c i * spectralBoundaryValue (h i) x = 0) ∨
      ∃ g : (Fin k → ℝ) → ℝ, ConvexOn ℝ univ g ∧ Monotone g ∧
        SymmetricProfile g ∧ ∀ x, (∀ i, 0 ≤ x i) →
          spectralBoundaryValue g x = ∑ i, c i * spectralBoundaryValue (h i) x := by
  by_cases hpos : ∃ i, 0 < c i
  · refine Or.inr ⟨nonnegativeSumProfile c h,
      (nonnegativeSumProfile_properties c h hc hpos hh hm hs).1,
      (nonnegativeSumProfile_properties c h hc hpos hh hm hs).2.1,
      (nonnegativeSumProfile_properties c h hc hpos hh hm hs).2.2, ?_⟩
    exact fun x hx => spectralBoundaryValue_nonnegativeSumProfile c h hc hpos hm hx
  · have hz (i : ι) : c i = 0 := le_antisymm
      (le_of_not_gt fun hi => hpos ⟨i, hi⟩) (hc i)
    exact Or.inl fun x => by simp only [hz, zero_mul, Finset.sum_const_zero]

def outerCompositionProfile (f : ℝ → ℝ) (h : (Fin k → ℝ) → ℝ)
    (x : Fin k → ℝ) : ℝ := Real.log (f (Real.exp (h x)))

theorem outerCompositionProfile_properties {f : ℝ → ℝ}
    (hf : GeometricallyLogConvex f) {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) (hs : SymmetricProfile h) :
    ConvexOn ℝ univ (outerCompositionProfile f h) ∧
      Monotone (outerCompositionProfile f h) ∧
      SymmetricProfile (outerCompositionProfile f h) := by
  refine ⟨⟨convex_univ, ?_⟩, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    apply le_trans (hf.monotone_log (hc.2 hx hy ha hb hab))
    exact hf.convex_log.2 (mem_univ _) (mem_univ _) ha hb hab
  · intro x y hxy
    exact hf.monotone_log (hm hxy)
  · intro σ x
    unfold outerCompositionProfile
    rw [hs σ x]

/-- Composition uses the outer function's actual, automatically existing
right limit at zero, with no extra boundary-continuity hypothesis. -/
theorem spectralBoundaryValue_outerCompositionProfile {f : ℝ → ℝ}
    (hf : GeometricallyLogConvex f) {h : (Fin k → ℝ) → ℝ}
    (hm : Monotone h) {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    spectralBoundaryValue (outerCompositionProfile f h) x =
      canonicalGeometricExtension f (spectralBoundaryValue h x) := by
  have hinner : Tendsto (spectralRegularization h x) atBot
      (𝓝[Ici 0] (spectralBoundaryValue h x)) := by
    refine tendsto_nhdsWithin_iff.mpr
      ⟨spectralBoundaryValue_tendsto hm hx, ?_⟩
    exact Filter.Eventually.of_forall fun t => (Real.exp_pos _).le
  have hlimit := ((hf.canonicalExtension_on_nonnegative.continuousOn _
    (spectralBoundaryValue_nonneg h x)).tendsto).comp hinner
  have hmcomp : Monotone (outerCompositionProfile f h) := fun u v huv =>
    hf.monotone_log (hm huv)
  apply tendsto_nhds_unique (spectralBoundaryValue_tendsto hmcomp hx)
  apply hlimit.congr'
  exact Filter.Eventually.of_forall fun t => by
    simp only [Function.comp_apply, spectralRegularization, outerCompositionProfile,
      canonicalGeometricExtension_pos f (Real.exp_pos _),
      Real.exp_log (hf.positive _ (Real.exp_pos _))]

end Wishart.Spectral
