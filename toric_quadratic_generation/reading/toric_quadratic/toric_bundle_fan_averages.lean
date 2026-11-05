module

public import PaperVerification.ToricBundleFanEndpoints


@[expose] public section
/-!
# Affine dependence of base divisors on homogeneous weights

The actual base coefficients are the barycentric average of the endpoint
coefficients, for every real homogeneous weight of the correct total degree.
Nonnegative weights therefore preserve strict support.  Addition and primitive
relation degrees use the same literal coefficient functions.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem IsStrictSupport.weighted_sum {κ : Type*} (s : Finset κ)
    (a : κ → Lattice n → ℝ) (w : κ → ℝ)
    (ha : ∀ i ∈ s, «Σ».IsStrictSupport (a i))
    (hw : ∀ i ∈ s, 0 ≤ w i) (hpos : ∃ i ∈ s, 0 < w i) :
    «Σ».IsStrictSupport (fun v => ∑ i ∈ s, w i * a i v) := by
  intro C hC
  let ℓ : κ → Ambient n →ₗ[ℝ] ℝ := fun i =>
    if hi : i ∈ s then Classical.choose (ha i hi C hC) else 0
  have he (i : κ) (hi : i ∈ s) : ∀ v ∈ C, ℓ i (embed n v) = a i v := by
    simpa only [ℓ, dif_pos hi] using (Classical.choose_spec (ha i hi C hC)).1
  have hlt (i : κ) (hi : i ∈ s) :
      ∀ v ∈ «Σ».rays, v ∉ C → ℓ i (embed n v) < a i v := by
    simpa only [ℓ, dif_pos hi] using (Classical.choose_spec (ha i hi C hC)).2
  refine ⟨∑ i ∈ s, w i • ℓ i, ?_, ?_⟩
  · intro v hv
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i hi v hv]
  · intro v hv hvC
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    have hgap : 0 < ∑ i ∈ s, w i * (a i v - ℓ i (embed n v)) := by
      apply Finset.sum_pos'
      · intro i hi
        exact mul_nonneg (hw i hi) (sub_pos.mpr (hlt i hi v hv hvC)).le
      · obtain ⟨i, hi, hiw⟩ := hpos
        exact ⟨i, hi, mul_pos hiw (sub_pos.mpr (hlt i hi v hv hvC))⟩
    simpa only [mul_sub, Finset.sum_sub_distrib, sub_pos] using hgap

namespace PrimitiveRelation

variable {«Σ»} (T : «Σ».PrimitiveRelation)

theorem degree_weighted_sum {κ : Type*} (s : Finset κ)
    (a : κ → Lattice n → ℝ) (w : κ → ℝ) :
    T.degree (fun v => ∑ i ∈ s, w i * a i v) = ∑ i ∈ s, w i * T.degree (a i) := by
  induction s using Finset.induction_on with
  | empty => simp [degree]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    change T.degree (w i • a i + (fun v => ∑ j ∈ s, w j * a j v)) = _
    rw [T.degree_add, T.degree_smul, ih]

end PrimitiveRelation

end SmoothCompleteFan

namespace SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

theorem baseWeight_add (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (a b α β : Lattice n → ℝ) :
    c.baseWeight hR hN (a + b) (α + β) =
      c.baseWeight hR hN a α + c.baseWeight hR hN b β := by
  funext q
  unfold baseWeight
  simp only [Pi.add_apply]
  have he (i : Fin n) :
      (c.basis.repr (c.baseRayLift hR hN q) i : ℝ) *
        ((α (c.basis i) + β (c.basis i)) - (a (c.basis i) + b (c.basis i))) =
      (c.basis.repr (c.baseRayLift hR hN q) i : ℝ) * (α (c.basis i) - a (c.basis i)) +
        (c.basis.repr (c.baseRayLift hR hN q) i : ℝ) * (β (c.basis i) - b (c.basis i)) := by ring
  simp only [he, Finset.sum_add_distrib]
  ring

theorem baseWeight_congr_weight (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (a α β : Lattice n → ℝ) (h : ∀ v ∈ R.positive, α v = β v) :
    c.baseWeight hR hN a α = c.baseWeight hR hN a β := by
  funext q
  unfold baseWeight
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [h _ (c.fiber_subset_positive (Finset.mem_image.mpr ⟨i, hi, rfl⟩))]

theorem normalized_weights_sum (c : R.BundleCoordinates) (a α : Lattice n → ℝ)
    (hk : (∑ v ∈ R.positive, a v) ≠ 0)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v) :
    (∑ v ∈ R.positive, α v / (∑ w ∈ R.positive, a w)) = 1 := by
  rw [← Finset.sum_div, hα, div_self hk]

/-- The precise barycentric formula in Section 3.2, for all real weights
with the correct total fiber degree. -/
theorem baseWeight_convex_combination (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℝ)
    (hk : (∑ v ∈ R.positive, a v) ≠ 0)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v) :
    c.baseWeight hR hN a α = fun q =>
      ∑ v ∈ R.positive, (α v / (∑ w ∈ R.positive, a w)) *
        c.baseWeight hR hN a (c.endpointWeight a v) q := by
  funext q
  let k := ∑ w ∈ R.positive, a w
  let A := c.baseWeight hR hN a 0 q
  let E : Fin n → ℝ := fun i => (c.basis.repr (c.baseRayLift hR hN q) i : ℝ)
  have hsum : (∑ v ∈ R.positive, α v / k) = 1 := c.normalized_weights_sum a α hk hα
  have hi (i : Fin n) (hi : i ∈ c.fiberIndices) :
      (∑ v ∈ R.positive, α v / k * c.endpointWeight a v (c.basis i)) = α (c.basis i) := by
    have hbi := c.fiber_subset_positive (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    simp only [endpointWeight, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [if_pos hbi]
    exact div_mul_cancel₀ _ hk
  have he (v : Lattice n) : c.baseWeight hR hN a (c.endpointWeight a v) q =
      A + ∑ i ∈ c.fiberIndices, E i * c.endpointWeight a v (c.basis i) :=
    c.baseWeight_affine hR hN a (c.endpointWeight a v) q
  rw [c.baseWeight_affine hR hN a α q]
  change A + (∑ i ∈ c.fiberIndices, E i * α (c.basis i)) = _
  simp_rw [he, mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hii
  calc
    E i * α (c.basis i) = E i *
        (∑ v ∈ R.positive, α v / k * c.endpointWeight a v (c.basis i)) := by rw [hi i hii]
    _ = ∑ v ∈ R.positive,
        α v / k * (E i * c.endpointWeight a v (c.basis i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring

/-- Every nonnegative homogeneous slice has a genuine strictly supported
base divisor, including boundary weights with zero entries. -/
theorem baseWeight_isStrictSupport (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (hα0 : ∀ v ∈ R.positive, 0 ≤ α v) :
    c.baseFan.IsStrictSupport (c.baseWeight hR hN a α) := by
  have hk : 0 < ∑ v ∈ R.positive, a v := by
    have h := R.degree_pos_of_strictSupport ha
    simpa only [SmoothCompleteFan.PrimitiveRelation.degree, hN, Finset.sum_empty, sub_zero] using h
  have hw (v : Lattice n) (hv : v ∈ R.positive) :
      0 ≤ α v / (∑ w ∈ R.positive, a w) := div_nonneg (hα0 v hv) hk.le
  have hsum := c.normalized_weights_sum a α hk.ne' hα
  have hpos : ∃ v ∈ R.positive, 0 < α v / (∑ w ∈ R.positive, a w) := by
    apply (Finset.sum_pos_iff_of_nonneg hw).mp
    rw [hsum]
    exact zero_lt_one
  rw [c.baseWeight_convex_combination hR hN a α hk.ne' hα]
  exact SmoothCompleteFan.IsStrictSupport.weighted_sum c.baseFan R.positive
    (fun v => c.baseWeight hR hN a (c.endpointWeight a v))
    (fun v => α v / (∑ w ∈ R.positive, a w))
    (fun v hv => c.endpoint_isStrictSupport hR hN a ha hv) hw hpos

/-- Any lower bound valid on all endpoint relation degrees is retained at
every nonnegative homogeneous weight. -/
theorem baseWeight_degree_lower_bound (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℝ)
    (hk : 0 < ∑ v ∈ R.positive, a v)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (hα0 : ∀ v ∈ R.positive, 0 ≤ α v)
    (T : c.baseFan.PrimitiveRelation) (B : ℝ)
    (hB : ∀ u ∈ R.positive,
      B ≤ T.degree (c.baseWeight hR hN a (c.endpointWeight a u))) :
    B ≤ T.degree (c.baseWeight hR hN a α) := by
  rw [c.baseWeight_convex_combination hR hN a α hk.ne' hα, T.degree_weighted_sum]
  calc
    B = (∑ u ∈ R.positive, α u / (∑ w ∈ R.positive, a w)) * B := by
      rw [c.normalized_weights_sum a α hk.ne' hα, one_mul]
    _ = ∑ u ∈ R.positive, α u / (∑ w ∈ R.positive, a w) * B :=
      Finset.sum_mul R.positive (fun u => α u / (∑ w ∈ R.positive, a w)) B
    _ ≤ _ := Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left (hB u hu)
      (div_nonneg (hα0 u hu) hk.le))

end SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

end PaperVerification.ToricGeometry
