module

public import PaperVerification.ToricBundleFanIntegral


@[expose] public section
/-!
# Endpoint divisors on the genuine base fan

At each vertex of the projective fiber simplex the base coefficients inherit
strict support from the original fan.  The supporting functions and their
slacks are computed explicitly using the integral quotient section.  Thus
ampleness of the endpoint base divisors is proved, not assumed.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

def endpointWeight (c : R.BundleCoordinates) (a : Lattice n → ℝ) (u : Lattice n) (v : Lattice n) : ℝ :=
  if v = u then ∑ w ∈ R.positive, a w else 0

theorem endpointWeight_total (a : Lattice n → ℝ) {u : Lattice n}
    (hu : u ∈ R.positive) :
    (∑ v ∈ R.positive, c.endpointWeight a u v) = ∑ v ∈ R.positive, a v := by
  simp [endpointWeight, hu]

theorem endpointWeight_nonneg (a : Lattice n → ℝ)
    (hk : 0 ≤ ∑ w ∈ R.positive, a w) (u v : Lattice n) :
    0 ≤ c.endpointWeight a u v := by
  unfold endpointWeight
  split_ifs
  · exact hk
  · exact le_rfl

theorem weights_eq_endpoint (c : R.BundleCoordinates) {α : Lattice n → ℝ} {k : ℝ} {u : Lattice n}
    (hu : u ∈ R.positive) (hsum : (∑ v ∈ R.positive, α v) = k)
    (hzero : ∀ v ∈ R.positive.erase u, α v = 0) :
    ∀ v ∈ R.positive, α v = if v = u then k else 0 := by
  have hau : α u = k := by
    rw [← Finset.sum_erase_add R.positive α hu] at hsum
    have hz : (∑ v ∈ R.positive.erase u, α v) = 0 := Finset.sum_eq_zero hzero
    simpa only [hz, zero_add] using hsum
  intro v hv
  by_cases hvu : v = u
  · simp only [hvu, if_pos rfl, ite_true, hau]
  · rw [if_neg hvu]
    exact hzero v (Finset.mem_erase.mpr ⟨hvu, hv⟩)

theorem endpoint_support_coordinates (hN : R.negative = ∅)
    (a : Lattice n → ℝ) {u : Lattice n} (hu : u ∈ R.positive)
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (hℓ : ∀ v ∈ R.positive.erase u, ℓ (embed n v) = a v) :
    ∀ v ∈ R.positive, c.endpointWeight a u v - a v = -ℓ (embed n v) := by
  have hsum : (∑ v ∈ R.positive, ℓ (embed n v)) = 0 := by
    rw [← map_sum, ← map_sum, R.equation, hN, Finset.sum_empty, map_zero, map_zero]
  have hslack : (∑ v ∈ R.positive, (a v - ℓ (embed n v))) = ∑ v ∈ R.positive, a v := by
    rw [Finset.sum_sub_distrib, hsum, sub_zero]
  have he := c.weights_eq_endpoint hu hslack (fun v hv => by rw [hℓ v hv, sub_self])
  intro v hv
  have h := he v hv
  change a v - ℓ (embed n v) = c.endpointWeight a u v at h
  linarith

def liftBaseCone (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (D : Finset (Lattice (n - c.fiberIndices.card))) : Finset (Lattice n) :=
  D.image (c.baseRayLift hR hN)

theorem liftBaseCone_subset_nonfiber (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {D : Finset (Lattice (n - c.fiberIndices.card))}
    (hD : D ⊆ c.baseFan.rays) :
    c.liftBaseCone hR hN D ⊆ «Σ».rays \ R.positive := by
  intro v hv
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
  exact c.baseRayLift_mem hR hN (hD hq)

theorem quotient_liftBaseCone (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {D : Finset (Lattice (n - c.fiberIndices.card))}
    (hD : D ⊆ c.baseFan.rays) :
    (c.liftBaseCone hR hN D).image c.quotientLattice = D := by
  unfold liftBaseCone
  rw [Finset.image_image]
  have he : D.image (fun q => c.quotientLattice (c.baseRayLift hR hN q)) = D.image id := by
    apply Finset.image_congr
    intro q hq
    exact c.quotient_baseRayLift hR hN (hD hq)
  change D.image (fun q => c.quotientLattice (c.baseRayLift hR hN q)) = D
  rw [he, Finset.image_id]

theorem liftBaseCone_mem (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {D : Finset (Lattice (n - c.fiberIndices.card))}
    (hD : D ∈ c.baseFan.cones) : c.liftBaseCone hR hN D ∈ «Σ».cones := by
  have hDrays : D ⊆ c.baseFan.rays :=
    fun q hq => (c.baseFan.mem_rays_iff q).mpr ⟨D, hD, hq⟩
  have hnon := c.liftBaseCone_subset_nonfiber hR hN hDrays
  apply (c.nonfiber_cone_iff_projected_cone hR hN
    (fun v hv => (Finset.mem_sdiff.mp (hnon hv)).1) ?_).mpr
  · rw [c.quotient_liftBaseCone hR hN hDrays]
    exact hD
  · exact Finset.disjoint_left.mpr
      (fun v hv hvP => (Finset.mem_sdiff.mp (hnon hv)).2 hvP)

theorem baseWeight_support_residual (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℝ) (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (hα : ∀ i ∈ c.fiberIndices,
      α (c.basis i) - a (c.basis i) = -ℓ (embed n (c.basis i)))
    {q : Lattice (n - c.fiberIndices.card)} (hq : q ∈ c.baseFan.rays) :
    c.baseWeight hR hN a α q -
      ℓ (coneQuotientSectionReal c.basis c.fiberIndices (embed (n - c.fiberIndices.card) q)) =
        a (c.baseRayLift hR hN q) - ℓ (embed n (c.baseRayLift hR hN q)) := by
  let v := c.baseRayLift hR hN q
  have hd := coneQuotient_decomposition c.basis c.fiberIndices (embed n v)
  rw [coneQuotient_compatible, c.quotient_baseRayLift hR hN hq] at hd
  have he := congrArg ℓ hd
  simp only [map_add, map_sum, map_smul, smul_eq_mul,
    integralBasisReal_repr, integralBasisReal_apply] at he
  have hsum : (∑ i ∈ c.fiberIndices, (c.basis.repr v i : ℝ) *
      (α (c.basis i) - a (c.basis i))) =
      -(∑ i ∈ c.fiberIndices, (c.basis.repr v i : ℝ) * ℓ (embed n (c.basis i))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hα i hi, mul_neg]
  change a v + _ - _ = a v - _
  rw [hsum]
  linarith only [he]

/-- Every endpoint divisor is strictly supported on the actual base fan. -/
theorem endpoint_isStrictSupport (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    {u : Lattice n} (hu : u ∈ R.positive) :
    c.baseFan.IsStrictSupport (c.baseWeight hR hN a (c.endpointWeight a u)) := by
  intro D hD
  have hDrays : D ⊆ c.baseFan.rays :=
    fun q hq => (c.baseFan.mem_rays_iff q).mpr ⟨D, hD, hq⟩
  let C := c.liftBaseCone hR hN D
  have hC : C ∈ «Σ».cones := c.liftBaseCone_mem hR hN hD
  have hnon : C ⊆ «Σ».rays \ R.positive := c.liftBaseCone_subset_nonfiber hR hN hDrays
  have huC : u ∉ C := fun hu' => (Finset.mem_sdiff.mp (hnon hu')).2 hu
  have hfill : R.positive.erase u ∪ C ∈ «Σ».cones :=
    R.fill_cone_with_positive_except hR hC (by rw [hN]; exact Finset.empty_subset _) hu huC
  obtain ⟨ℓ, hℓ, hstrict⟩ := ha _ hfill
  have hcoord := c.endpoint_support_coordinates hN a hu ℓ
    (fun v hv => hℓ v (Finset.mem_union_left _ hv))
  have hα (i : Fin n) (hi : i ∈ c.fiberIndices) :
      c.endpointWeight a u (c.basis i) - a (c.basis i) = -ℓ (embed n (c.basis i)) :=
    hcoord _ (c.fiber_subset_positive (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  refine ⟨ℓ.comp (coneQuotientSectionReal c.basis c.fiberIndices), ?_, ?_⟩
  · intro q hqD
    have hq := hDrays hqD
    have hvC : c.baseRayLift hR hN q ∈ C := Finset.mem_image.mpr ⟨q, hqD, rfl⟩
    have he := c.baseWeight_support_residual hR hN a (c.endpointWeight a u) ℓ hα hq
    have hv := hℓ _ (Finset.mem_union_right _ hvC)
    simp only [LinearMap.comp_apply]
    linarith only [he, hv]
  · intro q hq hqD
    have hv := c.baseRayLift_mem hR hN hq
    have hvnot : c.baseRayLift hR hN q ∉ R.positive.erase u ∪ C := by
      intro hm
      rcases Finset.mem_union.mp hm with hmP | hmC
      · exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_of_mem_erase hmP)
      · obtain ⟨q', hq'D, he⟩ := Finset.mem_image.mp hmC
        have heq := congrArg c.quotientLattice he
        rw [c.quotient_baseRayLift hR hN (hDrays hq'D),
          c.quotient_baseRayLift hR hN hq] at heq
        exact hqD (heq ▸ hq'D)
    have hlt := hstrict _ (Finset.mem_sdiff.mp hv).1 hvnot
    have he := c.baseWeight_support_residual hR hN a (c.endpointWeight a u) ℓ hα hq
    simp only [LinearMap.comp_apply]
    linarith only [he, hlt]

end SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

end PaperVerification.ToricGeometry
