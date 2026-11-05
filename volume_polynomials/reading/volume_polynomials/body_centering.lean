module
public import VolumePolynomials.PositiveVolumePolynomial
public import VolumePolynomials.FinitePolytope

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Centering the tuple for the facet induction

An interior point of a Minkowski sum is the sum of points in its summands.
Translating by these points puts zero in every summand and in the interior of
the total sum. If the total sum has empty interior, all weighted sums have zero
ambient volume after centering. Thus no full-dimensional hypothesis is needed
in the eventual polynomiality theorem.
-/

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials
open PolytopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

theorem sum_translateBody (K : ι → ConvexBody E) (v : ι → E) :
    (∑ i, translateBody (v i) (K i)) = translateBody (∑ i, v i) (∑ i, K i) := by
  first
  | simp only [translateBody, Finset.sum_add_distrib]
    congr 1
    exact (map_sum (pointBodyHom (E := E)) _ _).symm

theorem zero_mem_sum_body (K : ι → ConvexBody E) (hK : ∀ i, (0 : E) ∈ K i) :
    (0 : E) ∈ ∑ i, K i := by
  first
  | rw [mem_sum_body]
    exact ⟨fun _ => 0, hK, Finset.sum_const_zero⟩

/-- The translation vectors are actual points of the original summands. -/
theorem exists_centered_translates (K : ι → ConvexBody E)
    (hfull : (interior ((∑ i, K i : ConvexBody E) : Set E)).Nonempty) :
    ∃ p : ι → E, (∀ i, p i ∈ K i) ∧
      (∀ i, (0 : E) ∈ translateBody (-p i) (K i)) ∧
      (0 : E) ∈ interior ((∑ i, translateBody (-p i) (K i) : ConvexBody E) : Set E) := by
  first
  | obtain ⟨x, hx⟩ := hfull
    obtain ⟨p, hp, hsum⟩ := (mem_sum_body K x).mp (interior_subset hx)
    refine ⟨p, hp, (fun i => zero_mem_translateBody_neg (hp i)), ?_⟩
    rw [sum_translateBody, Finset.sum_neg_distrib, hsum, coe_translateBody, interior_vadd]
    exact ⟨x, hx, neg_add_cancel x⟩

theorem isFiniteHull_translateBody {K : ConvexBody E}
    (hK : IsFiniteHull (K : Set E)) (v : E) :
    IsFiniteHull (translateBody v K : Set E) := by
  first
  | change IsFiniteHull (({v} : Set E) + (K : Set E))
    exact (IsFiniteHull.singleton v).add hK

section Measure
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem weighted_sum_measure_zero_of_empty_interior (K : ι → ConvexBody E)
    (hK : ∀ i, (0 : E) ∈ K i)
    (hempty : interior ((∑ i, K i : ConvexBody E) : Set E) = ∅) (t : ι → ℝ) :
    μ ((∑ i, t i • K i : ConvexBody E) : Set E) = 0 := by
  first
  | let S : Set E := ((∑ i, K i : ConvexBody E) : Set E)
    let U : Submodule ℝ E := Submodule.span ℝ S
    have hspan : affineSpan ℝ S ≠ ⊤ := by
      intro h
      have hn := (∑ i, K i : ConvexBody E).convex.interior_nonempty_iff_affineSpan_eq_top.mpr h
      rw [hempty] at hn
      exact Set.not_nonempty_empty hn
    have hU : U ≠ ⊤ := by
      intro h
      apply hspan
      rw [affineSpan_eq_span_of_zero_mem
        (mem_affineSpan ℝ (zero_mem_sum_body K hK))]
      change U.toAffineSubspace = ⊤
      rw [h]
      rfl
    apply measure_mono_null _ (Measure.addHaar_submodule μ U hU)
    intro x hx
    obtain ⟨p, hp, rfl⟩ := (mem_sum_body (fun i => t i • K i) x).mp hx
    apply Submodule.sum_mem
    intro i _
    obtain ⟨y, hy, heq⟩ := hp i
    rw [← heq]
    exact U.smul_mem (t i) (Submodule.subset_span (body_le_sum_of_zero_mem K hK i hy))

theorem hasPositiveVolumePolynomial_of_empty_interior {n : ℕ}
    (K : Fin n → ConvexBody E) (hK : ∀ i, (0 : E) ∈ K i)
    (hempty : interior ((∑ i, K i : ConvexBody E) : Set E) = ∅) :
    HasPositiveVolumePolynomial μ K := by
  first
  | refine ⟨0, MvPolynomial.isHomogeneous_zero (σ := Fin n) (R := ℝ) _,
      PolynomialNonnegativeCoefficients.zero, fun t _ => ?_⟩
    rw [map_zero, Measure.real,
      weighted_sum_measure_zero_of_empty_interior μ K hK hempty t, ENNReal.toReal_zero]

/-- Removing the centering and full-dimensional restrictions from the finite
polytope induction. Its premise is precisely the centered geometric case. -/
theorem hasPositiveVolumePolynomial_of_centered_case {n : ℕ}
    (hcenter : ∀ L : Fin n → ConvexBody E,
      (∀ i, IsFiniteHull (L i : Set E)) → (∀ i, (0 : E) ∈ L i) →
      (0 : E) ∈ interior ((∑ i, L i : ConvexBody E) : Set E) →
      HasPositiveVolumePolynomial μ L)
    (K : Fin n → ConvexBody E) (hpoly : ∀ i, IsFiniteHull (K i : Set E)) :
    HasPositiveVolumePolynomial μ K := by
  first
  | classical
    choose p hp using fun i => (K i).nonempty
    let L : Fin n → ConvexBody E := fun i => translateBody (-p i) (K i)
    have hzero : ∀ i, (0 : E) ∈ L i := fun i => zero_mem_translateBody_neg (hp i)
    have hfinite : ∀ i, IsFiniteHull (L i : Set E) :=
      fun i => isFiniteHull_translateBody (hpoly i) (-p i)
    have hL : HasPositiveVolumePolynomial μ L := by
      by_cases hfull : (interior ((∑ i, L i : ConvexBody E) : Set E)).Nonempty
      · obtain ⟨q, _, hqzero, hqfull⟩ := exists_centered_translates L hfull
        have hQ := hcenter (fun i => translateBody (-q i) (L i))
          (fun i => isFiniteHull_translateBody (hfinite i) (-q i)) hqzero hqfull
        have hback := HasPositiveVolumePolynomial.translate μ hQ (fun i => q i)
        simpa only [translateBody_translate, add_neg_cancel, translateBody_zero] using hback
      · exact hasPositiveVolumePolynomial_of_empty_interior μ L hzero
          (Set.not_nonempty_iff_eq_empty.mp hfull)
    have hback := HasPositiveVolumePolynomial.translate μ hL p
    simpa only [L, translateBody_translate, add_neg_cancel, translateBody_zero] using hback

end Measure
end VolumePolynomials
