module
public import VolumePolynomials.BodyCentering
public import VolumePolynomials.FiniteBodyApproximation
public import VolumePolynomials.PolytopeVolumeDecomposition

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Polynomiality of volume and nonnegative mixed coefficients

The proof is induction on ambient dimension for arbitrary finite convex hulls,
using the actual facet/kernel decomposition. Finite-hull approximation and the
closed evaluation embedding then give the theorem for every tuple of nonempty
compact convex bodies. Degenerate bodies and zero weights are included.
-/

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials
open PolytopeGeometry

theorem finiteHull_hasPositiveVolumePolynomial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    {n : ℕ} (K : Fin n → ConvexBody E)
    (hpoly : ∀ i, IsFiniteHull (K i : Set E)) :
    HasPositiveVolumePolynomial volume K := by
  first
  | classical
    suffices ∀ d, finrank ℝ E = d → HasPositiveVolumePolynomial volume K from this _ rfl
    intro d hdim
    induction d using Nat.strong_induction_on generalizing E with
    | h d ih =>
      cases d with
      | zero =>
          letI : Subsingleton E := Module.finrank_zero_iff.mp hdim
          refine ⟨MvPolynomial.C (volume.real (Set.univ : Set E)), ?_,
            PolynomialNonnegativeCoefficients.C ENNReal.toReal_nonneg, ?_⟩
          · rw [hdim]
            exact MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ)
              (volume.real (Set.univ : Set E))
          · intro t _
            have hset : ((∑ i, t i • K i : ConvexBody E) : Set E) = Set.univ := by
              apply Set.eq_univ_of_forall
              intro x
              obtain ⟨y, hy⟩ := (∑ i, t i • K i : ConvexBody E).nonempty
              exact (Subsingleton.elim y x) ▸ hy
            rw [MvPolynomial.eval_C, hset]
      | succ d =>
          letI : Nontrivial E := Module.finrank_pos_iff.mp (by rw [hdim]; exact Nat.zero_lt_succ d)
          apply hasPositiveVolumePolynomial_of_centered_case volume ?_ K hpoly
          intro L hL hzero hinterior
          have hint : (0 : E) ∈ interior (∑ i, (L i : Set E)) := by
            simpa only [coe_sum_body] using hinterior
          obtain ⟨D⟩ := exists_centeredDecomposition L hL hzero hint
          have hd : ∀ i, finrank ℝ (D.kernel i) = d := by
            intro i
            exact Nat.add_right_cancel ((D.lower_finrank i).trans hdim)
          have hsmall : ∀ i, HasPositiveVolumePolynomial (D.lowerMeasure i) (D.lowerBody i) := by
            intro i
            letI : MeasureSpace (D.kernel i) := ⟨D.lowerMeasure i⟩
            letI : Measure.IsAddHaarMeasure (volume : Measure (D.kernel i)) := D.lowerMeasure_haar i
            exact ih d (Nat.lt_succ_self d) (K := D.lowerBody i)
              (hpoly := D.lowerBody_finite i) (hd i)
          choose q hqdegree hqcoeff hqvolume using hsmall
          apply hasPositiveVolumePolynomial_of_facets volume L d hdim D.constant
            (fun i => (D.constant_pos i).le) D.height D.height_nonneg q
            (fun i => (hd i) ▸ hqdegree i) hqcoeff
          intro t ht
          rw [D.volume_identity t ht]
          apply Finset.sum_congr rfl
          intro i _
          rw [hqvolume i t (fun j => (ht j).le)]
          congr 2
          exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

/-- Minkowski's volume polynomial for every tuple and every dimension, with
ordinary monomial coefficients nonnegative and no interior assumption. -/
theorem exists_nonnegative_volume_polynomial {n d : ℕ} (K : Fin n → Body d) :
    ∃ c : Coefficients n d, (∀ α, 0 ≤ c α) ∧ Realizes K c := by
  first
  | apply exists_nonnegative_realizes_of_all_finiteHulls n d _ K
    intro L hL
    exact (finiteHull_hasPositiveVolumePolynomial L hL).exists_realizes

theorem exists_volume_polynomial {n d : ℕ} (K : Fin n → Body d) :
    ∃ c : Coefficients n d, Realizes K c := by
  first
  | obtain ⟨c, _, hc⟩ := exists_nonnegative_volume_polynomial K
    exact ⟨c, hc⟩

theorem Realizes.coefficients_nonnegative {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (hc : Realizes K c) : ∀ α, 0 ≤ c α := by
  first
  | obtain ⟨c', hn, hc'⟩ := exists_nonnegative_volume_polynomial K
    rw [hc.unique hc']
    exact hn

theorem volumeLocus_coefficients_nonnegative {n d : ℕ} {c : Coefficients n d}
    (hc : c ∈ VolumeLocus n d) : ∀ α, 0 ≤ c α := by
  first
  | obtain ⟨K, hK⟩ := hc
    exact hK.coefficients_nonnegative

end VolumePolynomials
