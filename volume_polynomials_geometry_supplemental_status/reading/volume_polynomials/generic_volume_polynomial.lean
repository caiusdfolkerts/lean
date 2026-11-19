module

public import VolumePolynomials.VolumePolynomialExistence
public import VolumePolynomials.RealizationContinuity
public import VolumePolynomials.LinearFrame
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# Volume polynomials in arbitrary finite-dimensional Haar spaces

An actual continuous linear coordinate equivalence transports a compact
convex tuple to the coordinate space. Haar uniqueness supplies its positive
volume factor. Thus the coordinate-space existence theorem gives the same
polynomial theorem for every specified additive Haar measure.
-/

open Set MeasureTheory Module MvPolynomial
open scoped BigOperators Pointwise

namespace VolumePolynomials

theorem polynomialNonnegativeCoefficients_coefficientPolynomial {n d : ℕ}
    {c : Coefficients n d} (hc : ∀ α, 0 ≤ c α) :
    PolynomialNonnegativeCoefficients (coefficientPolynomial c) := by
  first
  | classical
    intro m
    simp only [coefficientPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    apply Finset.sum_nonneg
    intro α _
    split_ifs <;> first | exact hc α | exact le_rfl

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- General Minkowski polynomiality, with a specified actual Haar measure
and no full-dimensionality assumption on any of the bodies. -/
theorem hasPositiveVolumePolynomial {n : ℕ} (K : Fin n → ConvexBody E) :
    HasPositiveVolumePolynomial μ K := by
  first
  | letI : MeasureSpace E := ⟨μ⟩
    letI : Measure.IsAddHaarMeasure (volume : Measure E) :=
      inferInstanceAs (Measure.IsAddHaarMeasure μ)
    let e : E ≃L[ℝ] Space (finrank ℝ E) := (Module.finBasis ℝ E).equivFunL
    let L : Fin n → Body (finrank ℝ E) := fun i => mapBody e.toContinuousLinearMap (K i)
    obtain ⟨c, hc, hreal⟩ := exists_nonnegative_volume_polynomial L
    let q := coefficientPolynomial c
    let a : ℝ := LinearFrame.volumeFactor e
    have ha : 0 ≤ a := NNReal.coe_nonneg _
    refine ⟨C a * q, (coefficientPolynomial_homogeneous c).C_mul a,
      (PolynomialNonnegativeCoefficients.C ha).mul
        (polynomialNonnegativeCoefficients_coefficientPolynomial hc), ?_⟩
    intro t ht
    have hm : (∑ i, t i • L i) = mapBody e.toContinuousLinearMap (∑ i, t i • K i) := by
      first
      | rw [show mapBody e.toContinuousLinearMap (∑ i, t i • K i) =
          ∑ i, mapBody e.toContinuousLinearMap (t i • K i) from
            map_sum (mapBodyHom e.toContinuousLinearMap) _ _]
        simp only [L, mapBody_smul]
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C]
    change a * MvPolynomial.eval t (coefficientPolynomial c) = _
    rw [← evaluate_eq_polynomial_eval, hreal t ht]
    change a * volume.real
      ((∑ i, t i • L i : ConvexBody (Space (finrank ℝ E))) : Set (Space (finrank ℝ E))) = _
    rw [hm, coe_mapBody]
    exact (LinearFrame.realVolume_eq_factor_mul_image e
      ((∑ i, t i • K i : ConvexBody E) : Set E)).symm

def volumePolynomial {n : ℕ} (K : Fin n → ConvexBody E) : MvPolynomial (Fin n) ℝ :=
  Classical.choose (hasPositiveVolumePolynomial μ K)

theorem volumePolynomial_homogeneous {n : ℕ} (K : Fin n → ConvexBody E) :
    (volumePolynomial μ K).IsHomogeneous (finrank ℝ E) :=
  (Classical.choose_spec (hasPositiveVolumePolynomial μ K)).1

theorem volumePolynomial_nonnegative {n : ℕ} (K : Fin n → ConvexBody E) :
    PolynomialNonnegativeCoefficients (volumePolynomial μ K) :=
  (Classical.choose_spec (hasPositiveVolumePolynomial μ K)).2.1

theorem volumePolynomial_eval {n : ℕ} (K : Fin n → ConvexBody E)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) :
    MvPolynomial.eval t (volumePolynomial μ K) =
      μ.real ((∑ i, t i • K i : ConvexBody E) : Set E) :=
  (Classical.choose_spec (hasPositiveVolumePolynomial μ K)).2.2 t ht

/-- The polynomial is unique from its values on the whole nonnegative
orthant. No assumed coefficient identity is used. -/
theorem volumePolynomial_eq_of_eval {n : ℕ} (K : Fin n → ConvexBody E)
    (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) →
      MvPolynomial.eval t p = μ.real ((∑ i, t i • K i : ConvexBody E) : Set E)) :
    volumePolynomial μ K = p := by
  first
  | apply MvPolynomial.funext_set (fun _ => Ici (0 : ℝ)) (fun _ => Ici_infinite 0)
    intro t ht
    exact (volumePolynomial_eval μ K t (fun i => ht i (mem_univ i))).trans
      (hp t (fun i => ht i (mem_univ i))).symm

def genericCoefficientMap {n : ℕ} (K : Fin n → ConvexBody E) :
    Coefficients n (finrank ℝ E) := coefficientsOfPolynomial (volumePolynomial μ K)

theorem coefficientPolynomial_genericCoefficientMap {n : ℕ} (K : Fin n → ConvexBody E) :
    coefficientPolynomial (genericCoefficientMap μ K) = volumePolynomial μ K :=
  coefficientPolynomial_coefficientsOfPolynomial _ (volumePolynomial_homogeneous μ K)

theorem evaluate_genericCoefficientMap {n : ℕ} (K : Fin n → ConvexBody E)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) :
    evaluate (genericCoefficientMap μ K) t =
      μ.real ((∑ i, t i • K i : ConvexBody E) : Set E) := by
  first
  | rw [evaluate_eq_polynomial_eval, coefficientPolynomial_genericCoefficientMap]
    exact volumePolynomial_eval μ K t ht

theorem continuous_genericCoefficientMap (n : ℕ) :
    Continuous (genericCoefficientMap μ (n := n)) := by
  first
  | apply (isClosedEmbedding_evaluation n (finrank ℝ E)).isEmbedding.continuous_iff.mpr
    apply continuous_pi
    intro t
    have heq : (fun K : Fin n → ConvexBody E =>
        evaluationEmbedding n (finrank ℝ E) (genericCoefficientMap μ K) t) =
        (fun K => μ.real ((∑ i, t.1 i • K i : ConvexBody E) : Set E)) := by
      first
      | funext K
        exact evaluate_genericCoefficientMap μ K t.1 t.2
    change Continuous (fun K : Fin n → ConvexBody E =>
      evaluationEmbedding n (finrank ℝ E) (genericCoefficientMap μ K) t)
    rw [heq]
    exact (continuous_convexBody_realMeasure μ).comp (by fun_prop)

theorem continuous_volumePolynomial_coeff {n : ℕ} (m : Fin n →₀ ℕ) :
    Continuous (fun K : Fin n → ConvexBody E => (volumePolynomial μ K).coeff m) := by
  first
  | have heq : (fun K : Fin n → ConvexBody E => (volumePolynomial μ K).coeff m) =
        (fun K => (coefficientPolynomial (genericCoefficientMap μ K)).coeff m) := by
      first
      | funext K
        rw [coefficientPolynomial_genericCoefficientMap]
    rw [heq]
    classical
    simp only [coefficientPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    apply continuous_finsetSum Finset.univ
    intro α _
    split_ifs
    · exact (continuous_apply α).comp (continuous_genericCoefficientMap μ n)
    · exact continuous_const

theorem volumePolynomial_translate {n : ℕ} (K : Fin n → ConvexBody E) (v : Fin n → E) :
    volumePolynomial μ (fun i => translateBody (v i) (K i)) = volumePolynomial μ K := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [volumePolynomial_eval μ K t ht]
    have hsum : (∑ i, t i • translateBody (v i) (K i)) =
        translateBody (∑ i, t i • v i) (∑ i, t i • K i) := by
      first
      | simp only [translateBody, smul_add, ← pointBody_smul, Finset.sum_add_distrib]
        congr 1
        exact (map_sum (pointBodyHom (E := E)) (fun i => t i • v i) Finset.univ).symm
    rw [hsum, coe_translateBody]
    simp only [measureReal_def, measure_vadd]

end Generic
end VolumePolynomials
