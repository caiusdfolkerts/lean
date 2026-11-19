module
public import VolumePolynomials.BodyContinuity
public import VolumePolynomials.BodyOperations
public import VolumePolynomials.BodyTopology
public import VolumePolynomials.PolynomialCoordinates
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Order.DenselyOrdered

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Algebra and continuity for the facet induction

The polynomial constructed from facet heights has its ordinary monomial
coefficients nonnegative. Its geometric inputs are actual lower-dimensional
volume polynomials and an exact pyramid-volume decomposition. This module
proves the algebraic induction step, including extension from positive to
nonnegative weights; it does not assume or assert that facet data exist.
-/

open Set MeasureTheory Module MvPolynomial
open scoped BigOperators Topology Pointwise

namespace VolumePolynomials

def PolynomialNonnegativeCoefficients {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∀ m, 0 ≤ p.coeff m

theorem PolynomialNonnegativeCoefficients.zero {σ : Type*} :
    PolynomialNonnegativeCoefficients (0 : MvPolynomial σ ℝ) := by
  first
  | intro m
    simp

theorem PolynomialNonnegativeCoefficients.C {σ : Type*} {c : ℝ} (hc : 0 ≤ c) :
    PolynomialNonnegativeCoefficients (MvPolynomial.C c : MvPolynomial σ ℝ) := by
  first
  | classical
    intro m
    rw [MvPolynomial.coeff_C]
    split_ifs <;> first | exact hc | exact le_rfl

theorem PolynomialNonnegativeCoefficients.X {σ : Type*} (i : σ) :
    PolynomialNonnegativeCoefficients (MvPolynomial.X i : MvPolynomial σ ℝ) := by
  first
  | classical
    intro m
    rw [MvPolynomial.coeff_X]
    split_ifs <;> first | exact zero_le_one | exact le_rfl

theorem PolynomialNonnegativeCoefficients.mul {σ : Type*}
    {p q : MvPolynomial σ ℝ} (hp : PolynomialNonnegativeCoefficients p)
    (hq : PolynomialNonnegativeCoefficients q) : PolynomialNonnegativeCoefficients (p * q) := by
  first
  | classical
    intro m
    rw [MvPolynomial.coeff_mul]
    exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp a.1) (hq a.2))

theorem PolynomialNonnegativeCoefficients.sum {σ ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial σ ℝ) (hp : ∀ i, PolynomialNonnegativeCoefficients (p i)) :
    PolynomialNonnegativeCoefficients (∑ i, p i) := by
  first
  | intro m
    rw [MvPolynomial.coeff_sum]
    exact Finset.sum_nonneg (fun i _ => hp i m)

def heightPolynomial {n : ℕ} (h : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, MvPolynomial.C (h i) * MvPolynomial.X i

theorem heightPolynomial_homogeneous {n : ℕ} (h : Fin n → ℝ) :
    (heightPolynomial h).IsHomogeneous 1 :=
  MvPolynomial.IsHomogeneous.sum _ _ _
    (fun i _ => MvPolynomial.isHomogeneous_C_mul_X (h i) i)

theorem heightPolynomial_nonnegative {n : ℕ} {h : Fin n → ℝ} (hh : ∀ i, 0 ≤ h i) :
    PolynomialNonnegativeCoefficients (heightPolynomial h) :=
  PolynomialNonnegativeCoefficients.sum _ (fun i =>
    (PolynomialNonnegativeCoefficients.C (hh i)).mul
      (PolynomialNonnegativeCoefficients.X i))

@[simp] theorem eval_heightPolynomial {n : ℕ} (h t : Fin n → ℝ) :
    MvPolynomial.eval t (heightPolynomial h) = ∑ i, h i * t i := by
  first
  | simp only [heightPolynomial, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]

section Volume
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  {n : ℕ}

def HasPositiveVolumePolynomial (K : Fin n → ConvexBody E) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.IsHomogeneous (finrank ℝ E) ∧ PolynomialNonnegativeCoefficients p ∧
    ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) →
      MvPolynomial.eval t p = μ.real ((∑ i, t i • K i : ConvexBody E) : Set E)

theorem continuous_weight_volume (K : Fin n → ConvexBody E) :
    Continuous (fun t : Fin n → ℝ =>
      μ.real ((∑ i, t i • K i : ConvexBody E) : Set E)) :=
  (continuous_convexBody_realMeasure μ).comp (by fun_prop)

/-- Equality on strictly positive weights extends to every boundary face of the
closed positive orthant by continuity of actual convex-body volume. -/
theorem polynomial_volume_eq_of_positive (K : Fin n → ConvexBody E)
    (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ t : Fin n → ℝ, (∀ i, 0 < t i) →
      MvPolynomial.eval t p = μ.real ((∑ i, t i • K i : ConvexBody E) : Set E)) :
    ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) →
      MvPolynomial.eval t p = μ.real ((∑ i, t i • K i : ConvexBody E) : Set E) := by
  first
  | have hc := isClosed_eq p.continuous_eval (continuous_weight_volume μ K)
    have hsub : Set.pi Set.univ (fun _ : Fin n => Set.Ioi (0 : ℝ)) ⊆
        {t | MvPolynomial.eval t p = μ.real ((∑ i, t i • K i : ConvexBody E) : Set E)} := by
      intro t ht
      exact hp t (fun i => ht i (Set.mem_univ i))
    intro t ht
    apply closure_minimal hsub hc
    rw [closure_pi_set]
    intro i _
    rw [closure_Ioi]
    exact ht i

/-- A geometric facet decomposition produces the next homogeneous polynomial.
The lower-dimensional polynomials and the displayed volume identity are
explicit proof obligations; this lemma supplies only their algebraic assembly. -/
theorem hasPositiveVolumePolynomial_of_facets {ι : Type*} [Fintype ι]
    (K : Fin n → ConvexBody E) (d : ℕ) (hdim : finrank ℝ E = d + 1)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (h : ι → Fin n → ℝ)
    (hh : ∀ i j, 0 ≤ h i j) (q : ι → MvPolynomial (Fin n) ℝ)
    (hqdegree : ∀ i, (q i).IsHomogeneous d)
    (hqcoeff : ∀ i, PolynomialNonnegativeCoefficients (q i))
    (hvolume : ∀ t : Fin n → ℝ, (∀ j, 0 < t j) →
      μ.real ((∑ j, t j • K j : ConvexBody E) : Set E) =
        ∑ i, c i * (∑ j, h i j * t j) * MvPolynomial.eval t (q i)) :
    HasPositiveVolumePolynomial μ K := by
  first
  | let p : MvPolynomial (Fin n) ℝ :=
      ∑ i, MvPolynomial.C (c i) * (heightPolynomial (h i) * q i)
    refine ⟨p, ?_, ?_, polynomial_volume_eq_of_positive μ K p ?_⟩
    · rw [hdim]
      apply MvPolynomial.IsHomogeneous.sum
      intro i _
      simpa only [Nat.add_comm] using
        ((heightPolynomial_homogeneous (h i)).mul (hqdegree i)).C_mul (c i)
    · exact PolynomialNonnegativeCoefficients.sum _ (fun i =>
        (PolynomialNonnegativeCoefficients.C (hc i)).mul
          ((heightPolynomial_nonnegative (hh i)).mul (hqcoeff i)))
    · intro t ht
      rw [hvolume t ht]
      simp only [p, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
        MvPolynomial.eval_C, eval_heightPolynomial, mul_assoc]

/-- Independent body translations do not change the resulting polynomial. -/
theorem HasPositiveVolumePolynomial.translate {K : Fin n → ConvexBody E}
    (hK : HasPositiveVolumePolynomial μ K) (v : Fin n → E) :
    HasPositiveVolumePolynomial μ (fun i => translateBody (v i) (K i)) := by
  first
  | obtain ⟨p, hp, hn, hv⟩ := hK
    refine ⟨p, hp, hn, fun t ht => ?_⟩
    have hsum : (∑ i, t i • translateBody (v i) (K i)) =
        translateBody (∑ i, t i • v i) (∑ i, t i • K i) := by
      simp only [translateBody, smul_add, ← pointBody_smul, Finset.sum_add_distrib]
      congr 1
      exact (map_sum (pointBodyHom (E := E)) _ _).symm
    rw [hsum, coe_translateBody, Measure.real, measure_vadd]
    exact hv t ht

end Volume

/-- The generic Haar formulation gives the exact ordinary coefficient convention
used by the paper's realization locus. -/
theorem HasPositiveVolumePolynomial.exists_realizes {n d : ℕ}
    {K : Fin n → Body d} (hK : HasPositiveVolumePolynomial volume K) :
    ∃ c : Coefficients n d, (∀ α, 0 ≤ c α) ∧ Realizes K c := by
  first
  | obtain ⟨p, hp, hn, hv⟩ := hK
    have hd : p.IsHomogeneous d := by simpa [Space] using hp
    refine ⟨coefficientsOfPolynomial (d := d) p,
      (fun α => hn (exponent α)), realizes_of_homogeneous_polynomial K p hd ?_⟩
    exact hv

end VolumePolynomials
