module

public import wishart.verified.field_residual03
public import wishart.verified.extended_log_submean

/-!
# Products of logarithmically subharmonic row functions

This is the actual Gaussian-law form of Lemma 7.2.  Each factor is assumed
continuous and nonnegative only on its positive semidefinite Hermitian cone,
with a polynomial upper bound there.  Its scalar row sections satisfy the
extended logarithmic submean inequality, including the value minus infinity
at a zero.  Fixed compressions and positive semidefinite shifts are allowed.

The polynomial envelope and the submean inequality for the product are
conclusions of the proof.  The covariance factor may be rectangular or
singular; no rank condition enters the Gaussian phase argument.
-/

@[expose] public section

noncomputable section

open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder BigOperators Matrix.Norms.Frobenius

namespace Wishart.FieldGaussian

open WishartVerification

section PolynomialRows

variable (F : Type*) [NormedDivisionRing F] [StarRing F] [CStarRing F]

/-- The Frobenius norm of a one-row Gram matrix is the squared row norm,
over either of the fields used in the paper. -/
theorem frobenius_norm_rowGram {k : ℕ} (z : Row F k) :
    ‖rowGram F z‖ = ‖z‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [rowGram, Matrix.of_apply, norm_mul, norm_star, Real.rpow_two, mul_pow]
  rw [← Finset.sum_mul_sum, ← PiLp.norm_sq_eq_of_L2 (fun _ : Fin k => F) z]
  simpa only [← pow_two] using Real.sqrt_sq (sq_nonneg ‖z‖)

variable [InnerProductSpace ℝ F] [StarModule ℝ F]
  [FiniteDimensional ℝ F] [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]
  [MeasurableSpace F] [BorelSpace F]

/-- A fixed compressed Gram update has polynomial growth jointly in the
Gaussian row and the scalar displacement. -/
theorem polynomial_compressedHermitianRowUpdate_norm {m k : ℕ}
    (Q : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F))
    (B : Matrix (Fin m) (Fin k) F) (v : Row F m) :
    JointPolynomialBound (fun w : Row F m × F =>
      ‖compressedHermitianRowUpdate F Q B v w‖) := by
  have h := (JointPolynomialBound.const ‖Q‖).add
    ((polynomial_compressedRow_norm F B v).mul (polynomial_compressedRow_norm F B v))
  apply h.mono
  intro w
  rw [norm_norm, Real.norm_of_nonneg (by positivity)]
  change ‖(Q : Matrix (Fin k) (Fin k) F) +
    rowGram F (rowShift F (rowFactorCLM F B w.1) w.2 (rowFactorCLM F B v))‖ ≤ _
  rw [← rowFactor_rowShift]
  exact (norm_add_le _ _).trans_eq (by
    rw [frobenius_norm_rowGram]
    change ‖Q‖ + _ = _
    ring)

/-- A polynomial upper bound on the image cone gives the joint envelope
needed for Gaussian integration.  No off-cone bound is used. -/
theorem polynomial_comp_compressedHermitianRowUpdate {m k : ℕ}
    (S : Set (selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F)))
    (φ : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F) → ℝ)
    (hφ : ∀ X ∈ S, 0 ≤ φ X)
    (hbound : ∃ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ X ∈ S, φ X ≤ C * (1 + ‖X‖) ^ d)
    (Q : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F))
    (B : Matrix (Fin m) (Fin k) F) (v : Row F m)
    (himage : ∀ w, compressedHermitianRowUpdate F Q B v w ∈ S) :
    JointPolynomialBound (fun w => φ (compressedHermitianRowUpdate F Q B v w)) := by
  obtain ⟨d, C, hC, hb⟩ := hbound
  have hbase := (JointPolynomialBound.const 1).add
    (polynomial_compressedHermitianRowUpdate_norm F Q B v)
  have hpow := hbase.rpow (a := (d : ℝ)) (Nat.cast_nonneg d)
  have h := (JointPolynomialBound.const C).mul hpow
  apply h.mono
  intro w
  rw [Real.norm_of_nonneg (hφ _ (himage w)), Real.rpow_natCast,
    Real.norm_of_nonneg (by positivity)]
  exact hb _ (himage w)

end PolynomialRows

section ConeProducts

variable (F : Type*) [NormedDivisionRing F]
  [StarRing F] [CStarRing F] [InnerProductSpace ℝ F] [StarModule ℝ F]
  [FiniteDimensional ℝ F] [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]
  [MeasurableSpace F] [BorelSpace F]

/-- The common actual-law argument.  The concrete endpoints below take the
positive semidefinite cones and discharge their preservation by row updates. -/
theorem row_product_integrable_monotone_of_cone_hypotheses
    (hunit : ∀ a : F, ‖a‖ = 1 → a ∈ unitary F)
    {r m : ℕ} {ι : Type*} [Fintype ι]
    (R : Matrix (Fin r) (Fin m) F) (v : Row F m)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) F)
    (Q : ∀ i, selfAdjoint.submodule ℝ (Matrix (Fin (k i)) (Fin (k i)) F))
    (S : ∀ i, Set (selfAdjoint.submodule ℝ (Matrix (Fin (k i)) (Fin (k i)) F)))
    (φ : ∀ i, selfAdjoint.submodule ℝ (Matrix (Fin (k i)) (Fin (k i)) F) → ℝ)
    (hφ : ∀ i X, X ∈ S i → 0 ≤ φ i X)
    (hcont : ∀ i, ContinuousOn (φ i) (S i))
    (hbound : ∀ i, ∃ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ X ∈ S i, φ i X ≤ C * (1 + ‖X‖) ^ d)
    (himage : ∀ i z a, hermitianRowUpdate F (Q i)
      (rowFactorCLM F (B i) z) (rowFactorCLM F (B i) v) a ∈ S i)
    (hlog : ∀ i z, ExtendedLogSubmean (fun a : F => φ i
      (hermitianRowUpdate F (Q i) (rowFactorCLM F (B i) z)
        (rowFactorCLM F (B i) v) a))) :
    (∀ t : ℝ, Integrable (fun z => ∏ i,
      φ i (compressedRowGram F (Q i) (B i) (z + Real.sqrt t • v)))
      (gaussianRowWithFactor F R)) ∧
    MonotoneOn (fun t : ℝ => ∫ z, ∏ i,
      φ i (compressedRowGram F (Q i) (B i) (z + Real.sqrt t • v))
      ∂gaussianRowWithFactor F R) (Ici 0) := by
  let G : Row F m × F → ℝ := fun w => ∏ i,
    φ i (compressedHermitianRowUpdate F (Q i) (B i) v w)
  have hcontinuous : Continuous G := continuous_finsetProd _ fun i _ =>
    (hcont i).comp_continuous
      (continuous_compressedHermitianRowUpdate F (Q i) (B i) v)
      (fun w => himage i w.1 w.2)
  have hpoly : JointPolynomialBound G := JointPolynomialBound.finset_prod
    Finset.univ _ (fun i _ => polynomial_comp_compressedHermitianRowUpdate F
      (S i) (φ i) (hφ i) (hbound i) (Q i) (B i) v (fun w => himage i w.1 w.2))
  have hsub : ∀ z, BallSubmean (fun a : F => G (z, a)) := by
    intro z
    exact ExtendedLogSubmean.finset_prod_ballSubmean Finset.univ _ (fun i _ => hlog i z)
  have hphase : ∀ a b : F, ‖a‖ = ‖b‖ → ∃ T : Row F m ≃ᵐ Row F m,
      MeasurePreserving T (gaussianRowWithFactor F R) (gaussianRowWithFactor F R) ∧
        ∀ z, G (z, a) = G (T z, b) := by
    intro a b hab
    obtain ⟨u, hu⟩ := exists_unitary_mul_of_norm_eq hunit a b hab
    refine ⟨(rowPhase F u).toHomeomorph.toMeasurableEquiv,
      measurePreserving_rowPhase F R u, ?_⟩
    intro z
    rw [← hu]
    apply Finset.prod_congr rfl
    intro i hi
    exact congrArg (φ i)
      (compressedHermitianRowUpdate_phase F (Q i) (B i) z v u a).symm
  constructor
  · intro t
    have hint := integrable_polynomial_section (norm_allFiniteMoments F R)
      hcontinuous hpoly (Real.sqrt t • (1 : F))
    simpa only [G, compressedHermitianRowUpdate_real] using hint
  · have hmono := monotone_integral_sqrt_smul_of_polynomial_submean
      (norm_allFiniteMoments F R) hcontinuous hpoly
      (Filter.Eventually.of_forall hsub) hphase (1 : F)
    simpa only [G, compressedHermitianRowUpdate_real] using hmono

end ConeProducts

/-- The complex positive semidefinite Hermitian cone. -/
def complexPsdCone (k : ℕ) : Set (FieldSpectral.Hermitian ℂ k) :=
  {X | (X : Matrix (Fin k) (Fin k) ℂ).PosSemidef}

/-- The quaternion positive semidefinite Hermitian cone. -/
def quaternionPsdCone (k : ℕ) : Set (QuaternionMatrix.Hermitian k) :=
  {X | QuaternionMatrix.PosSemidef (X : Matrix (Fin k) (Fin k) ℍ[ℝ])}

/-- Lemma 7.2 for complex Gaussian rows, including singular covariance and
zero-valued factors.  All regularity and growth assumptions are restricted
to the positive semidefinite cone. -/
theorem complex_row_logsubharmonic_product {r m : ℕ} {ι : Type*} [Fintype ι]
    (R : Matrix (Fin r) (Fin m) ℂ) (v : Row ℂ m)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) ℂ)
    (Q : ∀ i, FieldSpectral.Hermitian ℂ (k i))
    (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (φ : ∀ i, FieldSpectral.Hermitian ℂ (k i) → ℝ)
    (hnonneg : ∀ i X, X ∈ complexPsdCone (k i) → 0 ≤ φ i X)
    (hcont : ∀ i, ContinuousOn (φ i) (complexPsdCone (k i)))
    (hbound : ∀ i, ∃ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ X ∈ complexPsdCone (k i), φ i X ≤ C * (1 + ‖X‖) ^ d)
    (hlog : ∀ i (A : FieldSpectral.Hermitian ℂ (k i)),
      (A : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef →
      ∀ a w : Row ℂ (k i), ExtendedLogSubmean (fun u : ℂ =>
        φ i (hermitianRowUpdate ℂ A a w u))) :
    (∀ t : ℝ, Integrable (fun z => ∏ i,
      φ i (compressedRowGram ℂ (Q i) (B i) (z + Real.sqrt t • v)))
      (gaussianRowWithFactor ℂ R)) ∧
    MonotoneOn (fun t : ℝ => ∫ z, ∏ i,
      φ i (compressedRowGram ℂ (Q i) (B i) (z + Real.sqrt t • v))
      ∂gaussianRowWithFactor ℂ R) (Ici 0) := by
  apply row_product_integrable_monotone_of_cone_hypotheses ℂ
    (fun _ => complex_mem_unitary_of_norm_one) R v k B Q
    (fun i => complexPsdCone (k i)) φ hnonneg hcont hbound
  · intro i z a
    exact complex_rowUpdate_posSemidef (Q i) (hQ i) _ _ a
  · intro i z
    exact hlog i (Q i) (hQ i) _ _

/-- Lemma 7.2 for quaternion Gaussian rows.  The left unit-scalar symmetry
is used before taking the Gram matrix, so the statement allows arbitrary
fixed quaternion compressions and singular covariance factors. -/
theorem quaternion_row_logsubharmonic_product {r m : ℕ} {ι : Type*} [Fintype ι]
    (R : Matrix (Fin r) (Fin m) ℍ[ℝ]) (v : Row ℍ[ℝ] m)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) ℍ[ℝ])
    (Q : ∀ i, QuaternionMatrix.Hermitian (k i))
    (hQ : ∀ i, QuaternionMatrix.PosSemidef
      (Q i : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ]))
    (φ : ∀ i, QuaternionMatrix.Hermitian (k i) → ℝ)
    (hnonneg : ∀ i X, X ∈ quaternionPsdCone (k i) → 0 ≤ φ i X)
    (hcont : ∀ i, ContinuousOn (φ i) (quaternionPsdCone (k i)))
    (hbound : ∀ i, ∃ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ X ∈ quaternionPsdCone (k i), φ i X ≤ C * (1 + ‖X‖) ^ d)
    (hlog : ∀ i (A : QuaternionMatrix.Hermitian (k i)),
      QuaternionMatrix.PosSemidef (A : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ]) →
      ∀ a w : Row ℍ[ℝ] (k i), ExtendedLogSubmean (fun u : ℍ[ℝ] =>
        φ i (hermitianRowUpdate ℍ[ℝ] A a w u))) :
    (∀ t : ℝ, Integrable (fun z => ∏ i,
      φ i (compressedRowGram ℍ[ℝ] (Q i) (B i) (z + Real.sqrt t • v)))
      (gaussianRowWithFactor ℍ[ℝ] R)) ∧
    MonotoneOn (fun t : ℝ => ∫ z, ∏ i,
      φ i (compressedRowGram ℍ[ℝ] (Q i) (B i) (z + Real.sqrt t • v))
      ∂gaussianRowWithFactor ℍ[ℝ] R) (Ici 0) := by
  apply row_product_integrable_monotone_of_cone_hypotheses ℍ[ℝ]
    (fun _ => quaternion_mem_unitary_of_norm_one) R v k B Q
    (fun i => quaternionPsdCone (k i)) φ hnonneg hcont hbound
  · intro i z a
    exact quaternion_rowUpdate_posSemidef (Q i) (hQ i) _ _ a
  · intro i z
    exact hlog i (Q i) (hQ i) _ _

end Wishart.FieldGaussian

end
