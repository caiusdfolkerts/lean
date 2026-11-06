module

public import wishart.verified.field_row_logsubharmonic

@[expose] public section

/-!
# Literal statement gates for Lemma 7.2

The logarithmic hypothesis below is written as its extended submean
inequality, with value infinity for the nonnegative logarithmic defect at
a zero.  Continuity and nonnegativity of the scalar sections are derived
from the hypotheses on the positive semidefinite cone.  Neither product
submean nor an integrable dominating function is an input to these gates.
-/

noncomputable section

open Matrix MeasureTheory Set Wishart Wishart.FieldGaussian
open scoped Classical Quaternion ComplexOrder BigOperators ENNReal Matrix.Norms.Frobenius

namespace WishartAudit

theorem lemma_7_2_complex_literal {r m : ℕ} {ι : Type*} [Fintype ι]
    (R : Matrix (Fin r) (Fin m) ℂ) (v : Row ℂ m)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) ℂ)
    (Q : ∀ i, FieldSpectral.Hermitian ℂ (k i))
    (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (Φ : ∀ i, FieldSpectral.Hermitian ℂ (k i) → ℝ)
    (hnonneg : ∀ i (X : FieldSpectral.Hermitian ℂ (k i)),
      (X : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef → 0 ≤ Φ i X)
    (hcont : ∀ i, ContinuousOn (Φ i)
      {X | (X : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef})
    (hbound : ∀ i, ∃ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : FieldSpectral.Hermitian ℂ (k i),
        (X : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef →
          Φ i X ≤ C * (1 + ‖X‖) ^ d)
    (hlog : ∀ i (A : FieldSpectral.Hermitian ℂ (k i)),
      (A : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef →
      ∀ (a w : Row ℂ (k i)) (x : ℂ) (ρ : ℝ), 0 < ρ → ∀ M : ℝ,
        (∀ y ∈ Metric.ball x ρ, Φ i (hermitianRowUpdate ℂ A a w y) ≤ Real.exp M) →
        (⨍⁻ y in Metric.ball x ρ,
          (if Φ i (hermitianRowUpdate ℂ A a w y) = 0 then ∞
           else ENNReal.ofReal (M - Real.log (Φ i (hermitianRowUpdate ℂ A a w y))))
          ∂volume) ≤
        (if Φ i (hermitianRowUpdate ℂ A a w x) = 0 then ∞
         else ENNReal.ofReal (M - Real.log (Φ i (hermitianRowUpdate ℂ A a w x))))) :
    (∀ t : ℝ, Integrable (fun z => ∏ i,
      Φ i (compressedRowGram ℂ (Q i) (B i) (z + Real.sqrt t • v)))
      (gaussianRowWithFactor ℂ R)) ∧
    MonotoneOn (fun t : ℝ => ∫ z, ∏ i,
      Φ i (compressedRowGram ℂ (Q i) (B i) (z + Real.sqrt t • v))
      ∂gaussianRowWithFactor ℂ R) (Ici 0) := by
  apply complex_row_logsubharmonic_product R v k B Q hQ Φ hnonneg hcont hbound
  intro i A hA a w
  refine ⟨?_, ?_, ?_⟩
  · intro u
    exact hnonneg i _ (complex_rowUpdate_posSemidef A hA a w u)
  · exact (hcont i).comp_continuous (continuous_hermitianRowUpdate ℂ A a w)
      (fun u => complex_rowUpdate_posSemidef A hA a w u)
  · exact hlog i A hA a w

theorem lemma_7_2_quaternion_literal {r m : ℕ} {ι : Type*} [Fintype ι]
    (R : Matrix (Fin r) (Fin m) ℍ[ℝ]) (v : Row ℍ[ℝ] m)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) ℍ[ℝ])
    (Q : ∀ i, QuaternionMatrix.Hermitian (k i))
    (hQ : ∀ i, QuaternionMatrix.PosSemidef
      (Q i : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ]))
    (Φ : ∀ i, QuaternionMatrix.Hermitian (k i) → ℝ)
    (hnonneg : ∀ i (X : QuaternionMatrix.Hermitian (k i)), QuaternionMatrix.PosSemidef
      (X : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ]) → 0 ≤ Φ i X)
    (hcont : ∀ i, ContinuousOn (Φ i)
      {X | QuaternionMatrix.PosSemidef (X : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ])})
    (hbound : ∀ i, ∃ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : QuaternionMatrix.Hermitian (k i),
        QuaternionMatrix.PosSemidef (X : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ]) →
          Φ i X ≤ C * (1 + ‖X‖) ^ d)
    (hlog : ∀ i (A : QuaternionMatrix.Hermitian (k i)),
      QuaternionMatrix.PosSemidef (A : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ]) →
      ∀ (a w : Row ℍ[ℝ] (k i)) (x : ℍ[ℝ]) (ρ : ℝ), 0 < ρ → ∀ M : ℝ,
        (∀ y ∈ Metric.ball x ρ,
          Φ i (hermitianRowUpdate ℍ[ℝ] A a w y) ≤ Real.exp M) →
        (⨍⁻ y in Metric.ball x ρ,
          (if Φ i (hermitianRowUpdate ℍ[ℝ] A a w y) = 0 then ∞
           else ENNReal.ofReal
             (M - Real.log (Φ i (hermitianRowUpdate ℍ[ℝ] A a w y)))) ∂volume) ≤
        (if Φ i (hermitianRowUpdate ℍ[ℝ] A a w x) = 0 then ∞
         else ENNReal.ofReal (M - Real.log (Φ i (hermitianRowUpdate ℍ[ℝ] A a w x))))) :
    (∀ t : ℝ, Integrable (fun z => ∏ i,
      Φ i (compressedRowGram ℍ[ℝ] (Q i) (B i) (z + Real.sqrt t • v)))
      (gaussianRowWithFactor ℍ[ℝ] R)) ∧
    MonotoneOn (fun t : ℝ => ∫ z, ∏ i,
      Φ i (compressedRowGram ℍ[ℝ] (Q i) (B i) (z + Real.sqrt t • v))
      ∂gaussianRowWithFactor ℍ[ℝ] R) (Ici 0) := by
  apply quaternion_row_logsubharmonic_product R v k B Q hQ Φ hnonneg hcont hbound
  intro i A hA a w
  refine ⟨?_, ?_, ?_⟩
  · intro u
    exact hnonneg i _ (quaternion_rowUpdate_posSemidef A hA a w u)
  · exact (hcont i).comp_continuous (continuous_hermitianRowUpdate ℍ[ℝ] A a w)
      (fun u => quaternion_rowUpdate_posSemidef A hA a w u)
  · exact hlog i A hA a w

end WishartAudit

end
