module

public import wishart.verified.lemma_3_3

@[expose] public section

/-!
# Literal partition statement for Lemma 3.3

The partition is given by its nonempty blocks and unique-membership property.
The integrands below display the actual principal submatrices of
`A + W + (z + sqrt(t) v)(z + sqrt(t) v)ᵀ`, under the independent Wishart and
Gaussian product measure.  The only shape condition is `N > m`.
-/

noncomputable section

open Matrix MeasureTheory ProbabilityTheory TauCeti.Probability Set WishartVerification
open scoped Classical BigOperators

namespace WishartAudit

theorem lemma_3_3_literal {m d : ℕ} {N : ℝ}
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef) (hN : (m : ℝ) < N)
    (A : SymmetricMatrix m) (hA : (A : Matrix (Fin m) (Fin m) ℝ).PosSemidef)
    (J : Fin d → Finset (Fin m)) (hJnonempty : ∀ i, (J i).Nonempty)
    (hJpartition : ∀ a : Fin m, ∃! i : Fin d, a ∈ J i)
    (η : Fin d → ℝ) (hη : ∀ i, 0 ≤ η i) (v : EuclideanSpace ℝ (Fin m)) :
    (∀ t : ℝ, Integrable (fun Y : SymmetricMatrix m × EuclideanSpace ℝ (Fin m) =>
      ∏ i, (((A : Matrix (Fin m) (Fin m) ℝ) + Y.1 +
        Matrix.vecMulVec (Y.2 + Real.sqrt t • v).ofLp (Y.2 + Real.sqrt t • v).ofLp).submatrix
          (fun a : J i => (a : Fin m)) (fun a : J i => (a : Fin m))).det ^ η i)
      ((nonsingularWishartMeasure (N - 1) C).prod (multivariateGaussian 0 C))) ∧
    MonotoneOn (fun t : ℝ => ∫ Y : SymmetricMatrix m × EuclideanSpace ℝ (Fin m),
      ∏ i, (((A : Matrix (Fin m) (Fin m) ℝ) + Y.1 +
        Matrix.vecMulVec (Y.2 + Real.sqrt t • v).ofLp (Y.2 + Real.sqrt t • v).ofLp).submatrix
          (fun a : J i => (a : Fin m)) (fun a : J i => (a : Fin m))).det ^ η i
      ∂(nonsingularWishartMeasure (N - 1) C).prod (multivariateGaussian 0 C)) (Ici 0) := by
  simpa only [principalMinor, radialInput, Submodule.coe_add, coe_rankOneSymmetric, add_assoc]
    using lemma_3_3 (⟨J, hJnonempty, hJpartition⟩ : PrincipalPartition m d)
      hC hN A hA η hη v

theorem lemma_3_3_single_block_strict_literal {m : ℕ} {N : ℝ}
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef) (hN : (m : ℝ) < N)
    (A : SymmetricMatrix m) (hA : (A : Matrix (Fin m) (Fin m) ℝ).PosSemidef)
    {η : ℝ} (hη : 0 < η) {v : EuclideanSpace ℝ (Fin m)} (hv : v ≠ 0) :
    StrictMonoOn (fun t : ℝ => ∫ Y : SymmetricMatrix m × EuclideanSpace ℝ (Fin m),
      ((A : Matrix (Fin m) (Fin m) ℝ) + Y.1 +
        Matrix.vecMulVec (Y.2 + Real.sqrt t • v).ofLp (Y.2 + Real.sqrt t • v).ofLp).det ^ η
      ∂(nonsingularWishartMeasure (N - 1) C).prod (multivariateGaussian 0 C)) (Ici 0) := by
  simpa only [radialInput, Submodule.coe_add, coe_rankOneSymmetric, add_assoc]
    using strictMonoOn_radial_full_determinant hC hN A hA hv hη

end WishartAudit

end
