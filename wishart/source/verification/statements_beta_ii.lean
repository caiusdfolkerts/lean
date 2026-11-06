module

public import wishart.verified.real_tail01

@[expose] public section

/-!
# Independent literal targets for density (19) and Theorem 6.3

These targets write the density, the actual hierarchy, the logarithmic outer
function conditions and the almost-sure retained-rank condition explicitly.
The rank condition is the permutation-invariant triple formulation proved
equivalent to the largest-plus-third-largest condition. The assignments below
check these literal statements against the proved declarations.
-/

noncomputable section

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open WishartVerification.MomentAssembly
open scoped Classical BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace WishartVerification.Audit

/-- The literal density (19), including its normalizer and probability mass.
The original declaration name is retained for checkpoint compatibility. -/
theorem betaII_density_eighteen_normalized {p : ℕ} {α β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β) :
    IsProbabilityMeasure (Wishart.matrixBetaIIMeasure α β Omega) ∧
    Wishart.matrixBetaIIMeasure α β Omega =
      (symmetricLebesgue p).withDensity (fun X : WishartVerification.SymmetricMatrix p ↦
        ENNReal.ofReal (if (X : Matrix (Fin p) (Fin p) ℝ).PosDef then
          (multivariateGamma p ((α + β) / 2) /
            (multivariateGamma p (α / 2) * multivariateGamma p (β / 2)) *
              Omega.det ^ (β / 2)) *
            (X : Matrix (Fin p) (Fin p) ℝ).det ^ ((α - p - 1) / 2) *
              (Omega + (X : Matrix (Fin p) (Fin p) ℝ)).det ^ (-((α + β) / 2))
          else 0)) :=
  ⟨Wishart.isProbabilityMeasure_matrixBetaIIMeasure hOmega hα hβ, rfl⟩

alias betaII_density_nineteen_normalized := betaII_density_eighteen_normalized

/-- The density is strictly positive exactly on the positive definite cone.
This prevents the rank test from treating a factor as constant merely because
the probability law had lost some part of its intended support. -/
theorem betaII_density_positive_exactly_on_cone {p : ℕ} {α β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (X : WishartVerification.SymmetricMatrix p) :
    0 < Wishart.matrixBetaIIPDF α β Omega X ↔
      (X : Matrix (Fin p) (Fin p) ℝ).PosDef :=
  Wishart.matrixBetaIIPDF_pos_iff hOmega hα hβ X

/-- Almost-sure constancy under the actual beta-II density agrees with
constancy on every positive definite matrix. All continuity needed for this
equivalence is derived from the displayed geometric hypotheses. -/
theorem betaII_ae_constant_iff_on_positive_cone {p d : ℕ} {α β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (f : Fin d → ℝ → ℝ)
    (hpos : ∀ i t, 0 < t → 0 < f i t)
    (hconvex : ∀ i, ConvexOn ℝ Set.univ (fun t ↦ Real.log (f i (Real.exp t))))
    (hmono : ∀ i, Monotone (fun t ↦ Real.log (f i (Real.exp t))))
    (i : Fin d) :
    (∃ c : ℝ, ∀ᵐ X : WishartVerification.SymmetricMatrix p
        ∂Wishart.matrixBetaIIMeasure α β Omega,
      f i ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det = c) ↔
    ∃ c : ℝ, ∀ X : WishartVerification.SymmetricMatrix p,
      (X : Matrix (Fin p) (Fin p) ℝ).PosDef →
        f i ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det = c := by
  let hf (j : Fin d) : GeometricallyLogConvex (f j) :=
    ⟨hpos j, hconvex j, hmono j⟩
  simpa only [Wishart.GeometricCompressionFamily.ConstantFactor,
    Wishart.betaIIGeometricFamily_factor] using
      (Wishart.betaIIGeometricFamily_constantFactor_iff_ae_constant
        hOmega hα hβ k B hB f hf i).symm

/-- The explicit triple condition in the product target is exactly the
largest-plus-third-largest condition, and is vacuous for at most two retained
factors. The descending list is a permutation of precisely `A`. -/
theorem betaII_rank_condition_exact {p d : ℕ} (k : Fin d → ℕ)
    (A : Finset (Fin d)) (α : ℝ) :
    (∀ h : 3 ≤ Fintype.card A,
      min ((descendingRanks k A ⟨0, by omega⟩ : ℝ) +
        descendingRanks k A ⟨2, by omega⟩) ((p : ℝ) + 1) ≤ α) ↔
    (∀ i ∈ A, ∀ j ∈ A, ∀ l ∈ A,
      i ≠ j → i ≠ l → j ≠ l → k i ≤ k j → k i ≤ k l →
        min ((k i : ℝ) + k j) ((p : ℝ) + 1) ≤ α) :=
  orderedRankThreshold_iff k A p α

/-- Both the conditional hierarchy and its independent congruence realization
are equalities of the actual density-defined probability measures. -/
theorem betaII_actual_hierarchy_and_independent_congruence {p : ℕ} {α β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β) :
    Wishart.matrixBetaIIMeasure α β Omega =
      (inverseWishartMeasure β Omega).bind
        (fun Y : WishartVerification.SymmetricMatrix p ↦
          nonsingularWishartMeasure α (Y : Matrix (Fin p) (Fin p) ℝ)) ∧
    ((inverseWishartMeasure β Omega).prod
      (nonsingularWishartMeasure α (1 : Matrix (Fin p) (Fin p) ℝ))).map
        (fun z : WishartVerification.SymmetricMatrix p × WishartVerification.SymmetricMatrix p ↦
          Matrix.symmetricCongruenceLinearMap
            (CFC.sqrt (z.1 : Matrix (Fin p) (Fin p) ℝ)) z.2) =
      Wishart.matrixBetaIIMeasure α β Omega :=
  ⟨Wishart.matrixBetaIIMeasure_eq_bind hOmega hα hβ,
    Wishart.map_matrixBetaIISample hOmega hα hβ⟩

/-- Every active proper triple satisfies the exact rank bound; equivalently,
after removing the actual almost-sure constants and full-rank factors, at most
two factors remain or the largest-plus-third-largest bound holds. -/
theorem betaII_product_complete_ae_rank {p d : ℕ} {α β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (f : Fin d → ℝ → ℝ)
    (hpos : ∀ i t, 0 < t → 0 < f i t)
    (hconvex : ∀ i, ConvexOn ℝ Set.univ (fun t ↦ Real.log (f i (Real.exp t))))
    (hmono : ∀ i, Monotone (fun t ↦ Real.log (f i (Real.exp t))))
    (hrank : ∀ i j l : Fin d, k i < p → k j < p → k l < p →
      (¬ ∃ c : ℝ, ∀ᵐ X : WishartVerification.SymmetricMatrix p
        ∂Wishart.matrixBetaIIMeasure α β Omega,
          f i ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det = c) →
      (¬ ∃ c : ℝ, ∀ᵐ X : WishartVerification.SymmetricMatrix p
        ∂Wishart.matrixBetaIIMeasure α β Omega,
          f j ((B j)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B j).det = c) →
      (¬ ∃ c : ℝ, ∀ᵐ X : WishartVerification.SymmetricMatrix p
        ∂Wishart.matrixBetaIIMeasure α β Omega,
          f l ((B l)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B l).det = c) →
      i ≠ j → i ≠ l → j ≠ l → k i ≤ k j → k i ≤ k l →
        min ((k i : ℝ) + k j) ((p : ℝ) + 1) ≤ α)
    (J : Finset (Fin d)) :
    (∏ i ∈ J, ∫⁻ X : WishartVerification.SymmetricMatrix p,
      ENNReal.ofReal (f i ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det)
        ∂Wishart.matrixBetaIIMeasure α β Omega) ≤
      ∫⁻ X : WishartVerification.SymmetricMatrix p,
        ENNReal.ofReal (∏ i ∈ J,
          f i ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det)
            ∂Wishart.matrixBetaIIMeasure α β Omega := by
  let hf (i : Fin d) : GeometricallyLogConvex (f i) :=
    ⟨hpos i, hconvex i, hmono i⟩
  apply Wishart.theorem_6_3_ae_constant_rank hOmega hα hβ k B hB f hf _ J
  apply (orderedRankThreshold_iff _ _ _ _).mpr
  intro i hi j hj l hl hij hil hjl hrij hril
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj hl
  exact hrank i j l hi.1 hj.1 hl.1 hi.2 hj.2 hl.2 hij hil hjl hrij hril

/-- Disjoint principal blocks, including empty blocks, impose no condition
beyond the two admissible degrees. Their determinants are actual submatrices;
an empty block contributes its constant value `f i 1`. -/
theorem betaII_disjoint_principal_blocks_all_shapes {p d : ℕ} {α β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (I : Fin d → Finset (Fin p))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (I i) (I j)))
    (f : Fin d → ℝ → ℝ) (hpos : ∀ i t, 0 < t → 0 < f i t)
    (hconvex : ∀ i, ConvexOn ℝ Set.univ (fun t ↦ Real.log (f i (Real.exp t))))
    (hmono : ∀ i, Monotone (fun t ↦ Real.log (f i (Real.exp t))))
    (J : Finset (Fin d)) :
    (∏ i ∈ J, ∫⁻ X : WishartVerification.SymmetricMatrix p,
      ENNReal.ofReal (f i ((X : Matrix (Fin p) (Fin p) ℝ).submatrix
        (fun a : I i ↦ (a : Fin p)) (fun a : I i ↦ (a : Fin p))).det)
          ∂Wishart.matrixBetaIIMeasure α β Omega) ≤
      ∫⁻ X : WishartVerification.SymmetricMatrix p,
        ENNReal.ofReal (∏ i ∈ J,
          f i ((X : Matrix (Fin p) (Fin p) ℝ).submatrix
            (fun a : I i ↦ (a : Fin p)) (fun a : I i ↦ (a : Fin p))).det)
              ∂Wishart.matrixBetaIIMeasure α β Omega := by
  exact Wishart.theorem_6_3_disjoint_principal_blocks_allow_empty hOmega hα hβ I hdisjoint f
    (fun i ↦ ⟨hpos i, hconvex i, hmono i⟩) J



end WishartVerification.Audit
