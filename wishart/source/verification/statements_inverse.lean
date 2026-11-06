module

public import wishart.verified.real_tail01

@[expose] public section

noncomputable section

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification Wishart
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace WishartAudit

/- Literal targets for Corollary 6.2. The exact-threshold target makes the
positive-active-rank convention explicit. The PDF's necessity proof needs
this condition; the separate zero-column audit explains why it cannot be
silently omitted when Lean dimensions include zero. -/

def InverseDeterminantProductStatement : Prop :=
  ∀ {p d : ℕ} {β : ℝ} {Omega : Matrix (Fin p) (Fin p) ℝ}
    (hOmega : Omega.PosDef) (hβ : (p : ℝ) - 1 < β)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hrange : ((∀ i, 0 ≤ ν i) ∧ 2 * (∑ i, ν i) < β - p + 1) ∨
      (∀ i, ν i ≤ 0)),
    (∀ J : Finset (Fin d), Integrable (inverseDeterminantProduct Omega k B c ν J)
      (inverseWishartMeasure β Omega)) ∧
    (∏ i, inverseDeterminantMoment β Omega k B c ν {i}) ≤
      inverseDeterminantMoment β Omega k B c ν Finset.univ ∧
    ∀ j : Fin d,
      (∏ i, inverseDeterminantMoment β Omega k B c ν {i}) ≤
        inverseDeterminantMoment β Omega k B c ν {j} *
          inverseDeterminantMoment β Omega k B c ν (Finset.univ.erase j) ∧
      inverseDeterminantMoment β Omega k B c ν {j} *
          inverseDeterminantMoment β Omega k B c ν (Finset.univ.erase j) ≤
        inverseDeterminantMoment β Omega k B c ν Finset.univ

theorem inverse_determinant_product_exact : InverseDeterminantProductStatement :=
  @Wishart.corollary_6_2

def InverseDeterminantExactMomentStatement : Prop :=
  ∀ {p d : ℕ} {β : ℝ} {Omega : Matrix (Fin p) (Fin p) ℝ}
    (hOmega : Omega.PosDef) (hβ : (p : ℝ) - 1 < β)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    (hactive : ∀ i, 0 < ν i → 0 < k i),
    Integrable (inverseDeterminantProduct Omega k B c ν Finset.univ)
      (inverseWishartMeasure β Omega) ↔
      2 * (∑ i, ν i) < β - p + 1

theorem inverse_determinant_moment_exact : InverseDeterminantExactMomentStatement :=
  @Wishart.corollary_6_2_finite_moment_iff

def InverseDeterminantGammaMomentStatement : Prop :=
  ∀ {p k : ℕ} {β r : ℝ} {Omega : Matrix (Fin p) (Fin p) ℝ}
    (hOmega : Omega.PosDef) (hβ : (p : ℝ) - 1 < β)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k)
    (hr : 2 * r < β - p + 1),
    (∫ Y : Wishart.SymmetricMatrix p,
      (Bᵀ * (Y : Matrix (Fin p) (Fin p) ℝ) * B).det ^ r
        ∂inverseWishartMeasure β Omega) =
      (compressionScale Omega B).det ^ r * (2 : ℝ) ^ (-(k : ℝ) * r) *
        (multivariateGamma k ((β - p + k) / 2 - r) /
          multivariateGamma k ((β - p + k) / 2))

theorem inverse_determinant_gamma_exact : InverseDeterminantGammaMomentStatement :=
  @Wishart.corollary_6_2_gamma_moment

/-- The corrected exact threshold includes all column dimensions. -/
theorem inverse_all_rank_moment_exact
    {p d : ℕ} {β : ℝ} {Omega : Matrix (Fin p) (Fin p) ℝ}
    (hOmega : Omega.PosDef) (hβ : (p : ℝ) - 1 < β)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (c ν : Fin d → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i) :
    Integrable (inverseDeterminantProduct Omega k B c ν Finset.univ)
      (inverseWishartMeasure β Omega) ↔
      2 * (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < k i), ν i) < β - p + 1 :=
  Wishart.corollary_6_2_finite_moment_iff_positive_ranks hOmega hβ k B hB c ν hc hν

/-- The inverse-Wishart gamma identity on its complete all-rank domain. -/
theorem inverse_all_rank_gamma_exact
    {p k : ℕ} {β r : ℝ} {Omega : Matrix (Fin p) (Fin p) ℝ}
    (hOmega : Omega.PosDef) (hβ : (p : ℝ) - 1 < β)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k)
    (hr : k = 0 ∨ 2 * r < β - p + 1) :
    (∫ Y : Wishart.SymmetricMatrix p,
      (Bᵀ * (Y : Matrix (Fin p) (Fin p) ℝ) * B).det ^ r
        ∂inverseWishartMeasure β Omega) =
      (compressionScale Omega B).det ^ r * (2 : ℝ) ^ (-(k : ℝ) * r) *
        (multivariateGamma k ((β - p + k) / 2 - r) /
          multivariateGamma k ((β - p + k) / 2)) :=
  Wishart.corollary_6_2_gamma_moment_effective_rank hOmega hβ B hB hr


end WishartAudit
