module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# A literal canonical-only component of the Wishart statement translation

This source-only component is not a replacement for the full frozen Challenge.
It explicitly retains the upper-triangular unit-cube normalization of Lebesgue
measure, every real degree and scale, both invalid-parameter branches, and the
totalized matrix inverse. No Tau Ceti import or unspecified measure is used.
Canonical elaboration and the actual source equality bridges remain pending.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal Matrix

namespace WishartLiteralLaws

/-- The same self-adjoint carrier and all on-or-above-diagonal coordinates. -/
abbrev SymmetricMatrix (p : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)
abbrev UpperTriangle (p : ℕ) := {ij : Fin p × Fin p // ij.1 ≤ ij.2}

/-- Reflection of the supplied upper-triangular entries, including the diagonal. -/
def mirrorMatrix {p : ℕ} (x : UpperTriangle p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j =>
    if h : i ≤ j then x ⟨(i, j), h⟩ else x ⟨(j, i), le_of_not_ge h⟩

/-- Genuine symmetry of the completely specified reflection formula. -/
theorem mirror_isHermitian {p : ℕ} (x : UpperTriangle p → ℝ) :
    (mirrorMatrix x).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [mirrorMatrix, Matrix.of_apply, star_trivial]
  rcases le_total i j with h | h
  · rcases h.lt_or_eq with hlt | rfl
    · rw [dite_eq_right (not_le.2 hlt), dite_eq_left h]
    · rfl
  · rcases h.lt_or_eq with hlt | rfl
    · rw [dite_eq_left h, dite_eq_right (not_le.2 hlt)]
    · rfl

/-- The literal coordinate reconstruction as an actual symmetric matrix. -/
def reconstruct {p : ℕ} (x : UpperTriangle p → ℝ) : SymmetricMatrix p :=
  ⟨mirrorMatrix x, mirror_isHermitian x⟩

/-- The upper-triangle coordinate cube has measure one; Frobenius volume or
an unspecified Haar normalization is not substituted. -/
def symmetricLebesgue (p : ℕ) : Measure (SymmetricMatrix p) :=
  (volume : Measure (UpperTriangle p → ℝ)).map reconstruct

/-- The complete multivariate Gamma product, including all totalized values. -/
def multivariateGamma (p : ℕ) (a : ℝ) : ℝ :=
  Real.pi ^ (((p : ℝ) * ((p : ℝ) - 1)) / (Nat.cast 4 : ℝ)) *
    ∏ i : Fin p, Real.Gamma (a - (i.1 : ℝ) / (Nat.cast 2 : ℝ))

open Classical in
/-- Exact real Wishart density, with no restriction hidden in the data value. -/
def wishartPDFReal {p : ℕ} (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (A : SymmetricMatrix p) : ℝ :=
  if (A : Matrix (Fin p) (Fin p) ℝ).PosDef then
    (A : Matrix (Fin p) (Fin p) ℝ).det ^
        ((n - (p : ℝ) - 1) / (Nat.cast 2 : ℝ)) *
      Real.exp (-Matrix.trace (S⁻¹ * (A : Matrix (Fin p) (Fin p) ℝ)) /
        (Nat.cast 2 : ℝ)) /
      ((Nat.cast 2 : ℝ) ^ (n * (p : ℝ) / (Nat.cast 2 : ℝ)) *
        S.det ^ (n / (Nat.cast 2 : ℝ)) * multivariateGamma p (n / (Nat.cast 2 : ℝ)))
  else 0

def wishartPDF {p : ℕ} (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (A : SymmetricMatrix p) : ℝ≥0∞ := ENNReal.ofReal (wishartPDFReal n S A)

open Classical in
/-- The exact valid-parameter branch and zero elsewhere are both retained. -/
def nonsingularWishartMeasure {p : ℕ} (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measure (SymmetricMatrix p) :=
  if S.PosDef ∧ (p : ℝ) - 1 < n then
    (symmetricLebesgue p).withDensity (wishartPDF n S)
  else 0

/-- The canonical total inverse is retained even on singular inputs. -/
def symmetricInv {p : ℕ} (A : SymmetricMatrix p) : SymmetricMatrix p :=
  ⟨(A : Matrix (Fin p) (Fin p) ℝ)⁻¹,
    Matrix.isHermitian_iff_isSelfAdjoint.1
      (Matrix.isHermitian_iff_isSelfAdjoint.2 A.property).inv⟩

/-- The inverse-Wishart law uses the inverted scale and the complete inverse map. -/
def inverseWishartMeasure {p : ℕ} (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measure (SymmetricMatrix p) :=
  (nonsingularWishartMeasure n S⁻¹).map symmetricInv

end WishartLiteralLaws
