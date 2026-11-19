module
public import PalomarMain13Proofs
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial Matrix
variable {K : Type*} [Field K] {s n : ℕ}
/-- Literal coordinate-chart or saturation identification of the actual Plücker ring in Theorem 1.3; original characteristic and rank hypotheses retained. -/
abbrev PluckerChartVariable (p : PluckerIndex s n) :=
  Fin s × {j : Fin n // j ∉ Set.range p.val}
end
end PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
namespace PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial Matrix
variable {K : Type*} [Field K] {s n : ℕ}
/-- Literal coordinate-chart or saturation identification of the actual Plücker ring in Theorem 1.3; original characteristic and rank hypotheses retained. -/
def pluckerChartMatrix (p : PluckerIndex s n) :
    Matrix (Fin s) (Fin n) (MvPolynomial (PluckerChartVariable p) K) :=
  Matrix.of fun i j => if j=p.val i then 1 else if h : j ∈ Set.range p.val then 0
    else X (i,⟨j,h⟩)
end
end PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
namespace PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial Matrix
variable {K : Type*} [Field K] {t n m : ℕ}
/-- Literal coordinate-chart or saturation identification of the actual Plücker ring in Theorem 1.3; original characteristic and rank hypotheses retained. -/
def alternatingRowPair {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (A : Matrix (Fin (t+2)) (Fin n) R)
    (i j : Fin (t+2)) : R :=
  ∑ a : StrictPairs n, f a •
    (A i a.val.1*A j a.val.2 - A i a.val.2*A j a.val.1)
end
end PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
namespace PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial Matrix
variable {K : Type*} [Field K] {t n m : ℕ}
/-- Literal coordinate-chart or saturation identification of the actual Plücker ring in Theorem 1.3; original characteristic and rank hypotheses retained. -/
def isotropicChartIdeal (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    Ideal (MvPolynomial (PluckerChartVariable p) K) :=
  Ideal.span (Set.range fun a : Fin m × StrictPairs (t+2) =>
    alternatingRowPair (forms a.1) (pluckerChartMatrix p) a.2.val.1 a.2.val.2)
end
end PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
namespace PalomarAlternatingDegeneration.PaperVerification.WeightedInitialFiber
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial
variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K
variable {R : Type*} [CommRing R]
/-- Literal coordinate-chart or saturation identification of the actual Plücker ring in Theorem 1.3; original characteristic and rank hypotheses retained. -/
def IsSaturatedWithRespectTo (Q J : Ideal R) : Prop :=
  ∀ f : R, (∃ m : ℕ, ∀ g∈J^m,g*f∈Q) ↔ f∈Q
end
end PalomarAlternatingDegeneration.PaperVerification.WeightedInitialFiber
namespace PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial
open PaperVerification.WeightedInitialFiber
variable {K : Type*} [Field K] [CharZero K]
/-- Literal coordinate-chart or saturation identification of the actual Plücker ring in Theorem 1.3; original characteristic and rank hypotheses retained. -/
def pluckerIrrelevantIdeal (s n : ℕ) : Ideal (MvPolynomial (PluckerIndex s n) K) :=
  Ideal.span (Set.range (X : PluckerIndex s n → MvPolynomial (PluckerIndex s n) K))
end
end PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
namespace PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial
open PaperVerification.WeightedInitialFiber
variable {K : Type*} [Field K] [CharZero K]
/-- Literal coordinate-chart or saturation identification of the actual Plücker ring in Theorem 1.3; original characteristic and rank hypotheses retained. -/
theorem odd_isotropicPluckerIdeal_isPrime (k t : ℕ) (hs : t+2≤k+1) :
    (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k)).IsPrime := by
  exact _root_.PaperVerification.AlternatingForms.odd_isotropicPluckerIdeal_isPrime (K := K) (k := k) (t := t) (hs := hs)
end
end PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
namespace PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial
open PaperVerification.WeightedInitialFiber
variable {K : Type*} [Field K] [CharZero K]
/-- Literal coordinate-chart or saturation identification of the actual Plücker ring in Theorem 1.3; original characteristic and rank hypotheses retained. -/
theorem onePlane_ideal_isPrime (n : ℕ) :
    (matrixPluckerIdeal (K := K) (s := 1) (n := n)).IsPrime := by
  exact _root_.PaperVerification.AlternatingForms.onePlane_ideal_isPrime (K := K) (n := n)
end
end PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
namespace PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial
open PaperVerification.WeightedInitialFiber
variable {K : Type*} [Field K] [CharZero K]
/-- Literal coordinate-chart or saturation identification of the actual Plücker ring in Theorem 1.3; original characteristic and rank hypotheses retained. -/
theorem odd_isotropicPluckerIdeal_saturated (k t : ℕ) (hs : t+2≤k+1) :
    IsSaturatedWithRespectTo
      (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
      (pluckerIrrelevantIdeal (t+2) (2*k+1)) := by
  exact _root_.PaperVerification.AlternatingForms.odd_isotropicPluckerIdeal_saturated (K := K) (k := k) (t := t) (hs := hs)
end
end PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
namespace PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial
open PaperVerification.WeightedInitialFiber
variable {K : Type*} [Field K] [CharZero K]
/-- Literal coordinate-chart or saturation identification of the actual Plücker ring in Theorem 1.3; original characteristic and rank hypotheses retained. -/
theorem onePlane_PluckerIdeal_saturated (k : ℕ) :
    IsSaturatedWithRespectTo
      (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
      (pluckerIrrelevantIdeal 1 (2*k+1)) := by
  exact _root_.PaperVerification.AlternatingForms.onePlane_PluckerIdeal_saturated (K := K) (k := k)
end
end PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
namespace PalomarAlternatingDegeneration.PalomarAlternatingGeometry
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open PaperVerification.AlternatingForms MvPolynomial
universe uChart
/-- Literal coordinate-chart or saturation identification of the actual Plücker ring in Theorem 1.3; original characteristic and rank hypotheses retained. -/
theorem oddAffineCharts {K : Type uChart} [Field K] [CharZero K]
    (k t : ℕ) (hs : t+2 ≤ k+1) (p : PluckerIndex (t+2) (2*k+1)) :
    Nonempty ((MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸
      (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k) ⊔ Ideal.span {X p-1})) ≃ₐ[K]
      (MvPolynomial (PluckerChartVariable p) K ⧸
        isotropicChartIdeal p (oddPluckerForms (K := K) k))) := by
  exact ⟨_root_.PaperVerification.AlternatingForms.isotropicPluckerBigCellEquiv p
    (_root_.PaperVerification.AlternatingForms.oddPluckerForms (K := K) k)⟩
end
end PalomarAlternatingDegeneration.PalomarAlternatingGeometry
