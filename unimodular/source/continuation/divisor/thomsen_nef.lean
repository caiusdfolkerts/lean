module

public import Continuation.Divisor.NefBigTheorems
public import Continuation.Divisor.CoordinateCriterion

/-!
# Actual nefness of every positive Thomsen bundle

Ceiling coefficients are evaluated at every real character. Their
Cartier sheaves are the actual line bundles on the fan scheme. The
conclusion tests ordinary pullback degree on every proper integral
curve, including singular curves; no support-function predicate is renamed as geometric
nefness here.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u
namespace Unimodular.Thomsen

open PaperVerification.ToricGeometry

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
  (k : Type u) [Field k]

/-- The actual positive Thomsen bundle associated to a real character. -/
def positiveThomsenLineBundle (θ : Lattice n →ₗ[ℤ] ℝ) :=
  Unimodular.NefBig.cocycleInvertibleSheaf
    (F.fanCartierCocycle k F.isPure (positiveCoefficients θ))

/-- The unrestricted coordinate criterion gives ordinary nefness of every
positive Thomsen line bundle, for all curve pullbacks. -/
theorem positiveThomsen_isNefOnCurves
    (h : Unimodular.ConeBases.PositiveCriterion
      (Unimodular.FanInterfaces.dictionaryToricFan F))
    (θ : Lattice n →ₗ[ℤ] ℝ) :
    Unimodular.NefBig.IsNefOnCurves k (positiveThomsenLineBundle F k θ) := by
  apply Unimodular.NefBig.isNefOnCurves_of_isGloballyGenerated
  exact positiveThomsen_isGloballyGenerated F k
    ((Unimodular.FanInterfaces.dictionaryPositiveCriterion_iff F).mp h) θ

/-- The same ordinary conclusion in the standard all-integral-closed-curve predicate. -/
theorem positiveThomsen_isNef
    (h : Unimodular.ConeBases.PositiveCriterion
      (Unimodular.FanInterfaces.dictionaryToricFan F))
    (θ : Lattice n →ₗ[ℤ] ℝ) :
    AlgebraicGeometry.IsNef (baseField := k) (positiveThomsenLineBundle F k θ).obj :=
  Unimodular.NefBig.isNef_of_isNefOnCurves k _
    (positiveThomsen_isNefOnCurves F k h θ)

#print axioms positiveThomsen_isNef
#print axioms positiveThomsen_isNefOnCurves

end Unimodular.Thomsen
