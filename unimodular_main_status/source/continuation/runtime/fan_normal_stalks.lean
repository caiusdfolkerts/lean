module

public import Continuation.Divisor.Geometry
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Normal local rings of the original smooth fan scheme

The actual algebra of every full cone chart is a polynomial algebra over
the ground field. Its localizations are integrally closed, and the genuine
open-immersion stalk isomorphisms identify them with the local rings of the
original glued scheme. Neither a new toric realization nor a normality
hypothesis is introduced.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Unimodular.NefBig

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes PaperVerification.ToricCharacters
open PaperVerification.ToricGeometry

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
  (k : Type u) [Field k]

/-- The original full-chart algebra is normal via its proved polynomial
presentation. This includes dimension zero. -/
theorem fullChartAlgebra_isIntegrallyClosed (s : F.fullCones) :
    IsIntegrallyClosed
      (monoidChartAlgebra k (dualConeMonoid (s : Finset (Lattice n)))) :=
  IsIntegrallyClosed.of_equiv (fullChartPolynomialEquiv F k s).symm.toRingEquiv

/-- Normality of each actual local ring follows by an open chart and its
ordinary prime localization. No projectivity assumption is needed. -/
theorem fanScheme_stalk_isIntegrallyClosed (x : F.fanScheme k) :
    IsIntegrallyClosed ((F.fanScheme k).presheaf.stalk x) := by
  obtain ⟨s, y, rfl⟩ := F.fullChartOpen_cover k F.isPure x
  let A := monoidChartAlgebra k (dualConeMonoid (s : Finset (Lattice n)))
  let e := fullChartPolynomialEquiv F k s
  letI : IsDomain A := Function.Injective.isDomain e.toRingHom e.injective
  letI : IsIntegrallyClosed A := fullChartAlgebra_isIntegrallyClosed F k s
  let y' : Spec (CommRingCat.of A) := y
  letI : IsIntegrallyClosed (Localization.AtPrime y'.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime y'.asIdeal)
      y'.asIdeal.primeCompl y'.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsIntegrallyClosed ((coneChart k (F.fullConeIndex s).val).presheaf.stalk y) :=
    IsIntegrallyClosed.of_equiv
      (Spec.stalkIso (CommRingCat.of A) y').commRingCatIsoToRingEquiv.symm
  exact IsIntegrallyClosed.of_equiv
    (asIso ((F.fanChartMap k (F.fullConeIndex s)).stalkMap y)).commRingCatIsoToRingEquiv.symm

#print axioms fullChartAlgebra_isIntegrallyClosed
#print axioms fanScheme_stalk_isIntegrallyClosed

end Unimodular.NefBig

end
