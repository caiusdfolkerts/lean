module

public import ToricPower.SerrePairingHomology

/-!
# The actual derived-morphism pairing from a bounded injective complex

This transfers the checked signed Hom-complex pairing through the
actual localization maps. It requires the bounded target to be
K-injective and its image to be K-projective. The source is arbitrary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex
open CochainComplex.HomComplex

namespace ToricPower.SerrePairing

universe u v w
variable (k : Type u) [Field k]
variable {A : Type v} [Category.{u} A] [Abelian A] [Linear k A]
variable [HasDerivedCategory.{w} A]

def homClassDerivedZeroEquivOfKInjective (E J : CochainComplex A ℤ) [J.IsKInjective] :
    CohomologyClass E J 0 ≃ₗ[k] (DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj J) :=
  (homClassDerivedLinearEquivOfKInjective k E J 0).trans
    (Linear.homCongr k (Iso.refl _) (DerivedCategory.Q.mapIso
      ((shiftFunctorZero (CochainComplex A ℤ) ℤ).app J)))

def homClassDerivedZeroEquivOfKProjective (P E : CochainComplex A ℤ) [P.IsKProjective] :
    CohomologyClass P E 0 ≃ₗ[k] (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj E) :=
  (homClassDerivedLinearEquivOfKProjective k P E 0).trans
    (Linear.homCongr k (Iso.refl _) (DerivedCategory.Q.mapIso
      ((shiftFunctorZero (CochainComplex A ℤ) ℤ).app E)))

def finiteDerivedSerreEquiv (T : A ⥤ A) [T.Additive]
    (J : CochainComplex A ℤ) (pairing : ∀ q, CodomainPairing k T (J.X q))
    (E : CochainComplex A ℤ)
    (compatible : ∀ p q, Compatible k (pairing p) (pairing q) (J.d p q))
    (support : Finset ℤ) (outside : ∀ q, q ∉ support → IsZero (J.X q))
    [J.IsKInjective] [(mappedCochainComplex T J).IsKProjective] :
    (DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj J) ≃ₗ[k]
      Module.Dual k (DerivedCategory.Q.obj (mappedCochainComplex T J) ⟶ DerivedCategory.Q.obj E) :=
  (homClassDerivedZeroEquivOfKInjective k E J).symm.trans
    ((finiteCochainSerreClassEquiv k T J pairing E compatible support outside).trans
      (homClassDerivedZeroEquivOfKProjective k (mappedCochainComplex T J) E).symm.dualMap)

end ToricPower.SerrePairing

end
