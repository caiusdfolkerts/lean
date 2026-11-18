module

public import ToricPower.FiniteDualDerivedHom
public import ToricPower.QuasicoherentFiniteDualHomModel
public import ToricPower.QuasicoherentEnoughInjectives

/-!
# Derived Hom through whole quasicoherent coefficient families

All coefficient comparisons and quasi-isomorphism preservation statements
are supplied as whole families before a geometric sheaf or an injective
resolution is substituted. The resulting comparison keeps the original
finite source and an explicitly identified bounded-below dual model.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CochainComplex HomComplex

namespace ToricPower

variable (k : Type) [Field k] (X : Scheme.{0}) [X.Over (Spec (.of k))]
  [HasFiniteBiproducts (QCoh X)] [EnoughInjectives (QCoh X)]
  [HasDerivedCategory.{1} (QCoh X)] [HasDerivedCategory.{1} (ModuleCat.{0} k)]
  (Φ : QCoh X ⥤ ChainComplex (QCoh X) ℕ) [Φ.Additive] (width : ℕ)
  (preservesInjectives : ∀ (q : ℕ) (M : QCoh X),
    Injective M → Injective ((Φ.obj M).X q))
  (K : CochainComplex (QCoh X) ℤ)
  (above : ∀ (M : QCoh X) (q : ℕ), width ≤ q → IsZero ((Φ.obj M).X q))
  (exactTotal : ∀ {P Q : CochainComplex (QCoh X) ℤ} (f : P ⟶ Q),
    QuasiIso f → QuasiIso (NegativeFunctorTotal.map Φ width f))
  (homModel : ∀ I : CochainComplex (QCoh X) ℤ,
    ((quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤).mapHomologicalComplex
      (.up ℤ)).obj (NegativeFunctorTotal.total Φ width I) ≅ linearHomComplex k K I)

local notation "Γ" => quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤

/-- Full derived Hom in every integer degree, with every geometric
coefficient family retained and the chosen source comparison explicit. -/
def quasicoherentFiniteDualDerivedHomEquiv (M : QCoh X)
    (C : CochainComplex.Plus (QCoh X))
    (identification : C ≅ finiteDualChainPlus Φ width M (above M)) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} k) q).obj
      ((Γ).rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj C)) ≃ₗ[k]
    (DerivedCategory.Q.obj K ⟶ ((DerivedCategory.singleFunctor (QCoh X) 0).obj M)⟦q⟧) :=
  ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} k) q).mapIso
    ((Γ).rightDerivedFunctorPlus.mapIso
      (DerivedCategory.Plus.Q.mapIso identification))).toLinearEquiv.trans
    (finiteDualDerivedHomEquiv k Φ width (Γ) preservesInjectives K M (above M)
      (exactTotal (singleInjectiveCochainι M) inferInstance)
      (homModel (singleInjectiveCochain M)) q)

end ToricPower
end
