module

public import ToricPower.ArrangementCellularHomTargetNaturality
public import ToricPower.FiniteDualHomModel

/-! # The two literal ordinary-Hom functor presentations agree -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open ToricPower.IntegralArrangement

namespace ToricPower

theorem cellularOrdinaryHomFunctor_eq
    {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [CommRing k]
    {B : Type*} [Category.{0} B] [Abelian B] [Linear k B] [HasFiniteBiproducts B]
    (Q : IncidenceObject A ⥤ B) :
    cellularOrdinaryHomFunctor A k Q =
      ordinaryCochainCoefficientFunctor k (arrangementCellularCochainComplex A k Q) := rfl

end ToricPower
end
