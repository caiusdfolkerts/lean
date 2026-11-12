module

public import ToricPower.CellularFiniteDerivedModels
public import ToricPower.DerivedBoundedRetracts

/-!
# Retracts of bounded finite incidence diagrams

Finiteness is checked on the actual homology vector spaces. Splitting a
derived idempotent therefore stays inside the bounded-finite collection;
the finite directed-resolution theorem then supplies an actual bounded
finite injective model for the resulting retract.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe u w
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)]

theorem pointwiseFiniteDerived_of_retract
    {X Y : DerivedCategory (C ⥤ ModuleCat.{u} k)} (r : Retract X Y)
    (finite : pointwiseFiniteDerived k Y) : pointwiseFiniteDerived k X := by
  intro q c
  letI : FiniteDimensional k
      (((evaluation C (ModuleCat.{u} k)).obj c).obj
        ((DerivedCategory.homologyFunctor _ q).obj Y)) := finite q c
  let rh := (r.map (DerivedCategory.homologyFunctor _ q)).map
    ((evaluation C (ModuleCat.{u} k)).obj c)
  exact FiniteDimensional.of_injective rh.i.hom
    ((ModuleCat.mono_iff_injective rh.i).mp inferInstance)

instance pointwiseFiniteDerived_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts (pointwiseFiniteDerived k (C := C)) where
  of_retract := pointwiseFiniteDerived_of_retract k

variable [Finite C] [∀ c d : C, Finite (c ⟶ d)] [∀ c : C, Subsingleton (c ⟶ c)]
variable (grade : C → ℕ)
  (grade_le : ∀ {c d : C} (_ : c ⟶ d), grade c ≤ grade d)
  (eq_of_grade_eq : ∀ {c d : C} (_ : c ⟶ d), grade c = grade d → c = d)
  (N : ℕ) (bound : ∀ c, grade c ≤ N)

include grade grade_le eq_of_grade_eq N bound

theorem finiteInjectiveModel_of_retract
    {X Y : DerivedCategory (C ⥤ ModuleCat.{u} k)} (r : Retract X Y)
    (model : finiteInjectiveModels k Y) : finiteInjectiveModels k X :=
  bounded_finiteInjectiveModel k grade grade_le eq_of_grade_eq N bound X
    (derived_bounded_of_retract r (finiteInjectiveModel_bounded k model))
    (pointwiseFiniteDerived_of_retract k r (finiteInjectiveModel_finite k model))

@[instance_reducible]
def finiteInjectiveModels_isStableUnderRetracts :
    (finiteInjectiveModels k (C := C)).IsStableUnderRetracts where
  of_retract := finiteInjectiveModel_of_retract k grade grade_le eq_of_grade_eq N bound

end ToricPower.Cellular

end
