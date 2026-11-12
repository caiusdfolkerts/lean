module

public import ToricPower.CellularFiniteDerivedHom
public import ToricPower.CellularFiniteDerivedIdempotents
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The actual bounded finite incidence-derived category

Objects are exactly those admitting the proved finite injective models.
The established characterization identifies them with bounded objects
whose actual cohomology diagrams are pointwise finite-dimensional.
The inclusion is full, scalar-linear, and triangulated; its Hom spaces
are finite-dimensional, and its idempotents split.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe u w
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)]

abbrev FiniteDerivedDiagrams := (finiteInjectiveModels k (C := C)).FullSubcategory

/-- The ordinary full inclusion into the unbounded derived category. -/
abbrev finiteDerivedInclusion :
    FiniteDerivedDiagrams k (C := C) ⥤ DerivedCategory (C ⥤ ModuleCat.{u} k) :=
  (finiteInjectiveModels k).ι

/-- The same objects canonically belong to the actual bounded-below
category; its underlying unbounded object is unchanged. -/
def finiteDerivedToPlus :
    FiniteDerivedDiagrams k (C := C) ⥤ DerivedCategory.Plus (C ⥤ ModuleCat.{u} k) :=
  DerivedCategory.TStructure.t.plus.lift (finiteDerivedInclusion k)
    (fun X => (finiteInjectiveModel_bounded k X.property).1)

instance : (finiteDerivedToPlus k (C := C)).CommShift ℤ := by
  unfold finiteDerivedToPlus
  infer_instance

instance : (finiteDerivedToPlus k (C := C)).IsTriangulated := by
  unfold finiteDerivedToPlus
  infer_instance

instance : (finiteDerivedToPlus k (C := C)).Linear k where
  map_smul _ _ := rfl

/-- This is the literal map on the full subcategory's morphisms. -/
def finiteDerivedHomLinearEquiv (X Y : FiniteDerivedDiagrams k (C := C)) :
    (X ⟶ Y) ≃ₗ[k] (X.obj ⟶ Y.obj) :=
  LinearEquiv.ofBijective ((finiteDerivedInclusion k).mapLinearMap k)
    ⟨(finiteDerivedInclusion k).map_injective, (finiteDerivedInclusion k).map_surjective⟩

@[simp]
theorem finiteDerivedHomLinearEquiv_apply
    {X Y : FiniteDerivedDiagrams k (C := C)} (f : X ⟶ Y) :
    finiteDerivedHomLinearEquiv k X Y f = f.hom := rfl

variable [Finite C]

instance (X Y : FiniteDerivedDiagrams k (C := C)) :
    FiniteDimensional k (X ⟶ Y) := by
  letI := finiteInjectiveModel_derivedHom_finite k X.property Y.property
  exact FiniteDimensional.of_injective
    (finiteDerivedHomLinearEquiv k X Y).toLinearMap
    (finiteDerivedHomLinearEquiv k X Y).injective

variable [∀ c d : C, Finite (c ⟶ d)] [∀ c : C, Subsingleton (c ⟶ c)]
variable (grade : C → ℕ)
  (grade_le : ∀ {c d : C} (_ : c ⟶ d), grade c ≤ grade d)
  (eq_of_grade_eq : ∀ {c d : C} (_ : c ⟶ d), grade c = grade d → c = d)
  (N : ℕ) (bound : ∀ c, grade c ≤ N)

include grade grade_le eq_of_grade_eq N bound

theorem finiteDerivedDiagrams_isIdempotentComplete :
    IsIdempotentComplete (FiniteDerivedDiagrams k (C := C)) :=
  finiteDiagramDerived_isIdempotentComplete k grade grade_le eq_of_grade_eq N bound

end ToricPower.Cellular

end
