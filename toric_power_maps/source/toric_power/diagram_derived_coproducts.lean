module

public import ToricPower.DerivedKProjectiveCoproducts
public import ToricPower.CellularConeKProjective

/-!
# Actual coproducts in the full unbounded diagram-derived category

A bounded grading on a direct category gives the already checked finite
K-projective replacement of every unbounded coefficient complex. This
discharges the representative hypothesis in the coproduct construction.
The result applies to arbitrary coefficient complexes and arbitrary
coproducts, with no finite-dimensional or bounded-complex assumption.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

namespace ToricPower.Cellular

universe u w
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)]
  (grade : C → ℕ)
  (grade_le : ∀ {c d : C} (_ : c ⟶ d), grade c ≤ grade d)
  (eq_of_grade_eq : ∀ {c d : C} (_ : c ⟶ d), grade c = grade d → c = d)
  [∀ c : C, Subsingleton (c ⟶ c)]
  (N : ℕ) (bound : ∀ c : C, grade c ≤ N)

include grade grade_le eq_of_grade_eq N bound

/-- Every actual unbounded derived diagram has a genuine K-projective
complex representative, supplied by the finite cone construction. -/
theorem diagramDerived_kProjective_representative
    (X : DerivedCategory (C ⥤ ModuleCat.{u} k)) :
    ∃ (K : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ), K.IsKProjective ∧
      Nonempty (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≅ X) := by
  let L := (DerivedCategory.Q (C := C ⥤ ModuleCat.{u} k)).objPreimage X
  let R := finiteConeResolution k (C := C) (N + 1)
  let K := R.functor.obj L
  letI : K.IsKProjective := finiteConeResolution_isKProjective k (N + 1) L
  letI : QuasiIso (R.augmentation.app L) :=
    finiteConeResolution_augmentation_quasiIso k grade grade_le eq_of_grade_eq N bound L
  refine ⟨K, inferInstance, ⟨?_⟩⟩
  exact (DerivedCategory.quotientCompQhIso _).app K ≪≫
    asIso (DerivedCategory.Q.map (R.augmentation.app L)) ≪≫
    DerivedCategory.Q.objObjPreimageIso X

/-- Arbitrary coproducts exist in the actual unbounded derived category
of diagrams on a bounded direct category. -/
theorem diagramDerived_hasCoproducts :
    HasCoproducts.{u} (DerivedCategory (C ⥤ ModuleCat.{u} k)) :=
  CoproductComplex.derived_hasCoproducts
    (diagramDerived_kProjective_representative k grade grade_le eq_of_grade_eq N bound)

/-- The actual derived category remains locally small in the coefficient
universe. No enlargement of vector spaces is needed for its coproducts. -/
theorem diagramDerived_locallySmall :
    LocallySmall.{u} (DerivedCategory (C ⥤ ModuleCat.{u} k)) :=
  CoproductComplex.derived_locallySmall
    (diagramDerived_kProjective_representative k grade grade_le eq_of_grade_eq N bound)

end ToricPower.Cellular

end

