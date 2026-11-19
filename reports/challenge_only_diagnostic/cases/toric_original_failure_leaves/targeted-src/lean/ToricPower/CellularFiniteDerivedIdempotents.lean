module

public import ToricPower.CellularFiniteDerivedRetracts
public import ToricPower.DiagramDerivedCoproducts
public import ToricPower.TriangulatedIdempotents
public import ToricPower.RetractClosedIdempotents

/-!
# Actual split idempotents for bounded finite incidence diagrams

The unbounded derived diagram category has actual coproducts, hence the
verified telescope construction splits its idempotents. The image stays
bounded and finite-dimensional by the proved retract-closure lemmas.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe u w
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  [Finite C] [∀ c d : C, Finite (c ⟶ d)] [∀ c : C, Subsingleton (c ⟶ c)]
  [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)]
variable (grade : C → ℕ)
  (grade_le : ∀ {c d : C} (_ : c ⟶ d), grade c ≤ grade d)
  (eq_of_grade_eq : ∀ {c d : C} (_ : c ⟶ d), grade c = grade d → c = d)
  (N : ℕ) (bound : ∀ c, grade c ≤ N)

include grade grade_le eq_of_grade_eq N bound

theorem diagramDerived_isIdempotentComplete :
    IsIdempotentComplete (DerivedCategory (C ⥤ ModuleCat.{u} k)) := by
  letI := diagramDerived_hasCoproducts k grade grade_le eq_of_grade_eq N bound
  letI : HasCoproducts.{0} (DerivedCategory (C ⥤ ModuleCat.{u} k)) :=
    has_smallest_coproducts_of_hasCoproducts
  exact CompactExtraction.idempotentComplete_of_countableCoproducts

theorem finiteDiagramDerived_isIdempotentComplete :
    IsIdempotentComplete (finiteInjectiveModels k (C := C)).FullSubcategory := by
  letI := diagramDerived_isIdempotentComplete k grade grade_le eq_of_grade_eq N bound
  letI := finiteInjectiveModels_isStableUnderRetracts k grade grade_le eq_of_grade_eq N bound
  infer_instance

end ToricPower.Cellular

end
