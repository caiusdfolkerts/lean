module

public import ToricPower.DiagramDerivedCoproducts
public import ToricPower.ArrangementIncidenceCategory

/-!
# Unbounded coproducts for the actual arrangement diagram category

The original translated-incidence category supplies the bounded grading.
Every actual coproduct and every local-smallness assertion below is
therefore unconditional for the incidence diagram category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.IntegralArrangement

universe w
variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  [HasDerivedCategory.{w} (IncidenceObject A ⥤ ModuleCat.{0} k)]

theorem arrangementDerived_hasCoproducts :
    HasCoproducts.{0} (DerivedCategory (IncidenceObject A ⥤ ModuleCat.{0} k)) :=
  Cellular.diagramDerived_hasCoproducts k (fun c : IncidenceObject A => c.1)
    (fun f => incidence_dimension_le A f)
    (fun f h => (incidence_eq_of_dimension_eq A f h).1) n
    (fun c => cell_dimension_le A c.2.val)

theorem arrangementDerived_locallySmall :
    LocallySmall.{0} (DerivedCategory (IncidenceObject A ⥤ ModuleCat.{0} k)) :=
  Cellular.diagramDerived_locallySmall k (fun c : IncidenceObject A => c.1)
    (fun f => incidence_dimension_le A f)
    (fun f h => (incidence_eq_of_dimension_eq A f h).1) n
    (fun c => cell_dimension_le A c.2.val)

end ToricPower.IntegralArrangement

end

