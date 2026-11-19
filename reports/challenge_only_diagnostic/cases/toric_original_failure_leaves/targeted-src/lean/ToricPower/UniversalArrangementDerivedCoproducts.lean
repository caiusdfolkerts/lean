module

public import ToricPower.DiagramDerivedCoproducts
public import ToricPower.DerivedExactCoproducts
public import ToricPower.ArrangementLocalSupport
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory

/-! # Genuine arbitrary coproducts on the whole universal arrangement -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]

local instance universalCoproductsDerived :
    HasDerivedCategory.{1} (UniversalIncidenceObject A ⥤ ModuleCat.{0} k) :=
  HasDerivedCategory.standard _

/-- The finite dimension grading supplies actual K-projective models,
even though the original universal cell category is infinite. -/
theorem universalArrangement_kProjective_representatives
    (X : DerivedCategory (UniversalIncidenceObject A ⥤ ModuleCat.{0} k)) :
    ∃ K : CochainComplex (UniversalIncidenceObject A ⥤ ModuleCat.{0} k) ℤ,
      K.IsKProjective ∧ Nonempty
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≅ X) :=
  Cellular.diagramDerived_kProjective_representative k
    (fun c : UniversalIncidenceObject A => c.1)
    (fun f => universalIncidence_dimension_le A f.le)
    (fun f h => universalIncidence_eq_of_dimension_eq A f.le h) n
    (fun c => cell_dimension_le A c.2) X

/-- Localization preserves the full coproduct of arbitrary complexes. -/
theorem universalArrangementLocalization_preservesCoproducts (I : Type) :
    PreservesColimitsOfShape (Discrete I)
      (DerivedCategory.Q (C := UniversalIncidenceObject A ⥤ ModuleCat.{0} k)) :=
  CoproductComplex.derivedQ_preservesCoproducts
    (universalArrangement_kProjective_representatives A k) I

/-- In particular the actual degree-zero derived inclusion preserves
the entire family of closed affine-plane coefficient diagrams. -/
theorem universalArrangementSingle_preservesCoproducts (I : Type) (q : ℤ) :
    PreservesColimitsOfShape (Discrete I)
      (DerivedCategory.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat.{0} k) q) := by
  letI := universalArrangementLocalization_preservesCoproducts A k I
  change PreservesColimitsOfShape (Discrete I)
    (CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat.{0} k) q ⋙
      DerivedCategory.Q)
  infer_instance

end ToricPower.IntegralArrangement

end
