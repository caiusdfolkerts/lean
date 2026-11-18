module

public import ToricPower.ArrangementMorseIsoTransport

/-! # Whole-functor transport of the exact Morse vanishing predicate -/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
  {D : Type*} [Category D]

theorem universalLocalMorse_single_acyclic_of_functorIso
    (F G : D ⥤ UniversalIncidenceObject A ⥤ ModuleCat k) (e : F ≅ G)
    (h : ∀ X : D, ((universalLocalMorse A k c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj
        (F.obj X))).Acyclic) (X : D) :
    ((universalLocalMorse A k c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj
        (G.obj X))).Acyclic := by
  let comparison := (universalLocalMorse A k c region).mapIso
    ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).mapIso
      (e.app X))
  intro q
  exact (exactAt_iff_of_quasiIsoAt comparison.hom q).mp (h X q)

/-- Expose composite evaluation before any geometric functor is substituted. -/
theorem property_of_composite_obj {C D E : Type*}
    [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (P : E → Prop) (X : C)
    (h : P ((F ⋙ G).obj X)) : P (G.obj (F.obj X)) := h

end ToricPower.IntegralArrangement

end
