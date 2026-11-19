module

public import ToricPower.ArrangementMorseComplexIsoTransport

/-! # Opaque whole-functor transport of the actual Morse calculation -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] CommRing.toRing
attribute [local instance 2100] Complex.instRing
attribute [local instance 2000] Ring.toAddCommGroup
attribute [local instance 2000] Ring.toSemiring
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
  {C D : Type*} [Category* C] [Category* D]

theorem universalLocalMorse_single_acyclic_of_functor_equality_complex
    (F G : C ⥤ UniversalIncidenceObject A ⥤ ModuleCat ℂ) (same : F=G) (X : C)
    (acyclic : ((universalLocalMorse A ℂ c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj
        (F.obj X))).Acyclic) :
    ((universalLocalMorse A ℂ c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj
        (G.obj X))).Acyclic := by
  let comparison := (universalLocalMorse A ℂ c region).mapIso
    ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).mapIso
      ((eqToIso same).app X))
  intro q
  exact (exactAt_iff_of_quasiIsoAt comparison.hom q).mp (acyclic q)

theorem universalLocalMorse_single_acyclic_of_composite_complex
    (F : C ⥤ D) (G : D ⥤ UniversalIncidenceObject A ⥤ ModuleCat ℂ) (X : C)
    (acyclic : ((universalLocalMorse A ℂ c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj
        ((F ⋙ G).obj X))).Acyclic) :
    ((universalLocalMorse A ℂ c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj
        (G.obj (F.obj X)))).Acyclic := acyclic

end ToricPower.IntegralArrangement

end

