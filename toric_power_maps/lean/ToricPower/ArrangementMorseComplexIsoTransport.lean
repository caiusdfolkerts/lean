module

public import ToricPower.ArrangementMorseIsoTransport

/-! # The canonical complex scalar presentation of Morse transport

This small boundary records the same equivalence argument with the
literal complex ring structure used by the algebraic-geometric section
functors. The whole coefficient functor is kept abstract when its
presentation is changed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] CommRing.toRing
attribute [local instance 2100] Complex.instRing
attribute [local instance 2000] Ring.toAddCommGroup
attribute [local instance 2000] Ring.toSemiring
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.IntegralArrangement

theorem universalLocalMorse_single_acyclic_of_equivalence_functor_complex
    {n s : ℕ} (A : Fin s → Fin n → ℤ)
    (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
    {C D : Type*} [Category* C] [Category* D] (e : C ≌ D)
    (F : C ⥤ UniversalIncidenceObject A ⥤ ModuleCat ℂ)
    (G : D ⥤ UniversalIncidenceObject A ⥤ ModuleCat ℂ)
    (same : F = e.functor ⋙ G)
    (acyclic : ∀ X : C, ((universalLocalMorse A ℂ c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj
        (F.obj X))).Acyclic) (Y : D) :
    ((universalLocalMorse A ℂ c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj
        (G.obj Y))).Acyclic := by
  let coefficient : F.obj (e.inverse.obj Y) ≅ G.obj Y :=
    (eqToIso same).app (e.inverse.obj Y) ≪≫ G.mapIso (e.counitIso.app Y)
  let comparison := (universalLocalMorse A ℂ c region).mapIso
    ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).mapIso
      coefficient)
  intro q
  exact (exactAt_iff_of_quasiIsoAt comparison.hom q).mp (acyclic (e.inverse.obj Y) q)

end ToricPower.IntegralArrangement

end
