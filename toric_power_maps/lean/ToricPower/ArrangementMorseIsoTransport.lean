module

public import ToricPower.ArrangementLocalMorse

/-! # Actual coefficient-isomorphism transport for local Morse fibers

The single-complex and Morse functors are assembled with their original
module-category structures before a geometric label functor is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))

theorem universalLocalMorse_single_acyclic_of_iso
    {F G : UniversalIncidenceObject A ⥤ ModuleCat k} (e : F ≅ G)
    (acyclic : ((universalLocalMorse A k c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj F)).Acyclic) :
    ((universalLocalMorse A k c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj G)).Acyclic := by
  let comparison := (universalLocalMorse A k c region).mapIso
    ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).mapIso e)
  intro q
  exact (exactAt_iff_of_quasiIsoAt comparison.hom q).mp (acyclic q)

theorem universalLocalMorse_single_acyclic_of_equivalence
    {C D : Type*} [Category* C] [Category* D] (e : C ≌ D)
    (F : D ⥤ UniversalIncidenceObject A ⥤ ModuleCat k)
    (acyclic : ∀ X : C, ((universalLocalMorse A k c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj
        (F.obj (e.functor.obj X)))).Acyclic) (Y : D) :
    ((universalLocalMorse A k c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj
        (F.obj Y))).Acyclic :=
  universalLocalMorse_single_acyclic_of_iso A k c region (F.mapIso (e.counitIso.app Y))
    (acyclic (e.inverse.obj Y))

end ToricPower.IntegralArrangement

end
