module

public import ToricPower.ArrangementMorseModuleVanishing
public import ToricPower.ArrangementMorseSumVanishing
public import ToricPower.ModuleDirectSumComplex

/-! # From the actual rank-one affine calculation to every module

The coefficient functor is exact and preserves the unrestricted
coproduct of free rank-one modules. The true local Morse functor has a
uniform upper degree bound and preserves the coproduct comparison.
Consequently its rank-one calculation extends to every affine module,
without choosing a finite resolution or imposing finite generation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped Classical

namespace ToricPower

/-- The unrestricted free module is the categorical sum of rank-one
modules, through the literal dependent finitely supported module. -/
def moduleFreeCoproductIso (R : Type) [CommRing R] (I : Type) :
    (∐ fun _ : I => ModuleCat.of R R) ≅ ModuleCat.of R (I →₀ R) :=
  (ModuleDirectSum.sumColimitIso R
      (Discrete.functor (fun _ : I => ModuleCat.of R R))).symm ≪≫
    (finsuppLequivDFinsupp R).symm.toModuleIso

namespace IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))

/-- Every free coefficient module is handled by the literal rank-one
calculation and the actual categorical coproduct comparison. -/
theorem universalLocalMorse_freeModules_acyclic_of_rankOne
    (R : Type) [CommRing R]
    (H : ModuleCat.{0} R ⥤ (UniversalIncidenceObject A ⥤ ModuleCat k))
    (preserves : ∀ I : Type,
      PreservesColimit (Discrete.functor (fun _ : I => ModuleCat.of R R)) H)
    (rankOne : ((universalLocalMorse A k c region).obj
      ((singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj
        (H.obj (ModuleCat.of R R)))).Acyclic)
    (I : Type) :
    ((universalLocalMorse A k c region).obj
      ((singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj
        (H.obj (ModuleCat.of R (I →₀ R))))).Acyclic := by
  letI := preserves I
  let single := singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0
  let family : I → UniversalIncidenceObject A ⥤ ModuleCat k :=
    fun _ => H.obj (ModuleCat.of R R)
  let e : (∐ fun i : I => single.obj (family i)) ≅
      single.obj (H.obj (ModuleCat.of R (I →₀ R))) :=
    (PreservesCoproduct.iso single family).symm ≪≫
      single.mapIso ((PreservesCoproduct.iso H (fun _ : I => ModuleCat.of R R)).symm ≪≫
        H.mapIso (moduleFreeCoproductIso R I))
  have vanishes := universalLocalMorse_coproduct_acyclic A k c region
    (fun i : I => single.obj (family i)) (fun _ => rankOne)
  let iso := (universalLocalMorse A k c region).mapIso e
  intro q
  exact (exactAt_iff_of_quasiIsoAt iso.hom q).mp (vanishes q)

/-- Actual exact affine coefficient functors need only a checked
rank-one calculation; every module, of every cardinality, then follows. -/
theorem universalLocalMorse_affineModules_acyclic_of_rankOne
    (R : Type) [CommRing R]
    (H : ModuleCat.{0} R ⥤ (UniversalIncidenceObject A ⥤ ModuleCat k))
    [H.PreservesZeroMorphisms]
    (exact : ∀ S : ShortComplex (ModuleCat.{0} R),
      S.ShortExact → (S.map H).ShortExact)
    (preserves : ∀ I : Type,
      PreservesColimit (Discrete.functor (fun _ : I => ModuleCat.of R R)) H)
    (rankOne : ((universalLocalMorse A k c region).obj
      ((singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj
        (H.obj (ModuleCat.of R R)))).Acyclic)
    (M : ModuleCat.{0} R) :
    ((universalLocalMorse A k c region).obj
      ((singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj (H.obj M))).Acyclic :=
  universalLocalMorse_affineModules_acyclic_of_free A k c region R H exact
    (universalLocalMorse_freeModules_acyclic_of_rankOne A k c region R H preserves rankOne) M

end IntegralArrangement
end ToricPower

end
