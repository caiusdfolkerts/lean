module

public import ToricPower.ArrangementCellularSingle
public import ToricPower.ArrangementClosedDerivedHom
public import ToricPower.ArrangementClosedRowsAdjunction

/-!
# Nonzero cohomology of the actual dual chain gives the closed-row test

The source of the normalized adjunction is identified with the original
cellular complex. The actual derived-Hom equivalence then transports a
nonzero cohomology class to a nonzero morphism, and the original
adjunction gives the closed-row scalar test used in generation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones]
  (regular : fan.IsRegular) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "X" => fan.algebraicRealization
local notation "Γ" => quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections ℂ X ⊤

local instance closedDerivedTestIntegral : IsIntegral X := toricSchemeIntegral fan nonempty
local instance closedDerivedTestNoetherian : IsNoetherian X := toricScheme_isNoetherian fan
local instance closedDerivedTestSeparated : fan.algebraicRealization.IsSeparated :=
  fan.algebraicRealization_isSeparated
local instance closedDerivedTestBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance closedDerivedTestTarget : HasDerivedCategory.{1} (QCoh X) :=
  HasDerivedCategory.standard _
local instance closedDerivedTestScalar : HasDerivedCategory.{1} (ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _
local instance closedDerivedTestSource : HasDerivedCategory.{1} (IncidenceObject A ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _

/-- The actual normalized source, with the named closed-row cochain
introduced by an equality of entire complexes. -/
def arrangementNormalizedClosedRowsSingleIso (selected : Set (Fin s ⊕ Fin n)) :
    (arrangementNormalizedDerivedRealization fan regular basis rays).obj
      ((DerivedCategory.singleFunctor (IncidenceObject A ⥤ ModuleCat.{0} ℂ) 0).obj
        (closedIntegralRowsDiagram A selected ℂ)) ≅
    DerivedCategory.Q.obj
      ((arrangementClosedSubtorusCochain fan regular basis rays selected).extend
        ComplexShape.embeddingUpNat) :=
  arrangementNormalizedRealizationSingleIso fan regular basis rays
    (closedIntegralRowsDiagram A selected ℂ) ≪≫
  eqToIso (congrArg (fun K : CochainComplex (QCoh X) ℕ =>
    DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat))
    (show (arrangementQuasicoherentCellularRealization fan nonempty regular basis rays).obj
      (closedIntegralRowsDiagram A selected ℂ) =
      arrangementClosedSubtorusCochain fan regular basis rays selected from rfl))

theorem normalizedClosedRowsTest_of_dualCohomology
    (b : fan.Ray → ℤ) (selected : Set (Fin s ⊕ Fin n)) (q : ℤ)
    (nonzero : ¬ IsZero
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} ℂ) q).obj
        ((Γ).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            (arrangementClosedDualChainPlus fan regular basis rays selected
              (arrangementCartierCoefficient fan regular b)))))) :
    NormalizedClosedRowsTest fan regular basis rays b selected := by
  let M := arrangementCartierCoefficient fan regular b
  let e := arrangementClosedDualDerivedHomEquiv fan regular basis rays selected M q
  haveI : Nontrivial ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} ℂ) q).obj
      ((Γ).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj
          (arrangementClosedDualChainPlus fan regular basis rays selected M)))) :=
    not_subsingleton_iff_nontrivial.mp
      (fun h => nonzero (ModuleCat.isZero_iff_subsingleton.mpr h))
  obtain ⟨x, hx⟩ := exists_ne (0 : ((DerivedCategory.Plus.homologyFunctor
      (ModuleCat.{0} ℂ) q).obj ((Γ).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj
          (arrangementClosedDualChainPlus fan regular basis rays selected M)))))
  exact normalizedClosedRowsTest_of_realizationMap fan regular basis rays b selected _
    (arrangementNormalizedClosedRowsSingleIso fan regular basis rays selected) q (e x)
    (fun zero => hx (e.injective (zero.trans e.map_zero.symm)))

end ToricPower
end
