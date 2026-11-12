module

public import ToricPower.CellularRHomPlus
public import ToricPower.DerivedHomPlusExt
public import ToricPower.ModuleUnitExtCohomology
public import ToricPower.ExactGeneratorObstruction
public import ToricPower.CoherentRestriction

/-!
# Actual derived global sections and a coherent generation obstruction

Global sections are `Hom(O,-)`. We derive this actual additive functor on
the category of module sheaves, whose enough-injectives theorem is proved.
Its value on a sheaf has ordinary sheaf cohomology in every nonnegative
degree and vanishes in negative degrees. Restriction to an open subscheme
then gives an exact functor on the literal bounded coherent derived category.

No derived equivalence of coherent and quasicoherent categories, regular
embedding duality, or compact-generation theorem is used here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Abelian MonoidalCategory Opposite
open scoped ZeroObject

namespace ToricPower

universe u

local instance globalSectionsOver (X : Scheme.{u}) :
    X.Over (Spec (.of Γ(X, ⊤))) := ⟨X.toSpecΓ⟩

local instance globalSectionsModulesDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

local instance globalSectionsCoefficientsDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} (ModuleCat.{u} Γ(X, ⊤)) := HasDerivedCategory.standard _

local instance globalSectionsCoherentDerived (X : Scheme.{u}) [IsLocallyNoetherian X] :
    HasDerivedCategory.{u+1} (Coh X) := HasDerivedCategory.standard _

local instance globalSectionsHasExt (X : Scheme.{u}) : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- Actual global sections, expressed as linear Hom from the structure sheaf.
The checked `moduleUnitSectionsLinearEquiv` identifies these literally with
sections on the whole scheme. -/
def moduleGlobalSectionsHomFunctor (X : Scheme.{u}) :
    X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  (linearCoyoneda Γ(X, ⊤) X.Modules).obj (op (𝟙_ X.Modules))

instance (X : Scheme.{u}) : (moduleGlobalSectionsHomFunctor X).Additive := by
  unfold moduleGlobalSectionsHomFunctor
  infer_instance

/-- The genuine bounded-below derived global-sections functor. -/
def moduleDerivedGlobalSectionsPlus (X : Scheme.{u}) :
    DerivedCategory.Plus X.Modules ⥤ DerivedCategory.Plus (ModuleCat.{u} Γ(X, ⊤)) :=
  (moduleGlobalSectionsHomFunctor X).rightDerivedFunctorPlus

instance (X : Scheme.{u}) : (moduleDerivedGlobalSectionsPlus X).CommShift ℤ := by
  unfold moduleDerivedGlobalSectionsPlus
  infer_instance

instance (X : Scheme.{u}) : (moduleDerivedGlobalSectionsPlus X).IsTriangulated := by
  unfold moduleDerivedGlobalSectionsPlus
  infer_instance

/-- Actual derived global sections recover the paper's ordinary cohomology
groups, in every nonnegative degree. -/
def moduleDerivedGlobalSectionsPlusSingleCohomology
    (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) (n : ℤ)).obj
        ((moduleDerivedGlobalSectionsPlus X).obj
          (DerivedCategory.Plus.Q.obj (singlePlusComplex M))) ≃+
      TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology M n := by
  letI : Module Γ(X, ⊤) (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology M n) :=
    Scheme.Modules.cohomologyBaseModule Γ(X, ⊤) X M n
  exact
    (rightDerivedPlusSingleHomologyIso (moduleGlobalSectionsHomFunctor X) M (n : ℤ)).toLinearEquiv.toAddEquiv.trans
      ((injectiveTermwiseHomExtEquiv Γ(X, ⊤) (𝟙_ X.Modules) M n).trans
        (moduleUnitExtCohomology Γ(X, ⊤) X M n).toAddEquiv)

/-- A derived object is zero precisely when every actual homology object is
zero. This is the nondegeneracy of the canonical derived t-structure. -/
theorem derivedPlus_isZero_iff_homology
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (K : DerivedCategory.Plus A) :
    IsZero K ↔ ∀ n : ℤ, IsZero ((DerivedCategory.Plus.homologyFunctor A n).obj K) := by
  constructor
  · intro h n
    exact (DerivedCategory.Plus.homologyFunctor A n).map_isZero h
  · intro h
    have hle : K.obj.IsLE 0 := (DerivedCategory.isLE_iff _ _).mpr (fun n _ => h n)
    have hge : K.obj.IsGE 1 := (DerivedCategory.isGE_iff _ _).mpr (fun n _ => h n)
    letI := hle
    letI := hge
    have hz : IsZero K.obj := DerivedCategory.TStructure.t.isZero _ 0 1
    apply (IsZero.iff_id_eq_zero K).mpr
    apply ObjectProperty.hom_ext
    exact (IsZero.iff_id_eq_zero K.obj).mp hz

/-- Vanishing of the actual derived functor on a sheaf is equivalent to
vanishing of all of its ordinary sheaf-cohomology groups. -/
theorem moduleDerivedGlobalSectionsPlusSingle_isZero_iff
    (X : Scheme.{u}) (M : X.Modules) :
    IsZero ((moduleDerivedGlobalSectionsPlus X).obj
      (DerivedCategory.Plus.Q.obj (singlePlusComplex M))) ↔
      ∀ n : ℕ, Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology M n) := by
  rw [derivedPlus_isZero_iff_homology]
  constructor
  · intro h n
    exact (moduleDerivedGlobalSectionsPlusSingleCohomology X M n).toEquiv.subsingleton_congr.mp
      (ModuleCat.isZero_iff_subsingleton.mp (h n))
  · intro h n
    by_cases hn : n < 0
    · exact rightDerivedPlusSingle_negativeHomology_isZero
        (moduleGlobalSectionsHomFunctor X) M n hn
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hn)
      apply ModuleCat.isZero_iff_subsingleton.mpr
      exact (moduleDerivedGlobalSectionsPlusSingleCohomology X M m).toEquiv.subsingleton_congr.mpr (h m)

variable {U X : Scheme.{u}} [IsLocallyNoetherian U] [IsLocallyNoetherian X]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual exact coherent restriction followed by the actual inclusion
in module sheaves and the actual right-derived global-sections functor. -/
def coherentOpenDerivedGlobalSectionsPlus :
    DbCoh X ⥤ DerivedCategory.Plus (ModuleCat.{u} Γ(U, ⊤)) :=
  coherentDerivedRestriction j ⋙ coherentToModuleDerivedPlus U ⋙
    moduleDerivedGlobalSectionsPlus U

instance : (coherentOpenDerivedGlobalSectionsPlus j).CommShift ℤ := by
  unfold coherentOpenDerivedGlobalSectionsPlus
  infer_instance

instance : (coherentOpenDerivedGlobalSectionsPlus j).IsTriangulated := by
  unfold coherentOpenDerivedGlobalSectionsPlus
  infer_instance

/-- The inclusion into bounded-below module complexes agrees with placing
the underlying coherent sheaf in degree zero. -/
def coherentToModuleDerivedPlusSingleIso (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (M : Coh Y) :
    (coherentToModuleDerivedPlus Y).obj (coherentSingle Y M) ≅
      DerivedCategory.Plus.Q.obj (singlePlusComplex M.obj) :=
  ObjectProperty.isoMk _ ((DerivedCategory.Bounded.ι (C := Y.Modules)).mapIso
    (((coherentModuleInclusion Y).mapBoundedDerivedCategorySingleFunctor 0).app M))

/-- Calculation of the open derived-sections functor on an actual coherent
sheaf, with no unproved derived-category comparison. -/
def coherentOpenDerivedGlobalSectionsPlusSingleIso (M : Coh X) :
    (coherentOpenDerivedGlobalSectionsPlus j).obj (coherentSingle X M) ≅
      (moduleDerivedGlobalSectionsPlus U).obj
        (DerivedCategory.Plus.Q.obj (singlePlusComplex
          ((Scheme.Modules.restrictFunctor j).obj M.obj))) :=
  (coherentToModuleDerivedPlus U ⋙ moduleDerivedGlobalSectionsPlus U).mapIso
      (coherentDerivedRestrictionSingleIso j M) ≪≫
    (moduleDerivedGlobalSectionsPlus U).mapIso
      (coherentToModuleDerivedPlusSingleIso U _)

/-- A coherent object whose restriction has zero cohomology cannot generate
if another coherent object has nonzero cohomology on the same open set.
Every functor, cohomology group, and generator notion here is literal. -/
theorem not_generatesDbCoh_of_open_cohomology_vanishes
    (G M : Coh X)
    (hG : ∀ n : ℕ, Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      ((Scheme.Modules.restrictFunctor j).obj G.obj) n))
    (hM : ¬ ∀ n : ℕ, Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      ((Scheme.Modules.restrictFunctor j).obj M.obj) n)) :
    ¬ generatesDbCoh (coherentSingle X G) := by
  apply not_classicalGenerator_of_exactFunctor
    (coherentOpenDerivedGlobalSectionsPlus j) (coherentSingle X G) (coherentSingle X M)
  · exact (coherentOpenDerivedGlobalSectionsPlusSingleIso j G).isZero_iff.mpr
      ((moduleDerivedGlobalSectionsPlusSingle_isZero_iff U _).mpr hG)
  · intro h
    exact hM ((moduleDerivedGlobalSectionsPlusSingle_isZero_iff U _).mp
      ((coherentOpenDerivedGlobalSectionsPlusSingleIso j M).isZero_iff.mp h))

end ToricPower

end

