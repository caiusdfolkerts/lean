module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.FreeYoneda
public import ToricPower.Cohomology.SchemeBasic
public import ToricPower.Cohomology.SheafFlasque
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Injective module sheaves are flasque

An injective `O_X`-module need not be assumed injective after forgetting
its module structure.  Instead, a section over an open is represented
by the sheafified free `O_X`-module on that open.  Open inclusions induce
actual monomorphisms between these representing module sheaves.  Module
injectivity therefore extends every section to every larger open.

This proves the acyclicity needed to compare the actual module-derived
Hom functor with the paper's ordinary sheaf cohomology.  No change of
meaning of either injectivity or sheaf cohomology is made.

-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace ToricPower

universe u

variable (X : Scheme.{u})

/-- The actual free presheaf of `O_X`-modules on a represented open. -/
abbrev moduleOpenFreePresheaf (U : X.Opens) :
    PresheafOfModules.{u} X.ringCatSheaf.obj :=
  (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U)

/-- Its actual associated sheaf of modules. -/
def moduleOpenFree (U : X.Opens) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (moduleOpenFreePresheaf X U)

/-- The map of actual representing module sheaves induced by an open
inclusion. -/
def moduleOpenFreeMap {U V : X.Opens} (i : U ⟶ V) :
    moduleOpenFree X U ⟶ moduleOpenFree X V :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i))

/-- At every open, the underlying free-module map is the injective map
on basis indices induced by composition with an open inclusion. -/
theorem moduleOpenFreePresheafMap_mono {U V : X.Opens} (i : U ⟶ V) :
    Mono ((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i)) := by
  apply PresheafOfModules.mono_of_injective
  intro W
  change Function.Injective (Finsupp.mapDomain (fun f : W.unop ⟶ U => f ≫ i))
  exact Finsupp.mapDomain_injective (fun a b _ => Subsingleton.elim a b)

instance moduleOpenFreeMap_mono {U V : X.Opens} (i : U ⟶ V) :
    Mono (moduleOpenFreeMap X i) := by
  letI := moduleOpenFreePresheafMap_mono X i
  letI : PreservesFiniteLimits
      (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)) :=
    inferInstance
  exact Functor.map_mono _ _

/-- Actual sections are corepresented by the sheafified free module;
this uses the proved sheafification adjunction and ordinary Yoneda. -/
def moduleOpenFreeSectionsEquiv (U : X.Opens) (M : X.Modules) :
    (moduleOpenFree X U ⟶ M) ≃ Γ(M, U) :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv (moduleOpenFreePresheaf X U) M).trans
      PresheafOfModules.freeYonedaEquiv

theorem moduleOpenFreeSectionsEquiv_naturality_left
    {U V : X.Opens} (i : U ⟶ V) (M : X.Modules)
    (f : moduleOpenFree X V ⟶ M) :
    moduleOpenFreeSectionsEquiv X U M (moduleOpenFreeMap X i ≫ f) =
      M.val.map i.op (moduleOpenFreeSectionsEquiv X V M f) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let g := adj.homEquiv (moduleOpenFreePresheaf X V) M f
  change PresheafOfModules.freeYonedaEquiv
      (adj.homEquiv (moduleOpenFreePresheaf X U) M
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          ((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i)) ≫ f)) = _
  rw [adj.homEquiv_naturality_left]
  change g.app (op U)
      ((ModuleCat.free (X.ringCatSheaf.obj.obj (op U))).map
        ((yoneda.map i).app (op U)) (ModuleCat.freeMk (𝟙 U))) =
    M.val.map i.op (PresheafOfModules.freeYonedaEquiv g)
  rw [ModuleCat.free_map_apply]
  change g.app (op U) (ModuleCat.freeMk (𝟙 U ≫ i)) = _
  rw [Category.id_comp]
  have h :=
    (TauCeti.PresheafOfModules.freeYonedaEquiv_symm_app_freeMk
      (P := (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj M.val)
      (PresheafOfModules.freeYonedaEquiv g) i)
  rw [Equiv.symm_apply_apply] at h
  exact h

theorem moduleOpenFreeSectionsEquiv_naturality_right (U : X.Opens)
    {M N : X.Modules} (f : moduleOpenFree X U ⟶ M) (g : M ⟶ N) :
    moduleOpenFreeSectionsEquiv X U N (f ≫ g) =
      g.app U (moduleOpenFreeSectionsEquiv X U M f) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have h := adj.homEquiv_naturality_right
    (X := moduleOpenFreePresheaf X U) f g
  have h' := congrArg PresheafOfModules.freeYonedaEquiv h
  exact h'

/-- Every actual injective `O_X`-module is flasque as an abelian sheaf.
No preservation of injectives by the forgetful functor is assumed. -/
instance injectiveModule_isFlasque (M : X.Modules) [Injective M] :
    M.presheaf.IsFlasque where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    let f := (moduleOpenFreeSectionsEquiv X V.unop M).symm s
    let g := Injective.factorThru f (moduleOpenFreeMap X i.unop)
    refine ⟨moduleOpenFreeSectionsEquiv X U.unop M g, ?_⟩
    have h := moduleOpenFreeSectionsEquiv_naturality_left X i.unop M g
    rw [Injective.comp_factorThru] at h
    exact h.symm.trans (Equiv.apply_symm_apply _ s)

/-- Positive ordinary sheaf cohomology vanishes on the actual injective
module sheaves used by the bounded-below derived Hom construction. -/
theorem injectiveModule_cohomology_isZero (M : X.Modules) [Injective M] (n : ℕ) :
    IsZero (AddCommGrpCat.of (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology M (n+1))) := by
  letI : Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology M (n+1)) :=
    by
      letI : TopCat.Presheaf.IsFlasque
          ((_root_.SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj M).obj :=
        injectiveModule_isFlasque X M
      exact TauCeti.Topology.subsingleton_H_succ_of_isFlasque (X := X.toTopCat)
        ((_root_.SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj M) n
  apply (IsZero.iff_id_eq_zero _).2
  ext x
  exact Subsingleton.elim _ _

end ToricPower

end
