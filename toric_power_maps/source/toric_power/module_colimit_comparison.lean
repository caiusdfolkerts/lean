module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.NatIso

/-!
# Checking a colimit-preserving module comparison on the free rank-one module

The isomorphism locus of a natural transformation is closed under every
colimit preserved by both functors. Every module is presented by two
unrestricted coproducts of the rank-one free module. Consequently an
actual natural comparison between colimit-preserving functors out of
modules is an isomorphism on all modules once it is so on the ring.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v w z

section Colimit

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  {F G : C ⥤ D} (α : F ⟶ G)
  {J : Type*} [Category J] {K : J ⥤ C} {c : Cocone K}
  [PreservesColimit K F] [PreservesColimit K G]

/-- The actual component at a preserved colimit is invertible if all diagram
components are invertible. No exactness hypothesis is hidden here. -/
theorem isIso_natTrans_app_of_isColimit (hc : IsColimit c)
    (components : ∀ j, IsIso (α.app (K.obj j))) : IsIso (α.app c.pt) := by
  letI : ∀ j, IsIso (α.app (K.obj j)) := components
  let t := Functor.whiskerLeft K α
  letI : IsIso t := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro j
    exact components j
  let hF := isColimitOfPreserves F hc
  let hG := isColimitOfPreserves G hc
  let inverse := hG.map (F.mapCocone c) (inv t)
  have naturality (j : J) : F.map (c.ι.app j) ≫ α.app c.pt =
      α.app (K.obj j) ≫ G.map (c.ι.app j) := by
    simpa using α.naturality (c.ι.app j)
  have left : α.app c.pt ≫ inverse = 𝟙 _ := by
    apply hF.hom_ext
    intro j
    change F.map (c.ι.app j) ≫ α.app c.pt ≫ inverse = F.map (c.ι.app j) ≫ 𝟙 _
    rw [← Category.assoc, naturality j, Category.assoc]
    change α.app (K.obj j) ≫ (G.mapCocone c).ι.app j ≫
      hG.map (F.mapCocone c) (inv t) = _
    rw [IsColimit.ι_map]
    change t.app j ≫ (inv t).app j ≫ F.map (c.ι.app j) = _
    simp
  have right : inverse ≫ α.app c.pt = 𝟙 _ := by
    apply hG.hom_ext
    intro j
    change (G.mapCocone c).ι.app j ≫ hG.map (F.mapCocone c) (inv t) ≫
      α.app c.pt = G.map (c.ι.app j) ≫ 𝟙 _
    rw [IsColimit.ι_map_assoc]
    change (inv t).app j ≫ F.map (c.ι.app j) ≫ α.app c.pt = _
    rw [naturality j]
    change (inv t).app j ≫ t.app j ≫ G.map (c.ι.app j) = _
    simp
  exact ⟨⟨inverse, left, right⟩⟩

end Colimit

section Modules

variable (R : Type u) [CommRing R]
  {D : Type w} [Category.{v} D]
  {F G : ModuleCat.{u} R ⥤ D}
  [PreservesColimitsOfSize.{u,u} F] [PreservesColimitsOfSize.{u,u} G]
  (α : F ⟶ G)

/-- A comparison is invertible on every free module, with no bound on its basis. -/
theorem isIso_natTrans_app_free (unit : IsIso (α.app (ModuleCat.of R R)))
    (I : Type u) : IsIso (α.app (ModuleCat.of R (I →₀ R))) :=
  isIso_natTrans_app_of_isColimit α (ModuleCat.finsuppCoconeIsColimit R R I)
    (fun _ => unit)

/-- The canonical free-module epimorphism. -/
def freeModuleEvaluation (M : ModuleCat.{u} R) :
    ModuleCat.of R (M →₀ R) ⟶ M :=
  ModuleCat.ofHom (Finsupp.linearCombination R (fun m : M => m))

theorem freeModuleEvaluation_surjective (M : ModuleCat.{u} R) :
    Function.Surjective (freeModuleEvaluation R M).hom := by
  intro m
  refine ⟨Finsupp.single m 1, ?_⟩
  simp [freeModuleEvaluation]

/-- The canonical free module on all relations of the preceding epimorphism. -/
def freeModuleRelations (M : ModuleCat.{u} R) :
    ModuleCat.of R ((freeModuleEvaluation R M).hom.ker →₀ R) ⟶
      ModuleCat.of R (M →₀ R) :=
  freeModuleEvaluation R (ModuleCat.of R (freeModuleEvaluation R M).hom.ker) ≫
    ModuleCat.ofHom (freeModuleEvaluation R M).hom.ker.subtype

theorem freeModulePresentation_exact (M : ModuleCat.{u} R) :
    Function.Exact (freeModuleRelations R M).hom (freeModuleEvaluation R M).hom := by
  intro x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := freeModuleEvaluation_surjective R
      (ModuleCat.of R (freeModuleEvaluation R M).hom.ker) ⟨x,hx⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  · rintro ⟨a, rfl⟩
    exact (freeModuleEvaluation R (ModuleCat.of R (freeModuleEvaluation R M).hom.ker) a).property

/-- An actual comparison between colimit-preserving functors out of modules
is invertible everywhere once it is invertible on the rank-one free module. -/
theorem isIso_natTrans_app_of_free_unit (unit : IsIso (α.app (ModuleCat.of R R)))
    (M : ModuleCat.{u} R) : IsIso (α.app M) := by
  letI : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  letI : PreservesFiniteColimits G := PreservesColimitsOfSize.preservesFiniteColimits G
  let p := freeModuleEvaluation R M
  let r := freeModuleRelations R M
  let c := CokernelCofork.ofπ (f := r) p (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (freeModulePresentation_exact R M).apply_apply_eq_zero x)
  have hc : IsColimit c := ModuleCat.isColimitCokernelCofork r p
    (freeModulePresentation_exact R M) (freeModuleEvaluation_surjective R M)
  apply isIso_natTrans_app_of_isColimit α hc
  intro j
  cases j <;> exact isIso_natTrans_app_free R α unit _

end Modules

end ToricPower

end
