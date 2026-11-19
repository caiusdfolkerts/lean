module

public import ToricPower.ElementProductAdjunction
public import ToricPower.ModuleSumProductSupport
public import ToricPower.ExactTransformationQuasiIso

/-!
# The canonical sum-to-product map on a discrete covering

The comparison inserts every sheet into the corresponding product
coordinate. Both incidence naturality and coefficient naturality are
checked on the genuine inclusion/projection matrix. For a target with
finite nonzero support in every fiber this original map is invertible.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.ElementComparison

variable {C : Type} [SmallCategory C] (B : C ⥤ Type)
  (bijective : ∀ {c d : C} (f : c ⟶ d), Function.Bijective (B.map f))
  (R : Type) [CommRing R]

set_option quotPrecheck false in
local notation "ModR" => ModuleCat.{0} R

def fiber (E : B.Elements ⥤ ModR) (c : C) : Discrete (B.obj c) ⥤ ModR :=
  Discrete.functor (fun r => E.obj (B.elementsMk c r))

/-- The two coordinate isomorphisms surround the original inclusion
of finitely supported functions into all functions. -/
def cellComparison (E : B.Elements ⥤ ModR) (c : C) :
    ElementPushdown.cell B E c ⟶ ElementProduct.cell B E c :=
  (ModuleDirectSum.sumColimitIso R (fiber B R E c)).inv ≫
    (ModuleDirectSum.sumToProduct R).app (fiber B R E c) ≫
      (ModuleDirectSum.productLimitIso R (fiber B R E c)).hom

@[reassoc]
theorem inclusion_comparison_projection_self (E : B.Elements ⥤ ModR)
    (c : C) (r : B.obj c) :
    ElementPushdown.inclusion B E c r ≫ cellComparison B R E c ≫
        ElementProduct.projection B E c r = 𝟙 (E.obj (B.elementsMk c r)) := by
  classical
  change colimit.ι (fiber B R E c) ⟨r⟩ ≫ cellComparison B R E c ≫
    limit.π (fiber B R E c) ⟨r⟩ = _
  rw [← ModuleDirectSum.sumColimitIso_inclusion R (fiber B R E c) r]
  simp only [cellComparison,Category.assoc,Iso.hom_inv_id_assoc,
    ModuleDirectSum.productLimitIso_projection]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (DFinsupp.single (β := fun b : B.obj c => (fiber B R E c).obj ⟨b⟩) r x) r = x
  exact DFinsupp.single_eq_same

@[reassoc]
theorem inclusion_comparison_projection_ne (E : B.Elements ⥤ ModR)
    (c : C) (r t : B.obj c) (hne : r ≠ t) :
    ElementPushdown.inclusion B E c r ≫ cellComparison B R E c ≫
        ElementProduct.projection B E c t = 0 := by
  classical
  change colimit.ι (fiber B R E c) ⟨r⟩ ≫ cellComparison B R E c ≫
    limit.π (fiber B R E c) ⟨t⟩ = _
  rw [← ModuleDirectSum.sumColimitIso_inclusion R (fiber B R E c) r]
  simp only [cellComparison,Category.assoc,Iso.hom_inv_id_assoc,
    ModuleDirectSum.productLimitIso_projection]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (DFinsupp.single (β := fun b : B.obj c => (fiber B R E c).obj ⟨b⟩) r x) t = 0
  exact DFinsupp.single_eq_of_ne hne.symm

/-- Literal covering incidences commute with the whole comparison. -/
theorem cellComparison_incidence (E : B.Elements ⥤ ModR) {c d : C} (f : c ⟶ d) :
    ElementPushdown.map B E f ≫ cellComparison B R E d =
      cellComparison B R E c ≫ ElementProduct.map B bijective E f := by
  classical
  apply Sigma.hom_ext
  intro r
  apply Pi.hom_ext
  intro t
  obtain ⟨w,rfl⟩ := (bijective f).surjective t
  have incoming := ElementProduct.map_projection_lifted B bijective E
    (ElementPushdown.lift B f w)
  change ElementProduct.map B bijective E f ≫
      ElementProduct.projection B E d (B.map f w) =
    ElementProduct.projection B E c w ≫ E.map (ElementPushdown.lift B f w) at incoming
  change (ElementPushdown.inclusion B E c r ≫
      (ElementPushdown.map B E f ≫ cellComparison B R E d)) ≫
        ElementProduct.projection B E d (B.map f w) =
    (ElementPushdown.inclusion B E c r ≫
      (cellComparison B R E c ≫ ElementProduct.map B bijective E f)) ≫
        ElementProduct.projection B E d (B.map f w)
  simp only [Category.assoc,ElementPushdown.inclusion_map_assoc]
  rw [incoming]
  by_cases h : r = w
  · subst w
    simp only [inclusion_comparison_projection_self,
      inclusion_comparison_projection_self_assoc,Category.comp_id,Category.id_comp]
  · have different : B.map f r ≠ B.map f w := fun e => h ((bijective f).injective e)
    simp only [inclusion_comparison_projection_ne B R E d _ _ different,
      inclusion_comparison_projection_ne_assoc B R E c _ _ h,comp_zero,zero_comp]

def diagramComparison (E : B.Elements ⥤ ModR) :
    (ElementPushdown.functor B).obj E ⟶ (ElementProduct.functor B bijective).obj E where
  app := cellComparison B R E
  naturality {_ _} f := cellComparison_incidence B bijective R E f

/-- The inclusion/projection matrix is also natural in every
coefficient transformation, without support restrictions. -/
def comparison : ElementPushdown.functor B (D := ModR) ⟶
    ElementProduct.functor B bijective where
  app := diagramComparison B bijective R
  naturality {E F} α := by
    apply NatTrans.ext
    funext c
    apply Sigma.hom_ext
    intro r
    apply Pi.hom_ext
    intro t
    change (ElementPushdown.inclusion B E c r ≫
        (ElementPushdown.cellMap B α c ≫ cellComparison B R F c)) ≫
          ElementProduct.projection B F c t =
      (ElementPushdown.inclusion B E c r ≫
        (cellComparison B R E c ≫ ElementProduct.cellMap B α c)) ≫
          ElementProduct.projection B F c t
    simp only [Category.assoc,ElementPushdown.inclusion_cellMap_assoc,
      ElementProduct.cellMap_projection]
    by_cases h : r = t
    · subst t
      simp only [inclusion_comparison_projection_self,
        inclusion_comparison_projection_self_assoc,Category.comp_id,Category.id_comp]
    · simp only [inclusion_comparison_projection_ne B R F c _ _ h,
        inclusion_comparison_projection_ne_assoc B R E c _ _ h,comp_zero,zero_comp]

/-- Finite support makes the actual canonical comparison invertible
on this fiber. There is no bound on the ambient lattice of sheets. -/
theorem cellComparison_isIso (E : B.Elements ⥤ ModR) (c : C)
    (finite : {r : B.obj c | ¬ IsZero (E.obj (B.elementsMk c r))}.Finite) :
    IsIso (cellComparison B R E c) := by
  letI := ModuleDirectSum.sumToProduct_app_isIso R (fiber B R E c) finite
  unfold cellComparison
  infer_instance

theorem comparison_app_isIso (E : B.Elements ⥤ ModR)
    (finite : ∀ c : C, {r : B.obj c | ¬ IsZero (E.obj (B.elementsMk c r))}.Finite) :
    IsIso ((comparison B bijective R).app E) := by
  haveI (c : C) : IsIso (((comparison B bijective R).app E).app c) :=
    cellComparison_isIso B R E c (finite c)
  exact NatIso.isIso_of_isIso_app _

/-- Only cohomological fiber support is required for the actual
covering sum-to-product map on arbitrary unbounded complexes. -/
theorem comparison_complex_quasiIso
    (K : CochainComplex (B.Elements ⥤ ModR) ℤ)
    (finite : ∀ (q : ℤ) (c : C),
      {r : B.obj c | ¬ IsZero ((K.homology q).obj (B.elementsMk c r))}.Finite) :
    QuasiIso ((NatTrans.mapHomologicalComplex (comparison B bijective R) (.up ℤ)).app K) :=
  exactTransformation_complex_quasiIso (comparison B bijective R) (.up ℤ) K
    (fun q => comparison_app_isIso B bijective R (K.homology q) (finite q))

end ToricPower.ElementComparison

end
