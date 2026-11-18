module

public import ToricPower.ModuleDirectSumComplex

/-!
# Sums and products agree on finite cohomological support

The canonical inclusion of a full direct sum into the full product is
an isomorphism when only finitely many coefficient modules are nonzero.
Exactness of both functors then proves the corresponding assertion for
unbounded complexes with finite support in each cohomological degree.
The hypothesis concerns homology, not the support of the cochain terms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.ModuleDirectSum

variable (R : Type) [CommRing R] {I : Type}

/-- The literal dependent product of a discrete module diagram. -/
def productFunctor : (Discrete I ⥤ ModuleCat.{0} R) ⥤ ModuleCat.{0} R where
  obj F := ModuleCat.of R ((i : I) → F.obj ⟨i⟩)
  map α := ModuleCat.ofHom
    { toFun := fun x i => α.app ⟨i⟩ (x i)
      map_add' := by intros; funext i; exact map_add _ _ _
      map_smul' := by intros; funext i; exact map_smul _ _ _ }
  map_id _ := rfl
  map_comp _ _ := rfl

def productCone (F : Discrete I ⥤ ModuleCat.{0} R) : Cone F where
  pt := (productFunctor R).obj F
  π := Discrete.natTrans (fun i => ModuleCat.ofHom (LinearMap.proj i.as))

def productConeIsLimit (F : Discrete I ⥤ ModuleCat.{0} R) :
    IsLimit (productCone R F) where
  lift s := ModuleCat.ofHom
    { toFun := fun x i => s.π.app ⟨i⟩ x
      map_add' := by intros; funext i; exact map_add _ _ _
      map_smul' := by intros; funext i; exact map_smul _ _ _ }
  fac _ _ := rfl
  uniq s f compatible := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    exact ConcreteCategory.congr_hom (compatible ⟨i⟩) x

def productLimitIso (F : Discrete I ⥤ ModuleCat.{0} R) :
    (productFunctor R).obj F ≅ limit F :=
  (productConeIsLimit R F).conePointUniqueUpToIso (limit.isLimit F)

@[reassoc]
theorem productLimitIso_projection (F : Discrete I ⥤ ModuleCat.{0} R) (i : I) :
    (productLimitIso R F).hom ≫ limit.π F ⟨i⟩ =
      ModuleCat.ofHom (LinearMap.proj i) :=
  (limit.isLimit F).fac (productCone R F) ⟨i⟩

def productFunctorIsoLim : productFunctor R (I := I) ≅ lim :=
  NatIso.ofComponents (productLimitIso R) (by
    intro F G α
    apply limit.hom_ext
    intro i
    change ((productFunctor R).map α ≫ (productLimitIso R G).hom) ≫ limit.π G i =
      ((productLimitIso R F).hom ≫ limMap α) ≫ limit.π G i
    rw [Category.assoc,productLimitIso_projection,Category.assoc,limMap_π,
      ← Category.assoc,productLimitIso_projection]
    rfl)

instance productFunctorAdditive : (productFunctor R (I := I)).Additive where
  map_add := by intros; rfl

instance productFunctorPreservesFiniteLimits :
    PreservesFiniteLimits (productFunctor R (I := I)) :=
  preservesFiniteLimits_of_natIso (productFunctorIsoLim R).symm

instance productFunctorPreservesFiniteColimits :
    PreservesFiniteColimits (productFunctor R (I := I)) :=
  preservesFiniteColimits_of_natIso (productFunctorIsoLim R).symm

/-- The canonical map sends a finitely supported family to the same family. -/
def sumToProduct : sumFunctor R (I := I) ⟶ productFunctor R where
  app F := ModuleCat.ofHom (DFinsupp.coeFnLinearMap R)
  naturality {_ _} _ := rfl

/-- The original canonical map is invertible for finite module support. -/
theorem sumToProduct_app_isIso (F : Discrete I ⥤ ModuleCat.{0} R)
    (finite : {i : I | ¬ IsZero (F.obj ⟨i⟩)}.Finite) :
    IsIso ((sumToProduct R).app F) := by
  classical
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y h
    apply DFinsupp.ext
    intro i
    exact congrFun h i
  · intro x
    refine ⟨DFinsupp.mk finite.toFinset (fun i => x i.val), ?_⟩
    change (DFinsupp.mk finite.toFinset (fun i => x i.val) : (i : I) → F.obj ⟨i⟩) = x
    funext i
    by_cases hi : i ∈ finite.toFinset
    · exact DFinsupp.mk_of_mem hi
    · rw [DFinsupp.mk_of_notMem hi]
      have zero : IsZero (F.obj ⟨i⟩) := by
        by_contra h
        exact hi (finite.mem_toFinset.mpr h)
      haveI := ModuleCat.isZero_iff_subsingleton.mp zero
      exact Subsingleton.elim _ _

/-- The same canonical comparison is a quasi-isomorphism whenever
each homology diagram has finite support. The complexes may be unbounded. -/
theorem sumToProduct_complex_quasiIso
    (K : CochainComplex (Discrete I ⥤ ModuleCat.{0} R) ℤ)
    (finite : ∀ q : ℤ, {i : I | ¬ IsZero ((K.homology q).obj ⟨i⟩)}.Finite) :
    QuasiIso ((NatTrans.mapHomologicalComplex (sumToProduct R) (.up ℤ)).app K) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff,ShortComplex.quasiIso_iff]
  change IsIso (ShortComplex.homologyMap ((K.sc q).mapNatTrans (sumToProduct R)))
  have equality := NatTrans.app_homology (sumToProduct R) (K.sc q)
  have full : IsIso
      (((K.sc q).mapHomologyIso (sumFunctor R)).inv ≫
        ShortComplex.homologyMap ((K.sc q).mapNatTrans (sumToProduct R)) ≫
          ((K.sc q).mapHomologyIso (productFunctor R)).hom) := by
    rw [← equality]
    exact sumToProduct_app_isIso R (K.homology q) (finite q)
  have tail : IsIso
      (ShortComplex.homologyMap ((K.sc q).mapNatTrans (sumToProduct R)) ≫
        ((K.sc q).mapHomologyIso (productFunctor R)).hom) :=
    (isIso_comp_left_iff ((K.sc q).mapHomologyIso (sumFunctor R)).inv _).mp full
  exact (isIso_comp_right_iff _ ((K.sc q).mapHomologyIso (productFunctor R)).hom).mp tail

end ToricPower.ModuleDirectSum

end
