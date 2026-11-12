module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# A genuine point-supported model on a local face star

The right adjoint to evaluation at a cell is the diagram of functions
from the actual incoming incidences. On an upper face star this is the
closed-cell skyscraper: its value away from the minimal cell is zero.
The evaluation unit is a quasi-isomorphism whenever the original complex
is acyclic at every other cell. This works for arbitrary unbounded
complexes and arbitrary coefficient modules.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe u

variable (R : Type u) [Ring R] {C : Type u} [Category.{u} C]

/-- Coinduction from an actual cell uses every actual incoming incidence. -/
def pointCoinduced (c : C) (M : ModuleCat.{u} R) : C ⥤ ModuleCat.{u} R where
  obj d := ModuleCat.of R ((d ⟶ c) → M)
  map f := ModuleCat.ofHom
    { toFun := fun x g => x (f ≫ g)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_id d := by
    ext x g
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id, LinearMap.id_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Category.id_comp]
  map_comp f g := by
    ext x h
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.comp_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Category.assoc]

/-- Coinduction is functorial in its actual coefficient module. -/
def pointCoinducedFunctor (c : C) : ModuleCat.{u} R ⥤ C ⥤ ModuleCat.{u} R where
  obj := pointCoinduced R c
  map f :=
    { app d := ModuleCat.ofHom
        { toFun := fun x g => f (x g)
          map_add' := by intros; ext g; exact map_add f.hom _ _
          map_smul' := by intros; ext g; exact map_smul f.hom _ _ }
      naturality {_ _} _ := rfl }
  map_id M := rfl
  map_comp f g := rfl

instance pointCoinducedFunctor_additive (c : C) :
    (pointCoinducedFunctor R c).Additive where
  map_add := rfl

/-- The literal evaluation unit transports a section along every
incoming incidence. In particular it includes all face maps. -/
def pointCoinducedUnit (c : C) :
    𝟭 (C ⥤ ModuleCat.{u} R) ⟶
      (evaluation C (ModuleCat.{u} R)).obj c ⋙ pointCoinducedFunctor R c where
  app F :=
    { app d := ModuleCat.ofHom
        { toFun := fun x f => F.map f x
          map_add' := by intros; ext f; exact map_add (F.map f).hom _ _
          map_smul' := by intros; ext f; exact map_smul (F.map f).hom _ _ }
      naturality {_ _} f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        funext g
        exact (ConcreteCategory.congr_hom (F.map_comp f g) x).symm }
  naturality {_ _} f := by
    apply NatTrans.ext
    funext d
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext g
    exact (ConcreteCategory.congr_hom (f.naturality g) x).symm

/-- At a cell with only its identity endomorphism, the unit is an
isomorphism, with inverse evaluation at that identity. -/
instance pointCoinducedUnit_self_isIso (c : C) [Subsingleton (c ⟶ c)]
    (F : C ⥤ ModuleCat.{u} R) :
    IsIso (((pointCoinducedUnit R c).app F).app c) := by
  let inverse : (pointCoinduced R c (F.obj c)).obj c ⟶ F.obj c :=
    ModuleCat.ofHom
      { toFun := fun x => x (𝟙 c)
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
  refine ⟨⟨inverse, ?_, ?_⟩⟩
  · ext x
    change F.map (𝟙 c) x = x
    simp only [CategoryTheory.Functor.map_id, ModuleCat.id_apply]
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext g
    have hg : g = 𝟙 c := Subsingleton.elim _ _
    subst g
    change F.map (𝟙 c) (x (𝟙 c)) = x (𝟙 c)
    simp only [CategoryTheory.Functor.map_id, ModuleCat.id_apply]

/-- Where no incidence enters the chosen cell, the actual coinduced
module is zero. -/
theorem pointCoinduced_isZero (c d : C) [IsEmpty (d ⟶ c)]
    (M : ModuleCat.{u} R) : IsZero ((pointCoinduced R c M).obj d) := by
  change IsZero (ModuleCat.of R ((d ⟶ c) → M))
  exact ModuleCat.isZero_of_subsingleton _

variable {ι : Type*} (shape : ComplexShape ι)

/-- The same unit on complete complexes of diagrams. -/
def pointComplexUnit (c : C) (K : HomologicalComplex (C ⥤ ModuleCat.{u} R) shape) :
    K ⟶ (((evaluation C (ModuleCat.{u} R)).obj c ⋙
      pointCoinducedFunctor R c).mapHomologicalComplex shape).obj K :=
  (NatTrans.mapHomologicalComplex (pointCoinducedUnit R c) shape).app K

/-- A maximal nonzero stratum in an upper face star has an actual
point-supported derived model. No bound is imposed on its cohomology
degrees, its vector-space dimension, or the size of the face category. -/
theorem pointComplexUnit_quasiIso (c : C) [Subsingleton (c ⟶ c)]
    (incoming : ∀ d : C, d ≠ c → IsEmpty (d ⟶ c))
    (K : HomologicalComplex (C ⥤ ModuleCat.{u} R) shape)
    (vanishes : ∀ d : C, d ≠ c →
      ((((evaluation C (ModuleCat.{u} R)).obj d).mapHomologicalComplex shape).obj K).Acyclic) :
    QuasiIso (pointComplexUnit R shape c K) := by
  classical
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro d
  by_cases hd : d = c
  · subst d
    have : IsIso ((((evaluation C (ModuleCat.{u} R)).obj c).mapHomologicalComplex shape).map
        (pointComplexUnit R shape c K)) := by
      letI : ∀ q, IsIso (((((evaluation C (ModuleCat.{u} R)).obj c).mapHomologicalComplex
          shape).map (pointComplexUnit R shape c K)).f q) :=
        fun q => pointCoinducedUnit_self_isIso R c (K.X q)
      exact HomologicalComplex.Hom.isIso_of_components _
    infer_instance
  · letI : IsEmpty (d ⟶ c) := incoming d hd
    rw [quasiIso_iff]
    intro q
    apply (quasiIsoAt_iff_exactAt _ q (vanishes d hd q)).mpr
    exact HomologicalComplex.ExactAt.of_isZero
      (pointCoinduced_isZero R c d ((K.X q).obj c))

end ToricPower.Cellular

end
