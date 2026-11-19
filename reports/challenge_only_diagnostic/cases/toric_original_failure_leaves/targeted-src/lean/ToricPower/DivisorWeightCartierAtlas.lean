module

public import ToricPower.CartierCore
public import ToricPower.DivisorWeightGeometry
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ToricPower.GeometricCore
public import ToricPower.FanRayIndex
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Cartier divisors on arbitrary smooth toric fans

The local characters are chosen on every cone, including cones of smaller
rank than the lattice. Their differences are units on overlaps, so their
Cartier classes glue in the actual Cartier divisor sheaf. The resulting
invertible sheaf has the local equation and generator signs used by the
Laurent divisor modules.

The general open-immersion and Cartier-atlas lemmas are adapted from
BondalThomsen/Toric/Divisor/DivisorLineBundle.lean, and the monomial-unit
lemmas from Toric/Scheme/TransitionUnits.lean, at commit
9a2bdcdcf6b25710459f7f476c9c62de3039b7bb. The toric construction below uses
the current TauCeti API and does not assume completeness.

Development status: this source is a draft until an ordinary Lean check of
its exact source hash succeeds. It contains no assumed splitting theorem.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.Toric Multiplicative

namespace ToricPower

universe schemeUniverse indexUniverse

def affineGlobalSectionsEquiv (R : Type*) [CommRing R] :
    R ≃+* Γ(Spec (CommRingCat.of R), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm

theorem openImmersion_sectionsIso_inv {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion] :
    (IsOpenImmersion.ΓIsoTop inclusion).inv = inclusion.appLE inclusion.opensRange ⊤
      (by rw [← inclusion.image_top_eq_opensRange, inclusion.preimage_image_eq]) := by
  simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv,
    eqToIso.inv, eqToHom_op, Iso.symm_inv, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

theorem openImmersion_sectionsIso_appLE {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (domain : Target.Opens) (contained : ⊤ ≤ inclusion ⁻¹ᵁ domain) :
    inclusion.appLE domain ⊤ contained ≫ (IsOpenImmersion.ΓIsoTop inclusion).hom =
      Target.presheaf.map (homOfLE (show inclusion.opensRange ≤ domain from by
        rintro point ⟨local_point, rfl⟩
        exact contained (show local_point ∈ (⊤ : Source.Opens) from trivial))).op := by
  simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.op_hom, eqToIso.hom, eqToHom_op]
  rw [← Category.assoc, Scheme.Hom.appLE_appIso_inv, ← Functor.map_comp]
  rfl

variable {SchemeModel : Scheme.{schemeUniverse}} [IsIntegral SchemeModel]

noncomputable def openImmersionGerm {Source : Scheme.{schemeUniverse}}
    [Nonempty Source] (inclusion : Source ⟶ SchemeModel) [IsOpenImmersion inclusion] :
    Γ(Source, ⊤) →+* SchemeModel.functionField := by
  letI : Nonempty inclusion.opensRange := by
    obtain ⟨local_point⟩ := (inferInstance : Nonempty Source)
    exact ⟨⟨_, ⟨local_point, rfl⟩⟩⟩
  exact (SchemeModel.germToFunctionField inclusion.opensRange).hom.comp
    (IsOpenImmersion.ΓIsoTop inclusion).hom.hom

omit [IsIntegral SchemeModel] in

theorem openImmersion_sectionsIso_comp {Source Middle : Scheme.{schemeUniverse}}
    (inner : Source ⟶ Middle) (outer : Middle ⟶ SchemeModel)
    [IsOpenImmersion inner] [IsOpenImmersion outer] :
    inner.appTop ≫ (IsOpenImmersion.ΓIsoTop (inner ≫ outer)).hom =
      (IsOpenImmersion.ΓIsoTop outer).hom ≫ SchemeModel.presheaf.map
        (homOfLE (show (inner ≫ outer).opensRange ≤ outer.opensRange from by
          rintro point ⟨local_point, rfl⟩
          exact ⟨inner local_point, rfl⟩)).op := by
  have outer_contains : ⊤ ≤ outer ⁻¹ᵁ outer.opensRange := by
    rintro point _
    exact ⟨point, rfl⟩
  have inner_contains : ⊤ ≤ inner ⁻¹ᵁ (⊤ : Middle.Opens) := le_top
  have composite_contains : ⊤ ≤ (inner ≫ outer) ⁻¹ᵁ outer.opensRange := by
    rintro point _
    exact ⟨inner point, rfl⟩
  have maps_comp := Scheme.Hom.appLE_comp_appLE inner outer outer.opensRange ⊤ ⊤
    outer_contains inner_contains
  have top_app : inner.appLE ⊤ ⊤ inner_contains = inner.appTop := by
    exact inner.appLE_eq_app
  rw [← openImmersion_sectionsIso_inv outer, top_app] at maps_comp
  calc
    inner.appTop ≫ (IsOpenImmersion.ΓIsoTop (inner ≫ outer)).hom =
        (IsOpenImmersion.ΓIsoTop outer).hom ≫
          ((IsOpenImmersion.ΓIsoTop outer).inv ≫ inner.appTop) ≫
            (IsOpenImmersion.ΓIsoTop (inner ≫ outer)).hom := by simp
    _ = (IsOpenImmersion.ΓIsoTop outer).hom ≫
        (inner ≫ outer).appLE outer.opensRange ⊤ composite_contains ≫
          (IsOpenImmersion.ΓIsoTop (inner ≫ outer)).hom := by rw [maps_comp]
    _ = _ := by rw [openImmersion_sectionsIso_appLE]

theorem openImmersionGerm_comp {Source Middle : Scheme.{schemeUniverse}}
    [Nonempty Source] [Nonempty Middle]
    (inner : Source ⟶ Middle) (outer : Middle ⟶ SchemeModel)
    [IsOpenImmersion inner] [IsOpenImmersion outer] (section_value : Γ(Middle, ⊤)) :
    openImmersionGerm (inner ≫ outer) (inner.appTop section_value) =
      openImmersionGerm outer section_value := by
  unfold openImmersionGerm
  dsimp only [RingHom.comp_apply]
  have sections_same := ConcreteCategory.congr_hom
    (openImmersion_sectionsIso_comp inner outer) section_value
  simp only [ConcreteCategory.comp_apply] at sections_same
  rw [sections_same]
  exact SchemeModel.presheaf.germ_res_apply _ _ _ _

theorem nonempty_integral_open_intersection (first second : SchemeModel.Opens)
    [Nonempty first] [Nonempty second] : Nonempty (first ⊓ second : SchemeModel.Opens) := by
  simpa using nonempty_preirreducible_inter first.isOpen second.isOpen
    (by simpa using (inferInstance : Nonempty first))
    (by simpa using (inferInstance : Nonempty second))

theorem regularUnitGerm_eqToHom {first second : SchemeModel.Opens}
    [Nonempty first] [Nonempty second] (same_open : first = second)
    (unit : Γ(SchemeModel, first)ˣ) :
    TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField SchemeModel second
        (Units.map (SchemeModel.presheaf.map (eqToHom same_open.symm).op).hom.toMonoidHom unit) =
      TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField SchemeModel first unit := by
  subst second
  apply Units.ext
  rw [TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField_apply,
    TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField_apply]
  change SchemeModel.germToFunctionField first
      ((SchemeModel.presheaf.map (eqToHom (rfl : first = first)).op) (unit : Γ(SchemeModel, first))) =
    SchemeModel.germToFunctionField first (unit : Γ(SchemeModel, first))
  simp only [eqToHom_refl, op_id]
  exact congrArg (SchemeModel.germToFunctionField first)
    (ConcreteCategory.congr_hom (SchemeModel.presheaf.map_id (op first))
      (unit : Γ(SchemeModel, first)))

structure CartierEquationAtlas (SchemeModel : Scheme.{schemeUniverse}) [IsIntegral SchemeModel] where
  Index : Type indexUniverse
  chart : Index → SchemeModel.Opens
  covers : IsOpenCover chart
  nonempty_chart : ∀ index, Nonempty (chart index)
  equation : Index → SchemeModel.functionFieldˣ
  transition : ∀ first second, Γ(SchemeModel, chart first ⊓ chart second)ˣ
  transition_equation : ∀ first second,
    letI := nonempty_chart first
    letI := nonempty_chart second
    letI := nonempty_integral_open_intersection (chart first) (chart second)
    TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField SchemeModel
      (chart first ⊓ chart second) (transition first second) * equation second = equation first

namespace CartierEquationAtlas

variable (atlas : CartierEquationAtlas SchemeModel)

noncomputable def localClass (index : atlas.Index) :
    ((TauCeti.AlgebraicGeometry.Scheme.cartierDivisorSheaf SchemeModel).obj.obj
      (op (atlas.chart index)) : Type schemeUniverse) :=
  haveI := atlas.nonempty_chart index
  TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass SchemeModel (atlas.chart index)
    (Additive.ofMul (atlas.equation index))

theorem localClass_compatible : TopCat.Presheaf.IsCompatible
    (TauCeti.AlgebraicGeometry.Scheme.cartierDivisorSheaf SchemeModel).obj
    atlas.chart atlas.localClass := by
  intro first second
  let := atlas.nonempty_chart first
  let := atlas.nonempty_chart second
  let := nonempty_integral_open_intersection (atlas.chart first) (atlas.chart second)
  have first_restriction := TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_restrict
    SchemeModel (U := atlas.chart first) (V := atlas.chart first ⊓ atlas.chart second)
    inf_le_left (Additive.ofMul (atlas.equation first))
  have second_restriction := TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_restrict
    SchemeModel (U := atlas.chart second) (V := atlas.chart first ⊓ atlas.chart second)
    inf_le_right (Additive.ofMul (atlas.equation second))
  have equal_classes := (TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_eq_rationalUnitClass_iff
    SchemeModel (atlas.chart first ⊓ atlas.chart second)
    (atlas.equation first) (atlas.equation second)).mpr
      ⟨atlas.transition first second, atlas.transition_equation first second⟩
  exact first_restriction.trans (equal_classes.trans second_restriction.symm)

theorem existsUnique_cartierDivisor :
    ∃! divisor : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor SchemeModel,
      ∀ index, divisor |_ atlas.chart index = atlas.localClass index := by
  exact (TauCeti.AlgebraicGeometry.Scheme.cartierDivisorSheaf SchemeModel).existsUnique_gluing'
    atlas.chart ⊤ (fun _ => homOfLE le_top)
    (by rw [atlas.covers.iSup_eq_top]) atlas.localClass atlas.localClass_compatible

noncomputable def cartierDivisor :
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor SchemeModel :=
  atlas.existsUnique_cartierDivisor.exists.choose

theorem cartierDivisor_restrict (index : atlas.Index) :
    atlas.cartierDivisor |_ atlas.chart index = atlas.localClass index :=
  atlas.existsUnique_cartierDivisor.exists.choose_spec index

noncomputable def invertibleSheaf : TauCeti.AlgebraicGeometry.InvertibleSheaf SchemeModel :=
  atlas.cartierDivisor.toInvertibleSheaf

noncomputable def chartTrivialization (index : atlas.Index) :
    (SheafOfModules.unit SchemeModel.ringCatSheaf).over (atlas.chart index) ≅
      atlas.invertibleSheaf.obj.over (atlas.chart index) := by
  letI := atlas.nonempty_chart index
  exact (SheafOfModules.overFunctor SchemeModel.ringCatSheaf (atlas.chart index)).mapIso
      (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.unitIsoSheafPrincipalCartierDivisor
        SchemeModel (atlas.equation index)) ≪≫
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheafOverIsoOfRestrictEq
      _ atlas.cartierDivisor (atlas.chart index)
      ((TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor_restrict
        SchemeModel (atlas.equation index) (atlas.chart index)).trans
          (atlas.cartierDivisor_restrict index).symm)

/-- The chosen frame is multiplication by the inverse local equation in the
actual rational-function sheaf. This fixes the sign and its gluing behavior. -/
theorem chartTrivialization_hom_ι (index : atlas.Index) :
    (atlas.chartTrivialization index).hom ≫ atlas.cartierDivisor.sheafι.over (atlas.chart index) =
      (TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions SchemeModel ≫
        TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsMul SchemeModel
          (((atlas.equation index)⁻¹ : SchemeModel.functionFieldˣ) : SchemeModel.functionField)).over
        (atlas.chart index) := by
  letI := atlas.nonempty_chart index
  simp only [chartTrivialization, Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheafOverIsoOfRestrictEq_hom_ι]
  change (SheafOfModules.overFunctor SchemeModel.ringCatSheaf (atlas.chart index)).map
      (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.unitToSheafPrincipalCartierDivisor
        SchemeModel (atlas.equation index)) ≫
    (SheafOfModules.overFunctor SchemeModel.ringCatSheaf (atlas.chart index)).map
      (TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor SchemeModel
        (atlas.equation index)).sheafι = _
  rw [← Functor.map_comp,
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.unitToSheafPrincipalCartierDivisor_ι]

theorem equation_isLocalEquationAt (index : atlas.Index) (point : SchemeModel)
    (contains : point ∈ atlas.chart index) :
    atlas.cartierDivisor.IsLocalEquationAt point (atlas.equation index) := by
  let := atlas.nonempty_chart index
  exact TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq
    (atlas.cartierDivisor_restrict index).symm contains

end CartierEquationAtlas

def cartierOverToAffine {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion] :
    SheafOfModules (Target.ringCatSheaf.over inclusion.opensRange) ⥤ Source.Modules :=
  (Scheme.Modules.overEquiv inclusion.opensRange).functor ⋙
    Scheme.Modules.restrictFunctor inclusion.isoOpensRange.hom

def cartierOverToAffineRestrictionIso {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion] (moduleSheaf : Target.Modules) :
    (cartierOverToAffine inclusion).obj (moduleSheaf.over inclusion.opensRange) ≅
      moduleSheaf.restrict inclusion :=
  (Scheme.Modules.restrictFunctor inclusion.isoOpensRange.hom).mapIso
      ((Scheme.Modules.overFunctorEquiv inclusion.opensRange).app moduleSheaf) ≪≫
    ((Scheme.Modules.restrictFunctorComp inclusion.isoOpensRange.hom inclusion.opensRange.ι).symm.app
      moduleSheaf) ≪≫
    (Scheme.Modules.restrictFunctorCongr inclusion.isoOpensRange_hom_ι).app moduleSheaf

def cartierOverToAffineFrame {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion] (moduleSheaf : Target.Modules)
    (frame : (SheafOfModules.unit Target.ringCatSheaf).over inclusion.opensRange ≅
      moduleSheaf.over inclusion.opensRange) :
    SheafOfModules.unit Source.ringCatSheaf ≅ moduleSheaf.restrict inclusion :=
  (Scheme.Modules.restrictUnitIso inclusion).symm ≪≫
    (cartierOverToAffineRestrictionIso inclusion (SheafOfModules.unit Target.ringCatSheaf)).symm ≪≫
    (cartierOverToAffine inclusion).mapIso frame ≪≫
    cartierOverToAffineRestrictionIso inclusion moduleSheaf


section CartierFrameValues

variable {X : Scheme.{schemeUniverse}} [IsIntegral X]

/-- The chosen atlas frame is the reciprocal equation, on actual sections. -/
theorem CartierEquationAtlas.chartTrivialization_value (atlas : CartierEquationAtlas X)
    (index : atlas.Index) (coefficient : Γ(X, atlas.chart index)) :
    letI := atlas.nonempty_chart index
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv (atlas.chart index)
      (Scheme.Modules.Hom.app atlas.cartierDivisor.sheafι (atlas.chart index)
        ((atlas.chartTrivialization index).hom.val.app
          (op (Over.mk (𝟙 (atlas.chart index)))) coefficient)) =
      (((atlas.equation index)⁻¹ : X.functionFieldˣ) : X.functionField) *
        X.germToFunctionField (atlas.chart index) coefficient := by
  letI := atlas.nonempty_chart index
  have frame := congrArg (fun comparison => comparison.val.app
    (op (Over.mk (𝟙 (atlas.chart index)))) coefficient)
      (atlas.chartTrivialization_hom_ι index)
  change Scheme.Modules.Hom.app atlas.cartierDivisor.sheafι (atlas.chart index)
    ((atlas.chartTrivialization index).hom.val.app
      (op (Over.mk (𝟙 (atlas.chart index)))) coefficient) = _ at frame
  rw [frame]
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv (atlas.chart index)
    (Scheme.Modules.Hom.app (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsMul X
      (((atlas.equation index)⁻¹ : X.functionFieldˣ) : X.functionField)) (atlas.chart index)
        (Scheme.Modules.Hom.app (TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions X)
          (atlas.chart index) coefficient)) = _
  rw [TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_rationalFunctionsMul_app,
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_toRationalFunctions_app]

end CartierFrameValues

section MonomialUnits

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [AddCommGroup Ambient] [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def dualCharacterUnit (lattice : IsIntegralLattice embedding)
    (cone : PointedCone ℝ Ambient) (character : Lattice →+ ℤ)
    (positive : character ∈ dualSemigroup lattice cone)
    (negative : -character ∈ dualSemigroup lattice cone) :
    (Multiplicative (dualSemigroup lattice cone))ˣ where
  val := ofAdd ⟨character, positive⟩
  inv := ofAdd ⟨-character, negative⟩
  val_inv := by
    change (⟨character, positive⟩ : dualSemigroup lattice cone) + ⟨-character, negative⟩ = 0
    apply Subtype.ext
    exact add_neg_cancel character
  inv_val := by
    change (⟨-character, negative⟩ : dualSemigroup lattice cone) + ⟨character, positive⟩ = 0
    apply Subtype.ext
    exact neg_add_cancel character

noncomputable def toricMonomialUnit (lattice : IsIntegralLattice embedding)
    (cone : PointedCone ℝ Ambient) (character : Lattice →+ ℤ)
    (positive : character ∈ dualSemigroup lattice cone)
    (negative : -character ∈ dualSemigroup lattice cone) :
    (affineCoordinateRing lattice cone)ˣ :=
  Units.map (MonoidAlgebra.of ℂ _) (dualCharacterUnit lattice cone character positive negative)

@[simp] theorem toricMonomialUnit_val (lattice : IsIntegralLattice embedding)
    (cone : PointedCone ℝ Ambient) (character : Lattice →+ ℤ)
    (positive : character ∈ dualSemigroup lattice cone)
    (negative : -character ∈ dualSemigroup lattice cone) :
    (toricMonomialUnit lattice cone character positive negative : affineCoordinateRing lattice cone) =
      MonoidAlgebra.single (ofAdd (⟨character, positive⟩ : dualSemigroup lattice cone)) 1 := rfl

theorem toricMonomialUnit_face_restriction (lattice : IsIntegralLattice embedding)
    {cone face : PointedCone ℝ Ambient} (face_of : face.IsFaceOf cone)
    (character : Lattice →+ ℤ) (positive : character ∈ dualSemigroup lattice cone)
    (negative : -character ∈ dualSemigroup lattice cone) :
    Units.map (faceAffineCoordinateRingMap lattice face_of).toMonoidHom
        (toricMonomialUnit lattice cone character positive negative) =
      toricMonomialUnit lattice face character
        (dualSemigroup_anti lattice face_of.le positive)
        (dualSemigroup_anti lattice face_of.le negative) := by
  apply Units.ext
  change faceAffineCoordinateRingMap lattice face_of
      (MonoidAlgebra.single (ofAdd (⟨character, positive⟩ : dualSemigroup lattice cone)) 1) = _
  rw [faceAffineCoordinateRingMap_single]
  rfl

theorem toricMonomialUnit_add (lattice : IsIntegralLattice embedding)
    (cone : PointedCone ℝ Ambient) (first second : Lattice →+ ℤ)
    (first_positive : first ∈ dualSemigroup lattice cone)
    (first_negative : -first ∈ dualSemigroup lattice cone)
    (second_positive : second ∈ dualSemigroup lattice cone)
    (second_negative : -second ∈ dualSemigroup lattice cone) :
    toricMonomialUnit lattice cone first first_positive first_negative *
        toricMonomialUnit lattice cone second second_positive second_negative =
      toricMonomialUnit lattice cone (first + second)
        ((dualSemigroup lattice cone).add_mem first_positive second_positive)
        (by simpa only [neg_add] using
          (dualSemigroup lattice cone).add_mem first_negative second_negative) := by
  apply Units.ext
  simp only [Units.val_mul, toricMonomialUnit_val, MonoidAlgebra.single_mul_single, one_mul]
  rfl

end MonomialUnits

section ToricCharacters

universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

theorem toricSchemeIntegral (fan : Fan i) (nonempty : Nonempty fan.cones) :
    IsIntegral fan.algebraicRealization := by
  obtain ⟨σ⟩ := nonempty
  exact toricScheme_isIntegral fan ⟨σ.val, σ.property⟩

def denseTorusCharacterUnit (fan : Fan i) (character : N →+ ℤ) :
    (affineCoordinateRing fan.lattice ⊥)ˣ :=
  toricMonomialUnit fan.lattice ⊥ character
    (by rw [dualSemigroup_bot]; trivial)
    (by rw [dualSemigroup_bot]; trivial)

theorem denseTorusCharacterUnit_add (fan : Fan i) (first second : N →+ ℤ) :
    denseTorusCharacterUnit fan (first + second) =
      denseTorusCharacterUnit fan first * denseTorusCharacterUnit fan second := by
  unfold denseTorusCharacterUnit
  exact (toricMonomialUnit_add _ _ _ _ _ _ _ _).symm

def toricLaurentGerm (fan : Fan i) (nonempty : Nonempty fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    affineCoordinateRing fan.lattice ⊥ →+* fan.algebraicRealization.functionField := by
  letI := toricSchemeIntegral fan nonempty
  exact (openImmersionGerm (fan.denseTorusι nonempty)).comp
    (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice ⊥)).toRingHom

def rationalCharacterUnit (fan : Fan i) (nonempty : Nonempty fan.cones)
    (character : N →+ ℤ) :
    letI := toricSchemeIntegral fan nonempty
    fan.algebraicRealization.functionFieldˣ := by
  letI := toricSchemeIntegral fan nonempty
  exact Units.map (toricLaurentGerm fan nonempty).toMonoidHom
    (denseTorusCharacterUnit fan character)

theorem rationalCharacterUnit_add (fan : Fan i) (nonempty : Nonempty fan.cones)
    (first second : N →+ ℤ) :
    rationalCharacterUnit fan nonempty (first + second) =
      rationalCharacterUnit fan nonempty first * rationalCharacterUnit fan nonempty second := by
  unfold rationalCharacterUnit
  rw [denseTorusCharacterUnit_add, map_mul]

def chartCoordinateSectionsEquiv (fan : Fan i) (cone : fan.cones) :
    affineCoordinateRing fan.lattice cone.val ≃+*
      Γ(fan.algebraicRealization, (fan.affineToricChartι cone).opensRange) :=
  (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val)).trans
    (IsOpenImmersion.ΓIsoTop (fan.affineToricChartι cone)).commRingCatIsoToRingEquiv

def chartCoordinateGerm (fan : Fan i) (nonempty : Nonempty fan.cones)
    (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    affineCoordinateRing fan.lattice cone.val →+* fan.algebraicRealization.functionField := by
  letI := toricSchemeIntegral fan nonempty
  exact (openImmersionGerm (fan.affineToricChartι cone)).comp
    (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val)).toRingHom

/-- A regular monomial and its Laurent restriction define the same rational
function, with equality proved through the actual open immersion maps. -/
theorem chartCoordinateGerm_torus (fan : Fan i) (nonempty : Nonempty fan.cones)
    (cone : fan.cones) (coordinate : affineCoordinateRing fan.lattice cone.val) :
    chartCoordinateGerm fan nonempty cone coordinate =
      toricLaurentGerm fan nonempty
        (faceAffineCoordinateRingMap fan.lattice
          ((fan.isToricCone cone.property).salient.bot_isFaceOf) coordinate) := by
  letI := toricSchemeIntegral fan nonempty
  let face_map := faceAffineToricSchemeMap fan.lattice
    ((fan.isToricCone cone.property).salient.bot_isFaceOf)
  letI : IsOpenImmersion face_map :=
    (fan.isToricCone cone.property).rational.isOpenImmersion_faceAffineToricSchemeMap _ _
  have same_inclusion := (fan.denseTorusι_eq nonempty (Nonempty.intro cone)).trans
    (fan.denseTorusι_face cone)
  change fan.denseTorusι nonempty = face_map ≫ fan.affineToricChartι cone at same_inclusion
  have naturality := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (faceAffineCoordinateRingMap fan.lattice
      ((fan.isToricCone cone.property).salient.bot_isFaceOf)).toRingHom)
  have naturality_value := ConcreteCategory.congr_hom naturality coordinate
  simp only [ConcreteCategory.comp_apply] at naturality_value
  rw [← faceAffineToricSchemeMap_def] at naturality_value
  change (Scheme.ΓSpecIso _).inv
      (faceAffineCoordinateRingMap fan.lattice
        ((fan.isToricCone cone.property).salient.bot_isFaceOf) coordinate) =
    face_map.appTop ((Scheme.ΓSpecIso _).inv coordinate) at naturality_value
  unfold chartCoordinateGerm toricLaurentGerm
  dsimp only [RingHom.comp_apply, affineGlobalSectionsEquiv]
  change openImmersionGerm (fan.affineToricChartι cone)
      ((Scheme.ΓSpecIso _).inv coordinate) =
    openImmersionGerm (fan.denseTorusι nonempty)
      ((Scheme.ΓSpecIso _).inv
        (faceAffineCoordinateRingMap fan.lattice
          ((fan.isToricCone cone.property).salient.bot_isFaceOf) coordinate))
  have restriction_same := (openImmersionGerm_comp face_map
    (fan.affineToricChartι cone) ((Scheme.ΓSpecIso _).inv coordinate)).symm
  have restriction_same' :
      openImmersionGerm (fan.affineToricChartι cone)
          ((Scheme.ΓSpecIso _).inv coordinate) =
        openImmersionGerm (fan.denseTorusι nonempty)
          (face_map.appTop ((Scheme.ΓSpecIso _).inv coordinate)) := by
    simpa only [← same_inclusion] using restriction_same
  exact restriction_same'.trans
    (congrArg (openImmersionGerm (fan.denseTorusι nonempty)) naturality_value).symm

theorem chartCoordinateGerm_monomialUnit (fan : Fan i) (nonempty : Nonempty fan.cones)
    (cone : fan.cones) (character : N →+ ℤ)
    (positive : character ∈ dualSemigroup fan.lattice cone.val)
    (negative : -character ∈ dualSemigroup fan.lattice cone.val) :
    Units.map (chartCoordinateGerm fan nonempty cone).toMonoidHom
        (toricMonomialUnit fan.lattice cone.val character positive negative) =
      rationalCharacterUnit fan nonempty character := by
  letI := toricSchemeIntegral fan nonempty
  apply Units.ext
  simp only [Units.coe_map]
  change chartCoordinateGerm fan nonempty cone
      (toricMonomialUnit fan.lattice cone.val character positive negative :
        affineCoordinateRing fan.lattice cone.val) = _
  rw [chartCoordinateGerm_torus]
  have restricted := toricMonomialUnit_face_restriction fan.lattice
    ((fan.isToricCone cone.property).salient.bot_isFaceOf) character positive negative
  have restricted_value := congrArg Units.val restricted
  simp only [Units.coe_map] at restricted_value
  exact (congrArg (toricLaurentGerm fan nonempty) restricted_value).trans (by rfl)

theorem chart_opensRange_intersection (fan : Fan i) (first second : fan.cones) :
    (fan.affineToricChartι (first ⊓ second)).opensRange =
      (fan.affineToricChartι first).opensRange ⊓ (fan.affineToricChartι second).opensRange := by
  apply TopologicalSpace.Opens.ext
  exact (fan.range_affineToricChartι_inter_range_affineToricChartι first second).symm

theorem chartOpen_nonempty (fan : Fan i) (cone : fan.cones) :
    Nonempty (fan.affineToricChartι cone).opensRange := by
  obtain ⟨local_point⟩ := (inferInstance : Nonempty (fan.affineToricChart cone))
  exact ⟨⟨_, ⟨local_point, rfl⟩⟩⟩

theorem chartCoordinateGerm_regularUnit (fan : Fan i) (nonempty : Nonempty fan.cones)
    (cone : fan.cones) (unit : (affineCoordinateRing fan.lattice cone.val)ˣ) :
    letI := toricSchemeIntegral fan nonempty
    letI := chartOpen_nonempty fan cone
    TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField
        fan.algebraicRealization (fan.affineToricChartι cone).opensRange
        (Units.map (chartCoordinateSectionsEquiv fan cone).toMonoidHom unit) =
      Units.map (chartCoordinateGerm fan nonempty cone).toMonoidHom unit := by
  apply Units.ext
  rw [TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField_apply]
  rfl

theorem denseTorusCharacterUnit_zero (fan : Fan i) : denseTorusCharacterUnit fan 0 = 1 := by
  apply Units.ext
  change MonoidAlgebra.single (ofAdd (0 : dualSemigroup fan.lattice ⊥)) 1 = 1
  rfl

theorem rationalCharacterUnit_zero (fan : Fan i) (nonempty : Nonempty fan.cones) :
    rationalCharacterUnit fan nonempty 0 = 1 := by
  unfold rationalCharacterUnit
  rw [denseTorusCharacterUnit_zero, map_one]

theorem rationalCharacterUnit_neg (fan : Fan i) (nonempty : Nonempty fan.cones)
    (character : N →+ ℤ) :
    rationalCharacterUnit fan nonempty (-character) =
      (rationalCharacterUnit fan nonempty character)⁻¹ := by
  have cancels := rationalCharacterUnit_add fan nonempty character (-character)
  rw [add_neg_cancel, rationalCharacterUnit_zero] at cancels
  exact mul_eq_one_iff_eq_inv.mp (by simpa only [mul_comm] using cancels.symm)

theorem rationalCharacterUnit_sub_mul (fan : Fan i) (nonempty : Nonempty fan.cones)
    (first second : N →+ ℤ) :
    rationalCharacterUnit fan nonempty (first - second) *
        rationalCharacterUnit fan nonempty second = rationalCharacterUnit fan nonempty first := by
  rw [← rationalCharacterUnit_add, sub_add_cancel]

/-- Cartier data on the full cone cover. Characters here are local equations;
their negatives are the generators of the associated divisor sheaf. -/
structure ToricCharacterAtlas (fan : Fan i) where
  equation : fan.cones → N →+ ℤ
  positive : ∀ first second, equation first - equation second ∈
    dualSemigroup fan.lattice (first ⊓ second).val
  negative : ∀ first second, -(equation first - equation second) ∈
    dualSemigroup fan.lattice (first ⊓ second).val

namespace ToricCharacterAtlas

variable {fan : Fan i}

def transition (atlas : ToricCharacterAtlas fan) (first second : fan.cones) :
    Γ(fan.algebraicRealization,
      (fan.affineToricChartι first).opensRange ⊓ (fan.affineToricChartι second).opensRange)ˣ :=
  Units.map (fan.algebraicRealization.presheaf.map
      (eqToHom (chart_opensRange_intersection fan first second).symm).op).hom.toMonoidHom
    (Units.map (chartCoordinateSectionsEquiv fan (first ⊓ second)).toMonoidHom
      (toricMonomialUnit fan.lattice _ (atlas.equation first - atlas.equation second)
        (atlas.positive first second) (atlas.negative first second)))

theorem transition_germ (atlas : ToricCharacterAtlas fan) (nonempty : Nonempty fan.cones)
    (first second : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    letI := chartOpen_nonempty fan first
    letI := chartOpen_nonempty fan second
    letI := nonempty_integral_open_intersection
      (fan.affineToricChartι first).opensRange (fan.affineToricChartι second).opensRange
    TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField fan.algebraicRealization
        _ (atlas.transition first second) =
      rationalCharacterUnit fan nonempty (atlas.equation first - atlas.equation second) := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan first
  letI := chartOpen_nonempty fan second
  letI := nonempty_integral_open_intersection
    (fan.affineToricChartι first).opensRange (fan.affineToricChartι second).opensRange
  letI := chartOpen_nonempty fan (first ⊓ second)
  have transported := chartCoordinateGerm_regularUnit fan nonempty (first ⊓ second)
    (toricMonomialUnit fan.lattice _ (atlas.equation first - atlas.equation second)
      (atlas.positive first second) (atlas.negative first second))
  have monomial := chartCoordinateGerm_monomialUnit fan nonempty (first ⊓ second)
    (atlas.equation first - atlas.equation second)
    (atlas.positive first second) (atlas.negative first second)
  unfold transition
  exact (regularUnitGerm_eqToHom (chart_opensRange_intersection fan first second) _).trans
    (transported.trans monomial)

def cartierEquationAtlas (atlas : ToricCharacterAtlas fan) (nonempty : Nonempty fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    CartierEquationAtlas fan.algebraicRealization := by
  letI := toricSchemeIntegral fan nonempty
  refine {
    Index := fan.cones
    chart := fun cone => (fan.affineToricChartι cone).opensRange
    covers := ?_
    nonempty_chart := chartOpen_nonempty fan
    equation := fun cone => rationalCharacterUnit fan nonempty (atlas.equation cone)
    transition := atlas.transition
    transition_equation := ?_ }
  · apply IsOpenCover.mk
    apply top_le_iff.mp
    intro point _
    obtain ⟨cone, local_point, rfl⟩ := fan.exists_affineToricChartι_apply_eq point
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨cone, local_point, rfl⟩
  · intro first second
    rw [atlas.transition_germ nonempty]
    exact rationalCharacterUnit_sub_mul fan nonempty _ _

def cartierDivisor (atlas : ToricCharacterAtlas fan) (nonempty : Nonempty fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor fan.algebraicRealization := by
  letI := toricSchemeIntegral fan nonempty
  exact (atlas.cartierEquationAtlas nonempty).cartierDivisor

theorem cartierDivisor_restrict (atlas : ToricCharacterAtlas fan)
    (nonempty : Nonempty fan.cones) (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    letI := chartOpen_nonempty fan cone
    atlas.cartierDivisor nonempty |_ (fan.affineToricChartι cone).opensRange =
      TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass fan.algebraicRealization
        (fan.affineToricChartι cone).opensRange
        (Additive.ofMul (rationalCharacterUnit fan nonempty (atlas.equation cone))) := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan cone
  exact (atlas.cartierEquationAtlas nonempty).cartierDivisor_restrict cone

def chartTrivialization (atlas : ToricCharacterAtlas fan) (nonempty : Nonempty fan.cones)
    (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    (SheafOfModules.unit fan.algebraicRealization.ringCatSheaf).over
        (fan.affineToricChartι cone).opensRange ≅
      (atlas.cartierDivisor nonempty).sheaf.over (fan.affineToricChartι cone).opensRange := by
  letI := toricSchemeIntegral fan nonempty
  exact (atlas.cartierEquationAtlas nonempty).chartTrivialization cone

end ToricCharacterAtlas

/-- The chosen primitive generator is independent of which cone contains the
ray. This is an equality in the integral lattice, not just in its real span. -/
theorem primitiveGenerator_face (hi : IsIntegralLattice i)
    {σ τ : PointedCone ℝ V} (hσ : IsToricCone i σ) (hτ : IsToricCone i τ)
    (hτσ : τ.IsFaceOf σ) (ρ : ToricRay τ) :
    primitiveGenerator hi hσ (ToricRay.faceEmbedding hτσ ρ) =
      primitiveGenerator hi hτ ρ := by
  symm
  exact ((isPrimitiveGenerator_faceEmbedding hτσ ρ).mpr
    (isPrimitiveGenerator_primitiveGenerator hi hτ ρ)).eq_primitiveGenerator hi hσ

/-- Coefficients on a cone are the coefficients of the same intrinsic fan
rays. -/
def coneDivisorCoefficients (fan : Fan i) (b : fan.Ray → ℤ) (cone : fan.cones) :
    ToricRay cone.val → ℤ :=
  fun ρ => b (Fan.Ray.ofToricRay fan cone ρ)

theorem coneDivisorCoefficients_face (fan : Fan i) (b : fan.Ray → ℤ)
    {σ τ : fan.cones} (hτσ : τ.val.IsFaceOf σ.val) (ρ : ToricRay τ.val) :
    coneDivisorCoefficients fan b σ (ToricRay.faceEmbedding hτσ ρ) =
      coneDivisorCoefficients fan b τ ρ := by
  apply congrArg b
  apply Subtype.ext
  apply Subtype.ext
  simpa only [Fan.Ray.toCone_ofToricRay] using
    ToricRay.toPointedCone_faceEmbedding hτσ ρ

/-- A local Cartier equation for every coefficient vector on every smooth
cone. The choice uses the integral basis extension, including its Laurent
coordinates when the cone has smaller dimension than the lattice. -/
def coneDivisorCharacter (fan : Fan i) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (cone : fan.cones) : N →+ ℤ :=
  Classical.choose (regularCone_exists_divisorCharacter fan.lattice
    (Fan.isRegular_iff.mp regular _ cone.property) (coneDivisorCoefficients fan b cone))

theorem coneDivisorCharacter_ray (fan : Fan i) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (cone : fan.cones) (ρ : ToricRay cone.val) :
    coneDivisorCharacter fan regular b cone
        (primitiveGenerator fan.lattice (fan.isToricCone cone.property) ρ) =
      coneDivisorCoefficients fan b cone ρ :=
  Classical.choose_spec (regularCone_exists_divisorCharacter fan.lattice
    (Fan.isRegular_iff.mp regular _ cone.property) (coneDivisorCoefficients fan b cone)) ρ

theorem coneDivisorCharacter_face_ray (fan : Fan i) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) {σ τ : fan.cones} (hτσ : τ.val.IsFaceOf σ.val)
    (ρ : ToricRay τ.val) :
    coneDivisorCharacter fan regular b σ
        (primitiveGenerator fan.lattice (fan.isToricCone τ.property) ρ) =
      coneDivisorCoefficients fan b τ ρ := by
  have h := coneDivisorCharacter_ray fan regular b σ (ToricRay.faceEmbedding hτσ ρ)
  rw [primitiveGenerator_face fan.lattice (fan.isToricCone σ.property)
    (fan.isToricCone τ.property) hτσ ρ, coneDivisorCoefficients_face] at h
  exact h

theorem coneDivisorCharacter_overlap_vanishes (fan : Fan i) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (first second : fan.cones)
    (ρ : ToricRay (first ⊓ second).val) :
    (coneDivisorCharacter fan regular b first - coneDivisorCharacter fan regular b second)
      (primitiveGenerator fan.lattice (fan.isToricCone (first ⊓ second).property) ρ) = 0 := by
  rw [AddMonoidHom.sub_apply,
    coneDivisorCharacter_face_ray fan regular b
      (fan.isFaceOf_of_le first.property (first ⊓ second).property inf_le_left),
    coneDivisorCharacter_face_ray fan regular b
      (fan.isFaceOf_of_le second.property (first ⊓ second).property inf_le_right), sub_self]

/-- All cone equations of an invariant divisor have invertible transition
functions on their actual overlap charts. No maximal-cone or completeness
choice occurs. -/
def invariantDivisorCharacterAtlas (fan : Fan i) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) : ToricCharacterAtlas fan where
  equation := coneDivisorCharacter fan regular b
  positive first second := by
    rw [mem_dualSemigroup_iff_primitiveGenerator fan.lattice
      (fan.isToricCone (first ⊓ second).property)]
    intro ρ
    rw [coneDivisorCharacter_overlap_vanishes]
  negative first second := by
    rw [mem_dualSemigroup_iff_primitiveGenerator fan.lattice
      (fan.isToricCone (first ⊓ second).property)]
    intro ρ
    rw [AddMonoidHom.neg_apply, coneDivisorCharacter_overlap_vanishes, neg_zero]

/-- The actual Cartier divisor attached to an arbitrary invariant coefficient
vector on a smooth, nonempty toric fan. Nonemptiness records the existence of
the dense torus and does not impose completeness or full-dimensional cones. -/
def invariantCartierDivisor (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) :
    letI := toricSchemeIntegral fan nonempty
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor fan.algebraicRealization :=
  (invariantDivisorCharacterAtlas fan regular b).cartierDivisor nonempty

theorem invariantCartierDivisor_localEquation (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) (b : fan.Ray → ℤ)
    (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    letI := chartOpen_nonempty fan cone
    invariantCartierDivisor fan nonempty regular b |_ (fan.affineToricChartι cone).opensRange =
      TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass fan.algebraicRealization
        (fan.affineToricChartι cone).opensRange
        (Additive.ofMul (rationalCharacterUnit fan nonempty
          (coneDivisorCharacter fan regular b cone))) :=
  (invariantDivisorCharacterAtlas fan regular b).cartierDivisor_restrict nonempty cone

def invariantCartierSheafChartTrivialization (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) (b : fan.Ray → ℤ)
    (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    (SheafOfModules.unit fan.algebraicRealization.ringCatSheaf).over
        (fan.affineToricChartι cone).opensRange ≅
      (invariantCartierDivisor fan nonempty regular b).sheaf.over
        (fan.affineToricChartι cone).opensRange :=
  (invariantDivisorCharacterAtlas fan regular b).chartTrivialization nonempty cone

section ChartModuleComparison

variable {κ : Type u} [Fintype κ]

/-- The divisor module over the actual chart coordinate ring. Restriction of
scalars uses the proved integral-character coordinate isomorphism. -/
def toricDivisorChartModule (fan : Fan i) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (b : fan.Ray → ℤ) (cone : fan.cones) :
    ModuleCat (affineCoordinateRing fan.lattice cone.val) :=
  (ModuleCat.restrictScalars
    (affineToricRayChartRingEquiv fan.lattice (fan.isToricCone cone.property) basis).toRingHom).obj
      (ModuleCat.of (RayChartRing ℂ (characterRayMatrix fan.lattice
        (fan.isToricCone cone.property) basis))
        (DivisorSectionModule ℂ (characterRayMatrix fan.lattice
          (fan.isToricCone cone.property) basis) (coneDivisorCoefficients fan b cone) 1))

def toricDivisorChartModuleTrivialization (fan : Fan i) (regular : fan.IsRegular)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ) (cone : fan.cones) :
    affineCoordinateRing fan.lattice cone.val ≃ₗ[affineCoordinateRing fan.lattice cone.val]
      toricDivisorChartModule fan basis b cone := by
  let A := characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis
  let e := affineToricRayChartRingEquiv fan.lattice (fan.isToricCone cone.property) basis
  let q := basis.equivFun (coneDivisorCharacter fan regular b cone)
  have hq : coneDivisorCoefficients fan b cone = rayMap A q := by
    funext ρ
    change coneDivisorCoefficients fan b cone ρ =
      rayMap (characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis)
        (basis.equivFun (coneDivisorCharacter fan regular b cone)) ρ
    rw [characterRayMatrix_apply, coneDivisorCharacter_ray]
  let t := divisorCartierTrivialization ℂ A (coneDivisorCoefficients fan b cone) q hq
  exact {
    toFun := fun a => t (e a)
    invFun := fun x => e.symm (t.symm x)
    left_inv := fun a => by simp only [LinearEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
    right_inv := fun x => by simp only [RingEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    map_add' := fun a a' => by rw [map_add, map_add]
    map_smul' := fun a x => by
      change t (e (a * x)) = e a • t (e x)
      rw [map_mul]
      exact t.map_smul (e a) (e x) }

/-- The Laurent support module is the restriction of the genuine Cartier
divisor sheaf. Both frames use the same chosen equation character, so their
generator is the rational monomial with its negative exponent. -/
def affineCartierDivisorModuleIso (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (b : fan.Ray → ℤ) (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    tilde (toricDivisorChartModule fan basis b cone) ≅
      (invariantCartierDivisor fan nonempty regular b).sheaf.restrict
        (fan.affineToricChartι cone) := by
  letI := toricSchemeIntegral fan nonempty
  exact (tilde.functor (CommRingCat.of (affineCoordinateRing fan.lattice cone.val))).mapIso
      (toricDivisorChartModuleTrivialization fan regular basis b cone).symm.toModuleIso ≪≫
    tildeSelf ≪≫
    cartierOverToAffineFrame (fan.affineToricChartι cone)
      (invariantCartierDivisor fan nonempty regular b).sheaf
      (invariantCartierSheafChartTrivialization fan nonempty regular b cone)

end ChartModuleComparison

end ToricCharacters

end ToricPower
