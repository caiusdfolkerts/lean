module

public import ToricPower.ToricLineBundleFrames
public import ToricPower.FanRayPrimitive

/-!
# Invariant representatives of arbitrary toric line bundles

Every actual invertible sheaf is trivial on the dense torus and on every
smooth affine chart. Relative to a fixed torus frame, each chart generator
is a Laurent unit, hence a scalar times an integral character. The scalar
has zero Cartier class. The remaining character values agree on common
rays, producing an invariant coefficient vector. The actual Cartier
sheaves are then identified by their local equations.

All cone dimensions are retained. Equality of characters is needed only
on rays; complementary Laurent directions may differ by regular units.

The rational-frame argument adapts the genuine proofs in
BondalThomsen/Toric/Divisor/PicardSurjective.lean,
PicardCharacterGluing.lean, and CartierFaithfulness.lean at commit
9a2bdcdcf6b25710459f7f476c9c62de3039b7bb.

The invariant representative is proved independently of any power-map
splitting theorem. The latter wrappers are in `DivisorWeightClassification`.
-/

@[expose] public noncomputable section

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.Toric MonoidAlgebra
open scoped Classical

namespace ToricPower

universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The generic-point map for a nonempty open immersion is injective. -/
private theorem invariantClassification_openImmersionGerm_injective
    {Source Target : Scheme.{u}} [IsIntegral Target] [Nonempty Source]
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion] :
    Function.Injective (openImmersionGerm inclusion) := by
  letI : Nonempty inclusion.opensRange := by
    obtain ⟨point⟩ := (inferInstance : Nonempty Source)
    exact ⟨⟨_, ⟨point, rfl⟩⟩⟩
  exact (Target.germToFunctionField_injective inclusion.opensRange).comp
    (IsOpenImmersion.ΓIsoTop inclusion).commRingCatIsoToRingEquiv.injective

/-- The dense torus coordinates embed in the actual toric function field. -/
theorem toricLaurentGerm_injective (fan : Fan i) (nonempty : Nonempty fan.cones) :
    Function.Injective (toricLaurentGerm fan nonempty) := by
  letI := toricSchemeIntegral fan nonempty
  exact (invariantClassification_openImmersionGerm_injective
    (fan.denseTorusι nonempty)).comp
      (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice ⊥)).injective

/-- Chart coordinates embed in the actual function field. -/
theorem chartCoordinateGerm_injective (fan : Fan i) (nonempty : Nonempty fan.cones)
    (cone : fan.cones) : Function.Injective (chartCoordinateGerm fan nonempty cone) := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan cone
  change Function.Injective
    ((fan.algebraicRealization.germToFunctionField (fan.affineToricChartι cone).opensRange).hom.comp
      (chartCoordinateSectionsEquiv fan cone).toRingHom)
  exact (fan.algebraicRealization.germToFunctionField_injective _).comp
    (chartCoordinateSectionsEquiv fan cone).injective

/-- Restriction to the torus is literal inclusion of integral character
exponents in its group algebra. -/
theorem denseTorusCoordinateRingEquiv_face (fan : Fan i) (cone : fan.cones)
    (p : affineCoordinateRing fan.lattice cone.val) :
    denseTorusCoordinateRingEquiv fan.lattice
      (faceAffineCoordinateRingMap fan.lattice
        ((fan.isToricCone cone.property).salient.bot_isFaceOf) p) =
      mapDomain (dualSemigroup fan.lattice cone.val).subtype.toMultiplicative p := by
  induction p using induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq, mapDomain_add]
  | single m c =>
      change denseTorusCoordinateRingEquiv fan.lattice
        (faceAffineCoordinateRingMap fan.lattice
          ((fan.isToricCone cone.property).salient.bot_isFaceOf)
          (single (Multiplicative.ofAdd m.toAdd) c)) = _
      rw [faceAffineCoordinateRingMap_single fan.lattice
          ((fan.isToricCone cone.property).salient.bot_isFaceOf) m.toAdd c,
        denseTorusCoordinateRingEquiv_single, mapDomain_single]
      rfl

/-- If a rational character is regular on a chart, its exponent belongs to
that chart's actual dual semigroup. -/
theorem character_mem_dualSemigroup_of_chart_germ (fan : Fan i)
    (nonempty : Nonempty fan.cones) (cone : fan.cones) (character : N →+ ℤ)
    (p : affineCoordinateRing fan.lattice cone.val)
    (same : chartCoordinateGerm fan nonempty cone p =
      (rationalCharacterUnit fan nonempty character :
        (letI := toricSchemeIntegral fan nonempty; fan.algebraicRealization.functionField))) :
    character ∈ dualSemigroup fan.lattice cone.val := by
  letI := toricSchemeIntegral fan nonempty
  have torus_same : faceAffineCoordinateRingMap fan.lattice
      ((fan.isToricCone cone.property).salient.bot_isFaceOf) p =
      (denseTorusCharacterUnit fan character).val := by
    apply toricLaurentGerm_injective fan nonempty
    exact (chartCoordinateGerm_torus fan nonempty cone p).symm.trans same
  have laurent_same : mapDomain (dualSemigroup fan.lattice cone.val).subtype.toMultiplicative p =
      single (Multiplicative.ofAdd character) (1 : ℂ) := by
    rw [← denseTorusCoordinateRingEquiv_face, torus_same]
    exact denseTorusCoordinateRingEquiv_single fan.lattice _ 1
  have member : Multiplicative.ofAdd character ∈
      (mapDomain (dualSemigroup fan.lattice cone.val).subtype.toMultiplicative p).coeff.support := by
    rw [laurent_same]
    simp
  obtain ⟨m, hm, equal⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support member)
  have exponent : (Multiplicative.toAdd m).val = character :=
    congrArg Multiplicative.toAdd equal
  exact exponent ▸ (Multiplicative.toAdd m).property

/-- A regular monomial unit has both exponent signs in the dual semigroup. -/
theorem character_dualSemigroup_pair_of_chart_unit (fan : Fan i)
    (nonempty : Nonempty fan.cones) (cone : fan.cones) (character : N →+ ℤ)
    (unit : (affineCoordinateRing fan.lattice cone.val)ˣ)
    (same : Units.map (chartCoordinateGerm fan nonempty cone).toMonoidHom unit =
      rationalCharacterUnit fan nonempty character) :
    character ∈ dualSemigroup fan.lattice cone.val ∧
      -character ∈ dualSemigroup fan.lattice cone.val := by
  constructor
  · exact character_mem_dualSemigroup_of_chart_germ fan nonempty cone character unit.val
      (congrArg Units.val same)
  · apply character_mem_dualSemigroup_of_chart_germ fan nonempty cone (-character) unit.inv
    have inverse_same := congrArg (fun value => value⁻¹) same
    rw [← map_inv, ← rationalCharacterUnit_neg] at inverse_same
    exact congrArg Units.val inverse_same

/-- Equality of actual local Cartier classes of characters forces their
difference to be a regular monomial unit. -/
theorem character_pair_of_rationalUnitClass_eq (fan : Fan i)
    (nonempty : Nonempty fan.cones) (cone : fan.cones) (first second : N →+ ℤ)
    (same : letI := toricSchemeIntegral fan nonempty
      letI := chartOpen_nonempty fan cone
      TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass fan.algebraicRealization
        (fan.affineToricChartι cone).opensRange
        (Additive.ofMul (rationalCharacterUnit fan nonempty first)) =
      TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass fan.algebraicRealization
        (fan.affineToricChartι cone).opensRange
        (Additive.ofMul (rationalCharacterUnit fan nonempty second))) :
    first - second ∈ dualSemigroup fan.lattice cone.val ∧
      -(first - second) ∈ dualSemigroup fan.lattice cone.val := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan cone
  obtain ⟨section_unit, relation⟩ :=
    (TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_eq_rationalUnitClass_iff
      fan.algebraicRealization (fan.affineToricChartι cone).opensRange
      (rationalCharacterUnit fan nonempty first)
      (rationalCharacterUnit fan nonempty second)).mp same
  let coordinate_unit := Units.map (chartCoordinateSectionsEquiv fan cone).symm.toMonoidHom section_unit
  have transported := chartCoordinateGerm_regularUnit fan nonempty cone coordinate_unit
  have section_same : Units.map (chartCoordinateSectionsEquiv fan cone).toMonoidHom coordinate_unit =
      section_unit := by
    apply Units.ext
    exact (chartCoordinateSectionsEquiv fan cone).apply_symm_apply section_unit.val
  rw [section_same] at transported
  apply character_dualSemigroup_pair_of_chart_unit fan nonempty cone (first - second) coordinate_unit
  rw [← transported]
  apply mul_right_cancel (b := rationalCharacterUnit fan nonempty second)
  rw [relation, rationalCharacterUnit_sub_mul]

/-- The dense torus lies in every chart, including smaller-dimensional ones. -/
theorem toricTorusOpen_le_chartOpen (fan : Fan i) (nonempty : Nonempty fan.cones)
    (cone : fan.cones) :
    (fan.denseTorusι nonempty).opensRange ≤ (fan.affineToricChartι cone).opensRange := by
  have same := (fan.denseTorusι_eq nonempty (Nonempty.intro cone)).trans (fan.denseTorusι_face cone)
  rintro point ⟨torusPoint, rfl⟩
  rw [same]
  exact ⟨_, rfl⟩

/-- The scalar unit viewed in the actual global function field. -/
def rationalScalarUnit (fan : Fan i) (nonempty : Nonempty fan.cones) (c : ℂˣ) :
    letI := toricSchemeIntegral fan nonempty
    fan.algebraicRealization.functionFieldˣ :=
  Units.map (toricLaurentGerm fan nonempty).toMonoidHom (denseTorusScalarUnit fan c)

theorem rationalScalarUnit_chart (fan : Fan i) (nonempty : Nonempty fan.cones)
    (cone : fan.cones) (c : ℂˣ) :
    Units.map (chartCoordinateGerm fan nonempty cone).toMonoidHom
      (Units.map (algebraMap ℂ (affineCoordinateRing fan.lattice cone.val)).toMonoidHom c) =
      rationalScalarUnit fan nonempty c := by
  apply Units.ext
  change chartCoordinateGerm fan nonempty cone
    (algebraMap ℂ (affineCoordinateRing fan.lattice cone.val) (c : ℂ)) =
      toricLaurentGerm fan nonempty
        (algebraMap ℂ (affineCoordinateRing fan.lattice ⊥) (c : ℂ))
  rw [chartCoordinateGerm_torus]
  congr 1
  exact (faceAffineCoordinateRingMap fan.lattice
    ((fan.isToricCone cone.property).salient.bot_isFaceOf)).commutes _

/-- Scalars are regular units, so their actual Cartier class vanishes on
all affine charts. -/
theorem rationalScalarUnit_class_zero (fan : Fan i) (nonempty : Nonempty fan.cones)
    (cone : fan.cones) (c : ℂˣ) :
    letI := toricSchemeIntegral fan nonempty
    letI := chartOpen_nonempty fan cone
    TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass fan.algebraicRealization
      (fan.affineToricChartι cone).opensRange
        (Additive.ofMul (rationalScalarUnit fan nonempty c)) = 0 := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan cone
  let unit := Units.map (algebraMap ℂ (affineCoordinateRing fan.lattice cone.val)).toMonoidHom c
  rw [← rationalScalarUnit_chart fan nonempty cone c,
    ← chartCoordinateGerm_regularUnit fan nonempty cone unit]
  exact TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_germToFunctionField_eq_zero
    fan.algebraicRealization _ _

def torusCoordinateSectionsEquiv (fan : Fan i) (nonempty : Nonempty fan.cones) :
    affineCoordinateRing fan.lattice ⊥ ≃+*
      Γ(fan.algebraicRealization, (fan.denseTorusι nonempty).opensRange) :=
  (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice ⊥)).trans
    (IsOpenImmersion.ΓIsoTop (fan.denseTorusι nonempty)).commRingCatIsoToRingEquiv

/-- Relative to the torus frame, every chart basis is an actual Laurent
unit: it is the transition function between two genuine free frames. -/
theorem toricLineBundleChartRationalUnit_has_torusUnit (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F]
    (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    letI := chartOpen_nonempty fan cone
    ∃ unit : (affineCoordinateRing fan.lattice ⊥)ˣ,
      Units.map (toricLaurentGerm fan nonempty).toMonoidHom unit =
        Scheme.Modules.trivializationGeneratorRationalUnit F
          (toricLineBundleTorusFrame fan nonempty F) (toricTorusOpen_dense fan nonempty)
          (toricLineBundleChartFrame fan regular cone F) := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan cone
  let T := (fan.denseTorusι nonempty).opensRange
  letI : Nonempty T := by
    obtain ⟨point⟩ := (inferInstance : Nonempty fan.denseTorus)
    exact ⟨⟨_, ⟨point, rfl⟩⟩⟩
  let torusFrame := toricLineBundleTorusFrame fan nonempty F
  let chartFrame := toricLineBundleChartFrame fan regular cone F
  let included : T ⟶ (fan.affineToricChartι cone).opensRange :=
    homOfLE (toricTorusOpen_le_chartOpen fan nonempty cone)
  obtain ⟨sectionUnit, transition, _⟩ :=
    Scheme.Modules.existsUnique_map_trivializationGenerator_eq_smul F chartFrame torusFrame
      included (𝟙 T)
  let coordinateUnit := Units.map (torusCoordinateSectionsEquiv fan nonempty).symm.toMonoidHom sectionUnit
  refine ⟨coordinateUnit, Units.ext ?_⟩
  change fan.algebraicRealization.germToFunctionField T
    (torusCoordinateSectionsEquiv fan nonempty coordinateUnit.val) = _
  rw [show torusCoordinateSectionsEquiv fan nonempty coordinateUnit.val = sectionUnit.val from
    (torusCoordinateSectionsEquiv fan nonempty).apply_symm_apply _]
  rw [Scheme.Modules.coe_trivializationGeneratorRationalUnit,
    ← Scheme.Modules.rationalFunction_map F torusFrame
      (toricTorusOpen_dense fan nonempty) included, transition,
    Scheme.Modules.rationalFunction_smul]
  simp only [op_id]
  rw [F.presheaf.map_id]
  change _ = _ * Scheme.Modules.rationalFunction F torusFrame
    (toricTorusOpen_dense fan nonempty) T (Scheme.Modules.trivializationGenerator F torusFrame)
  rw [Scheme.Modules.rationalFunction_trivializationGenerator_self, mul_one]

/-- The rational value of every chart frame is a scalar times a character. -/
theorem toricLineBundleChartRationalUnit_eq_scalar_character (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F]
    (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    letI := chartOpen_nonempty fan cone
    ∃ character : N →+ ℤ, ∃ scalar : ℂˣ,
      Scheme.Modules.trivializationGeneratorRationalUnit F
        (toricLineBundleTorusFrame fan nonempty F) (toricTorusOpen_dense fan nonempty)
        (toricLineBundleChartFrame fan regular cone F) =
      rationalScalarUnit fan nonempty scalar * rationalCharacterUnit fan nonempty character := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan cone
  obtain ⟨unit, same⟩ := toricLineBundleChartRationalUnit_has_torusUnit fan nonempty regular F cone
  obtain ⟨character, scalar, classified⟩ := denseTorusUnit_eq_scalar_character fan unit
  refine ⟨character, scalar, ?_⟩
  rw [← same, classified, map_mul]
  rfl

def toricLineBundleChartCharacter (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F]
    (cone : fan.cones) : N →+ ℤ :=
  (toricLineBundleChartRationalUnit_eq_scalar_character fan nonempty regular F cone).choose

theorem toricLineBundleChartCharacter_spec (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F]
    (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    letI := chartOpen_nonempty fan cone
    ∃ scalar : ℂˣ,
      Scheme.Modules.trivializationGeneratorRationalUnit F
        (toricLineBundleTorusFrame fan nonempty F) (toricTorusOpen_dense fan nonempty)
        (toricLineBundleChartFrame fan regular cone F) =
      rationalScalarUnit fan nonempty scalar * rationalCharacterUnit fan nonempty
        (toricLineBundleChartCharacter fan nonempty regular F cone) :=
  (toricLineBundleChartRationalUnit_eq_scalar_character fan nonempty regular F cone).choose_spec

/-- The actual Cartier representative constructed from the fixed torus
frame; its local equations are inverses of rational frame generators. -/
def toricLineBundleCartier (fan : Fan i) (nonempty : Nonempty fan.cones)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F] :
    letI := toricSchemeIntegral fan nonempty
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor fan.algebraicRealization := by
  letI := toricSchemeIntegral fan nonempty
  exact (F.exists_cartierDivisor_restrict_eq (toricLineBundleTorusFrame fan nonempty F)
    (toricTorusOpen_dense fan nonempty)).choose

theorem toricLineBundleCartier_spec (fan : Fan i) (nonempty : Nonempty fan.cones)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F] :
    letI := toricSchemeIntegral fan nonempty
    ∀ (U : fan.algebraicRealization.Opens) [Nonempty U]
      (frame : SheafOfModules.free (R := fan.algebraicRealization.ringCatSheaf.over U) PUnit ≅ F.over U),
      toricLineBundleCartier fan nonempty F |_ U =
        TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass fan.algebraicRealization U
          (-Additive.ofMul (Scheme.Modules.trivializationGeneratorRationalUnit F
            (toricLineBundleTorusFrame fan nonempty F) (toricTorusOpen_dense fan nonempty) frame)) := by
  letI := toricSchemeIntegral fan nonempty
  exact (F.exists_cartierDivisor_restrict_eq (toricLineBundleTorusFrame fan nonempty F)
    (toricTorusOpen_dense fan nonempty)).choose_spec

def toricLineBundleCartierIso (fan : Fan i) (nonempty : Nonempty fan.cones)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F] :
    letI := toricSchemeIntegral fan nonempty
    F ≅ (toricLineBundleCartier fan nonempty F).sheaf := by
  letI := toricSchemeIntegral fan nonempty
  exact TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.isoSheafOfRestrictEq
    (toricLineBundleCartier_spec fan nonempty F)

/-- Removing the scalar part does not change the actual local Cartier
class, leaving the inverse chart character as local equation. -/
theorem toricLineBundleCartier_chart (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F]
    (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    letI := chartOpen_nonempty fan cone
    toricLineBundleCartier fan nonempty F |_ (fan.affineToricChartι cone).opensRange =
      TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass fan.algebraicRealization
        (fan.affineToricChartι cone).opensRange
        (Additive.ofMul (rationalCharacterUnit fan nonempty
          (-toricLineBundleChartCharacter fan nonempty regular F cone))) := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan cone
  rw [toricLineBundleCartier_spec fan nonempty F _ (toricLineBundleChartFrame fan regular cone F)]
  obtain ⟨scalar, same⟩ := toricLineBundleChartCharacter_spec fan nonempty regular F cone
  rw [same, ofMul_mul, neg_add, map_add, map_neg, map_neg,
    rationalScalarUnit_class_zero, neg_zero, zero_add, rationalCharacterUnit_neg]
  exact (map_neg _ _).symm

/-- Inclusion of cones gives inclusion of their actual chart opens. -/
theorem toricChartOpen_mono (fan : Fan i) {face cone : fan.cones}
    (included : face ≤ cone) :
    (fan.affineToricChartι face).opensRange ≤ (fan.affineToricChartι cone).opensRange := by
  have same := chart_opensRange_intersection fan face cone
  rw [inf_eq_left.mpr included] at same
  exact same.le.trans inf_le_right

/-- The chart characters agree on every ray of a common face. Equality
of entire characters would be too strong for smaller-dimensional cones. -/
theorem toricLineBundleChartCharacter_face_ray (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F]
    {face cone : fan.cones} (included : face ≤ cone) (ρ : ToricRay face.val) :
    toricLineBundleChartCharacter fan nonempty regular F cone
        (primitiveGenerator fan.lattice (fan.isToricCone face.property) ρ) =
      toricLineBundleChartCharacter fan nonempty regular F face
        (primitiveGenerator fan.lattice (fan.isToricCone face.property) ρ) := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan face
  letI := chartOpen_nonempty fan cone
  have restricted :=
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.rationalUnitClass_eq_of_le
      (toricChartOpen_mono fan included)
      (toricLineBundleCartier_chart fan nonempty regular F cone).symm
  have same := restricted.trans (toricLineBundleCartier_chart fan nonempty regular F face)
  obtain ⟨positive, negative⟩ := character_pair_of_rationalUnitClass_eq fan nonempty face
    (-toricLineBundleChartCharacter fan nonempty regular F cone)
    (-toricLineBundleChartCharacter fan nonempty regular F face) same
  have first := (mem_dualSemigroup_iff_primitiveGenerator fan.lattice
    (fan.isToricCone face.property) _).mp positive ρ
  have second := (mem_dualSemigroup_iff_primitiveGenerator fan.lattice
    (fan.isToricCone face.property) _).mp negative ρ
  simp only [AddMonoidHom.sub_apply, AddMonoidHom.neg_apply] at first second
  omega

/-- The invariant coefficient at a fan ray is the negative of the
corresponding rational frame character evaluated on its primitive generator. -/
def toricLineBundleInvariantCoefficients (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F] :
    fan.Ray → ℤ :=
  fun ρ => -toricLineBundleChartCharacter fan nonempty regular F ρ.val
    (fanRayPrimitiveGenerator fan ρ)

theorem toricLineBundleInvariantCoefficients_ray (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F]
    (cone : fan.cones) (ρ : ToricRay cone.val) :
    coneDivisorCoefficients fan
        (toricLineBundleInvariantCoefficients fan nonempty regular F) cone ρ =
      -toricLineBundleChartCharacter fan nonempty regular F cone
        (primitiveGenerator fan.lattice (fan.isToricCone cone.property) ρ) := by
  let globalRay := Fan.Ray.ofToricRay fan cone ρ
  have same := toricLineBundleChartCharacter_face_ray fan nonempty regular F
    (Fan.Ray.toCone_ofToricRay_le fan cone ρ)
    (Fan.Ray.toToricRay fan globalRay globalRay.val le_rfl)
  change toricLineBundleChartCharacter fan nonempty regular F cone
      (fanRayPrimitiveGenerator fan globalRay) =
    toricLineBundleChartCharacter fan nonempty regular F globalRay.val
      (fanRayPrimitiveGenerator fan globalRay) at same
  change -toricLineBundleChartCharacter fan nonempty regular F globalRay.val
      (fanRayPrimitiveGenerator fan globalRay) = _
  rw [← same]
  exact congrArg (fun point => -toricLineBundleChartCharacter fan nonempty regular F cone point)
    (fanRayPrimitiveGenerator_ofToricRay fan cone ρ)

/-- The arbitrary chart character and the chosen invariant Cartier
character have the same local Cartier class. Their difference is an
actual regular Laurent unit on this chart. -/
theorem toricLineBundleInvariant_localClass (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F]
    (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    letI := chartOpen_nonempty fan cone
    TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass fan.algebraicRealization
      (fan.affineToricChartι cone).opensRange
      (Additive.ofMul (rationalCharacterUnit fan nonempty
        (coneDivisorCharacter fan regular
          (toricLineBundleInvariantCoefficients fan nonempty regular F) cone))) =
    TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass fan.algebraicRealization
      (fan.affineToricChartι cone).opensRange
      (Additive.ofMul (rationalCharacterUnit fan nonempty
        (-toricLineBundleChartCharacter fan nonempty regular F cone))) := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan cone
  let first := coneDivisorCharacter fan regular
    (toricLineBundleInvariantCoefficients fan nonempty regular F) cone
  let second := -toricLineBundleChartCharacter fan nonempty regular F cone
  have vanishes : ∀ ρ : ToricRay cone.val,
      (first - second) (primitiveGenerator fan.lattice (fan.isToricCone cone.property) ρ) = 0 := by
    intro ρ
    change coneDivisorCharacter fan regular
        (toricLineBundleInvariantCoefficients fan nonempty regular F) cone _ -
      (-toricLineBundleChartCharacter fan nonempty regular F cone) _ = 0
    rw [coneDivisorCharacter_ray, toricLineBundleInvariantCoefficients_ray,
      AddMonoidHom.neg_apply, sub_self]
  have positive : first - second ∈ dualSemigroup fan.lattice cone.val := by
    rw [mem_dualSemigroup_iff_primitiveGenerator fan.lattice (fan.isToricCone cone.property)]
    intro ρ
    rw [vanishes]
  have negative : -(first - second) ∈ dualSemigroup fan.lattice cone.val := by
    rw [mem_dualSemigroup_iff_primitiveGenerator fan.lattice (fan.isToricCone cone.property)]
    intro ρ
    rw [AddMonoidHom.neg_apply, vanishes, neg_zero]
  let unit := toricMonomialUnit fan.lattice cone.val (first - second) positive negative
  apply (TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_eq_rationalUnitClass_iff
    fan.algebraicRealization (fan.affineToricChartι cone).opensRange
    (rationalCharacterUnit fan nonempty first) (rationalCharacterUnit fan nonempty second)).mpr
  refine ⟨Units.map (chartCoordinateSectionsEquiv fan cone).toMonoidHom unit, ?_⟩
  rw [chartCoordinateGerm_regularUnit, chartCoordinateGerm_monomialUnit,
    rationalCharacterUnit_sub_mul]

/-- The invariant divisor is literally the Cartier representative of the
arbitrary invertible sheaf, by uniqueness of actual sheaf gluing. -/
theorem toricLineBundleInvariantCartier_eq (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F] :
    letI := toricSchemeIntegral fan nonempty
    invariantCartierDivisor fan nonempty regular
      (toricLineBundleInvariantCoefficients fan nonempty regular F) =
        toricLineBundleCartier fan nonempty F := by
  letI := toricSchemeIntegral fan nonempty
  let atlas := (invariantDivisorCharacterAtlas fan regular
    (toricLineBundleInvariantCoefficients fan nonempty regular F)).cartierEquationAtlas nonempty
  apply atlas.existsUnique_cartierDivisor.unique
    (fun cone => atlas.cartierDivisor_restrict cone)
  intro cone
  letI := chartOpen_nonempty fan cone
  exact (toricLineBundleCartier_chart fan nonempty regular F cone).trans
    (toricLineBundleInvariant_localClass fan nonempty regular F cone).symm

/-- Every actual line bundle on a smooth toric fan is isomorphic to the
actual Cartier sheaf of an invariant ray coefficient vector. -/
def toricLineBundleInvariantIso (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F] :
    letI := toricSchemeIntegral fan nonempty
    F ≅ (invariantCartierDivisor fan nonempty regular
      (toricLineBundleInvariantCoefficients fan nonempty regular F)).sheaf := by
  letI := toricSchemeIntegral fan nonempty
  exact toricLineBundleCartierIso fan nonempty F ≪≫
    eqToIso (congrArg TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheaf
      (toricLineBundleInvariantCartier_eq fan nonempty regular F).symm)

theorem toricLineBundle_exists_invariant (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F] :
    letI := toricSchemeIntegral fan nonempty
    ∃ b : fan.Ray → ℤ, Nonempty
      (F ≅ (invariantCartierDivisor fan nonempty regular b).sheaf) := by
  letI := toricSchemeIntegral fan nonempty
  exact ⟨toricLineBundleInvariantCoefficients fan nonempty regular F,
    ⟨toricLineBundleInvariantIso fan nonempty regular F⟩⟩

end ToricPower
