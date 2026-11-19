module

public import Continuation.Divisor.FanoClosure
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# The ordinary polynomial O(1) sheaf and generic gluing helpers

These recovered proof bodies, with recorded API repairs, construct the
actual sheaf of local homogeneous fractions of degree one and its coordinate
frames. The source selection excludes all fan-specific realizations. The
original source hashes, selected-body hashes and proof-only port changes are
recorded beside this file. These definitions are used to prove the genuine
pullback-O(1) comparison for the original section morphism.
-/

@[expose] public section

section
/- Source: Toric/Projective/DegreeOneDescent.lean; generic schemes and polynomial Proj only. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TopCat

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

attribute [local instance] MvPolynomial.gradedAlgebra

variable (Index : Type)

noncomputable section

abbrev polynomialDegreeOneProj :=
  Proj (MvPolynomial.homogeneousSubmodule Index 𝕜)

abbrev polynomialDegreeOnePointLocalization (point : polynomialDegreeOneProj 𝕜 Index) :=
  Localization point.asHomogeneousIdeal.toIdeal.primeCompl

def polynomialDegreeOneIsFraction {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (section_value : ∀ point : open_set, polynomialDegreeOnePointLocalization 𝕜 Index point.val) : Prop :=
  ∃ (degree : ℕ) (numerator : MvPolynomial.homogeneousSubmodule Index 𝕜 (degree + 1))
    (denominator : MvPolynomial.homogeneousSubmodule Index 𝕜 degree)
    (denominator_nonzero : ∀ point : open_set, denominator.val ∉ point.val.asHomogeneousIdeal),
    ∀ point : open_set, section_value point =
      Localization.mk numerator.val ⟨denominator.val, denominator_nonzero point⟩

def polynomialDegreeOneFractionPrelocal :
    PrelocalPredicate (fun point : polynomialDegreeOneProj 𝕜 Index =>
      polynomialDegreeOnePointLocalization 𝕜 Index point) where
  pred := polynomialDegreeOneIsFraction 𝕜 Index
  res := by
    rintro smaller larger inclusion section_value
      ⟨degree, numerator, denominator, denominator_nonzero, equal⟩
    exact ⟨degree, numerator, denominator, fun point => denominator_nonzero (inclusion point),
      fun point => equal (inclusion point)⟩

def polynomialDegreeOneLocallyFraction :
    LocalPredicate (fun point : polynomialDegreeOneProj 𝕜 Index =>
      polynomialDegreeOnePointLocalization 𝕜 Index point) :=
  (polynomialDegreeOneFractionPrelocal 𝕜 Index).sheafify

noncomputable def polynomialDegreeOneTypeSheaf :
    TopCat.Sheaf (Type) (polynomialDegreeOneProj 𝕜 Index).toTopCat :=
  subsheafToTypes (polynomialDegreeOneLocallyFraction 𝕜 Index)

theorem polynomialDegreeOneLocallyFraction_zero
    (open_set : (polynomialDegreeOneProj 𝕜 Index).Opens) :
    (polynomialDegreeOneLocallyFraction 𝕜 Index).pred
      (0 : ∀ point : open_set, polynomialDegreeOnePointLocalization 𝕜 Index point.val) := by
  apply PrelocalPredicate.sheafifyOf
  refine ⟨0, ⟨0, Submodule.zero_mem _⟩, ⟨1, SetLike.one_mem_graded _⟩,
    fun point => point.val.asHomogeneousIdeal.toIdeal.primeCompl.one_mem, ?_⟩
  intro point
  exact (Localization.mk_zero _).symm

theorem polynomialDegreeOneLocallyFraction_add
    {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (first second : ∀ point : open_set, polynomialDegreeOnePointLocalization 𝕜 Index point.val)
    (first_regular : (polynomialDegreeOneLocallyFraction 𝕜 Index).pred first)
    (second_regular : (polynomialDegreeOneLocallyFraction 𝕜 Index).pred second) :
    (polynomialDegreeOneLocallyFraction 𝕜 Index).pred (first + second) := by
  apply (polynomialDegreeOneFractionPrelocal 𝕜 Index).sheafify_inductionOn₂'
    (polynomialDegreeOneFractionPrelocal 𝕜 Index) (polynomialDegreeOneFractionPrelocal 𝕜 Index)
    (fun first_value second_value => first_value + second_value) _ first_regular second_regular
  rintro first_open second_open first_value second_value
    ⟨first_degree, first_num, first_den, first_nonzero, first_equal⟩
    ⟨second_degree, second_num, second_den, second_nonzero, second_equal⟩
  refine ⟨first_degree + second_degree,
    ⟨first_den.val * second_num.val + second_den.val * first_num.val, ?_⟩,
    ⟨first_den.val * second_den.val, SetLike.mul_mem_graded first_den.property second_den.property⟩,
    fun point => point.val.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (first_nonzero ⟨point.val, point.property.1⟩) (second_nonzero ⟨point.val, point.property.2⟩), ?_⟩
  · apply Submodule.add_mem
    · simpa only [Nat.add_assoc] using
        (SetLike.mul_mem_graded first_den.property second_num.property)
    · simpa only [← Nat.add_assoc, Nat.add_comm second_degree first_degree] using
        (SetLike.mul_mem_graded second_den.property first_num.property)
  · intro point
    dsimp only
    rw [first_equal, second_equal, Localization.add_mk]
    rfl

theorem polynomialDegreeOneLocallyFraction_neg
    {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (section_value : ∀ point : open_set, polynomialDegreeOnePointLocalization 𝕜 Index point.val)
    (regular : (polynomialDegreeOneLocallyFraction 𝕜 Index).pred section_value) :
    (polynomialDegreeOneLocallyFraction 𝕜 Index).pred (-section_value) := by
  apply (polynomialDegreeOneFractionPrelocal 𝕜 Index).sheafify_inductionOn'
    (fun value => -value) _ regular
  rintro local_open local_value ⟨degree, numerator, denominator, denominator_nonzero, equal⟩
  refine ⟨degree, -numerator, denominator, denominator_nonzero, ?_⟩
  intro point
  simp only [equal, Localization.neg_mk, Submodule.coe_neg]

noncomputable def polynomialDegreeOneSectionAddSubgroup
    (open_set : (polynomialDegreeOneProj 𝕜 Index).Opens) :
    AddSubgroup (∀ point : open_set, polynomialDegreeOnePointLocalization 𝕜 Index point.val) where
  carrier := {section_value | (polynomialDegreeOneLocallyFraction 𝕜 Index).pred section_value}
  zero_mem' := polynomialDegreeOneLocallyFraction_zero 𝕜 Index open_set
  add_mem' := polynomialDegreeOneLocallyFraction_add 𝕜 Index _ _
  neg_mem' := polynomialDegreeOneLocallyFraction_neg 𝕜 Index _

noncomputable def polynomialDegreeOneScalarEvaluation
    (open_set : (polynomialDegreeOneProj 𝕜 Index).Opens) :
    Γ(polynomialDegreeOneProj 𝕜 Index, open_set) →+*
      (∀ point : open_set, polynomialDegreeOnePointLocalization 𝕜 Index point.val) where
  toFun scalar point := (scalar.val point).val
  map_zero' := by funext point; exact HomogeneousLocalization.val_zero
  map_one' := by funext point; exact HomogeneousLocalization.val_one
  map_add' first second := by funext point; exact HomogeneousLocalization.val_add _ _
  map_mul' first second := by funext point; exact HomogeneousLocalization.val_mul _ _

variable {𝕜} in
noncomputable instance polynomialDegreeOnePointwiseModule
    (open_set : (polynomialDegreeOneProj 𝕜 Index).Opens) :
    Module Γ(polynomialDegreeOneProj 𝕜 Index, open_set)
      (∀ point : open_set, polynomialDegreeOnePointLocalization 𝕜 Index point.val) :=
  Module.compHom _ (polynomialDegreeOneScalarEvaluation 𝕜 Index open_set)

theorem polynomialDegreeOneLocallyFraction_smul
    {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (scalar : Γ(polynomialDegreeOneProj 𝕜 Index, open_set))
    (section_value : ∀ point : open_set, polynomialDegreeOnePointLocalization 𝕜 Index point.val)
    (regular : (polynomialDegreeOneLocallyFraction 𝕜 Index).pred section_value) :
    (polynomialDegreeOneLocallyFraction 𝕜 Index).pred (scalar • section_value) := by
  apply (ProjectiveSpectrum.StructureSheaf.isFractionPrelocal
    (MvPolynomial.homogeneousSubmodule Index 𝕜)).sheafify_inductionOn₂'
    (polynomialDegreeOneFractionPrelocal 𝕜 Index) (polynomialDegreeOneFractionPrelocal 𝕜 Index)
    (fun scalar_value section_value => scalar_value.val * section_value) _ scalar.property regular
  rintro scalar_open section_open scalar_value section_value
    ⟨scalar_degree, scalar_num, scalar_den, scalar_nonzero, scalar_equal⟩
    ⟨section_degree, section_num, section_den, section_nonzero, section_equal⟩
  refine ⟨scalar_degree + section_degree,
    ⟨scalar_num.val * section_num.val, ?_⟩,
    ⟨scalar_den.val * section_den.val, SetLike.mul_mem_graded scalar_den.property section_den.property⟩,
    fun point => point.val.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (scalar_nonzero ⟨point.val, point.property.1⟩) (section_nonzero ⟨point.val, point.property.2⟩), ?_⟩
  · simpa only [Nat.add_assoc] using
      (SetLike.mul_mem_graded scalar_num.property section_num.property)
  · intro point
    dsimp only
    rw [scalar_equal, section_equal, HomogeneousLocalization.val_mk, Localization.mk_mul]
    rfl

noncomputable def polynomialDegreeOneSectionSubmodule
    (open_set : (polynomialDegreeOneProj 𝕜 Index).Opens) :
    Submodule Γ(polynomialDegreeOneProj 𝕜 Index, open_set)
      (∀ point : open_set, polynomialDegreeOnePointLocalization 𝕜 Index point.val) where
  toAddSubmonoid := (polynomialDegreeOneSectionAddSubgroup 𝕜 Index open_set).toAddSubmonoid
  smul_mem' scalar section_value regular :=
    polynomialDegreeOneLocallyFraction_smul 𝕜 Index scalar section_value regular

noncomputable def polynomialDegreeOnePresheaf :
    (polynomialDegreeOneProj 𝕜 Index).PresheafOfModules where
  obj open_set := ModuleCat.of _ (polynomialDegreeOneSectionSubmodule 𝕜 Index open_set.unop)
  map {larger smaller} inclusion := ModuleCat.semilinearMapAddEquiv _ _ _
    (show polynomialDegreeOneSectionSubmodule 𝕜 Index larger.unop →ₛₗ[
      ((polynomialDegreeOneProj 𝕜 Index).ringCatSheaf.obj.map inclusion).hom]
        (polynomialDegreeOneSectionSubmodule 𝕜) Index smaller.unop from
    { toFun section_value := ⟨fun point => section_value.val (inclusion.unop point),
        (polynomialDegreeOneLocallyFraction 𝕜 Index).res inclusion.unop section_value.val section_value.property⟩
      map_add' first second := rfl
      map_smul' scalar section_value := rfl })
  map_id open_set := by ext section_value; rfl
  map_comp first second := by ext section_value; rfl

noncomputable def polynomialDegreeOnePresheafForgetIso :
    (polynomialDegreeOnePresheaf 𝕜 Index).presheaf ⋙ forget AddCommGrpCat ≅
      (polynomialDegreeOneTypeSheaf 𝕜 Index).obj :=
  NatIso.ofComponents (fun open_set => Iso.refl _) (by intros; rfl)

theorem polynomialDegreeOnePresheaf_isSheaf :
    TopCat.Presheaf.IsSheaf (polynomialDegreeOnePresheaf 𝕜 Index).presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).mpr
  exact TopCat.Presheaf.isSheaf_of_iso
    (polynomialDegreeOnePresheafForgetIso 𝕜 Index).symm (polynomialDegreeOneTypeSheaf 𝕜 Index).property

noncomputable def polynomialProjDegreeOneSheaf :
    (polynomialDegreeOneProj 𝕜 Index).Modules :=
  ⟨polynomialDegreeOnePresheaf 𝕜 Index, polynomialDegreeOnePresheaf_isSheaf 𝕜 Index⟩

abbrev polynomialDegreeOneCoordinateOpen (coordinate : Index) :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X coordinate)

abbrev polynomialDegreeZeroPointLocalization (point : polynomialDegreeOneProj 𝕜 Index) :=
  HomogeneousLocalization.AtPrime (MvPolynomial.homogeneousSubmodule Index 𝕜)
    point.asHomogeneousIdeal.toIdeal

noncomputable def polynomialDegreeOnePointCoefficient
    (point : polynomialDegreeOneProj 𝕜 Index) (coordinate : Index)
    (coordinate_nonzero : MvPolynomial.X coordinate ∉ point.asHomogeneousIdeal)
    (degree : ℕ) (numerator : MvPolynomial.homogeneousSubmodule Index 𝕜 (degree + 1))
    (denominator : MvPolynomial.homogeneousSubmodule Index 𝕜 degree)
    (denominator_nonzero : denominator.val ∉ point.asHomogeneousIdeal) :
    polynomialDegreeZeroPointLocalization 𝕜 Index point :=
  HomogeneousLocalization.mk
    ⟨degree + 1, numerator,
      ⟨denominator.val * MvPolynomial.X coordinate,
        SetLike.mul_mem_graded denominator.property (MvPolynomial.isHomogeneous_X 𝕜 coordinate)⟩,
      point.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem denominator_nonzero coordinate_nonzero⟩

theorem polynomialDegreeOnePointCoefficient_mul_coordinate
    (point : polynomialDegreeOneProj 𝕜 Index) (coordinate : Index)
    (coordinate_nonzero : MvPolynomial.X coordinate ∉ point.asHomogeneousIdeal)
    (degree : ℕ) (numerator : MvPolynomial.homogeneousSubmodule Index 𝕜 (degree + 1))
    (denominator : MvPolynomial.homogeneousSubmodule Index 𝕜 degree)
    (denominator_nonzero : denominator.val ∉ point.asHomogeneousIdeal) :
    (polynomialDegreeOnePointCoefficient 𝕜 Index point coordinate coordinate_nonzero degree
        numerator denominator denominator_nonzero).val *
      algebraMap (MvPolynomial Index 𝕜) (polynomialDegreeOnePointLocalization 𝕜 Index point)
        (MvPolynomial.X coordinate) =
      Localization.mk numerator.val ⟨denominator.val, denominator_nonzero⟩ := by
  rw [polynomialDegreeOnePointCoefficient, HomogeneousLocalization.val_mk,
    ← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, mul_one]
  ring

theorem polynomialDegreeOneCoordinate_isUnit
    (point : polynomialDegreeOneProj 𝕜 Index) (coordinate : Index)
    (coordinate_nonzero : MvPolynomial.X coordinate ∉ point.asHomogeneousIdeal) :
    IsUnit (algebraMap (MvPolynomial Index 𝕜) (polynomialDegreeOnePointLocalization 𝕜 Index point)
      (MvPolynomial.X coordinate)) :=
  IsLocalization.map_units (M := point.asHomogeneousIdeal.toIdeal.primeCompl)
    (polynomialDegreeOnePointLocalization 𝕜 Index point) ⟨MvPolynomial.X coordinate, coordinate_nonzero⟩

theorem polynomialDegreeOneChartCoefficient_exists
    (coordinate : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (inclusion : open_set ≤ polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate)
    (section_value : Γ(polynomialProjDegreeOneSheaf 𝕜 Index, open_set)) (point : open_set) :
    ∃ coefficient : polynomialDegreeZeroPointLocalization 𝕜 Index point.val,
      coefficient.val * algebraMap (MvPolynomial Index 𝕜)
        (polynomialDegreeOnePointLocalization 𝕜 Index point.val) (MvPolynomial.X coordinate) =
          section_value.val point := by
  obtain ⟨local_open, point_member, local_inclusion, degree, numerator, denominator,
    denominator_nonzero, equal⟩ := section_value.property point
  refine ⟨polynomialDegreeOnePointCoefficient 𝕜 Index point.val coordinate (inclusion point.property)
    degree numerator denominator (denominator_nonzero ⟨point.val, point_member⟩), ?_⟩
  rw [polynomialDegreeOnePointCoefficient_mul_coordinate]
  exact (equal ⟨point.val, point_member⟩).symm

noncomputable def polynomialDegreeOneChartCoefficientValue
    (coordinate : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (inclusion : open_set ≤ polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate)
    (section_value : Γ(polynomialProjDegreeOneSheaf 𝕜 Index, open_set)) (point : open_set) :
    polynomialDegreeZeroPointLocalization 𝕜 Index point.val :=
  (polynomialDegreeOneChartCoefficient_exists 𝕜 Index coordinate inclusion section_value point).choose

theorem polynomialDegreeOneChartCoefficientValue_spec
    (coordinate : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (inclusion : open_set ≤ polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate)
    (section_value : Γ(polynomialProjDegreeOneSheaf 𝕜 Index, open_set)) (point : open_set) :
    (polynomialDegreeOneChartCoefficientValue 𝕜 Index coordinate inclusion section_value point).val *
        algebraMap (MvPolynomial Index 𝕜) (polynomialDegreeOnePointLocalization 𝕜 Index point.val)
          (MvPolynomial.X coordinate) = section_value.val point :=
  (polynomialDegreeOneChartCoefficient_exists 𝕜 Index coordinate inclusion section_value point).choose_spec

theorem polynomialDegreeOneChartCoefficientValue_locallyFraction
    (coordinate : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (inclusion : open_set ≤ polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate)
    (section_value : Γ(polynomialProjDegreeOneSheaf 𝕜 Index, open_set)) :
    (ProjectiveSpectrum.StructureSheaf.isLocallyFraction
      (MvPolynomial.homogeneousSubmodule Index 𝕜)).pred
        (polynomialDegreeOneChartCoefficientValue 𝕜 Index coordinate inclusion section_value) := by
  intro point
  obtain ⟨local_open, point_member, local_inclusion, degree, numerator, denominator,
    denominator_nonzero, equal⟩ := section_value.property point
  refine ⟨local_open, point_member, local_inclusion, degree + 1, numerator,
    ⟨denominator.val * MvPolynomial.X coordinate,
      SetLike.mul_mem_graded denominator.property (MvPolynomial.isHomogeneous_X 𝕜 coordinate)⟩,
    fun local_point => local_point.val.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (denominator_nonzero local_point) (inclusion (local_inclusion local_point).property), ?_⟩
  intro local_point
  apply HomogeneousLocalization.val_injective _
  apply (polynomialDegreeOneCoordinate_isUnit 𝕜 Index local_point.val coordinate
    (inclusion (local_inclusion local_point).property)).mul_right_cancel
  dsimp only
  erw [polynomialDegreeOneChartCoefficientValue_spec]
  change section_value.val (local_inclusion local_point) =
    (polynomialDegreeOnePointCoefficient 𝕜 Index local_point.val coordinate
      (inclusion (local_inclusion local_point).property) degree
      numerator denominator (denominator_nonzero local_point)).val * _
  rw [polynomialDegreeOnePointCoefficient_mul_coordinate]
  exact equal local_point

noncomputable def polynomialDegreeOneChartCoefficient
    (coordinate : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (inclusion : open_set ≤ polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate)
    (section_value : Γ(polynomialProjDegreeOneSheaf 𝕜 Index, open_set)) :
    Γ(polynomialDegreeOneProj 𝕜 Index, open_set) :=
  ⟨polynomialDegreeOneChartCoefficientValue 𝕜 Index coordinate inclusion section_value,
    polynomialDegreeOneChartCoefficientValue_locallyFraction 𝕜 Index coordinate inclusion section_value⟩

theorem polynomialDegreeOneChartFrame_locallyFraction
    (coordinate : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (scalar : Γ(polynomialDegreeOneProj 𝕜 Index, open_set)) :
    (polynomialDegreeOneLocallyFraction 𝕜 Index).pred (fun point : open_set =>
      (scalar.val point).val * algebraMap (MvPolynomial Index 𝕜)
        (polynomialDegreeOnePointLocalization 𝕜 Index point.val) (MvPolynomial.X coordinate)) := by
  intro point
  obtain ⟨local_open, point_member, local_inclusion, degree, numerator, denominator,
    denominator_nonzero, equal⟩ := scalar.property point
  refine ⟨local_open, point_member, local_inclusion, degree,
    ⟨numerator.val * MvPolynomial.X coordinate,
      SetLike.mul_mem_graded numerator.property (MvPolynomial.isHomogeneous_X 𝕜 coordinate)⟩,
    denominator, denominator_nonzero, ?_⟩
  intro local_point
  dsimp only
  have scalar_equal := equal local_point
  dsimp only at scalar_equal
  erw [scalar_equal, HomogeneousLocalization.val_mk, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul]
  simp only [mul_one]

noncomputable def polynomialDegreeOneChartFrame
    (coordinate : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (scalar : Γ(polynomialDegreeOneProj 𝕜 Index, open_set)) :
    Γ(polynomialProjDegreeOneSheaf 𝕜 Index, open_set) :=
  ⟨fun point => (scalar.val point).val * algebraMap (MvPolynomial Index 𝕜)
      (polynomialDegreeOnePointLocalization 𝕜 Index point.val) (MvPolynomial.X coordinate),
    polynomialDegreeOneChartFrame_locallyFraction 𝕜 Index coordinate scalar⟩

noncomputable def polynomialDegreeOneChartSectionsLinearEquiv
    (coordinate : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (inclusion : open_set ≤ polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate) :
    Γ(polynomialDegreeOneProj 𝕜 Index, open_set) ≃ₗ[Γ(polynomialDegreeOneProj 𝕜 Index, open_set)]
      Γ(polynomialProjDegreeOneSheaf 𝕜 Index, open_set) where
  toFun := polynomialDegreeOneChartFrame 𝕜 Index coordinate
  invFun := polynomialDegreeOneChartCoefficient 𝕜 Index coordinate inclusion
  map_add' first second := by
    apply Subtype.ext
    funext point
    dsimp [polynomialDegreeOneChartFrame]
    erw [Proj.add_apply, HomogeneousLocalization.val_add]
    change _ = (first.val point).val * _ + (second.val point).val * _
    exact add_mul _ _ _
  map_smul' scalar coefficient := by
    apply Subtype.ext
    funext point
    dsimp [polynomialDegreeOneChartFrame, polynomialDegreeOnePointwiseModule,
      Module.compHom, polynomialDegreeOneScalarEvaluation]
    erw [Proj.mul_apply, HomogeneousLocalization.val_mul]
    change _ = (scalar.val point).val * ((coefficient.val point).val * _)
    exact mul_assoc _ _ _
  left_inv coefficient := by
    apply Subtype.ext
    funext point
    apply HomogeneousLocalization.val_injective _
    apply (polynomialDegreeOneCoordinate_isUnit 𝕜 Index point.val coordinate
      (inclusion point.property)).mul_right_cancel
    exact polynomialDegreeOneChartCoefficientValue_spec 𝕜 Index coordinate inclusion _ point
  right_inv section_value := by
    apply Subtype.ext
    funext point
    exact polynomialDegreeOneChartCoefficientValue_spec 𝕜 Index coordinate inclusion section_value point

noncomputable def polynomialDegreeOneCoordinateOpenSheafFrame (coordinate : Index) :
    SheafOfModules.unit ((polynomialDegreeOneProj 𝕜 Index).ringCatSheaf.over
      (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate)) ≅
    (polynomialProjDegreeOneSheaf 𝕜 Index).over (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun local_open =>
    (polynomialDegreeOneChartSectionsLinearEquiv 𝕜 Index coordinate
      local_open.unop.hom.le).toModuleIso) ?_
  intro larger smaller inclusion
  ext
  apply Subtype.ext
  funext point
  rfl

theorem polynomialDegreeOneCoordinateOpen_cover :
    IsOpenCover (polynomialDegreeOneCoordinateOpen 𝕜 Index) := by
  apply IsOpenCover.mk
  apply Proj.iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule Index 𝕜)
    (MvPolynomial.X : Index → MvPolynomial Index 𝕜)
    (fun coordinate => ⟨1, MvPolynomial.isHomogeneous_X 𝕜 coordinate⟩)
  apply top_unique
  intro polynomial
  induction polynomial using MvPolynomial.induction_on with
  | C scalar =>
      intro _
      exact Subalgebra.algebraMap_mem
        (Algebra.adjoin (MvPolynomial.homogeneousSubmodule Index 𝕜 0) (Set.range MvPolynomial.X))
        (⟨MvPolynomial.C scalar, MvPolynomial.isHomogeneous_C Index scalar⟩ :
          MvPolynomial.homogeneousSubmodule Index 𝕜 0)
  | add first second first_member second_member =>
      intro _
      exact Subalgebra.add_mem _ (first_member trivial) (second_member trivial)
  | mul_X polynomial coordinate polynomial_member =>
      intro _
      exact Subalgebra.mul_mem _ (polynomial_member trivial) (Algebra.subset_adjoin ⟨coordinate, rfl⟩)

noncomputable def polynomialProjDegreeOneLocalTrivializations :
    TauCeti.SheafOfModules.LocalTrivializations (polynomialProjDegreeOneSheaf 𝕜 Index) :=
  TauCeti.AlgebraicGeometry.SheafOfModules.LocalTrivializations.ofIsOpenCover
    (polynomialDegreeOneProj 𝕜 Index) (polynomialDegreeOneCoordinateOpen 𝕜 Index)
      (polynomialDegreeOneCoordinateOpen_cover 𝕜 Index)
        (polynomialDegreeOneCoordinateOpenSheafFrame 𝕜 Index)

variable {𝕜} in
instance polynomialProjDegreeOneSheaf_isInvertible :
    TauCeti.SheafOfModules.IsInvertible (polynomialProjDegreeOneSheaf 𝕜 Index) :=
  (polynomialProjDegreeOneLocalTrivializations 𝕜 Index).isInvertible

noncomputable def polynomialProjDegreeOneGlobalCoordinate (coordinate : Index) :
    Γ(polynomialProjDegreeOneSheaf 𝕜 Index, ⊤) :=
  polynomialDegreeOneChartFrame 𝕜 Index coordinate 1

theorem polynomialProjDegreeOneGlobalCoordinate_restrict (coordinate : Index)
    (open_set : (polynomialDegreeOneProj 𝕜 Index).Opens) :
    (polynomialProjDegreeOneSheaf 𝕜 Index).presheaf.map (homOfLE le_top).op
        (polynomialProjDegreeOneGlobalCoordinate 𝕜 Index coordinate) =
      polynomialDegreeOneChartFrame 𝕜 Index coordinate
        (1 : Γ(polynomialDegreeOneProj 𝕜 Index, open_set)) := by
  apply Subtype.ext
  funext point
  rfl

noncomputable def polynomialDegreeOneChartRatio
    (first second : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (inclusion : open_set ≤ polynomialDegreeOneCoordinateOpen 𝕜 Index first) :
    Γ(polynomialDegreeOneProj 𝕜 Index, open_set) := by
  let fraction : ∀ point : open_set, polynomialDegreeZeroPointLocalization 𝕜 Index point.val :=
    fun point => HomogeneousLocalization.mk
    (𝒜 := MvPolynomial.homogeneousSubmodule Index 𝕜)
    ⟨1, ⟨MvPolynomial.X second, MvPolynomial.isHomogeneous_X 𝕜 second⟩,
      ⟨MvPolynomial.X first, MvPolynomial.isHomogeneous_X 𝕜 first⟩, inclusion point.property⟩
  refine ⟨fraction, PrelocalPredicate.sheafifyOf ?_⟩
  exact ⟨1, ⟨MvPolynomial.X second, MvPolynomial.isHomogeneous_X 𝕜 second⟩,
    ⟨MvPolynomial.X first, MvPolynomial.isHomogeneous_X 𝕜 first⟩,
    fun point => inclusion point.property, fun point => rfl⟩

theorem polynomialDegreeOneChartRatio_mul_coordinate
    (first second : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (inclusion : open_set ≤ polynomialDegreeOneCoordinateOpen 𝕜 Index first) (point : open_set) :
    ((polynomialDegreeOneChartRatio 𝕜 Index first second inclusion).val point).val *
        algebraMap (MvPolynomial Index 𝕜) (polynomialDegreeOnePointLocalization 𝕜 Index point.val)
          (MvPolynomial.X first) =
      algebraMap (MvPolynomial Index 𝕜) (polynomialDegreeOnePointLocalization 𝕜 Index point.val)
        (MvPolynomial.X second) := by
  change (HomogeneousLocalization.mk
    (𝒜 := MvPolynomial.homogeneousSubmodule Index 𝕜) _).val * _ = _
  rw [HomogeneousLocalization.val_mk, ← Localization.mk_one_eq_algebraMap,
    ← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, mul_one]
  ring

theorem polynomialDegreeOneChartRatio_frame
    (first second : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (inclusion : open_set ≤ polynomialDegreeOneCoordinateOpen 𝕜 Index first) :
    polynomialDegreeOneChartFrame 𝕜 Index first (polynomialDegreeOneChartRatio 𝕜 Index first second inclusion) =
      polynomialDegreeOneChartFrame 𝕜 Index second (1 : Γ(polynomialDegreeOneProj 𝕜 Index, open_set)) := by
  apply Subtype.ext
  funext point
  change _ = HomogeneousLocalization.val (1 : polynomialDegreeZeroPointLocalization 𝕜 Index point.val) * _
  rw [HomogeneousLocalization.val_one, one_mul]
  exact polynomialDegreeOneChartRatio_mul_coordinate 𝕜 Index first second inclusion point

theorem polynomialDegreeOneChartRatio_eq_awayToSection (chart coordinate : Index) :
    polynomialDegreeOneChartRatio 𝕜 Index chart coordinate le_rfl =
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart))
        (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule Index 𝕜)
          (MvPolynomial.isHomogeneous_X 𝕜 chart) 1 (MvPolynomial.X coordinate)
            (by simpa using MvPolynomial.isHomogeneous_X 𝕜 coordinate)) := by
  apply Subtype.ext
  funext point
  change HomogeneousLocalization.mk
      (𝒜 := MvPolynomial.homogeneousSubmodule Index 𝕜) _ =
    HomogeneousLocalization.mapId (MvPolynomial.homogeneousSubmodule Index 𝕜)
      (Submonoid.powers_le.mpr point.property)
      (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule Index 𝕜)
        (MvPolynomial.isHomogeneous_X 𝕜 chart) 1 (MvPolynomial.X coordinate) _)
  rw [HomogeneousLocalization.Away.mk, HomogeneousLocalization.mapId,
    HomogeneousLocalization.map_mk]
  apply HomogeneousLocalization.val_injective _
  simp [HomogeneousLocalization.val_mk]

end

end BondalThomsen

end

section
/- Source: Toric/Projective/GlobalPullback.lean; generic schemes and polynomial Proj only. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TopCat

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

noncomputable section

def moduleGlobalSectionHom {scheme : Scheme} (sheaf : scheme.Modules)
    (section_value : Γ(sheaf, ⊤)) :
    SheafOfModules.unit scheme.ringCatSheaf ⟶ sheaf :=
  sheaf.unitHomEquiv.symm <| sheaf.val.sectionsMk
    (fun open_set => sheaf.presheaf.map (homOfLE le_top).op section_value)
    (by
      intro larger smaller inclusion
      change sheaf.presheaf.map inclusion
        (sheaf.presheaf.map (homOfLE le_top).op section_value) = _
      rw [← ConcreteCategory.comp_apply, ← sheaf.presheaf.map_comp]
      rfl)

theorem moduleGlobalSectionHom_app {scheme : Scheme} (sheaf : scheme.Modules)
    (section_value : Γ(sheaf, ⊤)) (open_set : scheme.Opens)
    (coefficient : Γ(scheme, open_set)) :
    Scheme.Modules.Hom.app (moduleGlobalSectionHom sheaf section_value) open_set coefficient =
      coefficient • sheaf.presheaf.map (homOfLE le_top).op section_value := by
  rfl

def modulePullbackSectionHom {source target : Scheme} (map : source ⟶ target)
    {sheaf : target.Modules}
    (section_map : SheafOfModules.unit target.ringCatSheaf ⟶ sheaf) :
    SheafOfModules.unit source.ringCatSheaf ⟶ (Scheme.Modules.pullback map).obj sheaf :=
  (Scheme.Modules.pullbackObjUnitIso map).inv ≫ (Scheme.Modules.pullback map).map section_map

theorem modulePullbackSectionHom_comp {source middle target : Scheme}
    (first : source ⟶ middle) (second : middle ⟶ target) {sheaf : target.Modules}
    (section_map : SheafOfModules.unit target.ringCatSheaf ⟶ sheaf) :
    modulePullbackSectionHom first (modulePullbackSectionHom second section_map) ≫
        (Scheme.Modules.pullbackComp first second).hom.app sheaf =
      modulePullbackSectionHom (first ≫ second) section_map := by
  have unit_compatibility := Scheme.Modules.pullbackObjUnitIso_comp first second
  have inverse_compatibility :
      (Scheme.Modules.pullbackObjUnitIso first).inv ≫
        (Scheme.Modules.pullback first).map (Scheme.Modules.pullbackObjUnitIso second).inv ≫
          (Scheme.Modules.pullbackComp first second).hom.app
            (SheafOfModules.unit target.ringCatSheaf) =
      (Scheme.Modules.pullbackObjUnitIso (first ≫ second)).inv := by
    have iso_compatibility :
        (Scheme.Modules.pullbackComp first second).symm.app
            (SheafOfModules.unit target.ringCatSheaf) ≪≫
          (Scheme.Modules.pullback first).mapIso (Scheme.Modules.pullbackObjUnitIso second) ≪≫
            Scheme.Modules.pullbackObjUnitIso first =
        Scheme.Modules.pullbackObjUnitIso (first ≫ second) := Iso.ext unit_compatibility
    exact congrArg Iso.inv iso_compatibility
  have naturality := (Scheme.Modules.pullbackComp first second).hom.naturality section_map
  dsimp only [Functor.comp_map] at naturality
  unfold modulePullbackSectionHom
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [naturality]
  simpa only [Category.assoc] using congrArg
    (fun comparison => comparison ≫ (Scheme.Modules.pullback (first ≫ second)).map section_map)
      inverse_compatibility

theorem modulePullback_isInvertible {source target : Scheme} (map : source ⟶ target)
    (sheaf : target.Modules) [TauCeti.SheafOfModules.IsInvertible sheaf] :
    TauCeti.SheafOfModules.IsInvertible ((Scheme.Modules.pullback map).obj sheaf) := by
  obtain ⟨generators, rank_one⟩ :=
    TauCeti.SheafOfModules.IsInvertible.exists_isInvertible (M := sheaf)
  let := rank_one.isLocallyFreeData
  refine ⟨generators.pullback map, ⟨inferInstance, ?_, ?_⟩⟩
  · intro chart
    rw [SheafOfModules.LocalGeneratorsData.pullback_generators,
      SheafOfModules.GeneratingSections.mapIso_I]
    exact rank_one.basisNonempty chart
  · intro chart
    rw [SheafOfModules.LocalGeneratorsData.pullback_generators,
      SheafOfModules.GeneratingSections.mapIso_I]
    exact rank_one.basisSubsingleton chart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (Index : Type)

def polynomialProjDegreeOneCoordinateHom (coordinate : Index) :
    SheafOfModules.unit (polynomialDegreeOneProj 𝕜 Index).ringCatSheaf ⟶
      polynomialProjDegreeOneSheaf 𝕜 Index :=
  moduleGlobalSectionHom _ (polynomialProjDegreeOneGlobalCoordinate 𝕜 Index coordinate)

theorem polynomialProjDegreeOneCoordinateHom_over (coordinate : Index) :
    (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate).over
        (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate) =
      (polynomialDegreeOneCoordinateOpenSheafFrame 𝕜 Index coordinate).hom := by
  apply SheafOfModules.hom_ext
  ext local_open : 2
  apply (LinearMap.ringLmapEquivSelf _ ℤ _).injective
  change ((polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate).over
      (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate)).val.app local_open
        (1 : Γ(polynomialDegreeOneProj 𝕜 Index, local_open.unop.left)) = _
  change (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate).val.app
    (op local_open.unop.left)
      (1 : Γ(polynomialDegreeOneProj 𝕜 Index, local_open.unop.left)) = _
  rw [← SheafOfModules.unitHomEquiv_apply_coe]
  simp only [polynomialProjDegreeOneCoordinateHom, moduleGlobalSectionHom,
    Equiv.apply_symm_apply]
  apply Subtype.ext
  funext point
  dsimp [polynomialDegreeOneCoordinateOpenSheafFrame, polynomialDegreeOneChartSectionsLinearEquiv,
    polynomialProjDegreeOneGlobalCoordinate, polynomialDegreeOneChartFrame]
  rfl

theorem polynomialProjDegreeOneCoordinateHom_over_isIso (coordinate : Index) :
    IsIso ((polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate).over
      (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate)) := by
  rw [polynomialProjDegreeOneCoordinateHom_over]
  infer_instance

def polynomialProjDegreeOnePullbackSheaf {source : Scheme}
    (map : source ⟶ polynomialDegreeOneProj 𝕜 Index) : source.Modules :=
  (Scheme.Modules.pullback map).obj (polynomialProjDegreeOneSheaf 𝕜 Index)

theorem polynomialProjDegreeOnePullbackSheaf_isInvertible {source : Scheme}
    (map : source ⟶ polynomialDegreeOneProj 𝕜 Index) :
    TauCeti.SheafOfModules.IsInvertible (polynomialProjDegreeOnePullbackSheaf 𝕜 Index map) :=
  modulePullback_isInvertible map _

def polynomialProjDegreeOnePullbackCoordinateHom {source : Scheme}
    (map : source ⟶ polynomialDegreeOneProj 𝕜 Index) (coordinate : Index) :
    SheafOfModules.unit source.ringCatSheaf ⟶ polynomialProjDegreeOnePullbackSheaf 𝕜 Index map :=
  modulePullbackSectionHom map (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate)

theorem polynomialProjDegreeOnePullbackCoordinateOpen_cover {source : Scheme}
    (map : source ⟶ polynomialDegreeOneProj 𝕜 Index) :
    IsOpenCover (fun coordinate => map ⁻¹ᵁ (polynomialDegreeOneCoordinateOpen 𝕜) Index coordinate) := by
  apply IsOpenCover.mk
  rw [← Scheme.Hom.preimage_iSup,
    (polynomialDegreeOneCoordinateOpen_cover 𝕜 Index).iSup_eq_top, Scheme.Hom.preimage_top]

end

end BondalThomsen

end

section
/- Source: ProjectiveBundle/GlobalRelativeQuotient.lean; generic schemes and polynomial Proj only. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open Classical AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

noncomputable def restrictLocalModuleHom {schemeModel : Scheme}
    {source target : schemeModel.Modules} {smaller larger : schemeModel.Opens}
    (contained : smaller ≤ larger) (morphism : source.over larger ⟶ target.over larger) :
    source.over smaller ⟶ target.over smaller :=
  ((SheafOfModules.overFunctorMap schemeModel.ringCatSheaf (homOfLE contained)).app source).inv ≫
    (SheafOfModules.overMap schemeModel.ringCatSheaf (homOfLE contained)).map morphism ≫
    ((SheafOfModules.overFunctorMap schemeModel.ringCatSheaf (homOfLE contained)).app target).hom

theorem restrictLocalModuleHom_app {schemeModel : Scheme}
    {source target : schemeModel.Modules} {smaller larger : schemeModel.Opens}
    (contained : smaller ≤ larger) (morphism : source.over larger ⟶ target.over larger)
    (subopen : Over smaller) (coefficient : Γ(source, subopen.left)) :
    (restrictLocalModuleHom contained morphism).val.app (op subopen) coefficient =
      morphism.val.app (op (Over.mk (subopen.hom ≫ homOfLE contained))) coefficient := by
  rfl

theorem restrictLocalModuleHom_global {schemeModel : Scheme}
    {source target : schemeModel.Modules} {smaller larger : schemeModel.Opens}
    (contained : smaller ≤ larger) (morphism : source ⟶ target) :
    restrictLocalModuleHom contained (morphism.over larger) = morphism.over smaller := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.Hom.ext
  funext subopen
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro coefficient
  cases subopen with
  | op subopen => rfl

theorem restrictLocalModuleHom_map_comp {schemeModel : Scheme}
    {source middle target : schemeModel.Modules} {smaller larger : schemeModel.Opens}
    (contained : smaller ≤ larger) (first : source.over larger ⟶ middle.over larger)
    (second : middle.over larger ⟶ target.over larger) :
    restrictLocalModuleHom contained (first ≫ second) =
      restrictLocalModuleHom contained first ≫ restrictLocalModuleHom contained second := by
  dsimp only [restrictLocalModuleHom]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

namespace LocalModuleGluing

variable {schemeModel : Scheme} {source target : schemeModel.Modules} {Index : Type}
    (charts : Index → schemeModel.Opens) (covers : IsOpenCover charts)
    (localMaps : ∀ index, source.over (charts index) ⟶ target.over (charts index))
    (compatible : ∀ first second,
      restrictLocalModuleHom (inf_le_left : charts first ⊓ charts second ≤ charts first)
          (localMaps first) =
        restrictLocalModuleHom (inf_le_right : charts first ⊓ charts second ≤ charts second)
          (localMaps second))

include covers in
theorem chartIntersection_covers (domain : schemeModel.Opens) :
    domain ≤ ⨆ index, domain ⊓ charts index := by
  rw [← inf_iSup_eq, covers.iSup_eq_top, inf_top_eq]

noncomputable def localImage (domain : schemeModel.Opens) (sectionValue : Γ(source, domain))
    (index : Index) : Γ(target, domain ⊓ charts index) :=
  (localMaps index).val.app
    (op (Over.mk (homOfLE (inf_le_right : domain ⊓ charts index ≤ charts index))))
    (source.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op sectionValue)

include compatible in
theorem localImage_compatible (domain : schemeModel.Opens) (sectionValue : Γ(source, domain)) :
    TopCat.Presheaf.IsCompatible target.presheaf (fun index => domain ⊓ charts index)
      (localImage charts localMaps domain sectionValue) := by
  intro first second
  let common := (domain ⊓ charts first) ⊓ (domain ⊓ charts second)
  have inOverlap : common ≤ charts first ⊓ charts second :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have mapsEqual := congrArg (fun morphism => morphism.val.app
      (op (Over.mk (homOfLE inOverlap)))
      (source.presheaf.map (homOfLE
        (inf_le_left.trans inf_le_left : common ≤ domain)).op sectionValue))
    (compatible first second)
  simp only [restrictLocalModuleHom_app] at mapsEqual
  have firstNatural := congrArg (fun morphism => morphism.hom
      (source.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts first ≤ domain)).op sectionValue))
    ((localMaps first).val.naturality
      (Over.homMk (U := Over.mk (homOfLE (inOverlap.trans inf_le_left)))
        (V := Over.mk (homOfLE (inf_le_right : domain ⊓ charts first ≤ charts first)))
        (homOfLE (inf_le_left : common ≤ domain ⊓ charts first))).op)
  have secondNatural := congrArg (fun morphism => morphism.hom
      (source.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts second ≤ domain)).op sectionValue))
    ((localMaps second).val.naturality
      (Over.homMk (U := Over.mk (homOfLE (inOverlap.trans inf_le_right)))
        (V := Over.mk (homOfLE (inf_le_right : domain ⊓ charts second ≤ charts second)))
        (homOfLE (inf_le_right : common ≤ domain ⊓ charts second))).op)
  change (localMaps first).val.app (op (Over.mk (homOfLE (inOverlap.trans inf_le_left))))
      (source.presheaf.map (homOfLE (inf_le_left : common ≤ domain ⊓ charts first)).op
        (source.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts first ≤ domain)).op
          sectionValue)) =
    target.presheaf.map (homOfLE (inf_le_left : common ≤ domain ⊓ charts first)).op
      (localImage charts localMaps domain sectionValue first) at firstNatural
  change (localMaps second).val.app (op (Over.mk (homOfLE (inOverlap.trans inf_le_right))))
      (source.presheaf.map (homOfLE (inf_le_right : common ≤ domain ⊓ charts second)).op
        (source.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts second ≤ domain)).op
          sectionValue)) =
    target.presheaf.map (homOfLE (inf_le_right : common ≤ domain ⊓ charts second)).op
      (localImage charts localMaps domain sectionValue second) at secondNatural
  simp only [← Functor.map_comp_apply] at firstNatural secondNatural
  dsimp only [localImage]
  change target.presheaf.map (homOfLE (inf_le_left : common ≤ domain ⊓ charts first)).op _ =
    target.presheaf.map (homOfLE (inf_le_right : common ≤ domain ⊓ charts second)).op _
  exact firstNatural.symm.trans (mapsEqual.trans secondNatural)

include covers compatible in

theorem existsUnique_image (domain : schemeModel.Opens) (sectionValue : Γ(source, domain)) :
    ∃! image : Γ(target, domain), ∀ index,
      target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op image =
        localImage charts localMaps domain sectionValue index := by
  exact (show TopCat.Sheaf Ab schemeModel from (SheafOfModules.toSheaf _).obj target).existsUnique_gluing'
    (fun index => domain ⊓ charts index) domain (fun index => homOfLE inf_le_left)
    (chartIntersection_covers charts covers domain) _
    (localImage_compatible charts localMaps compatible domain sectionValue)

noncomputable def image (domain : schemeModel.Opens) (sectionValue : Γ(source, domain)) :
    Γ(target, domain) :=
  (existsUnique_image charts covers localMaps compatible domain sectionValue).exists.choose

include covers compatible in
theorem image_restriction (domain : schemeModel.Opens) (sectionValue : Γ(source, domain))
    (index : Index) :
    target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op
        (image charts covers localMaps compatible domain sectionValue) =
      localImage charts localMaps domain sectionValue index :=
  (existsUnique_image charts covers localMaps compatible domain sectionValue).exists.choose_spec index

theorem localImage_add (domain : schemeModel.Opens) (first second : Γ(source, domain))
    (index : Index) :
    localImage charts localMaps domain (first + second) index =
      localImage charts localMaps domain first index + localImage charts localMaps domain second index := by
  dsimp only [localImage]
  rw [map_add, map_add]

theorem localImage_smul (domain : schemeModel.Opens) (scalar : Γ(schemeModel, domain))
    (sectionValue : Γ(source, domain)) (index : Index) :
    localImage charts localMaps domain (scalar • sectionValue) index =
      schemeModel.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op scalar •
        localImage charts localMaps domain sectionValue index := by
  dsimp only [localImage]
  rw [Scheme.Modules.map_smul]
  exact ((localMaps index).val.app _).hom.map_smul _ _

include covers compatible in
theorem image_add (domain : schemeModel.Opens) (first second : Γ(source, domain)) :
    image charts covers localMaps compatible domain (first + second) =
      image charts covers localMaps compatible domain first +
        image charts covers localMaps compatible domain second := by
  apply (show TopCat.Sheaf Ab schemeModel from (SheafOfModules.toSheaf _).obj target).eq_of_locally_eq'
    (fun index => domain ⊓ charts index) domain (fun index => homOfLE inf_le_left)
    (chartIntersection_covers charts covers domain)
  intro index
  change target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op
      (image charts covers localMaps compatible domain (first + second)) =
    target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op
      (image charts covers localMaps compatible domain first +
        image charts covers localMaps compatible domain second)
  rw [map_add, image_restriction, image_restriction, image_restriction, localImage_add]

include covers compatible in
theorem image_smul (domain : schemeModel.Opens) (scalar : Γ(schemeModel, domain))
    (sectionValue : Γ(source, domain)) :
    image charts covers localMaps compatible domain (scalar • sectionValue) =
      scalar • image charts covers localMaps compatible domain sectionValue := by
  apply (show TopCat.Sheaf Ab schemeModel from (SheafOfModules.toSheaf _).obj target).eq_of_locally_eq'
    (fun index => domain ⊓ charts index) domain (fun index => homOfLE inf_le_left)
    (chartIntersection_covers charts covers domain)
  intro index
  change target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op
      (image charts covers localMaps compatible domain (scalar • sectionValue)) =
    target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op
      (scalar • image charts covers localMaps compatible domain sectionValue)
  rw [Scheme.Modules.map_smul, image_restriction, image_restriction, localImage_smul]

theorem localImage_naturality {smaller larger : schemeModel.Opens} (contained : smaller ≤ larger)
    (sectionValue : Γ(source, larger)) (index : Index) :
    target.presheaf.map (homOfLE (inf_le_inf_right (charts index) contained)).op
        (localImage charts localMaps larger sectionValue index) =
      localImage charts localMaps smaller (source.presheaf.map (homOfLE contained).op sectionValue)
        index := by
  have naturality := congrArg (fun morphism => morphism.hom
      (source.presheaf.map (homOfLE (inf_le_left : larger ⊓ charts index ≤ larger)).op sectionValue))
    ((localMaps index).val.naturality
      (Over.homMk (U := Over.mk (homOfLE (inf_le_right : smaller ⊓ charts index ≤ charts index)))
        (V := Over.mk (homOfLE (inf_le_right : larger ⊓ charts index ≤ charts index)))
        (homOfLE (inf_le_inf_right (charts index) contained))).op)
  change (localMaps index).val.app
      (op (Over.mk (homOfLE (inf_le_right : smaller ⊓ charts index ≤ charts index))))
      (source.presheaf.map (homOfLE (inf_le_inf_right (charts index) contained)).op
        (source.presheaf.map (homOfLE (inf_le_left : larger ⊓ charts index ≤ larger)).op
          sectionValue)) =
    target.presheaf.map (homOfLE (inf_le_inf_right (charts index) contained)).op
      (localImage charts localMaps larger sectionValue index) at naturality
  dsimp only [localImage]
  simpa only [localImage, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp]
    using naturality.symm

include covers compatible in
theorem image_naturality {smaller larger : schemeModel.Opens} (contained : smaller ≤ larger)
    (sectionValue : Γ(source, larger)) :
    target.presheaf.map (homOfLE contained).op
        (image charts covers localMaps compatible larger sectionValue) =
      image charts covers localMaps compatible smaller
        (source.presheaf.map (homOfLE contained).op sectionValue) := by
  apply (show TopCat.Sheaf Ab schemeModel from (SheafOfModules.toSheaf _).obj target).eq_of_locally_eq'
    (fun index => smaller ⊓ charts index) smaller (fun index => homOfLE inf_le_left)
    (chartIntersection_covers charts covers smaller)
  intro index
  change target.presheaf.map (homOfLE (inf_le_left : smaller ⊓ charts index ≤ smaller)).op
      (target.presheaf.map (homOfLE contained).op
        (image charts covers localMaps compatible larger sectionValue)) =
    target.presheaf.map (homOfLE (inf_le_left : smaller ⊓ charts index ≤ smaller)).op
      (image charts covers localMaps compatible smaller
        (source.presheaf.map (homOfLE contained).op sectionValue))
  rw [image_restriction]
  rw [← localImage_naturality charts localMaps contained sectionValue index,
    ← image_restriction charts covers localMaps compatible larger sectionValue index]
  simp only [← Functor.map_comp_apply]
  rfl

noncomputable def glue : source ⟶ target where
  val.app domain := ModuleCat.ofHom
    { toFun := image charts covers localMaps compatible domain.unop
      map_add' := image_add charts covers localMaps compatible domain.unop
      map_smul' := image_smul charts covers localMaps compatible domain.unop }
  val.naturality {larger smaller} inclusion := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro sectionValue
    change image charts covers localMaps compatible smaller.unop
        (source.presheaf.map inclusion sectionValue) =
      target.presheaf.map inclusion (image charts covers localMaps compatible larger.unop sectionValue)
    exact (image_naturality charts covers localMaps compatible inclusion.unop.le sectionValue).symm

include covers compatible in
theorem image_eq_local (index : Index) (domain : schemeModel.Opens) (contained : domain ≤ charts index)
    (sectionValue : Γ(source, domain)) :
    image charts covers localMaps compatible domain sectionValue =
      (localMaps index).val.app (op (Over.mk (homOfLE contained))) sectionValue := by
  have restricted := image_restriction charts covers localMaps compatible domain sectionValue index
  have overlapEq : domain ⊓ charts index = domain := inf_eq_left.mpr contained
  dsimp only [localImage] at restricted
  generalize_proofs firstProof secondProof at restricted
  generalize commonDef : domain ⊓ charts index = common at firstProof secondProof restricted overlapEq
  clear commonDef
  cases overlapEq
  have firstMap : homOfLE firstProof = 𝟙 domain := Subsingleton.elim _ _
  rw [firstMap, op_id, target.presheaf.map_id, source.presheaf.map_id] at restricted
  exact restricted

theorem glue_over (index : Index) :
    (glue charts covers localMaps compatible).over (charts index) = localMaps index := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.Hom.ext
  funext subopen
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro sectionValue
  cases subopen with
  | op subopen =>
    change image charts covers localMaps compatible subopen.left sectionValue = _
    exact image_eq_local charts covers localMaps compatible index subopen.left subopen.hom.le sectionValue

include covers in

theorem hom_ext (first second : source ⟶ target)
    (localEq : ∀ index, first.over (charts index) = second.over (charts index)) : first = second := by
  apply Scheme.Modules.hom_ext
  intro domain
  ext sectionValue
  apply (show TopCat.Sheaf Ab schemeModel from (SheafOfModules.toSheaf _).obj target).eq_of_locally_eq'
    (fun index => domain ⊓ charts index) domain (fun index => homOfLE inf_le_left)
    (chartIntersection_covers charts covers domain)
  intro index
  have localValue := congrArg (fun morphism => morphism.val.app
      (op (Over.mk (homOfLE (inf_le_right : domain ⊓ charts index ≤ charts index))))
      (source.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op sectionValue))
    (localEq index)
  change target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op
      (Scheme.Modules.Hom.app first domain sectionValue) =
    target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op
      (Scheme.Modules.Hom.app second domain sectionValue)
  have firstNatural := ConcreteCategory.congr_hom
    (((Scheme.Modules.toPresheaf schemeModel).map first).naturality
      (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op) sectionValue
  have secondNatural := ConcreteCategory.congr_hom
    (((Scheme.Modules.toPresheaf schemeModel).map second).naturality
      (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op) sectionValue
  simp only [ConcreteCategory.comp_apply] at firstNatural secondNatural
  change Scheme.Modules.Hom.app first (domain ⊓ charts index)
      (source.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op sectionValue) =
    target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op
      (Scheme.Modules.Hom.app first domain sectionValue) at firstNatural
  change Scheme.Modules.Hom.app second (domain ⊓ charts index)
      (source.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op sectionValue) =
    target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op
      (Scheme.Modules.Hom.app second domain sectionValue) at secondNatural
  exact firstNatural.symm.trans (localValue.trans secondNatural)

end LocalModuleGluing

end BondalThomsen

end

section
/- Source: Toric/Projective/PullbackSheafIso.lean; generic schemes and polynomial Proj only. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TopCat

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

noncomputable section

theorem moduleRestrictUnitIso_pullbackUnit {source target : Scheme}
    (inclusion : source ⟶ target) [IsOpenImmersion inclusion] :
    (Scheme.Modules.restrictFunctorIsoPullback inclusion).hom.app
        (SheafOfModules.unit target.ringCatSheaf) ≫
      (Scheme.Modules.pullbackObjUnitIso inclusion).hom =
        (Scheme.Modules.restrictUnitIso inclusion).hom := by
  apply ((Scheme.Modules.restrictAdjunction inclusion).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right,
    Scheme.Modules.restrictFunctorIsoPullback,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [← Adjunction.homEquiv_unit]
  erw [Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom]
  ext open_set coefficient
  change inclusion.app open_set coefficient = _
  rw [Adjunction.homEquiv_unit]
  change inclusion.app open_set coefficient =
    (inclusion.appIso (inclusion ⁻¹ᵁ open_set)).hom
      (target.presheaf.map (homOfLE (inclusion.image_preimage_le open_set)).op coefficient)
  apply (ConcreteCategory.bijective_of_isIso
    (inclusion.appIso (inclusion ⁻¹ᵁ open_set)).inv).1
  rw [← ConcreteCategory.comp_apply, inclusion.app_appIso_inv,
    ← ConcreteCategory.comp_apply, Iso.hom_inv_id]
  rfl

theorem modulePullbackSectionHom_restrict {source target : Scheme}
    (inclusion : source ⟶ target) [IsOpenImmersion inclusion] {sheaf : target.Modules}
    (section_map : SheafOfModules.unit target.ringCatSheaf ⟶ sheaf) :
    modulePullbackSectionHom inclusion section_map =
      (Scheme.Modules.restrictUnitIso inclusion).inv ≫
        (Scheme.Modules.restrictFunctor inclusion).map section_map ≫
          (Scheme.Modules.restrictFunctorIsoPullback inclusion).hom.app sheaf := by
  have unit_equality := moduleRestrictUnitIso_pullbackUnit inclusion
  have inverse_equality :
      (Scheme.Modules.pullbackObjUnitIso inclusion).inv =
        (Scheme.Modules.restrictUnitIso inclusion).inv ≫
          (Scheme.Modules.restrictFunctorIsoPullback inclusion).hom.app
            (SheafOfModules.unit target.ringCatSheaf) := by
    apply (cancel_mono (Scheme.Modules.pullbackObjUnitIso inclusion).hom).mp
    simp only [Category.assoc, unit_equality, Iso.inv_hom_id]
  unfold modulePullbackSectionHom
  rw [inverse_equality, Category.assoc]
  rw [← (Scheme.Modules.restrictFunctorIsoPullback inclusion).hom.naturality section_map]

theorem moduleHom_restrict_isIso {source target : Scheme}
    (inclusion : source ⟶ target) [IsOpenImmersion inclusion]
    {first second : target.Modules} (morphism : first ⟶ second)
    (local_iso : IsIso (morphism.over inclusion.opensRange)) :
    IsIso ((Scheme.Modules.restrictFunctor inclusion).map morphism) := by
  let := local_iso
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro open_set
  let local_open : Over inclusion.opensRange :=
    Over.mk (homOfLE (show inclusion ''ᵁ open_set ≤ inclusion.opensRange from
      fun _ contained => by rcases contained with ⟨point, member, rfl⟩; exact ⟨point, rfl⟩))
  have app_iso := (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map_isIso
    (morphism.over inclusion.opensRange)
  let := app_iso
  have component_iso : IsIso
      (((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
        (morphism.over inclusion.opensRange)).app (op local_open)) := inferInstance
  exact component_iso

theorem moduleHom_over_isIso_of_restrict {source target : Scheme}
    (inclusion : source ⟶ target) [IsOpenImmersion inclusion]
    {first second : target.Modules} (morphism : first ⟶ second)
    (local_iso : IsIso ((Scheme.Modules.restrictFunctor inclusion).map morphism)) :
    IsIso (morphism.over inclusion.opensRange) := by
  let := local_iso
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.forget _)).mp
  apply (isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)).mp
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro local_open
  have image_equality : inclusion ''ᵁ (inclusion ⁻¹ᵁ local_open.unop.left) =
      local_open.unop.left := by
    apply Opens.ext
    exact Set.image_preimage_eq_of_subset local_open.unop.hom.le
  have component_iso := (Scheme.Modules.Hom.isIso_iff_isIso_app.mp local_iso)
    (inclusion ⁻¹ᵁ local_open.unop.left)
  change IsIso (Scheme.Modules.Hom.app morphism local_open.unop.left)
  change IsIso (Scheme.Modules.Hom.app morphism
    (inclusion ''ᵁ (inclusion ⁻¹ᵁ local_open.unop.left))) at component_iso
  rwa [image_equality] at component_iso

theorem modulePullbackSectionHom_comp_isIso {source middle target : Scheme}
    (first : source ⟶ middle) (second : middle ⟶ target) {sheaf : target.Modules}
    (section_map : SheafOfModules.unit target.ringCatSheaf ⟶ sheaf)
    (local_iso : IsIso (modulePullbackSectionHom second section_map)) :
    IsIso (modulePullbackSectionHom (first ≫ second) section_map) := by
  let := local_iso
  rw [← modulePullbackSectionHom_comp first second section_map]
  change IsIso ((Scheme.Modules.pullbackObjUnitIso first).inv ≫
    (Scheme.Modules.pullback first).map (modulePullbackSectionHom second section_map) ≫
      (Scheme.Modules.pullbackComp first second).hom.app sheaf)
  apply IsIso.comp_isIso'
  · infer_instance
  · apply IsIso.comp_isIso'
    · infer_instance
    · exact inferInstanceAs (IsIso ((Scheme.Modules.pullbackComp first second).hom.app sheaf))

theorem modulePullbackSectionHom_over_isIso {source target : Scheme}
    (inclusion : source ⟶ target) [IsOpenImmersion inclusion] {sheaf : target.Modules}
    (section_map : SheafOfModules.unit target.ringCatSheaf ⟶ sheaf)
    (local_iso : IsIso (modulePullbackSectionHom inclusion section_map)) :
    IsIso (section_map.over inclusion.opensRange) := by
  apply moduleHom_over_isIso_of_restrict inclusion
  rw [modulePullbackSectionHom_restrict] at local_iso
  exact (isIso_comp_right_iff _
    ((Scheme.Modules.restrictFunctorIsoPullback inclusion).hom.app sheaf)).mp
      ((isIso_comp_left_iff (Scheme.Modules.restrictUnitIso inclusion).inv _).mp local_iso)

attribute [local instance] MvPolynomial.gradedAlgebra

variable (Index : Type)

theorem polynomialProjDegreeOneCoordinateHom_restrict_isIso (coordinate : Index) :
    IsIso ((Scheme.Modules.restrictFunctor
      (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate).ι).map
        (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate)) := by
  apply moduleHom_restrict_isIso
  erw [Scheme.Opens.opensRange_ι]
  exact polynomialProjDegreeOneCoordinateHom_over_isIso 𝕜 Index coordinate

theorem polynomialProjDegreeOneCoordinateHom_pullbackChart_isIso (coordinate : Index) :
    IsIso (modulePullbackSectionHom (Proj.awayι (MvPolynomial.homogeneousSubmodule Index 𝕜)
      (MvPolynomial.X coordinate) (MvPolynomial.isHomogeneous_X 𝕜 coordinate) (by decide))
        (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate)) := by
  let chart_iso := Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule Index 𝕜)
    (MvPolynomial.X coordinate) (MvPolynomial.isHomogeneous_X 𝕜 coordinate) (by decide)
  let := polynomialProjDegreeOneCoordinateHom_restrict_isIso 𝕜 Index coordinate
  have local_iso : IsIso (modulePullbackSectionHom
      (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate).ι
        (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate)) := by
    rw [modulePullbackSectionHom_restrict]
    infer_instance
  have chart_map : Proj.awayι (MvPolynomial.homogeneousSubmodule Index 𝕜)
      (MvPolynomial.X coordinate) (MvPolynomial.isHomogeneous_X 𝕜 coordinate) (by decide) =
      chart_iso.inv ≫ (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate).ι := rfl
  rw [chart_map]
  exact modulePullbackSectionHom_comp_isIso chart_iso.inv
    (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate).ι
    (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate) local_iso

end

end BondalThomsen

end

section
/- Source: Toric/Projective/GlobalSheafIso.lean; generic schemes and polynomial Proj only. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TopCat

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

noncomputable section

theorem modulePullbackSectionHom_transpose {source target : Scheme}
    (map : source ⟶ target) {sheaf : target.Modules}
    (section_map : SheafOfModules.unit target.ringCatSheaf ⟶ sheaf) :
    section_map ≫ (Scheme.Modules.pullbackPushforwardAdjunction map).unit.app sheaf =
      SheafOfModules.unitToPushforwardObjUnit map.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward map).map (modulePullbackSectionHom map section_map) := by
  have transpose := (Scheme.Modules.pullbackPushforwardAdjunction map).homEquiv_naturality_right
    (Scheme.Modules.pullbackObjUnitIso map).hom (modulePullbackSectionHom map section_map)
  rw [Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom] at transpose
  have cancellation : (Scheme.Modules.pullbackObjUnitIso map).hom ≫
      modulePullbackSectionHom map section_map = (Scheme.Modules.pullback map).map section_map := by
    simp only [modulePullbackSectionHom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [cancellation, Adjunction.homEquiv_unit] at transpose
  exact ((Scheme.Modules.pullbackPushforwardAdjunction map).unit.naturality section_map).trans transpose

theorem modulePullbackSectionHom_app_one {source target : Scheme}
    (map : source ⟶ target) {sheaf : target.Modules}
    (section_map : SheafOfModules.unit target.ringCatSheaf ⟶ sheaf)
    (open_set : target.Opens) :
    Scheme.Modules.Hom.app (modulePullbackSectionHom map section_map) (map ⁻¹ᵁ open_set)
        (1 : Γ(source, map ⁻¹ᵁ open_set)) =
      Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app sheaf)
        open_set (Scheme.Modules.Hom.app section_map open_set (1 : Γ(target, open_set))) := by
  have transpose := congrArg (fun morphism : SheafOfModules.unit target.ringCatSheaf ⟶
      (Scheme.Modules.pushforward map).obj ((Scheme.Modules.pullback map).obj sheaf) =>
    Scheme.Modules.Hom.app morphism open_set
    (1 : Γ(target, open_set))) (modulePullbackSectionHom_transpose map section_map)
  change Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app sheaf)
      open_set (Scheme.Modules.Hom.app section_map open_set (1 : Γ(target, open_set))) =
    Scheme.Modules.Hom.app (modulePullbackSectionHom map section_map) (map ⁻¹ᵁ open_set)
      (map.app open_set (1 : Γ(target, open_set))) at transpose
  have mapped_one : map.app open_set (1 : Γ(target, open_set)) = 1 := map_one _
  rw [mapped_one] at transpose
  exact transpose.symm

theorem modulePullbackSectionHom_appLE_one {source target : Scheme}
    (map : source ⟶ target) {sheaf : target.Modules}
    (section_map : SheafOfModules.unit target.ringCatSheaf ⟶ sheaf)
    (target_open : target.Opens) (source_open : source.Opens)
    (contained : source_open ≤ map ⁻¹ᵁ target_open) :
    Scheme.Modules.Hom.app (modulePullbackSectionHom map section_map) source_open
        (1 : Γ(source, source_open)) =
      ((Scheme.Modules.pullback map).obj sheaf).presheaf.map (homOfLE contained).op
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app sheaf)
          target_open (Scheme.Modules.Hom.app section_map target_open (1 : Γ(target, target_open)))) := by
  have naturality := ConcreteCategory.congr_hom
    (((Scheme.Modules.toPresheaf source).map (modulePullbackSectionHom map section_map)).naturality
      (homOfLE contained).op) (1 : Γ(source, map ⁻¹ᵁ target_open))
  change Scheme.Modules.Hom.app (modulePullbackSectionHom map section_map) source_open
      (source.presheaf.map (homOfLE contained).op 1) =
    ((Scheme.Modules.pullback map).obj sheaf).presheaf.map (homOfLE contained).op
      (Scheme.Modules.Hom.app (modulePullbackSectionHom map section_map) (map ⁻¹ᵁ target_open)
        (1 : Γ(source, map ⁻¹ᵁ target_open))) at naturality
  have mapped_one : source.presheaf.map (homOfLE contained).op
      (1 : Γ(source, map ⁻¹ᵁ target_open)) = 1 := map_one _
  rw [mapped_one, modulePullbackSectionHom_app_one] at naturality
  exact naturality

theorem modulePullbackSectionHom_coefficient {source target : Scheme}
    (map : source ⟶ target) {sheaf : target.Modules}
    (first second : SheafOfModules.unit target.ringCatSheaf ⟶ sheaf)
    (target_open : target.Opens) (source_open : source.Opens)
    (contained : source_open ≤ map ⁻¹ᵁ target_open) (scalar : Γ(target, target_open))
    (relation : Scheme.Modules.Hom.app second target_open (1 : Γ(target, target_open)) =
      scalar • Scheme.Modules.Hom.app first target_open (1 : Γ(target, target_open))) :
    Scheme.Modules.Hom.app (modulePullbackSectionHom map second) source_open
        (1 : Γ(source, source_open)) =
      map.appLE target_open source_open contained scalar •
        Scheme.Modules.Hom.app (modulePullbackSectionHom map first) source_open
          (1 : Γ(source, source_open)) := by
  rw [modulePullbackSectionHom_appLE_one map second target_open source_open contained, relation,
    modulePullbackSectionHom_appLE_one map first target_open source_open contained]
  rw [Scheme.Modules.Hom.app_smul]
  let section_value : Γ((Scheme.Modules.pullback map).obj sheaf, map ⁻¹ᵁ target_open) :=
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app sheaf)
      target_open (Scheme.Modules.Hom.app first target_open (1 : Γ(target, target_open)))
  change ((Scheme.Modules.pullback map).obj sheaf).presheaf.map (homOfLE contained).op
      (map.app target_open scalar • section_value) = _
  rw [Scheme.Modules.map_smul]
  rfl

attribute [local instance] MvPolynomial.gradedAlgebra

theorem polynomialProjDegreeOneCoordinateHom_coefficient (Index : Type)
    (chart coordinate : Index) :
    Scheme.Modules.Hom.app (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate)
        (polynomialDegreeOneCoordinateOpen 𝕜 Index chart)
          (1 : Γ(polynomialDegreeOneProj 𝕜 Index, polynomialDegreeOneCoordinateOpen 𝕜 Index chart)) =
      polynomialDegreeOneChartRatio 𝕜 Index chart coordinate le_rfl •
        Scheme.Modules.Hom.app (polynomialProjDegreeOneCoordinateHom 𝕜 Index chart)
          (polynomialDegreeOneCoordinateOpen 𝕜 Index chart)
            (1 : Γ(polynomialDegreeOneProj 𝕜 Index, polynomialDegreeOneCoordinateOpen 𝕜 Index chart)) := by
  simp only [polynomialProjDegreeOneCoordinateHom, moduleGlobalSectionHom_app, one_smul]
  rw [polynomialProjDegreeOneGlobalCoordinate_restrict,
    polynomialProjDegreeOneGlobalCoordinate_restrict]
  rw [← polynomialDegreeOneChartRatio_frame 𝕜 Index chart coordinate le_rfl]
  change (polynomialDegreeOneChartSectionsLinearEquiv 𝕜 Index chart le_rfl)
      (polynomialDegreeOneChartRatio 𝕜 Index chart coordinate le_rfl) =
    polynomialDegreeOneChartRatio 𝕜 Index chart coordinate le_rfl •
      (polynomialDegreeOneChartSectionsLinearEquiv 𝕜 Index chart le_rfl) 1
  simpa only [smul_eq_mul, mul_one] using
    (polynomialDegreeOneChartSectionsLinearEquiv 𝕜 Index chart le_rfl).map_smul
      (polynomialDegreeOneChartRatio 𝕜 Index chart coordinate le_rfl) 1

theorem moduleSectionHom_coefficient_restrict {scheme : Scheme} {sheaf : scheme.Modules}
    (first second : SheafOfModules.unit scheme.ringCatSheaf ⟶ sheaf)
    (larger smaller : scheme.Opens) (contained : smaller ≤ larger) (scalar : Γ(scheme, larger))
    (relation : Scheme.Modules.Hom.app second larger (1 : Γ(scheme, larger)) =
      scalar • Scheme.Modules.Hom.app first larger (1 : Γ(scheme, larger))) :
    Scheme.Modules.Hom.app second smaller (1 : Γ(scheme, smaller)) =
      scheme.presheaf.map (homOfLE contained).op scalar •
        Scheme.Modules.Hom.app first smaller (1 : Γ(scheme, smaller)) := by
  have first_natural := ConcreteCategory.congr_hom
    (((Scheme.Modules.toPresheaf scheme).map first).naturality (homOfLE contained).op)
      (1 : Γ(scheme, larger))
  have second_natural := ConcreteCategory.congr_hom
    (((Scheme.Modules.toPresheaf scheme).map second).naturality (homOfLE contained).op)
      (1 : Γ(scheme, larger))
  change Scheme.Modules.Hom.app first smaller (scheme.presheaf.map (homOfLE contained).op 1) =
    sheaf.presheaf.map (homOfLE contained).op (Scheme.Modules.Hom.app first larger
      (1 : Γ(scheme, larger))) at first_natural
  change Scheme.Modules.Hom.app second smaller (scheme.presheaf.map (homOfLE contained).op 1) =
    sheaf.presheaf.map (homOfLE contained).op (Scheme.Modules.Hom.app second larger
      (1 : Γ(scheme, larger))) at second_natural
  have mapped_one : scheme.presheaf.map (homOfLE contained).op
      (1 : Γ(scheme, larger)) = 1 := map_one _
  rw [mapped_one] at first_natural second_natural
  rw [second_natural, relation, Scheme.Modules.map_smul, ← first_natural]

theorem restrictLocalModuleHom_isIso {scheme : Scheme} {first second : scheme.Modules}
    {smaller larger : scheme.Opens} (contained : smaller ≤ larger)
    (morphism : first.over larger ⟶ second.over larger) [IsIso morphism] :
    IsIso (restrictLocalModuleHom contained morphism) := by
  unfold restrictLocalModuleHom
  infer_instance

attribute [local instance] restrictLocalModuleHom_isIso

theorem restrictLocalModuleHom_inverse {scheme : Scheme} {first second : scheme.Modules}
    {smaller larger : scheme.Opens} (contained : smaller ≤ larger)
    (comparison : first.over larger ≅ second.over larger) :
    restrictLocalModuleHom contained comparison.inv =
      inv (restrictLocalModuleHom contained comparison.hom) := by
  let := restrictLocalModuleHom_isIso contained comparison.hom
  apply (cancel_epi (restrictLocalModuleHom contained comparison.hom)).mp
  rw [← restrictLocalModuleHom_map_comp, Iso.hom_inv_id, IsIso.hom_inv_id]
  rfl

theorem polynomialProjAwayToSection_comp_chartApp (Index : Type) (chart : Index) :
    Proj.awayToSection (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart) ≫
      (Proj.awayι (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart)
        (MvPolynomial.isHomogeneous_X 𝕜 chart) (by decide)).appLE
          (polynomialDegreeOneCoordinateOpen 𝕜 Index chart) ⊤
            (by
              intro point _member
              change _ ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart)
              rw [← Proj.opensRange_awayι _ _ (MvPolynomial.isHomogeneous_X 𝕜 chart) (by decide)]
              exact ⟨point, rfl⟩) =
      (Scheme.ΓSpecIso _).inv := by
  let chart_iso := Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule Index 𝕜)
    (MvPolynomial.X chart) (MvPolynomial.isHomogeneous_X 𝕜 chart) (by decide)
  have target_contains : ⊤ ≤
      (Proj.awayι (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart)
        (MvPolynomial.isHomogeneous_X 𝕜 chart) (by decide)) ⁻¹ᵁ
          (polynomialDegreeOneCoordinateOpen 𝕜) Index chart := by
    intro point member
    change _ ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart)
    rw [← Proj.opensRange_awayι _ _ (MvPolynomial.isHomogeneous_X 𝕜 chart) (by decide)]
    exact ⟨point, rfl⟩
  have composition := Scheme.Hom.appLE_comp_appLE chart_iso.hom
    (Proj.awayι (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart)
      (MvPolynomial.isHomogeneous_X 𝕜 chart) (by decide))
        (polynomialDegreeOneCoordinateOpen 𝕜 Index chart) ⊤ ⊤ target_contains (by simp)
  have chart_composite : chart_iso.hom ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart)
        (MvPolynomial.isHomogeneous_X 𝕜 chart) (by decide) =
      (polynomialDegreeOneCoordinateOpen 𝕜 Index chart).ι := by
    change chart_iso.hom ≫ (chart_iso.inv ≫ _) = _
    simp
  simp only [chart_composite] at composition
  have chart_app : chart_iso.hom.appLE ⊤ ⊤ (by simp) = chart_iso.hom.appTop := by
    exact chart_iso.hom.appLE_eq_app
  rw [chart_app] at composition
  have open_app : (polynomialDegreeOneCoordinateOpen 𝕜 Index chart).ι.appLE
      (polynomialDegreeOneCoordinateOpen 𝕜 Index chart) ⊤ (by simp) =
      (polynomialDegreeOneCoordinateOpen 𝕜 Index chart).topIso.inv := rfl
  rw [open_app] at composition
  change _ ≫ chart_iso.hom.appTop = _ at composition
  rw [Proj.basicOpenIsoSpec_hom] at composition
  change _ ≫ (Proj.basicOpenToSpec (MvPolynomial.homogeneousSubmodule Index 𝕜)
    (MvPolynomial.X chart)).app ⊤ = _ at composition
  rw [Proj.basicOpenToSpec_app_top] at composition
  have shortened :
      (Proj.awayι (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart)
        (MvPolynomial.isHomogeneous_X 𝕜 chart) (by decide)).appLE
          (polynomialDegreeOneCoordinateOpen 𝕜 Index chart) ⊤ target_contains ≫
        (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection
          (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart) = 𝟙 _ := by
    apply (cancel_mono (polynomialDegreeOneCoordinateOpen 𝕜 Index chart).topIso.inv).mp
    simpa only [Category.assoc, Category.id_comp] using composition
  let : IsIso (Proj.awayToSection (MvPolynomial.homogeneousSubmodule Index 𝕜)
      (MvPolynomial.X chart)) := inferInstanceAs (IsIso ((Proj.basicOpenIsoAway
        (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart)
          (MvPolynomial.isHomogeneous_X 𝕜 chart) (by decide)).hom))
  apply (cancel_mono (Scheme.ΓSpecIso _).hom).mp
  apply (cancel_mono (Proj.awayToSection
    (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart))).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp] using
    congrArg (fun morphism => Proj.awayToSection
      (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart) ≫ morphism) shortened

end

end BondalThomsen

end

end
