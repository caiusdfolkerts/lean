module

public import PaperVerification.HomogeneousChartDehomogenization
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.Localization.Basic

/-!
# Actual Proj restrictions in normalized homogeneous coordinates

For arbitrary naturally graded commutative rings, the intersection of the
actual degree-one basic opens is the localization of the normalized chart
at the second normalized coordinate. The comparison is induced by the
existing homogeneous-localization restriction map. Its compatibility with
the actual Proj structure-sheaf restriction is proved explicitly.

The other chart's homogeneous coordinates become the literal unit ratios.
All rings, quotients and localizations here retain nilpotents. This is an
uncompiled source candidate and does not assert a paper-level theorem.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.HomogeneousChartOverlap

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open PaperVerification.HomogeneousChartDehomogenization

universe u v
variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)

/-- The actual normalized chart localized at the other coordinate. -/
abbrev OverlapRing (f g : A) := Localization.Away (quotientMap f g)

/-- The original homogeneous coordinate map into this literal overlap. -/
def coordinateMap (f g : A) : A →+* OverlapRing f g :=
  (algebraMap (NormalizedRing f) (OverlapRing f g)).comp (quotientMap f)

@[simp] theorem coordinateMap_pivot (f g : A) : coordinateMap f g f = 1 := by
  rw [coordinateMap, RingHom.comp_apply, quotientMap_pivot, map_one]

/-- The second coordinate is a unit by the actual localization property. -/
theorem coordinateMap_other_isUnit (f g : A) : IsUnit (coordinateMap f g g) :=
  IsLocalization.Away.algebraMap_isUnit (S := OverlapRing f g) (quotientMap f g)

/-- The first coordinate remains the literal unit after localization. -/
theorem coordinateMap_pivot_isUnit (f g : A) : IsUnit (coordinateMap f g f) := by
  rw [coordinateMap_pivot]
  exact isUnit_one

/-- Hence the actual product basic open receives this coordinate map. -/
theorem coordinateMap_product_isUnit (f g : A) : IsUnit (coordinateMap f g (f * g)) := by
  rw [map_mul]
  exact (coordinateMap_pivot_isUnit f g).mul (coordinateMap_other_isUnit f g)

/-- Degree-one normalization sends the genuine localization element g/f
exactly to the class of g in A/(f-1). -/
theorem dehomogenize_localizationElement :
    awayEquivNormalized 𝒜 hf (Away.isLocalizationElem hf hg) = quotientMap f g := by
  change awayEquivNormalized 𝒜 hf (Away.mk 𝒜 hf 1 (g ^ 1) _) = quotientMap f g
  simpa only [pow_one,fraction] using
    awayEquivNormalized_fraction 𝒜 hf 1 (⟨g, hg⟩ : 𝒜 1)

/-- The actual multiplicative sets are carried to each other. -/
theorem powers_dehomogenize :
    (Submonoid.powers (Away.isLocalizationElem hf hg)).map
        (awayEquivNormalized 𝒜 hf).toMonoidHom =
      Submonoid.powers (quotientMap f g) := by
  rw [Submonoid.map_powers]
  congr 1
  exact dehomogenize_localizationElement 𝒜 hf hg

/-- The actual product basic-open ring, with the original awayMap algebra
structure, is the localization of the actual normalized chart. -/
def overlapEquiv : Away 𝒜 (f * g) ≃+* OverlapRing f g := by
  letI := (awayMap 𝒜 hg (rfl : f * g = f * g)).toAlgebra
  letI := Away.isLocalization_mul hf hg (rfl : f * g = f * g) one_ne_zero
  exact IsLocalization.ringEquivOfRingEquiv (Away 𝒜 (f * g)) (OverlapRing f g)
    (awayEquivNormalized 𝒜 hf) (powers_dehomogenize 𝒜 hf hg)

/-- On the original chart, this equivalence carries the genuine Proj
restriction to the canonical ordinary localization map. -/
theorem overlapEquiv_restriction (z : Away 𝒜 f) :
    overlapEquiv 𝒜 hf hg (awayMap 𝒜 hg (rfl : f * g = f * g) z) =
      algebraMap (NormalizedRing f) (OverlapRing f g) (awayEquivNormalized 𝒜 hf z) := by
  letI := (awayMap 𝒜 hg (rfl : f * g = f * g)).toAlgebra
  letI := Away.isLocalization_mul hf hg (rfl : f * g = f * g) one_ne_zero
  exact IsLocalization.ringEquivOfRingEquiv_eq (powers_dehomogenize 𝒜 hf hg) z

/-- The overlap equivalence is also the literal homogeneous-coordinate
localization lift. This identifies it on every homogeneous fraction. -/
theorem overlapEquiv_eq_lift :
    (overlapEquiv 𝒜 hf hg).toRingHom =
      Away.lift 𝒜 (coordinateMap f g) (coordinateMap_product_isUnit f g) := by
  letI := (awayMap 𝒜 hg (rfl : f * g = f * g)).toAlgebra
  letI := Away.isLocalization_mul hf hg (rfl : f * g = f * g) one_ne_zero
  apply IsLocalization.ringHom_ext (Submonoid.powers (Away.isLocalizationElem hf hg))
  ext z
  change overlapEquiv 𝒜 hf hg (awayMap 𝒜 hg (rfl : f * g = f * g) z) =
    Away.lift 𝒜 (coordinateMap f g) (coordinateMap_product_isUnit f g)
      (awayMap 𝒜 hg (rfl : f * g = f * g) z)
  rw [overlapEquiv_restriction]
  have hfirst := RingHom.congr_fun
    ((algebraMap (NormalizedRing f) (OverlapRing f g)).comp_homogeneousLocalizationAwayLift
      (quotientMap f) (quotientMap_pivot_isUnit f)) z
  have hsecond := RingHom.congr_fun
    (Away.lift_comp_awayMap (𝒜 := 𝒜) (coordinateMap f g) hg (rfl : f * g = f * g)
      (coordinateMap_product_isUnit f g) (coordinateMap_pivot_isUnit f g)) z
  exact hfirst.trans hsecond.symm

/-- Restrict a normalized coordinate from the other chart by the actual
homogeneous-localization restriction, followed by the proved overlap comparison. -/
def otherRestriction : NormalizedRing g →+* OverlapRing f g :=
  (overlapEquiv 𝒜 hf hg).toRingHom.comp
    ((awayMap 𝒜 hf (mul_comm f g)).comp (fromQuotient 𝒜 hg))

/-- Every homogeneous coordinate has the literal ratio formula. No
restriction to field-valued points or to reduced algebras is made. -/
theorem otherRestriction_homogeneous {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    otherRestriction 𝒜 hf hg (quotientMap g a) =
      coordinateMap f g a *
        (↑((coordinateMap_other_isUnit f g).unit ^ n)⁻¹ : OverlapRing f g) := by
  change overlapEquiv 𝒜 hf hg
    (awayMap 𝒜 hf (mul_comm f g)
      (fromQuotient 𝒜 hg (quotientMap g a))) = _
  rw [fromQuotient_quotientMap, normalize_of_mem 𝒜 hg ha]
  have he := RingHom.congr_fun (overlapEquiv_eq_lift 𝒜 hf hg)
    (awayMap 𝒜 hf (mul_comm f g) (fraction 𝒜 hg n ⟨a, ha⟩))
  refine he.trans ?_
  have hr := RingHom.congr_fun
    (Away.lift_comp_awayMap (𝒜 := 𝒜) (coordinateMap f g) hf (mul_comm f g)
      (coordinateMap_product_isUnit f g) (coordinateMap_other_isUnit f g))
    (fraction 𝒜 hg n ⟨a, ha⟩)
  refine hr.trans ?_
  exact Away.lift_mk (𝒜 := 𝒜) (coordinateMap f g)
    (coordinateMap_other_isUnit f g) hg n a (by simpa using ha)

/-- Clearing the actual unit denominator gives an equality in the entire
localized ring, including its possible nilpotents. -/
theorem otherRestriction_homogeneous_mul {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    otherRestriction 𝒜 hf hg (quotientMap g a) * coordinateMap f g g ^ n =
      coordinateMap f g a := by
  rw [otherRestriction_homogeneous 𝒜 hf hg ha]
  have hu : (↑((coordinateMap_other_isUnit f g).unit ^ n) : OverlapRing f g) =
      coordinateMap f g g ^ n := by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  rw [← hu, mul_assoc, Units.inv_mul, mul_one]

/-- In particular, the chart change on degree-one coordinates is division
by the second coordinate, with the unit actually supplied by localization. -/
theorem otherRestriction_degreeOne {a : A} (ha : a ∈ 𝒜 1) :
    otherRestriction 𝒜 hf hg (quotientMap g a) =
      (↑(coordinateMap_other_isUnit f g).unit⁻¹ : OverlapRing f g) *
        coordinateMap f g a := by
  rw [otherRestriction_homogeneous 𝒜 hf hg ha]
  simp only [pow_one, mul_comm]

/-- The inverse pivot is a unit in the other chart's actual overlap map. -/
theorem otherRestriction_pivot_isUnit :
    IsUnit (otherRestriction 𝒜 hf hg (quotientMap g f)) := by
  rw [otherRestriction_degreeOne 𝒜 hf hg hf, coordinateMap_pivot, mul_one]
  exact ((coordinateMap_other_isUnit f g).unit⁻¹).isUnit

/-- The genuine Proj overlap therefore induces a ring homomorphism on
both ordinary localized normalized-chart rings. -/
def overlapTransition : OverlapRing g f →+* OverlapRing f g :=
  IsLocalization.Away.lift (S := OverlapRing g f) (quotientMap g f)
    (otherRestriction_pivot_isUnit 𝒜 hf hg)

/-- Its value on every original normalized coordinate is the same literal
ratio, now as an equality of maps between the actual affine overlap rings. -/
theorem overlapTransition_coordinate {a : A} (ha : a ∈ 𝒜 1) :
    overlapTransition 𝒜 hf hg
        (algebraMap (NormalizedRing g) (OverlapRing g f) (quotientMap g a)) =
      (↑(coordinateMap_other_isUnit f g).unit⁻¹ : OverlapRing f g) *
        coordinateMap f g a := by
  rw [overlapTransition, IsLocalization.Away.lift_eq]
  exact otherRestriction_degreeOne 𝒜 hf hg ha

/-- The actual Proj overlap is the spectrum of the literal ordinary
localized normalized chart. -/
def projectiveOverlapIso :
    (Proj.basicOpen 𝒜 (f * g)).toScheme ≅ Spec (CommRingCat.of (OverlapRing f g)) :=
  Proj.basicOpenIsoSpec 𝒜 (f * g) (SetLike.mul_mem_graded hf hg) (by decide) ≪≫
    Scheme.Spec.mapIso (overlapEquiv 𝒜 hf hg).symm.toCommRingCatIso.op

/-- Normalized-chart sections are actual sections of the Proj structure sheaf. -/
def chartSections : CommRingCat.of (NormalizedRing f) ⟶
    Γ(Proj 𝒜, Proj.basicOpen 𝒜 f) :=
  CommRingCat.ofHom (fromQuotient 𝒜 hf) ≫ Proj.awayToSection 𝒜 f

/-- The analogous actual section map on the overlap. -/
def overlapSections : CommRingCat.of (OverlapRing f g) ⟶
    Γ(Proj 𝒜, Proj.basicOpen 𝒜 (f * g)) :=
  CommRingCat.ofHom (overlapEquiv 𝒜 hf hg).symm.toRingHom ≫
    Proj.awayToSection 𝒜 (f * g)

/-- The actual structure-sheaf restriction is the ordinary localization map
under the normalized-chart identifications. -/
theorem chartSections_restrict :
    chartSections 𝒜 hf ≫ (Proj 𝒜).presheaf.map
        (homOfLE (Proj.basicOpen_mono 𝒜 f (f * g) (dvd_mul_right f g))).op =
      CommRingCat.ofHom (algebraMap (NormalizedRing f) (OverlapRing f g)) ≫
        overlapSections 𝒜 hf hg := by
  rw [chartSections, Category.assoc, ← Proj.awayMap_awayToSection 𝒜 hg rfl,
    overlapSections, ← Category.assoc, ← Category.assoc]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change awayMap 𝒜 hg (rfl : f * g = f * g) (fromQuotient 𝒜 hf z) =
    (overlapEquiv 𝒜 hf hg).symm
      (algebraMap (NormalizedRing f) (OverlapRing f g) z)
  apply (overlapEquiv 𝒜 hf hg).injective
  rw [RingEquiv.apply_symm_apply, overlapEquiv_restriction]
  exact congrArg (algebraMap (NormalizedRing f) (OverlapRing f g))
    (toQuotient_fromQuotient 𝒜 hf z)

/-- The other actual structure-sheaf restriction is exactly the proved
unit-ratio map into the same overlap sections. -/
theorem otherChartSections_restrict :
    chartSections 𝒜 hg ≫ (Proj 𝒜).presheaf.map
        (homOfLE (Proj.basicOpen_mono 𝒜 g (f * g) (dvd_mul_left g f))).op =
      CommRingCat.ofHom (otherRestriction 𝒜 hf hg) ≫ overlapSections 𝒜 hf hg := by
  rw [chartSections, Category.assoc,
    ← Proj.awayMap_awayToSection 𝒜 hf (mul_comm f g),
    overlapSections, ← Category.assoc, ← Category.assoc]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change awayMap 𝒜 hf (mul_comm f g) (fromQuotient 𝒜 hg z) =
    (overlapEquiv 𝒜 hf hg).symm
      (overlapEquiv 𝒜 hf hg (awayMap 𝒜 hf (mul_comm f g) (fromQuotient 𝒜 hg z)))
  exact ((overlapEquiv 𝒜 hf hg).symm_apply_apply _).symm

end PaperVerification.HomogeneousChartOverlap
