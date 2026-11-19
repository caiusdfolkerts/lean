module

public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Degree-one dehomogenization of the actual Proj affine ring

For an arbitrary naturally graded commutative ring and a degree-one element f,
the actual degree-zero localization A_(f) is the literal quotient A/(f-1).
The construction sends a homogeneous fraction a/f^n to the class of a; its
inverse first normalizes every homogeneous component by its corresponding
power of f. Both inverses are proved. No domain, reducedness, or generation
in degree one is assumed.

This is the actual algebraic comparison needed to connect normalized
homogeneous charts to the affine basic opens of Proj. This source candidate
has not yet been compiled.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.HomogeneousChartDehomogenization

open DirectSum

universe u v
variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {f : A} (hf : f ∈ 𝒜 1)

/-- The full normalization ideal, without taking its radical. -/
def normalizationIdeal (f : A) : Ideal A := Ideal.span ({f - 1} : Set A)

/-- The literal normalized quotient ring. -/
abbrev NormalizedRing (f : A) := A ⧸ normalizationIdeal f

/-- The canonical quotient map. -/
def quotientMap (f : A) : A →+* NormalizedRing f :=
  Ideal.Quotient.mk (normalizationIdeal f)

@[simp] theorem quotientMap_pivot (f : A) : quotientMap f f = 1 := by
  apply sub_eq_zero.mp
  rw [← map_one (quotientMap f), ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

theorem quotientMap_pivot_isUnit (f : A) : IsUnit (quotientMap f f) := by
  rw [quotientMap_pivot]
  exact isUnit_one

/-- A degree-n element normalized by the literal power f^n. -/
def fraction (n : ℕ) (a : 𝒜 n) : HomogeneousLocalization.Away 𝒜 f :=
  HomogeneousLocalization.Away.mk 𝒜 hf n a (by simpa using a.property)

@[simp] theorem fraction_val (n : ℕ) (a : 𝒜 n) :
    (fraction 𝒜 hf n a).val =
      Localization.mk (a : A) (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f) := rfl

/-- For each fixed degree, normalization is genuinely additive. -/
def fractionAdd (n : ℕ) : 𝒜 n →+ HomogeneousLocalization.Away 𝒜 f where
  toFun := fraction 𝒜 hf n
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    simp only [fraction_val, ZeroMemClass.coe_zero,
      HomogeneousLocalization.val_zero, Localization.mk_zero]
  map_add' a b := by
    apply HomogeneousLocalization.val_injective
    simp only [fraction_val, HomogeneousLocalization.val_add, AddMemClass.coe_add]
    exact (Localization.add_mk_self _ _ _).symm

@[simp] theorem fractionAdd_apply (n : ℕ) (a : 𝒜 n) :
    fractionAdd 𝒜 hf n a = fraction 𝒜 hf n a := rfl

/-- The normalization maps preserve the actual graded unit. -/
theorem fractionAdd_one :
    fractionAdd 𝒜 hf 0
      (@GradedMonoid.GOne.one ℕ (fun n => ↥(𝒜 n)) _ _) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [fractionAdd_apply, fraction_val, SetLike.coe_gOne,
    HomogeneousLocalization.val_one, pow_zero]
  change Localization.mk (1 : A) (1 : Submonoid.powers f) = 1
  rw [Localization.mk_one_eq_algebraMap, map_one]

/-- The normalization maps preserve every actual graded product. -/
theorem fractionAdd_mul {i j : ℕ} (a : 𝒜 i) (b : 𝒜 j) :
    fractionAdd 𝒜 hf (i + j)
      (@GradedMonoid.GMul.mul ℕ (fun n => ↥(𝒜 n)) _ _ i j a b) =
      fractionAdd 𝒜 hf i a * fractionAdd 𝒜 hf j b := by
  apply HomogeneousLocalization.val_injective
  simp only [fractionAdd_apply, HomogeneousLocalization.val_mul, fraction_val,
    SetLike.coe_gMul, Localization.mk_eq_mk']
  rw [← IsLocalization.mk'_mul]
  exact congrArg
    (IsLocalization.mk' (Localization.Away f) ((a : A) * (b : A)))
    (Subtype.ext (pow_add f i j))

/-- First extend the homogeneous normalization maps to the actual direct sum. -/
def componentNormalization :
    (⨁ n : ℕ, 𝒜 n) →+* HomogeneousLocalization.Away 𝒜 f :=
  DirectSum.toSemiring (fractionAdd 𝒜 hf)
    (fractionAdd_one 𝒜 hf) (fractionAdd_mul 𝒜 hf)

/-- Normalize all homogeneous components using the actual graded decomposition. -/
def normalize : A →+* HomogeneousLocalization.Away 𝒜 f :=
  (componentNormalization 𝒜 hf).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom

/-- On a homogeneous element, the full map is its literal homogeneous fraction. -/
theorem normalize_of_mem {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    normalize 𝒜 hf a = fraction 𝒜 hf n ⟨a, ha⟩ := by
  change DirectSum.toAddMonoid (fractionAdd 𝒜 hf) (DirectSum.decompose 𝒜 a) = _
  rw [DirectSum.decompose_of_mem 𝒜 ha, DirectSum.toAddMonoid_of]
  rfl

@[simp] theorem normalize_pivot : normalize 𝒜 hf f = 1 := by
  rw [normalize_of_mem 𝒜 hf hf]
  apply HomogeneousLocalization.val_injective
  rw [fraction_val, HomogeneousLocalization.val_one]
  simp only [pow_one, Localization.mk_eq_mk']
  exact IsLocalization.mk'_self (Localization.Away f) (Submonoid.mem_powers f)

/-- The full normalization ideal is annihilated; no kernel equality is assumed. -/
theorem normalizationIdeal_le_ker :
    normalizationIdeal f ≤ RingHom.ker (normalize 𝒜 hf) := by
  apply Ideal.span_le.mpr
  intro a ha
  obtain rfl := Set.mem_singleton_iff.mp ha
  change normalize 𝒜 hf (f - 1) = 0
  rw [map_sub, normalize_pivot, map_one, sub_self]

/-- The map from the literal quotient to the actual homogeneous localization. -/
def fromQuotient : NormalizedRing f →+* HomogeneousLocalization.Away 𝒜 f :=
  Ideal.Quotient.lift (normalizationIdeal f) (normalize 𝒜 hf)
    (fun a ha => normalizationIdeal_le_ker 𝒜 hf ha)

@[simp] theorem fromQuotient_quotientMap (a : A) :
    fromQuotient 𝒜 hf (quotientMap f a) = normalize 𝒜 hf a := rfl

/-- Restrict the genuine localization lift of the quotient map to degree zero. -/
def toQuotient (_ : f ∈ 𝒜 1) : HomogeneousLocalization.Away 𝒜 f →+* NormalizedRing f :=
  HomogeneousLocalization.Away.lift 𝒜 (quotientMap f) (quotientMap_pivot_isUnit f)

/-- On every homogeneous fraction, setting f=1 retains its full numerator. -/
@[simp] theorem toQuotient_fraction (n : ℕ) (a : 𝒜 n) :
    toQuotient 𝒜 hf (fraction 𝒜 hf n a) = quotientMap f a := by
  have hu : (quotientMap_pivot_isUnit f).unit = 1 := by
    apply Units.ext
    exact (quotientMap_pivot_isUnit f).unit_spec.trans (quotientMap_pivot f)
  simp only [toQuotient, fraction, HomogeneousLocalization.Away.lift_mk,
    hu, one_pow, inv_one, Units.val_one, mul_one]

/-- Decomposition and subsequent normalization recover the original quotient map. -/
theorem toQuotient_normalize (a : A) :
    toQuotient 𝒜 hf (normalize 𝒜 hf a) = quotientMap f a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | homogeneous a =>
      rw [normalize_of_mem 𝒜 hf a.property, toQuotient_fraction]

/-- The quotient-to-localization-to-quotient composite is the identity. -/
theorem toQuotient_fromQuotient (x : NormalizedRing f) :
    toQuotient 𝒜 hf (fromQuotient 𝒜 hf x) = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [show Ideal.Quotient.mk (normalizationIdeal f) a = quotientMap f a from rfl,
    fromQuotient_quotientMap, toQuotient_normalize]

/-- The reverse composite is the identity on every homogeneous fraction. -/
theorem fromQuotient_toQuotient (z : HomogeneousLocalization.Away 𝒜 f) :
    fromQuotient 𝒜 hf (toQuotient 𝒜 hf z) = z := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf z
  have ha' : a ∈ 𝒜 n := by simpa using ha
  change fromQuotient 𝒜 hf
      (toQuotient 𝒜 hf (fraction 𝒜 hf n ⟨a, ha'⟩)) =
    fraction 𝒜 hf n ⟨a, ha'⟩
  rw [toQuotient_fraction, fromQuotient_quotientMap, normalize_of_mem 𝒜 hf ha']

/-- The actual degree-one affine Proj chart ring is the actual normalized quotient. -/
def awayEquivNormalized :
    HomogeneousLocalization.Away 𝒜 f ≃+* NormalizedRing f where
  toFun := toQuotient 𝒜 hf
  invFun := fromQuotient 𝒜 hf
  left_inv := fromQuotient_toQuotient 𝒜 hf
  right_inv := toQuotient_fromQuotient 𝒜 hf
  map_add' := map_add _
  map_mul' := map_mul _

/-- The equivalence has the defining formula on every degree-n fraction. -/
@[simp] theorem awayEquivNormalized_fraction (n : ℕ) (a : 𝒜 n) :
    awayEquivNormalized 𝒜 hf (fraction 𝒜 hf n a) = quotientMap f a :=
  toQuotient_fraction 𝒜 hf n a

/-- Its inverse on every homogeneous quotient element is the actual normalized fraction. -/
@[simp] theorem awayEquivNormalized_symm_quotientMap {n : ℕ} {a : A}
    (ha : a ∈ 𝒜 n) :
    (awayEquivNormalized 𝒜 hf).symm (quotientMap f a) =
      fraction 𝒜 hf n ⟨a, ha⟩ :=
  normalize_of_mem 𝒜 hf ha

end PaperVerification.HomogeneousChartDehomogenization

