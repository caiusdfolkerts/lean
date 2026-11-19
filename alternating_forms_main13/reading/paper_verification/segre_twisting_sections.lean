module

public import PaperVerification.SegreLocalizationGrading
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.BasicOpen
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Actual twisting-sheaf sections and Laurent homogeneous components

For a nonempty set of coordinate charts, the sections of `O(t)` on their
intersection are canonically the total-degree-`t` part of the coordinate
Laurent algebra. The map is evaluation in the actual prime localizations
used by the twisting sheaf. Its surjectivity uses the proved standard-open
section theorem, and its injectivity uses the standard-open vanishing criterion, over any
commutative base ring. Thus this comparison includes the whole section group.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.TwistingSections

open CoordinateLocalization AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

local notation "P" => MvPolynomial I K
local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K

instance denominator_isLocalization (S : Finset I) :
    IsLocalization.Away (denominator (K := K) S) (LocalLaurent K I S) := by
  change IsLocalization.Away (∏ i ∈ S, (MvPolynomial.X i : P)) (LocalLaurent K I S)
  exact localLaurent_isLocalization S

def chartIntersection (S : Finset I) : (Proj 𝒜).Opens := Proj.basicOpen 𝒜 (denominator S)

/-- The canonical localization map to every actual point of the chart intersection. -/
def toPoint (S : Finset I) (x : chartIntersection (K := K) S) :
    LocalLaurent K I S →+* ProjectiveSpectrum.TwistingSheaf.Localizations 𝒜 x.val := by
  letI : x.val.asHomogeneousIdeal.toIdeal.IsPrime := x.val.isPrime
  exact IsLocalization.Away.lift (denominator S)
    (g := algebraMap P (ProjectiveSpectrum.TwistingSheaf.Localizations 𝒜 x.val))
    (IsLocalization.map_units _
      (⟨denominator S, x.property⟩ : x.val.asHomogeneousIdeal.toIdeal.primeCompl))

@[simp] theorem toPoint_polynomial (S : Finset I) (x : chartIntersection (K := K) S)
    (p : P) : toPoint S x (localizationMap S p)=algebraMap P _ p := by
  letI : x.val.asHomogeneousIdeal.toIdeal.IsPrime := x.val.isPrime
  exact IsLocalization.Away.lift_eq _ _ _

theorem chart_le_power (S : Finset I) (m : ℕ) :
    chartIntersection (K := K) S ≤ Proj.basicOpen 𝒜 ((denominator S)^m) := by
  intro x hx hp
  exact hx (x.isPrime.mem_of_pow_mem m hp)

/-- A homogeneous Laurent fraction has the expected value in every point localization. -/
theorem toPoint_fraction (S : Finset I) (x : chartIntersection (K := K) S)
    (z : LocalLaurent K I S) (m : ℕ) (p : P)
    (hz : z*(localizationMap S (denominator S))^m=localizationMap S p) :
    toPoint S x z = Localization.mk p
      ⟨(denominator S)^m,chart_le_power S m x.property⟩ := by
  letI : x.val.asHomogeneousIdeal.toIdeal.IsPrime := x.val.isPrime
  let d : x.val.asHomogeneousIdeal.toIdeal.primeCompl :=
    ⟨(denominator S)^m,chart_le_power S m x.property⟩
  apply (IsLocalization.map_units
    (ProjectiveSpectrum.TwistingSheaf.Localizations 𝒜 x.val) d).mul_left_injective
  have he := congrArg (toPoint S x) hz
  rw [map_mul,map_pow,toPoint_polynomial,toPoint_polynomial,← map_pow] at he
  exact he.trans (by
    simpa only [Localization.mk_eq_mk'_apply] using
      (IsLocalization.mk'_spec (ProjectiveSpectrum.TwistingSheaf.Localizations 𝒜 x.val) p d).symm)

/-- The entire homogeneous Laurent component maps to actual sections. -/
def toSection (S : Finset I) (hS : S.Nonempty) (t : ℤ)
    (z : localDegree (K := K) S t) : Γ(Proj.twistingSheaf 𝒜 t,chartIntersection S) :=
  ⟨fun x => toPoint S x z.val,by
    obtain ⟨m,j,p,hj,hp,hz⟩ := homogeneous_fraction S hS t z.val z.property
    have hd : (denominator (K := K) S)^m ∈ 𝒜 (m*S.card) := by
      simpa [nsmul_eq_mul] using SetLike.pow_mem_graded m (denominator_homogeneous S)
    have he : (fun x : chartIntersection (K := K) S => toPoint S x z.val) =
        (Proj.twistingSheaf.const hj p ((denominator S)^m) hp hd _ (chart_le_power S m)).val := by
      funext x
      exact toPoint_fraction S x z.val m p hz
    exact he.symm ▸
      (Proj.twistingSheaf.const hj p ((denominator S)^m) hp hd _ (chart_le_power S m)).property⟩

@[simp] theorem toSection_apply (S : Finset I) (hS : S.Nonempty) (t : ℤ)
    (z : localDegree (K := K) S t) (x : chartIntersection (K := K) S) :
    (toSection S hS t z).val x=toPoint S x z.val := rfl

def toSectionHom (S : Finset I) (hS : S.Nonempty) (t : ℤ) :
    localDegree (K := K) S t →+ Γ(Proj.twistingSheaf 𝒜 t,chartIntersection S) where
  toFun := toSection S hS t
  map_zero' := Proj.twistingSheaf.ext (fun x => map_zero (toPoint S x))
  map_add' z w := Proj.twistingSheaf.ext (fun x => map_add (toPoint S x) z.val w.val)

/-- The standard-open vanishing criterion detects every homogeneous Laurent element.
This uses localization at a power of the denominator, so it works over an arbitrary
commutative base ring, including rings with zero divisors. -/
theorem toSection_eq_zero (S : Finset I) (hS : S.Nonempty) (t : ℤ)
    (z : localDegree (K := K) S t) (h : toSection S hS t z = 0) : z = 0 := by
  obtain ⟨m,j,p,hj,hp,hz⟩ := homogeneous_fraction S hS t z.val z.property
  have hd : (denominator (K := K) S)^m ∈ 𝒜 (m*S.card) := by
    simpa [nsmul_eq_mul] using SetLike.pow_mem_graded m (denominator_homogeneous S)
  have he : toSection S hS t z =
      Proj.twistingSheaf.const hj p ((denominator S)^m) hp hd _ (chart_le_power S m) :=
    Proj.twistingSheaf.ext (fun x => toPoint_fraction S x z.val m p hz)
  obtain ⟨N,hN⟩ := (Proj.twistingSheaf.const_eq_zero_iff
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hS.card_pos (denominator_homogeneous S))
    hj hp hd (chart_le_power S m)).mp (he.symm.trans h)
  have hp0 : localizationMap S p = 0 := by
    apply (IsUnit.mul_left_eq_zero ((denominator_image_isUnit (K := K) S).pow N)).mp
    rw [mul_comm]
    simpa only [map_mul,map_pow,map_zero] using congrArg (localizationMap S) hN
  apply Subtype.ext
  apply (IsUnit.mul_left_eq_zero ((denominator_image_isUnit (K := K) S).pow m)).mp
  rw [hz,hp0]

/-- No section information is lost in the Laurent-to-sheaf comparison. -/
theorem toSection_injective (S : Finset I) (hS : S.Nonempty) (t : ℤ) :
    Function.Injective (toSection (K := K) S hS t) := by
  intro z w h
  apply sub_eq_zero.mp
  apply toSection_eq_zero S hS t
  change toSectionHom S hS t (z-w) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr h

def inverseElement (S : Finset I) : LocalLaurent K I S :=
  AddMonoidAlgebra.single (inverseDenominator S) 1

theorem inverseElement_mul_denominator (S : Finset I) :
    inverseElement (K := K) S * localizationMap S (denominator S)=1 := by
  rw [inverseElement,localizationMap_denominator,AddMonoidAlgebra.single_mul_single,
    add_comm,denominator_add_inverse,one_mul,← AddMonoidAlgebra.one_def]

theorem inverseElement_degree (S : Finset I) :
    inverseElement (K := K) S ∈ localDegree S (-(S.card : ℤ)) := by
  have he : totalDegree S (inverseDenominator S)=-(S.card : ℤ) := by
    simp [totalDegree,inverseDenominator]
  rw [← he]
  exact AddMonoidAlgebra.single_mem_gradeBy _ _ _

theorem fraction_mem_degree (S : Finset I) (t : ℤ) (m j : ℕ) (p : P)
    (hj : (j : ℤ)=(m*S.card : ℕ)+t) (hp : p ∈ 𝒜 j) :
    localizationMap S p*(inverseElement S)^m ∈ localDegree (K := K) S t := by
  have h := SetLike.mul_mem_graded (localizationMap_mem_degree S hp)
    (SetLike.pow_mem_graded m (inverseElement_degree (K := K) S))
  have he : (j : ℤ)+m • (-(S.card : ℤ))=t := by
    simp only [nsmul_eq_mul,Int.natCast_mul,mul_neg] at hj ⊢
    omega
  simpa only [he] using h

theorem toSection_surjective (S : Finset I) (hS : S.Nonempty) (t : ℤ) :
    Function.Surjective (toSection (K := K) S hS t) := by
  intro s
  obtain ⟨m,j,hj,p,hp,hs⟩ := Proj.twistingSheaf.exists_eq_const_basicOpen
    (denominator_homogeneous (K := K) S) hS.card_pos s
  let z : LocalLaurent K I S := localizationMap S p*(inverseElement S)^m
  have hz : z*(localizationMap S (denominator S))^m=localizationMap S p := by
    dsimp [z]
    rw [mul_assoc,← mul_pow,inverseElement_mul_denominator,one_pow,mul_one]
  refine ⟨⟨z,fraction_mem_degree S t m j p hj hp⟩,?_⟩
  rw [hs]
  apply Proj.twistingSheaf.ext
  intro x
  exact toPoint_fraction S x z m p hz

/-- Canonical comparison with the full actual twisting-sheaf section group. -/
def sectionsEquiv (S : Finset I) (hS : S.Nonempty) (t : ℤ) :
    localDegree (K := K) S t ≃+ Γ(Proj.twistingSheaf 𝒜 t,chartIntersection S) :=
  AddEquiv.ofBijective (toSectionHom S hS t)
    ⟨toSection_injective S hS t,toSection_surjective S hS t⟩

end PaperVerification.Segre.TwistingSections
