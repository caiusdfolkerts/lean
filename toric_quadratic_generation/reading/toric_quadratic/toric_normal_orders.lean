module

public import PaperVerification.ToricNormalHeightOne
public import PaperVerification.ToricRegularRational
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.AlgebraicGeometry.OrderOfVanishing

@[expose] public section

/-!
# Orders detect regularity in normal local rings of dimension one

These statements use Mathlib's actual local-ring order and the actual
generic stalk of a scheme. In particular, order zero is identified with
an honest unit of the local ring, not stipulated in a divisor definition.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace

/-- A normal Noetherian local domain of dimension one is a DVR. -/
theorem discreteValuationRing_of_normal_dimensionOne (A : Type*)
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (hdim : ringKrullDim A = 1) :
    IsDiscreteValuationRing A := by
  have hnf : ¬ IsField A := by
    intro hf
    have hzero := ringKrullDim_eq_zero_of_isField hf
    rw [hdim] at hzero
    exact one_ne_zero hzero
  letI : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr hdim.le
  apply ((IsDiscreteValuationRing.TFAE A hnf).out 1 4).mpr
  refine ⟨inferInstance,IsLocalRing.maximalIdeal A,⟨?_,inferInstance⟩,?_⟩
  · exact (IsLocalRing.isField_iff_maximalIdeal_eq).not.mp hnf
  · intro P hP
    exact IsLocalRing.eq_maximalIdeal (hP.2.isMaximal_of_ne_bot hP.1)

/-- The exact unit criterion for the actual order homomorphism of a DVR. -/
theorem ordFrac_eq_one_iff_unit (A K : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] (z : K) :
    Ring.ordFrac A z = 1 ↔ ∃ u : Aˣ, algebraMap A K (u : A) = z := by
  change z ∈ MonoidHom.mker (Ring.ordFrac A) ↔ _
  rw [Ring.mker_ordFrac_eq_isUnitSubmonoid]
  change (∃ a : A, IsUnit a ∧ algebraMap A K a = z) ↔ _
  constructor
  · rintro ⟨a,⟨u,rfl⟩,ha⟩
    exact ⟨u,ha⟩
  · rintro ⟨u,hu⟩
    exact ⟨u,u.isUnit,hu⟩

/-- Nonnegative additive order is equivalent to actual regularity in a
DVR; in multiplicative notation this is the inequality `1 ≤ ordFrac`. -/
theorem one_le_ordFrac_iff_regular (A K : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (z : K) (hz : z ≠ 0) :
    1 ≤ Ring.ordFrac A z ↔ ∃ a : A, algebraMap A K a = z := by
  constructor
  · intro h
    rw [Ring.ordFrac_eq_valuation_inv] at h
    have hv0 : 0 < (IsDiscreteValuationRing.maximalIdeal A).valuation K z :=
      zero_lt_iff.mpr ((map_ne_zero _).mpr hz)
    exact IsDiscreteValuationRing.exists_lift_of_le_one ((one_le_inv₀ hv0).mp h)
  · rintro ⟨a,rfl⟩
    apply Ring.ordFrac_ge_one_of_ne_zero
    intro ha
    apply hz
    simp [ha]

section Schemes

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

theorem normal_codimensionOne_stalk_isDVR (x : X)
    [IsIntegrallyClosed (X.presheaf.stalk x)]
    (hx : Order.coheight x = 1) : IsDiscreteValuationRing (X.presheaf.stalk x) := by
  apply discreteValuationRing_of_normal_dimensionOne
  rw [ringKrullDim_stalk_eq_coheight,hx]
  rfl

/-- A nonzero rational function has order zero at a normal codimension-one
point exactly when it is the image of an actual unit of the stalk. -/
theorem rationalOrder_zero_iff_stalkUnit (x : X)
    [IsIntegrallyClosed (X.presheaf.stalk x)] (hx : Order.coheight x = 1)
    (z : X.functionField) (hz : z ≠ 0) :
    X.ord z x = 0 ↔
      ∃ u : (X.presheaf.stalk x)ˣ,
        algebraMap (X.presheaf.stalk x) X.functionField (u : X.presheaf.stalk x) = z := by
  letI := normal_codimensionOne_stalk_isDVR x hx
  rw [X.ord_eq_iff hx hz]
  change Ring.ordFrac (X.presheaf.stalk x) z = 1 ↔ _
  exact ordFrac_eq_one_iff_unit _ _ z

/-- The sign of the actual local order detects membership in the actual
local ring, under the proved normality and codimension hypotheses. -/
theorem rationalOrder_nonnegative_iff_regularAt (x : X)
    [IsIntegrallyClosed (X.presheaf.stalk x)] (hx : Order.coheight x = 1)
    (z : X.functionField) (hz : z ≠ 0) :
    0 ≤ X.ord z x ↔ z ∈ regularAtSubring X x := by
  letI := normal_codimensionOne_stalk_isDVR x hx
  rw [X.le_ord_iff hx hz]
  change 1 ≤ Ring.ordFrac (X.presheaf.stalk x) z ↔ _
  exact one_le_ordFrac_iff_regular _ _ z hz

end Schemes

end PaperVerification.ToricSchemes
