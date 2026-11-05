module

public import PaperVerification.HomogeneousChartOverlap
public import PaperVerification.HomogeneousQuotientCharts
public import PaperVerification.NormalizedHomogeneousChartRings

/-!
# The genuine Proj overlap maps are the normalized-coordinate transitions

A homogeneous system is interpreted in its literal polynomial quotient.
The actual Proj overlap restriction, transported by the proved ordinary
quotient and localization equivalences, is exactly transitionHom from the
normalized all-algebra point construction. Equality is proved on the full
coordinate rings, using the original polynomial generators and coefficients.
It consequently retains all nilpotents and every commutative test algebra.

This source is an uncompiled candidate. No comparison is postulated and no
paper-level verification is asserted here.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.NormalizedHomogeneousProjOverlap

open MvPolynomial
open PaperVerification

universe u v w
variable {K : Type u} [Field K] {ι : Type v} {η : Type w}
variable (E : NormalizedHomogeneousChart.System K ι η)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original homogeneous equations generate the actual projective ideal. -/
def equationIdeal : Ideal (MvPolynomial ι K) := Ideal.span (Set.range E.equation)

/-- Its homogeneity follows from the specified degrees of the actual equations. -/
theorem equationIdeal_isHomogeneous :
    (equationIdeal E).IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K) := by
  apply Ideal.homogeneous_span
  rintro a ⟨j, rfl⟩
  exact ⟨E.degree j, E.homogeneous j⟩

/-- The actual homogeneous quotient ring. -/
abbrev HomogeneousRing := MvPolynomial ι K ⧸ equationIdeal E

/-- Its canonical grading consists of images of the original polynomial pieces. -/
abbrev grading : ℕ → Submodule K (HomogeneousRing E) :=
  HomogeneousQuotientProjective.grading (equationIdeal E) (equationIdeal_isHomogeneous E)

/-- The original homogeneous coordinate in the quotient ring. -/
def homogeneousCoordinate (i : ι) : HomogeneousRing E :=
  Ideal.Quotient.mk (equationIdeal E) (MvPolynomial.X i)

 theorem homogeneousCoordinate_mem_one (i : ι) :
    homogeneousCoordinate E i ∈ grading E 1 :=
  HomogeneousQuotientProjective.quotient_X_mem_one _ _ i

/-- Double quotient identifies the genuine normalization of the original
homogeneous ring with the literal normalized-equation chart ring. -/
def normalizedEquiv (p : ι) :
    HomogeneousChartDehomogenization.NormalizedRing (homogeneousCoordinate E p) ≃+*
      NormalizedHomogeneousChart.ChartRing E p :=
  HomogeneousQuotientCharts.normalizedQuotientEquiv (equationIdeal E) p

@[simp] theorem normalizedEquiv_class (p : ι) (a : MvPolynomial ι K) :
    normalizedEquiv E p
      (HomogeneousChartDehomogenization.quotientMap (homogeneousCoordinate E p)
        (Ideal.Quotient.mk (equationIdeal E) a)) =
      NormalizedHomogeneousChart.quotientMap E p a :=
  HomogeneousQuotientCharts.normalizedQuotientEquiv_class (equationIdeal E) p a

/-- In particular, the second homogeneous coordinate becomes the literal
second coordinate of the normalized chart. -/
theorem normalizedEquiv_coordinate (p q : ι) :
    normalizedEquiv E p
      (HomogeneousChartDehomogenization.quotientMap (homogeneousCoordinate E p)
        (homogeneousCoordinate E q)) =
      NormalizedHomogeneousChart.coordinate E p q :=
  normalizedEquiv_class E p (MvPolynomial.X q)

/-- Ordinary localization transports this same double-quotient equivalence. -/
def localizedEquiv (p q : ι) :
    HomogeneousChartOverlap.OverlapRing (homogeneousCoordinate E p) (homogeneousCoordinate E q) ≃+*
      NormalizedHomogeneousChart.OverlapRing E p q :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (HomogeneousChartDehomogenization.quotientMap
      (homogeneousCoordinate E p) (homogeneousCoordinate E q)))
    (T := Submonoid.powers (NormalizedHomogeneousChart.coordinate E p q))
    _ _ (normalizedEquiv E p) (by
    rw [Submonoid.map_powers]
    congr 1 <;> exact normalizedEquiv_coordinate E p q)

/-- This comparison is the actual ordinary localization map on every
normalized polynomial class. -/
theorem localizedEquiv_class (p q : ι) (a : MvPolynomial ι K) :
    localizedEquiv E p q
      (algebraMap _ (HomogeneousChartOverlap.OverlapRing
        (homogeneousCoordinate E p) (homogeneousCoordinate E q))
        (HomogeneousChartDehomogenization.quotientMap (homogeneousCoordinate E p)
          (Ideal.Quotient.mk (equationIdeal E) a))) =
      NormalizedHomogeneousChart.overlapMap E p q
        (NormalizedHomogeneousChart.quotientMap E p a) := by
  rw [localizedEquiv, IsLocalization.ringEquivOfRingEquiv_eq, normalizedEquiv_class]
  rfl

/-- The transition obtained from the actual Proj restriction maps, conjugated
by the two proven normalized overlap equivalences. -/
def actualTransition (p q : ι) :
    NormalizedHomogeneousChart.OverlapRing E q p →+*
      NormalizedHomogeneousChart.OverlapRing E p q :=
  (localizedEquiv E p q).toRingHom.comp
    ((HomogeneousChartOverlap.overlapTransition (grading E)
      (homogeneousCoordinate_mem_one E p) (homogeneousCoordinate_mem_one E q)).comp
      (localizedEquiv E q p).symm.toRingHom)

/-- Its value on a normalized polynomial class uses exactly the genuine
other-chart restriction, not a separately imposed coordinate rule. -/
theorem actualTransition_class (p q : ι) (a : MvPolynomial ι K) :
    actualTransition E p q
      (NormalizedHomogeneousChart.overlapMap E q p
        (NormalizedHomogeneousChart.quotientMap E q a)) =
      localizedEquiv E p q
        (HomogeneousChartOverlap.otherRestriction (grading E)
          (homogeneousCoordinate_mem_one E p) (homogeneousCoordinate_mem_one E q)
          (HomogeneousChartDehomogenization.quotientMap (homogeneousCoordinate E q)
            (Ideal.Quotient.mk (equationIdeal E) a))) := by
  rw [← localizedEquiv_class E q p a]
  change localizedEquiv E p q
    (HomogeneousChartOverlap.overlapTransition (grading E)
      (homogeneousCoordinate_mem_one E p) (homogeneousCoordinate_mem_one E q)
      ((localizedEquiv E q p).symm (localizedEquiv E q p _))) = _
  rw [RingEquiv.symm_apply_apply, HomogeneousChartOverlap.overlapTransition,
    IsLocalization.Away.lift_eq]

/-- A degree-zero coefficient is unchanged by the actual transition. -/
theorem actualTransition_constant (p q : ι) (c : K) :
    actualTransition E p q
      (NormalizedHomogeneousChart.overlapMap E q p
        (NormalizedHomogeneousChart.quotientMap E q (MvPolynomial.C c))) =
      NormalizedHomogeneousChart.overlapMap E p q
        (NormalizedHomogeneousChart.quotientMap E p (MvPolynomial.C c)) := by
  rw [actualTransition_class]
  have hc : Ideal.Quotient.mk (equationIdeal E) (MvPolynomial.C c) ∈ grading E 0 := by
    rw [grading,HomogeneousQuotientProjective.grading_eq_piece]
    refine ⟨MvPolynomial.C c, ?_, rfl⟩
    change (MvPolynomial.C c : MvPolynomial ι K) ∈ MvPolynomial.homogeneousSubmodule ι K 0
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_C ι c
  rw [HomogeneousChartOverlap.otherRestriction_homogeneous (grading E)
    (homogeneousCoordinate_mem_one E p) (homogeneousCoordinate_mem_one E q) hc]
  simp only [pow_zero, inv_one, Units.val_one, mul_one]
  exact localizedEquiv_class E p q (MvPolynomial.C c)

/-- Clearing the localized coordinate in the actual Proj transition gives
the original normalized coordinate. This equality is in the full ring. -/
theorem actualTransition_coordinate_mul (p q i : ι) :
    actualTransition E p q
        (NormalizedHomogeneousChart.overlapMap E q p
          (NormalizedHomogeneousChart.coordinate E q i)) *
      NormalizedHomogeneousChart.overlapMap E p q
        (NormalizedHomogeneousChart.coordinate E p q) =
      NormalizedHomogeneousChart.overlapMap E p q
        (NormalizedHomogeneousChart.coordinate E p i) := by
  simp only [NormalizedHomogeneousChart.coordinate]
  rw [actualTransition_class]
  have hm := congrArg (localizedEquiv E p q)
    (HomogeneousChartOverlap.otherRestriction_homogeneous_mul (grading E)
      (homogeneousCoordinate_mem_one E p) (homogeneousCoordinate_mem_one E q)
      (homogeneousCoordinate_mem_one E i))
  rw [map_mul, pow_one] at hm
  have hcoordinate (j : ι) :
      localizedEquiv E p q
        (HomogeneousChartOverlap.coordinateMap (homogeneousCoordinate E p)
          (homogeneousCoordinate E q) (homogeneousCoordinate E j)) =
        NormalizedHomogeneousChart.overlapMap E p q
          (NormalizedHomogeneousChart.coordinate E p j) :=
    localizedEquiv_class E p q (MvPolynomial.X j)
  rw [hcoordinate q,hcoordinate i] at hm
  exact hm

/-- The universal normalized-coordinate transition satisfies the identical
actual equality after clearing the unit pivot. -/
theorem normalizedTransition_coordinate_mul (p q i : ι) :
    NormalizedHomogeneousChart.transitionHom E p q
        (NormalizedHomogeneousChart.overlapMap E q p
          (NormalizedHomogeneousChart.coordinate E q i)) *
      NormalizedHomogeneousChart.overlapMap E p q
        (NormalizedHomogeneousChart.coordinate E p q) =
      NormalizedHomogeneousChart.overlapMap E p q
        (NormalizedHomogeneousChart.coordinate E p i) := by
  let x := NormalizedHomogeneousChart.homToOverlap
    (AlgHom.id K (NormalizedHomogeneousChart.OverlapRing E p q))
  rw [NormalizedHomogeneousChart.transitionHom_coordinate]
  change ((↑x.pivot⁻¹ : NormalizedHomogeneousChart.OverlapRing E p q) * x.coordinate i) *
    x.coordinate q = x.coordinate i
  rw [← x.pivot_eq, mul_right_comm, Units.inv_mul, one_mul]

set_option maxRecDepth 2048 in
/-- The actual Proj transition and the previously constructed all-algebra
point transition are the same homomorphism of complete overlap rings. -/
theorem actualTransition_eq_transitionHom (p q : ι) :
    actualTransition E p q = (NormalizedHomogeneousChart.transitionHom E p q).toRingHom := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (NormalizedHomogeneousChart.coordinate E q p))
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    change actualTransition E p q
        (NormalizedHomogeneousChart.overlapMap E q p
          (NormalizedHomogeneousChart.quotientMap E q (MvPolynomial.C c))) =
      NormalizedHomogeneousChart.transitionHom E p q
        (NormalizedHomogeneousChart.overlapMap E q p
          (NormalizedHomogeneousChart.quotientMap E q (MvPolynomial.C c)))
    rw [actualTransition_constant]
    change algebraMap K (NormalizedHomogeneousChart.OverlapRing E p q) c =
      NormalizedHomogeneousChart.transitionHom E p q
        (algebraMap K (NormalizedHomogeneousChart.OverlapRing E q p) c)
    exact (AlgHom.commutes (NormalizedHomogeneousChart.transitionHom E p q) c).symm
  · intro i
    change actualTransition E p q
        (NormalizedHomogeneousChart.overlapMap E q p
          (NormalizedHomogeneousChart.coordinate E q i)) =
      NormalizedHomogeneousChart.transitionHom E p q
        (NormalizedHomogeneousChart.overlapMap E q p
          (NormalizedHomogeneousChart.coordinate E q i))
    apply (IsLocalization.Away.algebraMap_isUnit
      (S := NormalizedHomogeneousChart.OverlapRing E p q)
      (NormalizedHomogeneousChart.coordinate E p q)).mul_right_cancel
    exact (actualTransition_coordinate_mul E p q i).trans
      (normalizedTransition_coordinate_mul E p q i).symm

/-- In particular, the actual transition induces exactly the original
unit-ratio map on every commutative coefficient algebra, including rings
with nilpotents. -/
theorem actualTransition_on_all_algebra_points {B : Type*} [CommRing B] [Algebra K B]
    (p q : ι) (φ : NormalizedHomogeneousChart.OverlapRing E p q →ₐ[K] B) :
    φ.toRingHom.comp (actualTransition E p q) =
      (NormalizedHomogeneousChart.overlapToHom
        (NormalizedHomogeneousChart.homToOverlap φ).transition).toRingHom := by
  rw [actualTransition_eq_transitionHom]
  exact congrArg AlgHom.toRingHom
    (NormalizedHomogeneousChart.transitionHom_natural φ).symm

end PaperVerification.NormalizedHomogeneousProjOverlap
