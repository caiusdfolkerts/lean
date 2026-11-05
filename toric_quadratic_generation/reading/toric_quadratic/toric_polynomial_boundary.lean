module

public import PaperVerification.ToricAffineBoundaryOrders
public import PaperVerification.ToricCartierOrders
public import PaperVerification.ToricRationalPointDegrees
public import Mathlib.RingTheory.Polynomial.Ideal

@[expose] public section

/-!
# Boundary orders on an actual affine-line chart

The origin is the prime defined by evaluation at zero. Its ideal is
literally `(X)`, and its local ring is the actual DVR at that prime.
The coordinate has order one there and zero at every other point of
the affine chart. Arbitrary integral powers are treated without a
positivity restriction on the exponent.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical

variable (k : Type u) [Field k]

def polynomialOrigin : PrimeSpectrum (Polynomial k) :=
  ⟨RingHom.ker (Polynomial.evalRingHom (0 : k)),RingHom.ker_isPrime _⟩

theorem polynomialOrigin_ideal :
    (polynomialOrigin k).asIdeal = Ideal.span {Polynomial.X} := by
  change RingHom.ker (Polynomial.evalRingHom (0 : k)) = _
  simpa using Polynomial.ker_evalRingHom (0 : k)

instance polynomialOrigin_isMaximal : (polynomialOrigin k).asIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (Polynomial.evalRingHom (0 : k))
    (fun a => ⟨Polynomial.C a,by simp⟩)

theorem polynomial_X_mem_iff (p : PrimeSpectrum (Polynomial k)) :
    Polynomial.X ∈ p.asIdeal ↔ p = polynomialOrigin k := by
  constructor
  · intro h
    apply PrimeSpectrum.ext
    symm
    apply (polynomialOrigin_isMaximal k).eq_of_le p.isPrime.ne_top
    rw [polynomialOrigin_ideal]
    apply Ideal.span_le.mpr
    intro q hq
    obtain rfl := Set.mem_singleton_iff.mp hq
    exact h
  · rintro rfl
    rw [polynomialOrigin_ideal]
    exact Ideal.subset_span (Set.mem_singleton _)

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A regular germ outside the affine prime is a unit even if no DVR
structure is specified. At other codimensions the order is zero by its
ordinary definition. -/
theorem affineOpen_order_zero_of_not_mem (R : CommRingCat.{u})
    [IsDomain R] (j : Spec R ⟶ X) [IsOpenImmersion j]
    (p : PrimeSpectrum R) (r : R) (hr : r ∉ p.asIdeal) :
    X.ord (affineOpenCoordinateMap R j r) (j p) = 0 := by
  by_cases hc : Order.coheight (j p) = 1
  · letI : Ring.KrullDimLE 1 (X.presheaf.stalk (j p)) :=
      krullDimLE_of_coheight_le hc.le
    have hu : IsUnit (algebraMap R (Localization.AtPrime p.asIdeal) r) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff
        (S := Localization.AtPrime p.asIdeal) (I := p.asIdeal) r).mpr hr
    have hr0 : r ≠ 0 := fun h => hr (h ▸ p.asIdeal.zero_mem)
    have hr' : affineOpenCoordinateMap R j r ≠ 0 :=
      (map_ne_zero_iff _ (affineOpenCoordinateMap_injective R j)).mpr hr0
    rw [X.ord_eq_iff hc hr']
    change Ring.ordFrac (X.presheaf.stalk (j p))
      (affineOpenCoordinateMap R j r) = WithZero.exp (0 : ℤ)
    rw [← affineOpenStalkEquiv_functionField R j p r]
    have hu' : IsUnit ((affineOpenStalkEquiv R j p)
        (algebraMap R (Localization.AtPrime p.asIdeal) r)) :=
      hu.map (affineOpenStalkEquiv R j p).toRingHom
    simpa only [WithZero.exp_zero] using Ring.ordFrac_of_isUnit hu'
  · exact X.ord_eq_zero_of_coheight_neq_one hc _

variable (j : Spec (.of (Polynomial k)) ⟶ X) [IsOpenImmersion j]

/-- The order of the literal affine coordinate is supported precisely
at the actual origin of that chart. -/
theorem affineLine_coordinate_order (p : PrimeSpectrum (Polynomial k)) :
    X.ord (affineOpenCoordinateMap (.of (Polynomial k)) j Polynomial.X) (j p) =
      if p = polynomialOrigin k then 1 else 0 := by
  by_cases hp : p=polynomialOrigin k
  · subst p
    rw [if_pos rfl]
    exact affineOpen_order_principalPrime (.of (Polynomial k)) j
      (polynomialOrigin k) Polynomial.X Polynomial.X_ne_zero (polynomialOrigin_ideal k)
  · rw [if_neg hp]
    exact affineOpen_order_zero_of_not_mem (.of (Polynomial k)) j p Polynomial.X
      (fun h => hp ((polynomial_X_mem_iff k p).mp h))

theorem affineLine_coordinate_zpow_order (m : ℤ)
    (p : PrimeSpectrum (Polynomial k)) :
    X.ord ((affineOpenCoordinateMap (.of (Polynomial k)) j Polynomial.X)^m) (j p) =
      if p=polynomialOrigin k then m else 0 := by
  have hX : affineOpenCoordinateMap (.of (Polynomial k)) j Polynomial.X ≠ 0 :=
    (map_ne_zero_iff _ (affineOpenCoordinateMap_injective _ j)).mpr Polynomial.X_ne_zero
  rw [rationalOrder_zpow hX,affineLine_coordinate_order]
  split_ifs <;> simp

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.affineLine_coordinate_zpow_order
