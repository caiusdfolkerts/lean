module

public import PaperVerification.AlternatingFormsExteriorScalarChange
public import PaperVerification.AlternatingFormsOddCharacteristicCutoff
public import PaperVerification.FiniteFiberSpanning
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Divisibility.Units

/-!
# The actual odd quotient over integral coefficient rings

The good words span over every coefficient ring in which the required
factorial is a unit: this follows from the proved basis in every residue
field and the finite-module maximal-submodule argument.  Over a domain,
their independence follows by mapping to the fraction field.  Both maps
are the actual universal maps of exterior algebras, and the relation
spaces are the actual quadratic-generated ideal pieces.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms.IntegralOdd

variable (R : Type*) [CommRing R]

def goodWord (k s : ℕ) (I : GoodOddIndex k s) : quotientDegree R k s :=
  Submodule.Quotient.mk (powerBasis R s (2*k+1) I.val)

theorem firstForm_eq_canonical {K : Type*} [Field K] (k : ℕ) :
    firstForm K k = oddPathFirstQuadratic (Pi.basisFun K (Fin (2*k+1))) := rfl

theorem secondForm_eq_canonical {K : Type*} [Field K] (k : ℕ) :
    secondForm K k = oddPathSecondQuadratic (Pi.basisFun K (Fin (2*k+1))) := rfl

theorem powerBasis_eq_plucker {K : Type*} [Field K] (s n : ℕ) :
    powerBasis K s n = exteriorPluckerBasis (K := K) s n := rfl

theorem goodWord_eq_canonical {K : Type*} [Field K] (k s : ℕ)
    (I : GoodOddIndex k s) :
    goodWord K k s I = Submodule.Quotient.mk
      (exteriorPluckerBasis (K := K) s (2*k+1) I.val) := rfl

variable (S : Type*) [CommRing S] [Algebra R S]

@[simp] theorem quotientMap_goodWord (k s : ℕ) (I : GoodOddIndex k s) :
    quotientMap R S k s (goodWord R k s I) = goodWord S k s I := by
  rw [goodWord, quotientMap_mk, powerMap_basis]
  rfl

variable {S}

/-- The single factorial inverted in the integral statement controls all
the middle-degree inverse coefficients in every field over the ring. -/
theorem degreeFactorials_of_middle_factorial_unit
    {K : Type*} [Field K] [Algebra R K] (k : ℕ)
    (hunit : IsUnit (((k+1)/2).factorial : R)) : DegreeFactorials K (k+1) := by
  intro r hr
  have hr' : r≤(k+1)/2 := by omega
  have hd : (r.factorial : R) ∣ (((k+1)/2).factorial : R) := by
    obtain ⟨c,hc⟩ := Nat.factorial_dvd_factorial hr'
    refine ⟨(c : R), ?_⟩
    simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : R)) hc
  have hu : IsUnit (r.factorial : R) := isUnit_of_dvd_unit hd hunit
  have huK := hu.map (algebraMap R K)
  simpa only [map_natCast] using huK.ne_zero

def fieldGoodBasis {K : Type*} [Field K] (k s : ℕ)
    (hfac : DegreeFactorials K (k+1)) :
    Module.Basis (GoodOddIndex k s) K (quotientDegree K k s) :=
  oddExteriorBasisOfMiddleFactorials k s hfac

@[simp] theorem fieldGoodBasis_apply {K : Type*} [Field K] (k s : ℕ)
    (hfac : DegreeFactorials K (k+1)) (I : GoodOddIndex k s) :
    fieldGoodBasis k s hfac I = goodWord K k s I :=
  oddExteriorBasisOfMiddleFactorials_apply k s hfac I

set_option maxHeartbeats 800000 in
/-- Genuine spanning over the entire ring, including any torsion in the
quotient: all maximal residue fibers are tested. -/
theorem goodWord_span_eq_top (k s : ℕ)
    (hunit : IsUnit (((k+1)/2).factorial : R)) :
    Submodule.span R (Set.range (goodWord R k s)) = ⊤ := by
  classical
  apply PaperVerification.span_eq_top_of_residue_sup_eq_top
  intro m hm
  letI : m.IsMaximal := hm
  let K := R⧸m
  letI : Field K := Ideal.Quotient.field m
  let q : quotientDegree R k s →ₗ[R] quotientDegree K k s :=
    quotientMap R K k s
  have hsurj : Function.Surjective (algebraMap R K) := Ideal.Quotient.mk_surjective
  have hfac : DegreeFactorials K (k+1) :=
    degreeFactorials_of_middle_factorial_unit R k hunit
  have he : (fun I => fieldGoodBasis k s hfac I) = goodWord K k s := by
    funext I
    exact fieldGoodBasis_apply k s hfac I
  have hspanK : Submodule.span K (Set.range (goodWord K k s))=⊤ := by
    rw [← he]
    exact (fieldGoodBasis k s hfac).span_eq
  have hspanR : Submodule.span R (Set.range (goodWord K k s))=⊤ := by
    rw [PaperVerification.span_restrictScalars_of_surjective hsurj, hspanK]
    rfl
  have hmap : (Submodule.span R (Set.range (goodWord R k s))).map q=⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    have he : q ∘ goodWord R k s = goodWord K k s := by
      funext I
      exact quotientMap_goodWord R K k s I
    rw [he, hspanR]
  have hq : q.range=⊤ := LinearMap.range_eq_top.mpr
    (quotientMap_surjective R K hsurj k s)
  have hsup := (LinearMap.map_eq_top_iff hq).mp hmap
  simpa only [q, K, quotientMap_quotient_ker] using hsup

/-- Mapping to the fraction field proves independence of the same literal
good words; no assertion about saturation or torsion is used here. -/
theorem goodWord_linearIndependent [IsDomain R] (k s : ℕ)
    (hunit : IsUnit (((k+1)/2).factorial : R)) :
    LinearIndependent R (goodWord R k s) := by
  let K := FractionRing R
  have hfac : DegreeFactorials K (k+1) :=
    degreeFactorials_of_middle_factorial_unit R k hunit
  have he : (fun I => fieldGoodBasis k s hfac I) = goodWord K k s := by
    funext I
    exact fieldGoodBasis_apply k s hfac I
  have hK : LinearIndependent K (goodWord K k s) := by
    rw [← he]
    exact (fieldGoodBasis k s hfac).linearIndependent
  have hR : LinearIndependent R (goodWord K k s) :=
    hK.restrict_scalars' R
  have hcomp : LinearIndependent R
      ((quotientMap R K k s) ∘ goodWord R k s) := by
    simpa only [Function.comp_def, quotientMap_goodWord] using hR
  exact LinearIndependent.of_comp (quotientMap R K k s) hcomp

/-- The actual free good-word basis over a domain with the printed
factorial inverted, in every homogeneous degree. -/
def integralGoodBasis [IsDomain R] (k s : ℕ)
    (hunit : IsUnit (((k+1)/2).factorial : R)) :
    Module.Basis (GoodOddIndex k s) R (quotientDegree R k s) :=
  Module.Basis.mk (goodWord_linearIndependent R k s hunit)
    (by rw [goodWord_span_eq_top R k s hunit])

@[simp] theorem integralGoodBasis_apply [IsDomain R] (k s : ℕ)
    (hunit : IsUnit (((k+1)/2).factorial : R)) (I : GoodOddIndex k s) :
    integralGoodBasis R k s hunit I = goodWord R k s I :=
  Module.Basis.mk_apply _ _ _

end PaperVerification.AlternatingForms.IntegralOdd
