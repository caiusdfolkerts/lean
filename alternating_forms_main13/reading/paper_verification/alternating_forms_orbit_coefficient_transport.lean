module

public import PaperVerification.AlternatingFormsOrbitSlots
public import PaperVerification.AlternatingFormsExteriorGenericHilbert
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Equiv.Prod

/-!
# From literal matrix orbit coordinates to actual exterior Hilbert certificates

The blockwise coefficient slots are converted into a genuine basis of the
second exterior power.  The congruence polynomials are then proved to
parametrize the actual exterior images under an invertible linear map.
Consequently their surjective Jacobian supplies a principal open certificate
for the complete Hilbert function of the actual generated-ideal quotient.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial Matrix
open scoped BigOperators Classical

variable {K ν I σ κ : Type*} [Field K]

/-- The orbit calculations group the two coefficient vectors by a Boolean
tag; the relation matrices group them by a sum type. -/
def orbitPairCoefficientPoint (x : Bool × I → K) : (I ⊕ I) → K :=
  x ∘ (Equiv.boolProdEquivSum I).symm

def orbitPairPolynomialCoordinates (p : Bool × I → MvPolynomial σ K) :
    (I ⊕ I) → MvPolynomial σ K :=
  p ∘ (Equiv.boolProdEquivSum I).symm

theorem jacobian_surjective_reindex [Fintype σ] {J : Type*}
    (p : I → MvPolynomial σ K) (v : σ → K) (e : J ≃ I)
    (hJ : (TauCeti.jacobiMatrixAt p v).mulVec.Surjective) :
    (TauCeti.jacobiMatrixAt (p ∘ e) v).mulVec.Surjective := by
  intro y
  obtain ⟨w, hw⟩ := hJ (fun i => y (e.symm i))
  refine ⟨w, ?_⟩
  funext j
  have h := congrFun hw (e j)
  simpa only [TauCeti.jacobiMatrixAt, Matrix.mulVec, dotProduct,
    Matrix.of_apply, Function.comp_apply, Equiv.symm_apply_apply] using h

section CoordinateTransport

variable [Fintype ν] [DecidableEq ν] [Fintype I] [DecidableEq I]
    {row col : I → ν} (hslots : OrbitPairSlots row col)

theorem orbitFormsFromCoordinates_pair_slots (x : Bool × I → K) :
    orbitFormsFromCoordinates (orbitSlotBasis (K := K) hslots)
      (orbitPairCoefficientPoint x) =
      (orbitTwoFormOfSlots row col (fun i => x (false, i)),
        orbitTwoFormOfSlots row col (fun i => x (true, i))) := by
  apply Prod.ext <;>
    simp only [orbitFormsFromCoordinates, orbitPairCoefficientPoint,
      Function.comp_apply, Equiv.boolProdEquivSum, Equiv.coe_fn_symm_mk,
      Sum.elim_inl, Sum.elim_inr, orbitSlotBasis_apply, orbitTwoFormOfSlots]

include hslots in
theorem orbitSlotCoordinates_congruence (X : Matrix ν ν K)
    (f : ⋀[K]^2 (ν → K)) :
    orbitTwoFormOfSlots row col
      (fun i => (X.transpose * orbitExteriorCoefficientMatrix f * X) (row i) (col i)) =
      exteriorPower.map 2 (Matrix.toLin' X.transpose) f := by
  rw [← orbitExteriorCoefficientMatrix_map]
  exact orbitTwoFormOfSlots_reconstruct hslots _

def actualOrbitPolynomials (f g : ⋀[K]^2 (ν → K)) :
    Bool × I → MvPolynomial (ν × ν) K :=
  orbitCongruenceFamily
    (fun z => if z.1 then orbitExteriorCoefficientMatrix g else orbitExteriorCoefficientMatrix f)
    (fun z => row z.2) (fun z => col z.2)

def actualOrbitBasePoint (f g : ⋀[K]^2 (ν → K)) : Bool × I → K :=
  fun z => if z.1 then orbitExteriorCoefficientMatrix g (row z.2) (col z.2)
    else orbitExteriorCoefficientMatrix f (row z.2) (col z.2)

theorem actualOrbitBasePoint_forms (f g : ⋀[K]^2 (ν → K)) :
    orbitFormsFromCoordinates (orbitSlotBasis hslots)
      (orbitPairCoefficientPoint (actualOrbitBasePoint (row := row) (col := col) f g)) =
      (f, g) := by
  rw [orbitFormsFromCoordinates_pair_slots]
  simp only [actualOrbitBasePoint, Bool.false_eq_true, if_false, if_true,
    orbitTwoFormOfSlots_reconstruct hslots]

theorem actualOrbitPolynomials_forms_eval (f g : ⋀[K]^2 (ν → K))
    (x : (ν × ν) → K) :
    orbitFormsFromCoordinates (orbitSlotBasis hslots)
      (fun i => eval x (orbitPairPolynomialCoordinates
        (actualOrbitPolynomials (row := row) (col := col) f g) i)) =
      (exteriorPower.map 2 (Matrix.toLin' (Matrix.of fun i j => x (i, j)).transpose) f,
       exteriorPower.map 2 (Matrix.toLin' (Matrix.of fun i j => x (i, j)).transpose) g) := by
  change orbitFormsFromCoordinates (orbitSlotBasis hslots)
    (orbitPairCoefficientPoint (fun z => eval x
      (actualOrbitPolynomials (row := row) (col := col) f g z))) = _
  rw [orbitFormsFromCoordinates_pair_slots]
  apply Prod.ext <;>
    simp only [actualOrbitPolynomials, orbitCongruenceFamily,
      Bool.false_eq_true, if_false, if_true, orbitCongruenceCoordinate_eval] <;>
    exact orbitSlotCoordinates_congruence hslots _ _

end CoordinateTransport

section InvertibleTransport

variable [Fintype ν] [DecidableEq ν]

def orbitTransposeEquiv (X : Matrix ν ν K) (hX : X.det ≠ 0) :
    (ν → K) ≃ₗ[K] (ν → K) :=
  LinearEquiv.ofBijective (Matrix.toLin' X.transpose) (by
    have hu : IsUnit X.transpose :=
      (Matrix.isUnit_iff_isUnit_det _).mpr
        (isUnit_iff_ne_zero.mpr (by rwa [Matrix.det_transpose]))
    exact ⟨Matrix.mulVec_injective_of_isUnit hu, Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩)

@[simp] theorem orbitTransposeEquiv_toLinearMap (X : Matrix ν ν K) (hX : X.det ≠ 0) :
    (orbitTransposeEquiv X hX).toLinearMap = Matrix.toLin' X.transpose := rfl

end InvertibleTransport

section ActualOrbitCertificate

variable [Fintype ν] [DecidableEq ν] [Fintype I] [DecidableEq I] [Infinite K]
    {row col : I → ν} (hslots : OrbitPairSlots row col)

/-- The Jacobian hypothesis is about the explicitly defined orbit of these
actual exterior elements.  No dimension or orbit-classification hypothesis
is present.  Concrete odd-pencil Jacobian calculations instantiate it. -/
theorem actualOrbit_principal_hilbert_certificate (f g : ⋀[K]^2 (ν → K))
    (hJ : (TauCeti.jacobiMatrixAt
      (actualOrbitPolynomials (row := row) (col := col) f g)
      (orbitIdentityPoint (K := K) (ν := ν))).mulVec.Surjective) :
    ∃ Q : MvPolynomial (I ⊕ I) K,
      eval (orbitPairCoefficientPoint (actualOrbitBasePoint (row := row) (col := col) f g)) Q ≠ 0 ∧
      ∀ y : (I ⊕ I) → K, eval y Q ≠ 0 → ∀ d : ℕ,
        Module.finrank K (ExteriorQuotientDegree
          (orbitFormsFromCoordinates (orbitSlotBasis hslots) y).1
          (orbitFormsFromCoordinates (orbitSlotBasis hslots) y).2 d) =
        Module.finrank K (ExteriorQuotientDegree f g d) := by
  let p := actualOrbitPolynomials (row := row) (col := col) f g
  let base := orbitPairCoefficientPoint (actualOrbitBasePoint (row := row) (col := col) f g)
  have hJ' := jacobian_surjective_reindex p orbitIdentityPoint
    (Equiv.boolProdEquivSum I).symm hJ
  have horbit (x : (ν × ν) → K) (hx : eval x (orbitDeterminant (K := K) (ν := ν)) ≠ 0) :
      ∃ e : (ν → K) ≃ₗ[K] (ν → K),
      Submodule.span K
        ({exteriorPower.map 2 e.toLinearMap
            (orbitFormsFromCoordinates (orbitSlotBasis hslots) base).1,
          exteriorPower.map 2 e.toLinearMap
            (orbitFormsFromCoordinates (orbitSlotBasis hslots) base).2} :
              Set (⋀[K]^2 (ν → K))) =
      Submodule.span K
        ({(orbitFormsFromCoordinates (orbitSlotBasis hslots)
            (fun i => eval x (orbitPairPolynomialCoordinates p i))).1,
          (orbitFormsFromCoordinates (orbitSlotBasis hslots)
            (fun i => eval x (orbitPairPolynomialCoordinates p i))).2} :
              Set (⋀[K]^2 (ν → K))) := by
    let X : Matrix ν ν K := Matrix.of fun i j => x (i, j)
    have hX : X.det ≠ 0 := by simpa only [orbitDeterminant_eval] using hx
    refine ⟨orbitTransposeEquiv X hX, ?_⟩
    rw [show orbitFormsFromCoordinates (orbitSlotBasis hslots) base = (f, g) from
      actualOrbitBasePoint_forms hslots f g]
    rw [actualOrbitPolynomials_forms_eval hslots f g x]
    rfl
  obtain ⟨Q, hbase, hQ⟩ :=
    exteriorHilbert_principal_certificate_of_dominant_orbit (orbitSlotBasis hslots)
      (orbitPairPolynomialCoordinates p) orbitIdentityPoint hJ' orbitDeterminant
      orbitDeterminant_ne_zero base horbit
  refine ⟨Q, hbase, ?_⟩
  intro y hy d
  have h := hQ y hy d
  rw [show orbitFormsFromCoordinates (orbitSlotBasis hslots) base = (f, g) from
    actualOrbitBasePoint_forms hslots f g] at h
  exact h

end ActualOrbitCertificate

end PaperVerification.AlternatingForms
