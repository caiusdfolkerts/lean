module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# A faithful successive-indeterminate field for Newton deletion

The inductive determinant calculation treats the first variable as a fresh
indeterminate over the rational field of the suffix. The map from the
original multivariate polynomial ring is proved injective at every stage,
so nonvanishing in this model implies nonvanishing in the original ring.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

universe u

variable (F : Type u) [Field F]

def successiveFieldModel : ℕ → Σ R : Type u, Field R
  | 0 => ⟨F, inferInstance⟩
  | n + 1 =>
      letI : Field (successiveFieldModel n).1 := (successiveFieldModel n).2
      ⟨FractionRing (Polynomial (successiveFieldModel n).1), inferInstance⟩

abbrev SuccessiveField (n : ℕ) : Type u := (successiveFieldModel F n).1

instance successiveField_field (n : ℕ) : Field (SuccessiveField F n) :=
  (successiveFieldModel F n).2

def suffixCoefficientMap (n : ℕ) : SuccessiveField F n →+* SuccessiveField F (n + 1) :=
  algebraMap (SuccessiveField F n) (FractionRing (Polynomial (SuccessiveField F n)))

def newVariablePolynomialMap (n : ℕ) :
    Polynomial (SuccessiveField F n) →+* SuccessiveField F (n + 1) :=
  algebraMap (Polynomial (SuccessiveField F n)) (FractionRing (Polynomial (SuccessiveField F n)))

def newVariable (n : ℕ) : SuccessiveField F (n + 1) :=
  newVariablePolynomialMap F n Polynomial.X

theorem newVariablePolynomialMap_injective (n : ℕ) :
    Function.Injective (newVariablePolynomialMap F n) :=
  IsFractionRing.injective (Polynomial (SuccessiveField F n))
    (FractionRing (Polynomial (SuccessiveField F n)))

@[simp] theorem newVariablePolynomialMap_C (n : ℕ) (a : SuccessiveField F n) :
    newVariablePolynomialMap F n (Polynomial.C a) = suffixCoefficientMap F n a := rfl

theorem newVariable_ne_coefficient (n : ℕ) (a : SuccessiveField F n) :
    newVariable F n ≠ suffixCoefficientMap F n a := by
  intro h
  have he : (Polynomial.X : Polynomial (SuccessiveField F n)) = Polynomial.C a :=
    newVariablePolynomialMap_injective F n h
  exact Polynomial.X_ne_C a he

theorem newVariable_ne_zero (n : ℕ) : newVariable F n ≠ 0 := by
  simpa only [map_zero] using newVariable_ne_coefficient F n 0

def successiveCoordinateMap : (n : ℕ) → MvPolynomial (Fin n) F →+* SuccessiveField F n
  | 0 => (MvPolynomial.isEmptyRingEquiv F (Fin 0)).toRingHom
  | n + 1 => (newVariablePolynomialMap F n).comp
      ((Polynomial.mapRingHom (successiveCoordinateMap n)).comp
        (MvPolynomial.finSuccEquiv F n).toRingEquiv.toRingHom)

theorem successiveCoordinateMap_injective (n : ℕ) :
    Function.Injective (successiveCoordinateMap F n) := by
  induction n with
  | zero => exact (MvPolynomial.isEmptyRingEquiv F (Fin 0)).injective
  | succ n ih =>
      exact (newVariablePolynomialMap_injective F n).comp
        ((Polynomial.map_injective _ ih).comp (MvPolynomial.finSuccEquiv F n).injective)

def successiveBaseMap (n : ℕ) : F →+* SuccessiveField F n :=
  (successiveCoordinateMap F n).comp MvPolynomial.C

def successiveNode (n : ℕ) (i : Fin n) : SuccessiveField F n :=
  successiveCoordinateMap F n (MvPolynomial.X i)

@[simp] theorem successiveCoordinateMap_C (n : ℕ) (a : F) :
    successiveCoordinateMap F n (MvPolynomial.C a) = successiveBaseMap F n a := rfl

@[simp] theorem successiveCoordinateMap_X (n : ℕ) (i : Fin n) :
    successiveCoordinateMap F n (MvPolynomial.X i) = successiveNode F n i := rfl

@[simp] theorem successiveBaseMap_succ (n : ℕ) (a : F) :
    successiveBaseMap F (n + 1) a = suffixCoefficientMap F n (successiveBaseMap F n a) := by
  change newVariablePolynomialMap F n
    (Polynomial.map (successiveCoordinateMap F n)
      (MvPolynomial.finSuccEquiv F n (MvPolynomial.C a))) = _
  have hc : MvPolynomial.finSuccEquiv F n (MvPolynomial.C a) =
      Polynomial.C (MvPolynomial.C a) := by simp [MvPolynomial.finSuccEquiv_apply]
  rw [hc, Polynomial.map_C, newVariablePolynomialMap_C]
  rfl

@[simp] theorem successiveNode_zero (n : ℕ) :
    successiveNode F (n + 1) 0 = newVariable F n := by
  change newVariablePolynomialMap F n
    (Polynomial.map (successiveCoordinateMap F n)
      (MvPolynomial.finSuccEquiv F n (MvPolynomial.X 0))) = _
  rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]
  rfl

@[simp] theorem successiveNode_succ (n : ℕ) (i : Fin n) :
    successiveNode F (n + 1) i.succ = suffixCoefficientMap F n (successiveNode F n i) := by
  change newVariablePolynomialMap F n
    (Polynomial.map (successiveCoordinateMap F n)
      (MvPolynomial.finSuccEquiv F n (MvPolynomial.X i.succ))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C, newVariablePolynomialMap_C]
  rfl

theorem successiveNode_injective (n : ℕ) : Function.Injective (successiveNode F n) := by
  intro i j h
  exact MvPolynomial.X_injective (successiveCoordinateMap_injective F n h)

theorem successiveNode_ne_zero (n : ℕ) (i : Fin n) : successiveNode F n i ≠ 0 := by
  intro h
  apply MvPolynomial.X_ne_zero (R := F) i
  apply successiveCoordinateMap_injective F n
  simpa only [map_zero,successiveCoordinateMap_X] using h

end PaperVerification.Fermion.Newton
