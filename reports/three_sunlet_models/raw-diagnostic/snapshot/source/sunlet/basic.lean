module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# The five-family sunlet polynomial map

The parameter space is the full affine space, including parameters equal to
zero.  The coordinate polynomials below are the literal polynomials of the
normalized Latin-system model; no image or dimension assertion is built into
their definition.
-/

@[expose] public section
noncomputable section

namespace Sunlet

/-- The five independent families of affine parameter variables. -/
inductive ParamVar (ι Ω : Type*) where
  | s : Ω → ParamVar ι Ω
  | t : Ω → ParamVar ι Ω
  | h : Ω → ParamVar ι Ω
  | u : ι → ParamVar ι Ω
  | v : ι → ParamVar ι Ω
  deriving DecidableEq, Fintype

/-- An arbitrary point of the full parameter space. -/
structure Parameters (K ι Ω : Type*) where
  s : Ω → K
  t : Ω → K
  h : Ω → K
  u : ι → K
  v : ι → K

namespace Parameters

variable {K ι Ω : Type*}

def toCoordinates (p : Parameters K ι Ω) : ParamVar ι Ω → K
  | .s b => p.s b
  | .t b => p.t b
  | .h b => p.h b
  | .u a => p.u a
  | .v a => p.v a

def ofCoordinates (x : ParamVar ι Ω → K) : Parameters K ι Ω where
  s b := x (.s b)
  t b := x (.t b)
  h b := x (.h b)
  u a := x (.u a)
  v a := x (.v a)

@[simp] theorem ofCoordinates_toCoordinates (p : Parameters K ι Ω) :
    ofCoordinates p.toCoordinates = p := by
  cases p
  rfl

@[simp] theorem toCoordinates_ofCoordinates (x : ParamVar ι Ω → K) :
    (ofCoordinates x).toCoordinates = x := by
  funext i
  cases i <;> rfl

/-- The record parameter space is exactly the corresponding affine space. -/
def coordinatesEquiv : Parameters K ι Ω ≃ (ParamVar ι Ω → K) where
  toFun := toCoordinates
  invFun := ofCoordinates
  left_inv := ofCoordinates_toCoordinates
  right_inv := toCoordinates_ofCoordinates

end Parameters

section PolynomialMap

variable {K ι Ω : Type*} [CommSemiring K]

/-- The coordinate with color `a` and position `b`. -/
def coordinate (π : ι → Equiv.Perm Ω) (p : Parameters K ι Ω) (a : ι) (b : Ω) : K :=
  p.s b * p.t (π a b) * (p.u a * p.h (π a b) + p.v a * p.h b)

/-- The literal five-family map on the entire affine parameter space. -/
def parameterMap (π : ι → Equiv.Perm Ω) (p : Parameters K ι Ω) (ab : ι × Ω) : K :=
  coordinate π p ab.1 ab.2

/-- The coordinate map as a family of multivariate polynomials. -/
def coordinatePolynomial (π : ι → Equiv.Perm Ω) (ab : ι × Ω) :
    MvPolynomial (ParamVar ι Ω) K :=
  MvPolynomial.X (.s ab.2) * MvPolynomial.X (.t (π ab.1 ab.2)) *
    (MvPolynomial.X (.u ab.1) * MvPolynomial.X (.h (π ab.1 ab.2)) +
      MvPolynomial.X (.v ab.1) * MvPolynomial.X (.h ab.2))

@[simp] theorem aeval_coordinatePolynomial (π : ι → Equiv.Perm Ω)
    (p : Parameters K ι Ω) (ab : ι × Ω) :
    MvPolynomial.aeval p.toCoordinates (coordinatePolynomial (K := K) π ab) =
      parameterMap π p ab := by
  simp [coordinatePolynomial, parameterMap, coordinate, Parameters.toCoordinates]

@[simp] theorem aeval_coordinatePolynomial_ofCoordinates (π : ι → Equiv.Perm Ω)
    (x : ParamVar ι Ω → K) (ab : ι × Ω) :
    MvPolynomial.aeval x (coordinatePolynomial (K := K) π ab) =
      parameterMap π (Parameters.ofCoordinates x) ab := by
  simpa using aeval_coordinatePolynomial π (Parameters.ofCoordinates x) ab

/-- The same coordinate identity after extending the coefficient algebra. -/
@[simp] theorem aeval_coordinatePolynomial_algebra {A : Type*}
    [CommSemiring A] [Algebra K A] (π : ι → Equiv.Perm Ω)
    (p : Parameters A ι Ω) (ab : ι × Ω) :
    MvPolynomial.aeval p.toCoordinates (coordinatePolynomial (K := K) π ab) =
      parameterMap π p ab := by
  simp [coordinatePolynomial, parameterMap, coordinate, Parameters.toCoordinates]

end PolynomialMap

end Sunlet
