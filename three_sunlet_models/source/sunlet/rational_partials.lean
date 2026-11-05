module

public import sunlet.etale_derivations
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Coordinate derivations and the chain rule in a rational function field.
These are constructed from polynomial derivations and étale localization. -/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace Sunlet.RationalPartials

variable {k ι : Type*} [Field k] [DecidableEq ι]

abbrev PolynomialRing (k ι : Type*) [Field k] := MvPolynomial ι k
abbrev FunctionField (k ι : Type*) [Field k] := FractionRing (PolynomialRing k ι)

instance : Algebra.FormallyEtale (PolynomialRing k ι) (FunctionField k ι) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (PolynomialRing k ι))

def coordinateVariable (i : ι) : FunctionField k ι :=
  algebraMap (PolynomialRing k ι) (FunctionField k ι) (MvPolynomial.X i)

def partialDerivative (i : ι) : Derivation k (FunctionField k ι) (FunctionField k ι) :=
  EtaleDerivations.extend (T := FunctionField k ι)
    (MvPolynomial.mkDerivation k (fun j => if j = i then 1 else 0))

@[simp] theorem partial_variable (i j : ι) :
    partialDerivative (k := k) i (coordinateVariable j) = if j = i then 1 else 0 := by
  simp [partialDerivative, coordinateVariable]

variable {A : Type*} [CommRing A] [Algebra k A] [Algebra (FunctionField k ι) A]
  [Algebra (PolynomialRing k ι) A]
  [IsScalarTower k (FunctionField k ι) A]
  [IsScalarTower k (PolynomialRing k ι) A]
  [IsScalarTower (PolynomialRing k ι) (FunctionField k ι) A]

/-- A derivation of a rational function field is determined by its coordinate
values. No differential-field constant hypothesis is assumed. -/
theorem ext {D E : Derivation k (FunctionField k ι) A}
    (h : ∀ i, D (coordinateVariable i) = E (coordinateVariable i)) : D = E := by
  apply EtaleDerivations.ext (S := PolynomialRing k ι)
  have hp : D.compAlgebraMap (PolynomialRing k ι) = E.compAlgebraMap (PolynomialRing k ι) := by
    apply MvPolynomial.derivation_ext
    intro i
    exact h i
  intro p
  exact congrArg (fun f : Derivation k (PolynomialRing k ι) A => f p) hp

def partialTo (i : ι) : Derivation k (FunctionField k ι) A :=
  (Algebra.linearMap (FunctionField k ι) A).compDer (partialDerivative i)

@[simp] theorem partialTo_variable (i j : ι) :
    partialTo (k := k) (A := A) i (coordinateVariable j) = if j = i then 1 else 0 := by
  change algebraMap (FunctionField k ι) A (partialDerivative i (coordinateVariable j)) = _
  rw [partial_variable]
  split_ifs <;> simp

variable [Fintype ι]

/-- The exact chain rule in the rational function field. -/
theorem chain_rule (D : Derivation k (FunctionField k ι) A) (f : FunctionField k ι) :
    D f = ∑ i, D (coordinateVariable i) * algebraMap (FunctionField k ι) A (partialDerivative i f) := by
  have he : D = ∑ i, D (coordinateVariable i) • partialTo (k := k) (A := A) i := by
    apply ext
    intro j
    simp [partialTo_variable]
  have hh := congrArg (fun d : Derivation k (FunctionField k ι) A => d f) he
  simpa [partialTo, Algebra.smul_def] using hh

end Sunlet.RationalPartials
