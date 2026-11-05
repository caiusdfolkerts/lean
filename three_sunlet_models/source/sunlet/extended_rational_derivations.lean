module

public import sunlet.contact_development
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Perfect

/-!
# Actual derivation extensions to separable parameter-field extensions

The extensions below are constructed through the formally étale Kähler
equivalence. In particular, the canonical parameter embedding has a full
family of coordinate derivations; their existence is not an extra premise
of the tangent-range comparison theorem.
-/

@[expose] public section
noncomputable section

namespace Sunlet.ExtendedRationalDerivations

section Separable

variable {k E A : Type*} [Field k] [Field E] [Field A]
  [Algebra k E] [Algebra k A] [Algebra E A] [IsScalarTower k E A]
  [Algebra.IsSeparable E A]

/-- Extend an actual derivation through a separable field extension. -/
def extendTo (D : Derivation k E A) : Derivation k A A := by
  letI : Algebra.FormallyEtale E A := Algebra.FormallyEtale.of_isSeparable E A
  exact EtaleDerivations.extend (R := k) (S := E) (T := A) (M := A) D

@[simp] theorem extendTo_algebraMap (D : Derivation k E A) (x : E) :
    extendTo D (algebraMap E A x) = D x := by
  letI : Algebra.FormallyEtale E A := Algebra.FormallyEtale.of_isSeparable E A
  exact EtaleDerivations.extend_algebraMap (T := A) D x

/-- First map the values of a derivation into the extension field, then
extend its domain through the separable extension. -/
def extendEndomorphism (D : Derivation k E E) : Derivation k A A :=
  extendTo ((Algebra.linearMap E A).compDer D)

@[simp] theorem extendEndomorphism_algebraMap (D : Derivation k E E) (x : E) :
    extendEndomorphism (A := A) D (algebraMap E A x) = algebraMap E A (D x) := by
  change extendTo ((Algebra.linearMap E A).compDer D) (algebraMap E A x) = _
  rw [extendTo_algebraMap]
  rfl

end Separable

section Rational

open RationalPartials

variable {k J A : Type*} [Field k] [DecidableEq J] [Field A]
  [Algebra k A] [Algebra (FunctionField k J) A]
  [IsScalarTower k (FunctionField k J) A]
  [Algebra.IsSeparable (FunctionField k J) A]

/-- The canonical parameter-field embedding with its specified scalar tower. -/
def canonicalEmbedding : FunctionField k J →ₐ[k] A :=
  IsScalarTower.toAlgHom k (FunctionField k J) A

/-- The genuine extended coordinate derivation. -/
def coordinatePartial (i : J) : Derivation k A A :=
  extendTo (partialTo (k := k) (A := A) i)

@[simp] theorem partial_algebraMap_variable (i j : J) :
    coordinatePartial (k := k) (A := A) i
        (algebraMap (FunctionField k J) A (coordinateVariable j)) =
      if j = i then 1 else 0 := by
  change extendTo (partialTo (k := k) (A := A) i)
    (algebraMap (FunctionField k J) A (coordinateVariable j)) = _
  rw [extendTo_algebraMap]
  change algebraMap (FunctionField k J) A
    (partialDerivative i (coordinateVariable j)) = _
  rw [partial_variable]
  split_ifs <;> simp

@[simp] theorem partial_canonical_variable (i j : J) :
    coordinatePartial (k := k) (A := A) i
        (canonicalEmbedding (k := k) (J := J) (A := A) (coordinateVariable j)) =
      if j = i then 1 else 0 :=
  partial_algebraMap_variable i j

/-- The canonical embedding supplies the coordinate derivations required
by the checked tangent comparison. No derivation-existence hypothesis
remains in this statement. -/
theorem tangent_range_eq_of_canonical_coordinate_eq
    [Fintype J] {O : Type*} [Fintype O]
    (ψ : FunctionField k J →ₐ[k] A) (q : O → FunctionField k J)
    (hcoord : ∀ o, canonicalEmbedding (k := k) (J := J) (A := A) (q o) = ψ (q o))
    (hinj : Function.Injective
      (jacobianAt (canonicalEmbedding (k := k) (J := J) (A := A)) q).mulVecLin) :
    LinearMap.range
        (jacobianAt (canonicalEmbedding (k := k) (J := J) (A := A)) q).mulVecLin =
      LinearMap.range (jacobianAt ψ q).mulVecLin := by
  exact tangent_range_eq_of_coordinate_eq
    (canonicalEmbedding (k := k) (J := J) (A := A)) ψ q
    (coordinatePartial (k := k) (A := A)) (partial_canonical_variable (k := k) (A := A))
    hcoord hinj

end Rational

section ToricEuler

variable {k ι Ω A : Type*} [Field k] [CharZero k]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  [Field A] [Algebra k A] (o : Ω)
  [Algebra (ToricPairAlgebra.FunctionField (k := k) (ι := ι) o) A]
  [IsScalarTower k (ToricPairAlgebra.FunctionField (k := k) (ι := ι) o) A]
  [Algebra.IsSeparable (ToricPairAlgebra.FunctionField (k := k) (ι := ι) o) A]

/-- Extend the literal first-family Euler derivation of the toric pair. -/
def toricEuler : Derivation k A A :=
  extendEndomorphism (k := k) (E := ToricPairAlgebra.FunctionField (k := k) (ι := ι) o) (A := A) (ToricPairAlgebra.euler (k := k) (ι := ι) o)

@[simp] theorem toricEuler_coefficient (b : Bool) (a : ι) :
    toricEuler (k := k) (A := A) (ι := ι) o
        (algebraMap (ToricPairAlgebra.FunctionField (k := k) (ι := ι) o) A
          (ToricPairAlgebra.genericCoefficient o b a)) =
      if b then 0 else
        algebraMap (ToricPairAlgebra.FunctionField (k := k) (ι := ι) o) A
          (ToricPairAlgebra.genericCoefficient o b a) := by
  change extendEndomorphism (k := k) (E := ToricPairAlgebra.FunctionField (k := k) (ι := ι) o) (A := A) (ToricPairAlgebra.euler (k := k) (ι := ι) o)
    (algebraMap (ToricPairAlgebra.FunctionField (k := k) (ι := ι) o) A _) = _
  rw [extendEndomorphism_algebraMap, ToricPairAlgebra.euler_genericCoefficient]
  cases b <;> simp

@[simp] theorem toricEuler_torus (b : Bool) (x : Ω) :
    toricEuler (k := k) (A := A) (ι := ι) o
        (algebraMap (ToricPairAlgebra.FunctionField (k := k) (ι := ι) o) A
          (ToricPairAlgebra.genericTorus (k := k) (ι := ι) o b x).val) = 0 := by
  change extendEndomorphism (k := k) (E := ToricPairAlgebra.FunctionField (k := k) (ι := ι) o) (A := A) (ToricPairAlgebra.euler (k := k) (ι := ι) o)
    (algebraMap (ToricPairAlgebra.FunctionField (k := k) (ι := ι) o) A _) = 0
  rw [extendEndomorphism_algebraMap, ToricPairAlgebra.euler_genericTorus, map_zero]

end ToricEuler

section AlgebraicClosure

open RationalPartials

variable {k J : Type*} [Field k] [CharZero k] [DecidableEq J]

/-- Characteristic zero makes the actual algebraic closure a separable
extension of the rational function field. All algebra structures here
are Mathlib's canonical ones, with their canonical scalar tower. -/
def algebraicClosurePartial (i : J) :
    Derivation k (AlgebraicClosure (FunctionField k J))
      (AlgebraicClosure (FunctionField k J)) :=
  coordinatePartial (k := k) (A := AlgebraicClosure (FunctionField k J)) i

@[simp] theorem algebraicClosurePartial_variable (i j : J) :
    algebraicClosurePartial (k := k) i
        (algebraMap (FunctionField k J) (AlgebraicClosure (FunctionField k J))
          (coordinateVariable j)) = if j = i then 1 else 0 :=
  partial_algebraMap_variable i j

theorem tangent_range_eq_in_algebraicClosure
    [Fintype J] {O : Type*} [Fintype O]
    (ψ : FunctionField k J →ₐ[k] AlgebraicClosure (FunctionField k J))
    (q : O → FunctionField k J)
    (hcoord : ∀ o,
      algebraMap (FunctionField k J) (AlgebraicClosure (FunctionField k J)) (q o) = ψ (q o))
    (hinj : Function.Injective
      (jacobianAt (canonicalEmbedding (k := k) (J := J)
        (A := AlgebraicClosure (FunctionField k J))) q).mulVecLin) :
    LinearMap.range
        (jacobianAt (canonicalEmbedding (k := k) (J := J)
          (A := AlgebraicClosure (FunctionField k J))) q).mulVecLin =
      LinearMap.range (jacobianAt ψ q).mulVecLin :=
  tangent_range_eq_of_canonical_coordinate_eq ψ q hcoord hinj

end AlgebraicClosure

end Sunlet.ExtendedRationalDerivations
