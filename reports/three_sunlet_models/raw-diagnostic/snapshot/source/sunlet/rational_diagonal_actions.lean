module

public import sunlet.contact_development
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.Algebra.Algebra.Equiv

/-! Actual rational-field automorphisms induced by unit rescalings and
permutations of the independent polynomial parameters. -/

@[expose] public section
noncomputable section

namespace Sunlet.RationalDiagonalActions

open RationalPartials

variable {k J : Type*} [Field k] [DecidableEq J]

def polynomialMap (e : J ≃ J) (w : J → kˣ) :
    PolynomialRing k J →ₐ[k] PolynomialRing k J :=
  MvPolynomial.aeval (fun j => MvPolynomial.C (w j).val * MvPolynomial.X (e j))

@[simp] theorem polynomialMap_X (e : J ≃ J) (w : J → kˣ) (j : J) :
    polynomialMap e w (MvPolynomial.X j) =
      MvPolynomial.C (w j).val * MvPolynomial.X (e j) := by
  simp [polynomialMap]

@[simp] theorem polynomialMap_C (e : J ≃ J) (w : J → kˣ) (a : k) :
    polynomialMap e w (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [polynomialMap]

def polynomialEquiv (e : J ≃ J) (w : J → kˣ) :
    PolynomialRing k J ≃ₐ[k] PolynomialRing k J :=
  AlgEquiv.ofAlgHom (polynomialMap e w)
    (polynomialMap e.symm (fun j => (w (e.symm j))⁻¹))
    (by
      ext j
      simp [mul_assoc, ← MvPolynomial.C_mul])
    (by
      ext j
      simp [mul_assoc, ← MvPolynomial.C_mul])

@[simp] theorem polynomialEquiv_X (e : J ≃ J) (w : J → kˣ) (j : J) :
    polynomialEquiv e w (MvPolynomial.X j) =
      MvPolynomial.C (w j).val * MvPolynomial.X (e j) :=
  polynomialMap_X e w j

def fieldEquiv (e : J ≃ J) (w : J → kˣ) :
    FunctionField k J ≃ₐ[k] FunctionField k J :=
  IsFractionRing.algEquivOfAlgEquiv (polynomialEquiv e w)

@[simp] theorem fieldEquiv_variable (e : J ≃ J) (w : J → kˣ) (j : J) :
    fieldEquiv e w (coordinateVariable j) =
      algebraMap k (FunctionField k J) (w j).val * coordinateVariable (e j) := by
  rw [fieldEquiv, coordinateVariable, IsFractionRing.algEquivOfAlgEquiv_algebraMap,
    polynomialEquiv_X, map_mul]
  congr 1

theorem algHom_ext_variables {A : Type*} [Field A] [Algebra k A]
    {φ ψ : FunctionField k J →ₐ[k] A}
    (h : ∀ j, φ (coordinateVariable j) = ψ (coordinateVariable j)) : φ = ψ := by
  apply IsLocalization.algHom_ext (nonZeroDivisors (PolynomialRing k J))
  ext j
  exact h j

theorem algEquiv_ext_variables {φ ψ : FunctionField k J ≃ₐ[k] FunctionField k J}
    (h : ∀ j, φ (coordinateVariable j) = ψ (coordinateVariable j)) : φ = ψ := by
  have hh : φ.toAlgHom = ψ.toAlgHom := algHom_ext_variables h
  ext x
  exact congrArg (fun q : FunctionField k J →ₐ[k] FunctionField k J => q x) hh

@[simp] theorem fieldEquiv_one :
    fieldEquiv (Equiv.refl J) (fun _ => (1 : kˣ)) =
      AlgEquiv.refl (R := k) (A₁ := FunctionField k J) := by
  apply algEquiv_ext_variables
  intro j
  simp

theorem fieldEquiv_mul (e f : J ≃ J) (w v : J → kˣ) :
    fieldEquiv e w * fieldEquiv f v =
      fieldEquiv (f.trans e) (fun j => v j * w (f j)) := by
  apply algEquiv_ext_variables
  intro j
  simp [mul_assoc]

end Sunlet.RationalDiagonalActions

namespace Sunlet.GeneratedFieldActions

variable {k E O : Type*} [Field k] [Field E] [Algebra k E]

theorem fixes_adjoin (q : O → E) (σ : E ≃ₐ[k] E)
    (hσ : ∀ i, σ (q i) = q i) (x : IntermediateField.adjoin k (Set.range q)) :
    σ x.val = x.val := by
  refine IntermediateField.adjoin_induction k (motive := fun x _ => σ x = x)
    ?_ ?_ ?_ ?_ ?_ x.property
  · rintro _ ⟨i, rfl⟩
    exact hσ i
  · intro a
    exact σ.commutes a
  · intro x y _ _ hx hy
    simp [hx, hy]
  · intro x _ hx
    simp [hx]
  · intro x y _ _ hx hy
    simp [hx, hy]

/-- An actual base-field automorphism fixing all displayed generators
is an automorphism over their generated intermediate field. -/
def overGenerated (q : O → E) (σ : E ≃ₐ[k] E)
    (hσ : ∀ i, σ (q i) = q i) :
    E ≃ₐ[IntermediateField.adjoin k (Set.range q)] E where
  __ := σ.toRingEquiv
  commutes' x := fixes_adjoin q σ hσ x

@[simp] theorem overGenerated_apply (q : O → E) (σ : E ≃ₐ[k] E)
    (hσ : ∀ i, σ (q i) = q i) (x : E) : overGenerated q σ hσ x = σ x := rfl

end Sunlet.GeneratedFieldActions
