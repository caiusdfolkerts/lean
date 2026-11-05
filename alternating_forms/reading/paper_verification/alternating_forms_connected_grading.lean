module

public import PaperVerification.HomogeneousIdealPieces
public import Mathlib.Algebra.Algebra.Operations

/-!
# Connectedness of the original homogeneous quotient grading

The grading in this file is the image of the ordinary polynomial grading.
Its degree-zero subspace consists precisely of scalar multiples of the unit,
and multiplication adds degrees.  An actual augmentation to the coefficient
field proves that the scalar embedding is injective.  These facts are the
connected-graded hypotheses in the homological definition of a Koszul algebra;
they do not assert anything about Tor or assume a resolution.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K

/-- The degree-zero part of the actual quotient is its scalar subspace. -/
theorem homogeneousQuotient_degree_zero (Q : Ideal P) :
    HomogeneousIdealPieces.piece Q 0=(1 : Submodule K (P⧸Q)) := by
  rw [HomogeneousIdealPieces.piece,homogeneousSubmodule_zero]
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨c,rfl⟩ := Submodule.mem_one.mp hp
    exact Submodule.mem_one.mpr ⟨c,((Ideal.Quotient.mkₐ K Q).commutes c).symm⟩
  · intro hx
    obtain ⟨c,rfl⟩ := Submodule.mem_one.mp hx
    exact ⟨algebraMap K P c,Submodule.mem_one.mpr ⟨c,rfl⟩,
      (Ideal.Quotient.mkₐ K Q).commutes c⟩

/-- Multiplication in the original quotient adds the original Plücker degrees. -/
theorem homogeneousQuotient_mul_mem (Q : Ideal P) (i j : ℕ)
    (x y : P⧸Q)
    (hx : x∈HomogeneousIdealPieces.piece Q i)
    (hy : y∈HomogeneousIdealPieces.piece Q j) :
    x*y∈HomogeneousIdealPieces.piece Q (i+j) := by
  obtain ⟨p,hp,rfl⟩ := hx
  obtain ⟨q,hq,rfl⟩ := hy
  change p.IsHomogeneous i at hp
  change q.IsHomogeneous j at hq
  exact ⟨p*q,hp.mul hq,map_mul (Ideal.Quotient.mkₐ K Q) p q⟩

/-- An actual coefficient-field augmentation makes the scalar embedding
injective, so connectedness is not merely an equality with a zero subspace. -/
theorem augmentedQuotient_scalar_injective (Q : Ideal P) (ε : (P⧸Q) →ₐ[K] K) :
    Function.Injective (algebraMap K (P⧸Q)) := by
  apply Function.LeftInverse.injective (g := ε)
  intro c
  simpa only [Algebra.algebraMap_self,RingHom.id_apply] using ε.commutes c

/-- The ordinary homogeneous quotient grading is connected.  The actual
direct-sum decomposition is constructed by `HomogeneousIdealPieces.grading`;
its piece formula is retained here, alongside the scalar embedding and the
multiplication law. -/
theorem homogeneousQuotient_connected
    (Q : Ideal P) (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K))
    (ε : (P⧸Q) →ₐ[K] K) :
    (∀ r,(HomogeneousIdealPieces.grading Q hQ).piece r=
      HomogeneousIdealPieces.piece Q r) ∧
    HomogeneousIdealPieces.piece Q 0=(1 : Submodule K (P⧸Q)) ∧
    Function.Injective (algebraMap K (P⧸Q)) ∧
    (∀ i j (x y : P⧸Q),
      x∈HomogeneousIdealPieces.piece Q i →
      y∈HomogeneousIdealPieces.piece Q j →
      x*y∈HomogeneousIdealPieces.piece Q (i+j)) :=
  ⟨HomogeneousIdealPieces.grading_piece Q hQ,
    homogeneousQuotient_degree_zero Q,
    augmentedQuotient_scalar_injective Q ε,
    homogeneousQuotient_mul_mem Q⟩

end PaperVerification.AlternatingForms
