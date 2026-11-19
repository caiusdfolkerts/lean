module

public import PaperVerification.AlternatingFormsOrbitCoefficientTransport

/-!
# The concrete odd pencil and its actual generic Hilbert function

The two exterior elements here are literal sums of coordinate wedges.  Their
coefficient matrices are the two incidence matrices used in the explicit
Jacobian calculation.  The resulting nonempty principal open therefore
concerns the quotient by these actual exterior elements, in every degree.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped BigOperators Classical
open MvPolynomial

variable {K : Type*} [Field K]

/-- The literal quadratic exterior element of a bipartite incidence map. -/
def orbitIncidenceForm {a b : ℕ} (e : Fin a → Fin b) :
    ⋀[K]^2 ((Fin a ⊕ Fin b) → K) :=
  ∑ i, exteriorPower.ιMulti K 2
    ![Pi.basisFun K (Fin a ⊕ Fin b) (Sum.inl i),
      Pi.basisFun K (Fin a ⊕ Fin b) (Sum.inr (e i))]

theorem orbitIncidenceForm_coefficientMatrix {a b : ℕ} (e : Fin a → Fin b) :
    orbitExteriorCoefficientMatrix (orbitIncidenceForm (K := K) e) =
      orbitSkewIncidence e := by
  ext u v
  rcases u with i | i <;> rcases v with j | j <;>
    simp [orbitIncidenceForm, orbitExteriorCoefficientMatrix,
      orbitExteriorCoefficient_word, Pi.basisFun_apply, Pi.single_apply,
      orbitSkewIncidence, orbitIncidence, Finset.sum_neg_distrib, eq_comm]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro x _ hxi
      simp [Ne.symm hxi]
    · simp
  · rw [Finset.sum_eq_single j]
    · simp
    · intro x _ hxj
      simp [Ne.symm hxj]
    · simp

def oddOrbitFirstForm (t : ℕ) : ⋀[K]^2 (OddOrbitMode t → K) :=
  orbitIncidenceForm (Fin.succ : Fin (t + 1) → Fin (t + 2))

def oddOrbitSecondForm (t : ℕ) : ⋀[K]^2 (OddOrbitMode t → K) :=
  orbitIncidenceForm (Fin.castSucc : Fin (t + 1) → Fin (t + 2))

theorem oddOrbitFirstForm_coefficientMatrix (t : ℕ) :
    orbitExteriorCoefficientMatrix (oddOrbitFirstForm (K := K) t) =
      orbitSkewIncidence Fin.succ :=
  orbitIncidenceForm_coefficientMatrix _

theorem oddOrbitSecondForm_coefficientMatrix (t : ℕ) :
    orbitExteriorCoefficientMatrix (oddOrbitSecondForm (K := K) t) =
      orbitSkewIncidence Fin.castSucc :=
  orbitIncidenceForm_coefficientMatrix _

theorem oddOrbit_actual_polynomials (t : ℕ) :
    actualOrbitPolynomials (row := oddOrbitSlotRow t) (col := oddOrbitSlotCol t)
      (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm (K := K) t) =
      oddOrbitPolynomials t := by
  simp only [actualOrbitPolynomials, oddOrbitFirstForm_coefficientMatrix,
    oddOrbitSecondForm_coefficientMatrix, oddOrbitPolynomials, oddOrbitMatrices]
  rfl

theorem oddOrbit_actual_jacobian_surjective (t : ℕ) :
    (TauCeti.jacobiMatrixAt
      (actualOrbitPolynomials (row := oddOrbitSlotRow t) (col := oddOrbitSlotCol t)
        (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm (K := K) t))
      orbitIdentityPoint).mulVec.Surjective := by
  rw [oddOrbit_actual_polynomials]
  exact oddOrbit_jacobian_surjective t

/-- A nonempty principal open in the full space of pairs of exterior forms
has the complete Hilbert function of the explicit odd path pencil.  The
formula for that Hilbert function is supplied by the actual good basis. -/
theorem oddOrbit_actual_hilbert_certificate [Infinite K] (t : ℕ) :
    ∃ Q : MvPolynomial (OddOrbitSlot t ⊕ OddOrbitSlot t) K,
      eval (orbitPairCoefficientPoint
        (actualOrbitBasePoint (row := oddOrbitSlotRow t) (col := oddOrbitSlotCol t)
          (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm (K := K) t))) Q ≠ 0 ∧
      ∀ y : (OddOrbitSlot t ⊕ OddOrbitSlot t) → K, eval y Q ≠ 0 → ∀ d : ℕ,
        Module.finrank K (ExteriorQuotientDegree
          (orbitFormsFromCoordinates (oddOrbitExteriorBasis (K := K) t) y).1
          (orbitFormsFromCoordinates (oddOrbitExteriorBasis (K := K) t) y).2 d) =
        Module.finrank K (ExteriorQuotientDegree
          (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm (K := K) t) d) :=
  actualOrbit_principal_hilbert_certificate (oddOrbitPairSlots t)
    (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm (K := K) t) (oddOrbit_actual_jacobian_surjective t)

end PaperVerification.AlternatingForms
