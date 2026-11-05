module

public import PaperVerification.PowerComplex
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Change of coefficient ring for the actual power-tail complex

The recurrence correction uses the literal remainder modulo the monic
characteristic polynomial. Its coefficients, including their homogeneous
projections, commute with every coefficient-ring homomorphism. Thus the two
maps of the deformation complex really have polynomial coefficients in the
parameters; this property is proved here rather than assumed at specialization.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

theorem map_coefficient_smul (φ : R →+* S) (r : R) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.map φ (r • p) = φ r • MvPolynomial.map φ p := by
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

theorem map_euler (φ : R →+* S) (i : Fin n) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.map φ (euler i p) = euler i (MvPolynomial.map φ p) := by
  simp only [euler_apply, map_mul, MvPolynomial.map_X, pderiv_map]

theorem map_component (φ : R →+* S) (c lam : R) (i : Fin n) (k : ℕ)
    (p : MvPolynomial (Fin n) R) :
    MvPolynomial.map φ (component c lam i k p) =
      component (φ c) (φ lam) i k (MvPolynomial.map φ p) := by
  simp only [component_apply, map_mul, map_add, map_pow, MvPolynomial.map_X,
    map_coefficient_smul, map_euler, map_natCast]

theorem map_reversed (φ : R →+* S) (c : Fin n → R) (lam : R) (k : ℕ)
    (p : MvPolynomial (Fin n) R) :
    MvPolynomial.map φ (reversed c lam k p) =
      reversed (fun i => φ (c i)) (φ lam) k (MvPolynomial.map φ p) := by
  simp only [reversed_apply, map_sum, map_component]

theorem map_tailCoefficient (φ : R →+* S) (k : ℕ) (j : Fin n) :
    MvPolynomial.map φ (tailCoefficient (K := R) k j) =
      tailCoefficient (K := S) k j := by
  have hchar :
      (Fermion.parameterPolynomial (fun i : Fin n => (X i : MvPolynomial (Fin n) R))).map
          (MvPolynomial.map φ) =
        Fermion.parameterPolynomial (fun i : Fin n => (X i : MvPolynomial (Fin n) S)) := by
    simp only [Fermion.parameterPolynomial, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, MvPolynomial.map_X]
  unfold tailCoefficient
  rw [← Polynomial.coeff_map,
    Polynomial.map_modByMonic (MvPolynomial.map φ) (Fermion.parameterPolynomial_monic _),
    Polynomial.map_pow, Polynomial.map_X, hchar]

theorem map_homogeneousComponent (φ : R →+* S) (d : ℕ)
    (p : MvPolynomial (Fin n) R) :
    MvPolynomial.map φ (homogeneousComponent d p) =
      homogeneousComponent d (MvPolynomial.map φ p) := by
  ext a
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp only [map_zero]

theorem map_homogeneousTailCoefficient (φ : R →+* S) (k : ℕ) (j : Fin n) :
    MvPolynomial.map φ (homogeneousTailCoefficient (R := R) k j) =
      homogeneousTailCoefficient (R := S) k j := by
  unfold homogeneousTailCoefficient
  split_ifs
  · rw [map_homogeneousComponent, map_tailCoefficient]
  · exact map_zero _

theorem map_recurrenceVector (φ : R →+* S) (m : ℕ) (i j l : Fin n)
    (p : MvPolynomial (Fin n) R) :
    MvPolynomial.map φ (recurrenceVector m i j p l) =
      recurrenceVector m i j (MvPolynomial.map φ p) l := by
  simp only [recurrenceVector_apply, map_mul, map_homogeneousTailCoefficient]

theorem map_elementarySyzygy (φ : R →+* S) (c : Fin n → R) (lam : R) (m : ℕ)
    (i j l : Fin n) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.map φ (elementarySyzygy c lam m i j p l) =
      elementarySyzygy (fun a => φ (c a)) (φ lam) m i j (MvPolynomial.map φ p) l := by
  classical
  simp only [elementarySyzygy_apply, Pi.sub_apply, Pi.smul_apply, map_sub,
    map_coefficient_smul, map_recurrenceVector, map_mul, map_natCast, Pi.single_apply]
  split_ifs <;> simp only [map_reversed, map_zero]

theorem map_tailMap (φ : R →+* S) (c : Fin n → R) (lam : R) (m : ℕ)
    (v : Fin n → MvPolynomial (Fin n) R) :
    MvPolynomial.map φ (tailMap c lam m v) =
      tailMap (fun i => φ (c i)) (φ lam) m (fun i => MvPolynomial.map φ (v i)) := by
  simp only [tailMap_apply, map_sum, map_reversed]

theorem map_syzygyMap (φ : R →+* S) (c : Fin n → R) (lam : R) (m : ℕ)
    (A : Fin n → Fin n → MvPolynomial (Fin n) R) (l : Fin n) :
    MvPolynomial.map φ (syzygyMap c lam m A l) =
      syzygyMap (fun i => φ (c i)) (φ lam) m
        (fun i j => MvPolynomial.map φ (A i j)) l := by
  simp only [syzygyMap_apply, Finset.sum_apply, map_sum, map_elementarySyzygy]

end PaperVerification.PowerOperators
