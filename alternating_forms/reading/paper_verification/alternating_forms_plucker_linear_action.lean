module

public import PaperVerification.AlternatingFormsLinearPresentation
public import PaperVerification.AlternatingFormsExteriorTransport

/-!
# Linear changes of the actual Plücker coordinates

The coordinate substitution is induced by the ordinary exterior power of a
linear map.  Its compatibility with maximal minors is proved over every
commutative coefficient algebra.  In particular it preserves the universal
Grassmannian ideal, with its complete scheme structure.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial Matrix
open scoped BigOperators

variable {K : Type*} [Field K] {s n : ℕ}

/-- The literal substitution on Plücker variables induced by an exterior power. -/
def pluckerLinearAction (e : (Fin n → K) →ₗ[K] (Fin n → K)) (s : ℕ) :
    MvPolynomial (PluckerIndex s n) K →ₐ[K] MvPolynomial (PluckerIndex s n) K :=
  aeval fun I => exteriorPluckerCoordinates s n
    (exteriorPower.map s e (exteriorPluckerBasis s n I))

@[simp] theorem pluckerLinearAction_X
    (e : (Fin n → K) →ₗ[K] (Fin n → K)) (I : PluckerIndex s n) :
    pluckerLinearAction e s (X I) = exteriorPluckerCoordinates s n
      (exteriorPower.map s e (exteriorPluckerBasis s n I)) := by
  simp only [pluckerLinearAction, aeval_X]

/-- The substitution acts on every exterior vector by the intended exterior map. -/
theorem pluckerLinearAction_coordinates
    (e : (Fin n → K) →ₗ[K] (Fin n → K)) (x : ⋀[K]^s (Fin n → K)) :
    pluckerLinearAction e s (exteriorPluckerCoordinates s n x) =
      exteriorPluckerCoordinates s n (exteriorPower.map s e x) := by
  have h : (pluckerLinearAction e s).toLinearMap.comp
      (exteriorPluckerCoordinates s n) =
      (exteriorPluckerCoordinates s n).comp (exteriorPower.map s e) := by
    apply (exteriorPluckerBasis s n).ext
    intro I
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      exteriorPluckerCoordinates_basis, pluckerLinearAction_X]
  exact congrArg (fun f => f x) h

theorem pluckerLinearAction_comp
    (e f : (Fin n → K) →ₗ[K] (Fin n → K)) (s : ℕ) :
    (pluckerLinearAction e s).comp (pluckerLinearAction f s) =
      pluckerLinearAction (e.comp f) s := by
  apply MvPolynomial.algHom_ext
  intro I
  simp only [AlgHom.comp_apply, pluckerLinearAction_X,
    pluckerLinearAction_coordinates, exteriorPower.map_comp, LinearMap.comp_apply]

@[simp] theorem pluckerLinearAction_id (s : ℕ) :
    pluckerLinearAction (LinearMap.id : (Fin n → K) →ₗ[K] (Fin n → K)) s =
      AlgHom.id K (MvPolynomial (PluckerIndex s n) K) := by
  apply MvPolynomial.algHom_ext
  intro I
  simp only [pluckerLinearAction_X, exteriorPower.map_id, LinearMap.id_apply,
    exteriorPluckerCoordinates_basis, AlgHom.id_apply]

/-- Invertible linear changes give invertible substitutions on the full polynomial ring. -/
def pluckerLinearEquiv (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) (s : ℕ) :
    MvPolynomial (PluckerIndex s n) K ≃ₐ[K] MvPolynomial (PluckerIndex s n) K :=
  AlgEquiv.ofAlgHom (pluckerLinearAction e.toLinearMap s)
    (pluckerLinearAction e.symm.toLinearMap s)
    (by rw [pluckerLinearAction_comp, e.comp_symm, pluckerLinearAction_id])
    (by rw [pluckerLinearAction_comp, e.symm_comp, pluckerLinearAction_id])

/-- Evaluation of a covector against a row of an arbitrary coefficient matrix. -/
def matrixCovectorEvaluation {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin s) (Fin n) R) : (Fin n → K) →ₗ[K] (Fin s → R) where
  toFun v i := ∑ j, (v j) • A i j
  map_add' v w := by
    ext i
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

@[simp] theorem matrixCovectorEvaluation_basis {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin s) (Fin n) R) (j : Fin n) :
    matrixCovectorEvaluation A (Pi.basisFun K (Fin n) j) = fun i => A i j := by
  ext i
  simp [matrixCovectorEvaluation, Pi.basisFun_apply, Pi.single_apply]

/-- Determinants of evaluated covectors, regarded as a K-alternating map. -/
def matrixCovectorDeterminant {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin s) (Fin n) R) : (Fin n → K) [⋀^Fin s]→ₗ[K] R where
  toMultilinearMap :=
    ((Matrix.detRowAlternating : (Fin s → R) [⋀^Fin s]→ₗ[R] R).toMultilinearMap.restrictScalars K).compLinearMap
      (fun _ => matrixCovectorEvaluation A)
  map_eq_zero_of_eq' := by
    intro v i j hv hij
    exact (Matrix.detRowAlternating : (Fin s → R) [⋀^Fin s]→ₗ[R] R).map_eq_zero_of_eq
      (fun k => matrixCovectorEvaluation A (v k)) (congrArg (matrixCovectorEvaluation A) hv) hij

/-- Universal minor evaluation agrees with the determinant of arbitrary covectors. -/
theorem matrixMinorEvaluation_exterior_word
    {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin s) (Fin n) R) (v : Fin s → (Fin n → K)) :
    matrixMinorEvaluation A (exteriorPluckerCoordinates s n (exteriorPower.ιMulti K s v)) =
      Matrix.det (fun i j => ∑ l, v j l • A i l) := by
  let f := ((matrixMinorEvaluation (K := K) A).toLinearMap.comp
    (exteriorPluckerCoordinates s n)).compAlternatingMap (exteriorPower.ιMulti K s)
  have h : f = matrixCovectorDeterminant A := by
    apply (Pi.basisFun K (Fin n)).ext_alternating
    intro I hI
    change matrixMinorEvaluation A
      (exteriorPluckerCoordinates s n
        (exteriorPower.ιMulti K s (fun i => Pi.basisFun K (Fin n) (I i)))) = _
    rw [exteriorPluckerCoordinates_word, matrixMinorEvaluation_orderedCoordinate]
    change Matrix.det (fun i j => A i (I j)) =
      Matrix.det (fun j => matrixCovectorEvaluation A (Pi.basisFun K (Fin n) (I j)))
    simp only [matrixCovectorEvaluation_basis]
    exact Matrix.det_transpose _ |>.symm
  have hv := congrArg (fun a => a v) h
  change matrixMinorEvaluation A
    (exteriorPluckerCoordinates s n (exteriorPower.ιMulti K s v)) =
    Matrix.det (fun j i => ∑ l, v j l • A i l) at hv
  rw [hv]
  exact Matrix.det_transpose _

/-- The transformed row matrix has exactly the pullback entries under the linear map. -/
def matrixLinearChange {R : Type*} [CommRing R] [Algebra K R]
    (e : (Fin n → K) →ₗ[K] (Fin n → K)) (A : Matrix (Fin s) (Fin n) R) :
    Matrix (Fin s) (Fin n) R :=
  fun i j => ∑ l, (e (Pi.basisFun K (Fin n) j) l) • A i l

theorem matrixMinorEvaluation_pluckerLinearAction
    {R : Type*} [CommRing R] [Algebra K R]
    (e : (Fin n → K) →ₗ[K] (Fin n → K)) (A : Matrix (Fin s) (Fin n) R) :
    (matrixMinorEvaluation A).comp (pluckerLinearAction e s) =
      matrixMinorEvaluation (matrixLinearChange e A) := by
  apply MvPolynomial.algHom_ext
  intro I
  simp only [AlgHom.comp_apply, pluckerLinearAction_X, exteriorPluckerBasis_apply,
    exteriorPower.map_apply_ιMulti, matrixMinorEvaluation_exterior_word]
  simp only [matrixMinorEvaluation, aeval_X, matrixLinearChange]
  rfl

theorem pluckerLinearAction_preserves_matrixIdeal
    (e : (Fin n → K) →ₗ[K] (Fin n → K))
    (p : MvPolynomial (PluckerIndex s n) K) (hp : p ∈ matrixPluckerIdeal) :
    pluckerLinearAction e s p ∈ matrixPluckerIdeal := by
  let A : Matrix (Fin s) (Fin n) (MvPolynomial (Fin s × Fin n) K) :=
    fun i j => X (i,j)
  have he : matrixMinorEvaluation (K := K) A = genericPluckerMap := rfl
  change genericPluckerMap (pluckerLinearAction e s p) = 0
  rw [← he, ← AlgHom.comp_apply, matrixMinorEvaluation_pluckerLinearAction]
  exact matrixPluckerIdeal_le_matrixMinorKernel (matrixLinearChange e A) hp

end PaperVerification.AlternatingForms
