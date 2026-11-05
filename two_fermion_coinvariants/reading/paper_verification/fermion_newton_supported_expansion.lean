module

public import PaperVerification.FermionNewtonConstantProfile

/-!
# Expanding inside a supported principal block

An invertible principal block whose columns vanish outside that block expands
every vector supported there using coefficients supported there. This supplies
the exact support, rather than an informal choice of coefficients, in the
first multiplicity-jump step of the Newton determinant induction.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.Fermion.Newton

open scoped BigOperators Matrix

variable {L I J : Type*} [Field L] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def extendCoefficients (e : J ↪ I) (v : J → L) : I → L :=
  fun i ↦ ∑ j, if e j = i then v j else 0

@[simp] theorem extendCoefficients_apply (e : J ↪ I) (v : J → L) (j : J) :
    extendCoefficients e v (e j) = v j := by
  simp [extendCoefficients, e.injective.eq_iff]

theorem extendCoefficients_of_not_mem_range (e : J ↪ I) (v : J → L) (i : I)
    (hi : i ∉ Set.range e) : extendCoefficients e v i = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  exact if_neg (fun he ↦ hi ⟨j, he⟩)

theorem mulVec_extendCoefficients (e : J ↪ I) (M : Matrix I I L) (v : J → L) (i : I) :
    (M *ᵥ extendCoefficients e v) i = ∑ j, M i (e j) * v j := by
  change (∑ k, M i k * ∑ j, if e j = k then v j else 0) = _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem exists_supported_expansion
    (e : J ↪ I) (M : Matrix I I L)
    (hblock : (M.submatrix e e).det ≠ 0)
    (hsupport : ∀ i, i ∉ Set.range e → ∀ j, M i (e j) = 0)
    (w : I → L) (hw : ∀ i, i ∉ Set.range e → w i = 0) :
    ∃ a : I → L, M *ᵥ a = w ∧ ∀ i, i ∉ Set.range e → a i = 0 := by
  let v : J → L := (M.submatrix e e)⁻¹ *ᵥ (w ∘ e)
  have hv : M.submatrix e e *ᵥ v = w ∘ e := by
    dsimp only [v]
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hblock), Matrix.one_mulVec]
  refine ⟨extendCoefficients e v, ?_, extendCoefficients_of_not_mem_range e v⟩
  funext i
  rw [mulVec_extendCoefficients]
  by_cases hi : i ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hi
    exact congrFun hv j
  · simp only [hsupport i hi, zero_mul, Finset.sum_const_zero, hw i hi]

variable {F : Type*} [Field F] {n : ℕ}

/-- Algebraic independence is supplied as an actual injective polynomial
evaluation. This applies to every subset of the original independent nodes. -/
theorem constantProfile_det_of_injective_polynomial_map
    (φ : MvPolynomial (Fin n) F →+* L) (hφ : Function.Injective φ)
    (d : ℕ) (σ : Fin n → ℤ) (β : Fin n → F)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    (profileNewtonMatrix (fun _ ↦ d) σ (fun i ↦ φ (MvPolynomial.X i))
      (fun i ↦ φ (MvPolynomial.C (β i)))).det ≠ 0 := by
  let f : RationalFunctions (F := F) (n := n) →+* L := IsFractionRing.lift hφ
  have h := newtonColumn_constant_det_ne_zero F n d σ β hσ hβ
  simp_rw [newtonColumn_eq_profileNewtonMatrix F] at h
  change (profileNewtonMatrix (fun _ ↦ d) σ (rationalNode (F := F))
    (fun i ↦ algebraMap F (RationalFunctions (F := F)) (β i))).det ≠ 0 at h
  have hm : (profileNewtonMatrix (fun _ ↦ d) σ (rationalNode (F := F))
      (fun i ↦ algebraMap F (RationalFunctions (F := F)) (β i))).map f =
      profileNewtonMatrix (fun _ ↦ d) σ (fun i ↦ φ (MvPolynomial.X i))
        (fun i ↦ φ (MvPolynomial.C (β i))) := by
    rw [profileNewtonMatrix_map]
    congr 1
    · funext i
      exact IsFractionRing.lift_algebraMap hφ (MvPolynomial.X i)
    · funext i
      change f (algebraMap F (RationalFunctions (F := F) (n := n)) (β i)) = _
      rw [IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n) F)
        (RationalFunctions (F := F) (n := n)), MvPolynomial.algebraMap_eq]
      exact IsFractionRing.lift_algebraMap hφ (MvPolynomial.C (β i))
  rw [← hm, matrix_map_det]
  exact (map_ne_zero f).mpr h

end PaperVerification.Fermion.Newton
