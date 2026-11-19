/- Integral coordinate changes preserve the actual represented matroid
before and after passage to every field, including characteristic two. -/
module
public import Recovery.Unimodular.PriorExtensions.SignedSumsRealization
public import Mathlib.LinearAlgebra.Matrix.ToLin
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Unimodular.SignedSums

def castIntegralEquiv {I J : Type*} [Fintype I] [Fintype J]
    (K : Type*) [Field K] (e : (I → ℤ) ≃ₗ[ℤ] (J → ℤ)) :
    (I → K) ≃ₗ[K] (J → K) := by
  classical
  let A := LinearMap.toMatrix' e.toLinearMap
  let B := LinearMap.toMatrix' e.symm.toLinearMap
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by ext x; simp
    rw [he, LinearMap.toMatrix'_id]
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext x; simp
    rw [he, LinearMap.toMatrix'_id]
  have hABK : A.map (Int.castRingHom K) * B.map (Int.castRingHom K) = 1 := by
    rw [← Matrix.map_mul, hAB]
    simp
  have hBAK : B.map (Int.castRingHom K) * A.map (Int.castRingHom K) = 1 := by
    rw [← Matrix.map_mul, hBA]
    simp
  exact Matrix.toLin'OfInv hBAK hABK

theorem castIntegralEquiv_apply {I J : Type*} [Fintype I] [Fintype J]
    (K : Type*) [Field K] (e : (I → ℤ) ≃ₗ[ℤ] (J → ℤ)) (x : I → ℤ) :
    castIntegralEquiv K e (fun i => (x i : K)) = fun j => (e x j : K) := by
  classical
  change Matrix.mulVec ((LinearMap.toMatrix' e.toLinearMap).map (Int.castRingHom K))
    (fun i => (x i : K)) = fun j => (e x j : K)
  funext j
  have hmap := RingHom.map_mulVec (Int.castRingHom K)
    (LinearMap.toMatrix' e.toLinearMap) x j
  simpa only [Function.comp_def, LinearMap.toMatrix'_mulVec, Int.coe_castRingHom,
    LinearEquiv.coe_coe] using hmap.symm

/-- The ordinary vector matroid of an integer family is invariant under
any actual integral linear isomorphism, over every field. -/
theorem integralEquiv_matroid {I J E : Type*} [Fintype I] [Fintype J]
    (K : Type*) [Field K] (e : (I → ℤ) ≃ₗ[ℤ] (J → ℤ)) (U : E → I → ℤ) :
    VectorMatroid.ofFamily (K := K) (fun j i => (e (U j) i : K)) =
      VectorMatroid.ofFamily (K := K) (fun j i => (U j i : K)) := by
  have he : castIntegralEquiv K e ∘ (fun j i => (U j i : K)) =
      (fun j i => (e (U j) i : K)) := by
    funext j
    exact castIntegralEquiv_apply K e (U j)
  rw [← he]
  exact matroid_linearEquiv _ _

/-- In particular, the side normalization in the signed-sum theorem
represents the very same ordinary real matroid as the original lattice vectors. -/
theorem portNormalization_real_matroid {n r : ℕ} {E : Type*}
    (U : E → Lattice n) (a : Fin r → E) (N : PortNormalization U a) :
    VectorMatroid.ofFamily (K := ℝ)
      (fun j i => (productCoordinates N.equiv U i j : ℝ)) =
      VectorMatroid.ofFamily (K := ℝ) (fun j => embed (U j)) := by
  let e : Lattice n ≃ₗ[ℤ] (Fin r ⊕ N.Complement → ℤ) :=
    N.equiv.trans (LinearEquiv.sumArrowLequivProdArrow (Fin r) N.Complement ℤ ℤ).symm
  have h := integralEquiv_matroid ℝ e U
  convert h using 1 <;> rfl

/-- The entire normalized input matrix, including all deleted ports, is
exactly the augmented matrix used in the determinant argument. -/
theorem normalized_input_eq_augment {n r : ℕ} {T L : Type*}
    (C : Matrix (Fin r) T ℤ) (τ : Fin r → T)
    (U : T ⊕ L → Lattice n)
    (hport : ∀ t, U (.inl t) = portMap (fun i => U (.inl (τ i))) (fun i => C i t))
    (N : PortNormalization U (fun i => Sum.inl (τ i))) :
    productCoordinates N.equiv U = augment C (productCoordinates N.equiv (U ∘ Sum.inr)) := by
  ext i j
  cases j with
  | inr l => rfl
  | inl t =>
      have ht : N.equiv (U (.inl t)) = (fun i => C i t, 0) := by
        rw [hport]
        exact normalized_portMap U _ N _
      cases i <;> simp [augment, productCoordinates, ht]

/-- Packing the rows changes no independent subset; this identifies the
binary augmented matrix with the literal side representation. -/
theorem augmented_binary_matroid {P A T L : Type*}
    (C : Matrix P T ℤ) (U : Matrix (P ⊕ A) L ℤ) :
    VectorMatroid.ofFamily (K := Binary.F)
      (fun j i => (augment C U i j : Binary.F)) =
    VectorMatroid.ofFamily (K := Binary.F)
      (Binary.sideFamily (fun t p => (C p t : Binary.F)) (sideCast U)) := by
  let e := LinearEquiv.sumArrowLequivProdArrow P A Binary.F Binary.F
  have he : e ∘ (fun j i => (augment C U i j : Binary.F)) =
      Binary.sideFamily (fun t p => (C p t : Binary.F)) (sideCast U) := by
    funext j
    cases j <;> ext i <;>
      simp [e, Binary.sideFamily, augment, sideCast]
  have h := matroid_linearEquiv e (fun j i => (augment C U i j : Binary.F))
  rw [he] at h
  exact h.symm

/-- The binary side representation in the port sum is a representation of
exactly the original ordinary real matroid, not an extra assumed matroid. -/
theorem normalized_input_binary_matroid {n r : ℕ} {T L : Type*}
    [Fintype T] [Fintype L]
    (C : Matrix (Fin r) T ℤ) (τ : Fin r → T)
    (U : T ⊕ L → Lattice n)
    (hport : ∀ t, U (.inl t) = portMap (fun i => U (.inl (τ i))) (fun i => C i t))
    (N : PortNormalization U (fun i => Sum.inl (τ i))) :
    VectorMatroid.ofFamily (K := ℝ) (fun j => embed (U j)) =
    VectorMatroid.ofFamily (K := Binary.F)
      (Binary.sideFamily (fun t p => (C p t : Binary.F))
        (sideCast (productCoordinates N.equiv (U ∘ Sum.inr)))) := by
  have h := portNormalization_real_matroid U (fun i => Sum.inl (τ i)) N
  rw [normalized_input_eq_augment C τ U hport N] at h
  rw [← h]
  have ht : (augment C (productCoordinates N.equiv (U ∘ Sum.inr))).IsTotallyUnimodular := by
    rw [← normalized_input_eq_augment C τ U hport N]
    exact N.totallyUnimodular
  rw [tu_matroid_field_invariant (F := Binary.F) _ ht]
  exact augmented_binary_matroid _ _

end Unimodular.SignedSums
#print axioms Unimodular.SignedSums.castIntegralEquiv_apply
#print axioms Unimodular.SignedSums.integralEquiv_matroid
#print axioms Unimodular.SignedSums.portNormalization_real_matroid

#print axioms Unimodular.SignedSums.normalized_input_eq_augment
#print axioms Unimodular.SignedSums.normalized_input_binary_matroid
