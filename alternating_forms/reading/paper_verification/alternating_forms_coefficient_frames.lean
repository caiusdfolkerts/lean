module

public import PaperVerification.AlternatingFormsGenericHilbertCoordinates
public import PaperVerification.AlternatingFormsOddOrbitInterleaving
public import PaperVerification.AlternatingFormsOddTransport
public import PaperVerification.DominantPrincipalIntersection

/-!
# Full coefficient spaces and dominant orbit intersections

Increasing coordinate pairs give all coefficients of an alternating form.
The comparison with the blockwise odd-orbit coefficients is a proved linear
equivalence, so pulling back a nonzero genericity polynomial loses no points
or parameter directions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators Classical

variable {K : Type*} [Field K]

theorem strictPairSlots (n : ℕ) :
    OrbitPairSlots (fun a : StrictPairs n => a.val.1) (fun a => a.val.2) where
  injective := by
    intro a b hab
    exact Subtype.ext hab
  no_reverse := by
    intro a b h
    have ha := a.property
    have hb := b.property
    rw [h.1, h.2] at ha
    exact (not_lt_of_ge hb.le) ha
  covers := by
    intro u v huv
    rcases lt_or_gt_of_ne huv with h | h
    · exact ⟨⟨(u,v),h⟩,Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨⟨(v,u),h⟩,Or.inr ⟨rfl,rfl⟩⟩

/-- All increasing-pair coefficients, with the actual exterior two-form as value. -/
def strictCoefficientExteriorEquiv (n : ℕ) :
    (StrictPairs n → K) ≃ₗ[K] (⋀[K]^2 (Fin n → K)) :=
  orbitSlotLinearEquiv (strictPairSlots n)

@[simp] theorem strictCoefficientExteriorEquiv_apply (n : ℕ)
    (f : StrictPairs n → K) :
    strictCoefficientExteriorEquiv (K := K) n f =
      twoFormOfCoefficients f (Pi.basisFun K (Fin n)) := rfl

/-- The complete coefficient space used by generic smoothness parametrizes
every ordered pair of alternating forms bijectively. -/
def pairCoefficientExteriorEquiv (n : ℕ) :
    ((Fin 2 × StrictPairs n) → K) ≃ₗ[K]
      ((⋀[K]^2 (Fin n → K)) × (⋀[K]^2 (Fin n → K))) :=
  ((LinearEquiv.curry K K (Fin 2) (StrictPairs n)).trans
    (LinearEquiv.piCongrRight (fun _ : Fin 2 => strictCoefficientExteriorEquiv n))).trans
      (LinearEquiv.finTwoArrow K (⋀[K]^2 (Fin n → K)))

@[simp] theorem pairCoefficientExteriorEquiv_apply (n : ℕ)
    (a : (Fin 2 × StrictPairs n) → K) :
    pairCoefficientExteriorEquiv n a =
      (twoFormOfCoefficients (fun i => a (0,i)) (Pi.basisFun K (Fin n)),
       twoFormOfCoefficients (fun i => a (1,i)) (Pi.basisFun K (Fin n))) := rfl

/-- The actual permutation from the block orbit basis to path coordinates. -/
def oddOrbitToPathEquiv (t : ℕ) :
    (OddOrbitMode t → K) ≃ₗ[K] (Fin (2*(t+1)+1) → K) :=
  (standardBasisEquiv (oddOrbitInterleavedBasis t)).symm

/-- An invertible linear comparison of the two complete parameter spaces. -/
def oddOrbitToPairCoefficients (t : ℕ) :
    ((OddOrbitSlot t ⊕ OddOrbitSlot t) → K) ≃ₗ[K]
      ((Fin 2 × StrictPairs (2*(t+1)+1)) → K) :=
  (orbitPairCoordinateEquiv (oddOrbitExteriorBasis t)).trans
    (((exteriorPowerLinearEquiv (oddOrbitToPathEquiv t) 2).prodCongr
        (exteriorPowerLinearEquiv (oddOrbitToPathEquiv t) 2)).trans
      (pairCoefficientExteriorEquiv (2*(t+1)+1)).symm)

theorem oddOrbitToPairCoefficients_forms (t : ℕ)
    (y : (OddOrbitSlot t ⊕ OddOrbitSlot t) → K) :
    pairCoefficientExteriorEquiv (2*(t+1)+1)
        (oddOrbitToPairCoefficients t y) =
      (exteriorPower.map 2 (oddOrbitToPathEquiv t).toLinearMap
        (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).1,
       exteriorPower.map 2 (oddOrbitToPathEquiv t).toLinearMap
        (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).2) := by
  simp only [oddOrbitToPairCoefficients, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.prodCongr_apply,
    orbitPairCoordinateEquiv_apply, exteriorPowerLinearEquiv_apply]

section PolynomialPullback

variable {σ ι : Type*} [Fintype σ]

/-- The literal linear polynomials of a linear map between affine coefficient spaces. -/
def linearCoefficientPolynomials (L : (σ → K) →ₗ[K] (ι → K)) :
    ι → MvPolynomial σ K :=
  fun i => ∑ j, (L (Pi.basisFun K σ j) i) • X j

theorem linearCoefficientPolynomials_eval (L : (σ → K) →ₗ[K] (ι → K))
    (x : σ → K) (i : ι) :
    eval x (linearCoefficientPolynomials L i) = L x i := by
  simp only [linearCoefficientPolynomials, Algebra.smul_def, MvPolynomial.algebraMap_eq,
    map_sum, map_mul, eval_C, eval_X]
  have hx := (Pi.basisFun K σ).sum_repr x
  have h := congrArg (fun v => L v i) hx
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    Pi.basisFun_repr, smul_eq_mul] at h
  simpa only [mul_comm] using h

def linearCoefficientPullback (L : (σ → K) →ₗ[K] (ι → K)) :
    MvPolynomial ι K →ₐ[K] MvPolynomial σ K :=
  aeval (linearCoefficientPolynomials L)

theorem linearCoefficientPullback_eval (L : (σ → K) →ₗ[K] (ι → K))
    (q : MvPolynomial ι K) (x : σ → K) :
    eval x (linearCoefficientPullback L q) = eval (L x) q := by
  change eval x (aeval (linearCoefficientPolynomials L) q) = eval (L x) q
  rw [aeval_eq_bind₁]
  simpa only [aeval_eq_eval, linearCoefficientPolynomials_eval] using
    aeval_bind₁ x (linearCoefficientPolynomials L) q

/-- A surjective linear coordinate change pulls a nonzero polynomial back nontrivially. -/
theorem linearCoefficientPullback_ne_zero [Infinite K]
    (L : (σ → K) →ₗ[K] (ι → K)) (hL : Function.Surjective L)
    (q : MvPolynomial ι K) (hq : q ≠ 0) :
    linearCoefficientPullback L q ≠ 0 := by
  intro h
  apply hq
  apply MvPolynomial.funext
  intro y
  obtain ⟨x,rfl⟩ := hL y
  rw [← linearCoefficientPullback_eval, h, map_zero, map_zero]

end PolynomialPullback

/-- Every nonzero polynomial in the full ordinary pair-coefficient space
is nonzero at an invertible point of the actual canonical odd orbit. -/
theorem oddOrbit_meets_principal_open [Infinite K] (t : ℕ)
    (q : MvPolynomial (Fin 2 × StrictPairs (2*(t+1)+1)) K) (hq : q ≠ 0) :
    ∃ x : (OddOrbitMode t × OddOrbitMode t) → K,
      eval x (orbitDeterminant (K := K) (ν := OddOrbitMode t)) ≠ 0 ∧
      eval (oddOrbitToPairCoefficients t
        (fun i => eval x (orbitPairPolynomialCoordinates
          (actualOrbitPolynomials (row := oddOrbitSlotRow t) (col := oddOrbitSlotCol t)
            (oddOrbitFirstForm t) (oddOrbitSecondForm t)) i))) q ≠ 0 := by
  let p := actualOrbitPolynomials (row := oddOrbitSlotRow t) (col := oddOrbitSlotCol t)
    (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm t)
  let L := (oddOrbitToPairCoefficients (K := K) t).toLinearMap
  have hJ := jacobian_surjective_reindex p orbitIdentityPoint
    (Equiv.boolProdEquivSum (OddOrbitSlot t)).symm (oddOrbit_actual_jacobian_surjective t)
  obtain ⟨x,hx,hqx⟩ := exists_dominant_principal_intersection
    (orbitPairPolynomialCoordinates p) orbitIdentityPoint hJ
    orbitDeterminant orbitDeterminant_ne_zero (linearCoefficientPullback L q)
    (linearCoefficientPullback_ne_zero L (oddOrbitToPairCoefficients t).surjective q hq)
  refine ⟨x,hx,?_⟩
  rw [linearCoefficientPullback_eval] at hqx
  simpa only [L, p, LinearEquiv.coe_coe] using hqx

end PaperVerification.AlternatingForms
