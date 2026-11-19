module

public import PaperVerification.WeightedInitialFiber
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Flatness of the literal weighted Rees image

The parameter acts by the ordinary polynomial variable in `(P/Q)[t]`.
Every nonzero scalar polynomial has a unit coefficient after extension from
the original field, so it remains a nonzerodivisor even when `P/Q` has zero
divisors.  The actual image algebra is therefore torsion-free over `K[t]`,
and hence flat.  No reducedness, primality, or flatness premise is used.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.WeightedInitialFiber

variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K

/-- The structure map of the actual one-parameter algebra. -/
def reesParameterMap (Q : Ideal P) (w : σ → ℕ) :
    Polynomial K →ₐ[K] reesAlgebra Q w := Polynomial.aeval (reesParameter Q w)

instance reesAlgebra_polynomialAlgebra (Q : Ideal P) (w : σ → ℕ) :
    Algebra (Polynomial K) (reesAlgebra Q w) :=
  (reesParameterMap Q w).toRingHom.toAlgebra

instance reesAlgebra_parameterTower (Q : Ideal P) (w : σ → ℕ) :
    IsScalarTower K (Polynomial K) (reesAlgebra Q w) :=
  IsScalarTower.of_algHom (reesParameterMap Q w)

theorem reesParameterMap_val (Q : Ideal P) (w : σ → ℕ) (f : Polynomial K) :
    (reesParameterMap Q w f).val=Polynomial.map (algebraMap K (P ⧸ Q)) f := by
  have he : (reesAlgebra Q w).val.comp (reesParameterMap Q w)=
      Polynomial.mapAlg K (P ⧸ Q) := by
    apply Polynomial.algHom_ext
    change (reesParameterMap Q w Polynomial.X).val=
      Polynomial.map (algebraMap K (P ⧸ Q)) Polynomial.X
    rw [reesParameterMap,Polynomial.aeval_X,Polynomial.map_X]
    exact reesMap_X Q w
  exact DFunLike.congr_fun he f

theorem reesPolynomial_smul_val (Q : Ideal P) (w : σ → ℕ)
    (f : Polynomial K) (a : reesAlgebra Q w) :
    (f • a).val=Polynomial.map (algebraMap K (P ⧸ Q)) f*a.val := by
  change ((reesParameterMap Q w f)*a).val=_
  rw [Subalgebra.coe_mul,reesParameterMap_val]

/-- A nonzero polynomial over the original field remains regular after
coefficient extension to any algebra, including a nonreduced quotient. -/
theorem scalarPolynomial_regular {A : Type*} [CommRing A] [Algebra K A]
    (f : Polynomial K) (hf : f≠0) :
    Polynomial.map (algebraMap K A) f∈nonZeroDivisors (Polynomial A) := by
  have hc : f.coeff f.natDegree≠0 := by
    simpa only [Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hf
  have hu : IsUnit (algebraMap K A (f.coeff f.natDegree)) :=
    (isUnit_iff_ne_zero.mpr hc).map (algebraMap K A)
  apply Polynomial.mem_nonZeroDivisors_of_coeff_mem f.natDegree
  simpa only [Polynomial.coeff_map] using hu.mem_nonZeroDivisors

instance reesAlgebra_isTorsionFree (Q : Ideal P) (w : σ → ℕ) :
    Module.IsTorsionFree (Polynomial K) (reesAlgebra Q w) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro f a hfa
  by_cases hf : f=0
  · exact Or.inl hf
  · have hz : Polynomial.map (algebraMap K (P ⧸ Q)) f*a.val=0 := by
      simpa only [reesPolynomial_smul_val,ZeroMemClass.coe_zero] using
        congrArg Subtype.val hfa
    exact Or.inr (Subtype.ext ((scalarPolynomial_regular f hf).1 a.val hz))

/-- The actual family with the previously proved weighted-initial special
fiber is flat over the polynomial parameter ring. -/
instance reesAlgebra_flat (Q : Ideal P) (w : σ → ℕ) :
    Module.Flat (Polynomial K) (reesAlgebra Q w) := inferInstance

end PaperVerification.WeightedInitialFiber
