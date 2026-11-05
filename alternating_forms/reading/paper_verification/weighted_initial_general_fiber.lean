module

public import PaperVerification.WeightedInitialFlat

/-!
# Every nonzero fiber of the actual weighted Rees family

The fiber map is ordinary evaluation of the parameter.  Its kernel is
proved by lifting to `P[Y]`, subtracting a normalized homogenization of an
actual relation, and dividing by `Y-c`.  This identifies every nonzero
fiber with the original quotient, rather than merely identifying one fiber
or assuming isotriviality.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.WeightedInitialFiber

open scoped BigOperators
open MvPolynomial

variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K

def scalarEval {A : Type*} [CommRing A] [Algebra K A] (c : K) :
    Polynomial A →ₐ[K] A where
  toRingHom := Polynomial.evalRingHom (algebraMap K A c)
  commutes' a := by
    change Polynomial.eval (algebraMap K A c)
      (Polynomial.C (algebraMap K A a)) = algebraMap K A a
    exact Polynomial.eval_C

@[simp] theorem scalarEval_C {A : Type*} [CommRing A] [Algebra K A]
    (c : K) (a : A) : scalarEval c (Polynomial.C a)=a := Polynomial.eval_C

@[simp] theorem scalarEval_X {A : Type*} [CommRing A] [Algebra K A]
    (c : K) : scalarEval c (Polynomial.X : Polynomial A)=algebraMap K A c :=
  Polynomial.eval_X

theorem scalarEval_monomial {A : Type*} [CommRing A] [Algebra K A]
    (c : K) (j : ℕ) (a : A) : scalarEval c (Polynomial.monomial j a)=c^j • a := by
  change (Polynomial.monomial j a).eval (algebraMap K A c)=_
  rw [Polynomial.eval_monomial]
  rw [Algebra.smul_def,map_pow,mul_comm]

def weightScale (w : σ → ℕ) (c : K) : P →ₐ[K] P :=
  MvPolynomial.aeval (fun i => c^w i • X i)

@[simp] theorem weightScale_X (w : σ → ℕ) (c : K) (i : σ) :
    weightScale w c (X i : P)=c^w i • X i :=
  MvPolynomial.aeval_X (fun j : σ => c^w j • (X j : P)) i

theorem weightScale_one (w : σ → ℕ) : weightScale (K := K) w 1=AlgHom.id K P := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [weightScale_X,one_pow,one_smul,AlgHom.id_apply]

theorem weightScale_comp (w : σ → ℕ) (c d : K) :
    (weightScale w c).comp (weightScale w d)=weightScale w (c*d) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply,weightScale_X,map_smul,smul_smul,mul_pow]
  rw [mul_comm]

theorem weightScale_inv_cancel (w : σ → ℕ) (c : K) (hc : c≠0) (p : P) :
    weightScale w c⁻¹ (weightScale w c p)=p := by
  have he := DFunLike.congr_fun (weightScale_comp w c⁻¹ c) p
  simpa only [AlgHom.comp_apply,inv_mul_cancel₀ hc,weightScale_one,AlgHom.id_apply] using he

theorem weightScale_cancel_inv (w : σ → ℕ) (c : K) (hc : c≠0) (p : P) :
    weightScale w c (weightScale w c⁻¹ p)=p := by
  have he := DFunLike.congr_fun (weightScale_comp w c c⁻¹) p
  simpa only [AlgHom.comp_apply,mul_inv_cancel₀ hc,weightScale_one,AlgHom.id_apply] using he

theorem weightScale_homogeneous (w : σ → ℕ) (c : K) (p : P) (d : ℕ)
    (hp : p.IsWeightedHomogeneous w d) : weightScale w c p=c^d • p := by
  simpa only [weightScale,Algebra.smul_def,←map_pow,MvPolynomial.algebraMap_eq,
    MvPolynomial.aeval_X_left_apply] using hp.aeval_pow_mul (MvPolynomial.C c) MvPolynomial.X

theorem scalarEval_scaledQuotient (Q : Ideal P) (w : σ → ℕ) (c : K) (p : P) :
    scalarEval c (scaledQuotient Q w p)=Ideal.Quotient.mkₐ K Q (weightScale w c p) := by
  have he : (scalarEval c).comp (scaledQuotient Q w)=
      (Ideal.Quotient.mkₐ K Q).comp (weightScale w c) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [scaledQuotient,scaledPolynomial,AlgHom.comp_apply,aeval_X,map_mul,map_pow,
      Polynomial.coe_mapAlgHom,Polynomial.map_C,Polynomial.map_X,scalarEval_C,scalarEval_X,
      weightScale_X,map_smul,Algebra.smul_def,map_pow]
    rw [mul_comm,(Ideal.Quotient.mkₐ K Q).commutes c] <;> rfl
  exact DFunLike.congr_fun he p

def reesEvaluation (Q : Ideal P) (w : σ → ℕ) (c : K) :
    reesAlgebra Q w →ₐ[K] P ⧸ Q := (scalarEval c).comp (reesAlgebra Q w).val

theorem reesEvaluation_cover (Q : Ideal P) (w : σ → ℕ) (c : K) (g : Polynomial P) :
    reesEvaluation Q w c (reesCover Q w g)=
      Ideal.Quotient.mkₐ K Q (weightScale w c (scalarEval c g)) := by
  induction g using Polynomial.induction_on' with
  | add g h hg hh => simp only [map_add,hg,hh]
  | monomial j p =>
      change scalarEval c (reesMap Q w (Polynomial.monomial j p))=_
      rw [reesMap_monomial,map_mul,map_pow,scalarEval_X,scalarEval_scaledQuotient,
        scalarEval_monomial,map_smul,map_smul]
      calc
        _ = algebraMap K (P ⧸ Q) (c^j) *
            Ideal.Quotient.mkₐ K Q (weightScale w c p) := by
          rw [map_pow,mul_comm]
        _ = c^j • Ideal.Quotient.mkₐ K Q (weightScale w c p) :=
          (Algebra.smul_def (c^j)
            (Ideal.Quotient.mkₐ K Q (weightScale w c p))).symm

theorem reesEvaluation_surjective (Q : Ideal P) (w : σ → ℕ)
    (c : K) (hc : c≠0) : Function.Surjective (reesEvaluation Q w c) := by
  intro a
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective K Q a
  refine ⟨reesCover Q w (Polynomial.C (weightScale w c⁻¹ p)),?_⟩
  rw [reesEvaluation_cover,scalarEval_C,weightScale_cancel_inv w c hc]

theorem homogenize_scalarEval (w : σ → ℕ) (p : P) (d : ℕ) (hp : WeightBound w d p)
    (c : K) (hc : c≠0) :
    scalarEval c (homogenize w p d)=c^d • weightScale w c⁻¹ p := by
  rw [homogenize,map_sum]
  calc
    _ = ∑ j∈Finset.range (d+1),c^d • weightScale w c⁻¹
        (weightedHomogeneousComponent w j p) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [scalarEval_monomial,weightScale_homogeneous w c⁻¹ _ j
        (weightedHomogeneousComponent_isWeightedHomogeneous j p),smul_smul]
      congr 1
      have hle : j≤d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [pow_sub₀ c hc hle,inv_pow]
    _ = _ := by
      rw [←Finset.smul_sum,←map_sum,sum_components_of_bound w p d hp]

abbrev ParameterFiber (Q : Ideal P) (w : σ → ℕ) (c : K) :=
  reesAlgebra Q w ⧸ Ideal.span
    ({reesParameter Q w-algebraMap K (reesAlgebra Q w) c} : Set (reesAlgebra Q w))

theorem reesEvaluation_ker (Q : Ideal P) (w : σ → ℕ) (c : K) (hc : c≠0) :
    RingHom.ker (reesEvaluation Q w c).toRingHom=
      Ideal.span ({reesParameter Q w-algebraMap K (reesAlgebra Q w) c} :
        Set (reesAlgebra Q w)) := by
  apply le_antisymm
  · intro a ha
    obtain ⟨g,hg⟩ := reesCover_surjective Q w a
    let p : P := weightScale w c (scalarEval c g)
    have hp : p∈Q := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change Ideal.Quotient.mkₐ K Q (weightScale w c (scalarEval c g))=0
      rw [←reesEvaluation_cover Q w c g,hg]
      exact ha
    let d := weightedTotalDegree w p
    let H : Polynomial P := (c⁻¹)^d • homogenize w p d
    have hH : reesCover Q w H=0 := by
      apply Subtype.ext
      change reesMap Q w H=0
      dsimp only [H]
      rw [map_smul,reesMap_homogenize Q w p d (weightBound_total w p),
        show Ideal.Quotient.mkₐ K Q p=0 from Ideal.Quotient.eq_zero_iff_mem.mpr hp]
      simp only [Polynomial.C_0,zero_mul,smul_zero,ZeroMemClass.coe_zero]
    have hEval : scalarEval c H=scalarEval c g := by
      dsimp only [H]
      rw [map_smul,homogenize_scalarEval w p d (weightBound_total w p) c hc,
        smul_smul,←mul_pow,inv_mul_cancel₀ hc,one_pow,one_smul]
      exact weightScale_inv_cancel w c hc (scalarEval c g)
    have hdvd : Polynomial.X-Polynomial.C (MvPolynomial.C c) ∣ g-H := by
      apply Polynomial.dvd_iff_isRoot.mpr
      change scalarEval c (g-H)=0
      rw [map_sub,hEval,sub_self]
    obtain ⟨u,hu⟩ := hdvd
    have he : a=(reesParameter Q w-algebraMap K (reesAlgebra Q w) c)*reesCover Q w u := by
      rw [←hg,←sub_zero (reesCover Q w g),←hH,←map_sub,hu,map_mul,map_sub]
      congr 2
      exact (reesCover Q w).commutes c
    rw [he,mul_comm]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · apply Ideal.span_le.mpr
    rintro _ rfl
    change reesEvaluation Q w c (reesParameter Q w-algebraMap K (reesAlgebra Q w) c)=0
    rw [map_sub,AlgHom.commutes]
    change scalarEval c (reesMap Q w Polynomial.X)-_=0
    rw [reesMap_X,scalarEval_X,sub_self]

/-- Every actual nonzero parameter fiber is the original quotient algebra. -/
def nonzeroFiberEquiv (Q : Ideal P) (w : σ → ℕ) (c : K) (hc : c≠0) :
    ParameterFiber Q w c ≃ₐ[K] P ⧸ Q :=
  (Ideal.quotientEquivAlgOfEq K (reesEvaluation_ker Q w c hc).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (reesEvaluation_surjective Q w c hc))

end PaperVerification.WeightedInitialFiber
