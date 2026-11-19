module

public import PaperVerification.WeightedInitialFiber
public import TauCeti.RingTheory.KrullDimension.FiniteType
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Krull dimension of the actual weighted initial quotient

The image algebra constructed in `WeightedInitialFiber` embeds into `(P/Q)[t]`.
When `Q` is prime, this ambient domain is algebraic over the image algebra:
`t` belongs to the image, and `t^(w i) x̄_i` does also.  This is an algebraicity
argument, not an integrality claim.  Finite-type transcendence-degree theory
therefore identifies their dimensions.

The image of `t` is a nonzero nonunit.  A maximal ideal containing it has full
height by the affine-domain dimension theorem; the regular-element dimension
theorem then computes the special fiber.  The proved special-fiber kernel
identifies that fiber with the conventional initial quotient.

Finally, chains of primes above any ideal reduce the lower dimension bound
to the preceding calculation for prime ideals.  No flatness, dimension
equality, or initial-ideal identity is supplied as a hypothesis.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.WeightedInitialFiber

open MvPolynomial

variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K

/-- The ambient algebra is the literal inclusion of the actual image
subalgebra.  It is spelled out so the cached commutative-ring instance on
that image does not hide the standard subalgebra algebra structure. -/
instance reesAmbientAlgebra (Q : Ideal P) (w : σ → ℕ) :
    Algebra (reesAlgebra Q w) (Polynomial (P ⧸ Q)) where
  toSMul := inferInstance
  algebraMap :=
    { toFun := Subtype.val
      map_one' := rfl
      map_mul' := fun a b ↦ rfl
      map_zero' := rfl
      map_add' := fun a b ↦ rfl }
  commutes' := fun a p ↦ mul_comm a.val p
  smul_def' := fun a p ↦ rfl

@[simp] theorem reesAmbient_algebraMap_apply (Q : Ideal P) (w : σ → ℕ)
    (a : reesAlgebra Q w) :
    algebraMap (reesAlgebra Q w) (Polynomial (P ⧸ Q)) a=a.val := rfl

instance reesAmbientScalarTower (Q : Ideal P) (w : σ → ℕ) :
    IsScalarTower K (reesAlgebra Q w) (Polynomial (P ⧸ Q)) where
  smul_assoc a b p := by
    rw [Subalgebra.smul_def,Subalgebra.smul_def,Subalgebra.coe_smul]
    exact smul_assoc a (b : Polynomial (P ⧸ Q)) p

instance reesAmbientFaithfulSMul (Q : Ideal P) (w : σ → ℕ) :
    FaithfulSMul (reesAlgebra Q w) (Polynomial (P ⧸ Q)) where
  eq_of_smul_eq_smul h := by
    apply Subtype.ext
    simpa only [Subalgebra.smul_def,smul_eq_mul,mul_one] using
      h (1 : Polynomial (P ⧸ Q))

instance reesAlgebra_finiteType [Finite σ] (Q : Ideal P) (w : σ → ℕ) :
    Algebra.FiniteType K (reesAlgebra Q w) :=
  Algebra.FiniteType.of_surjective (reesCover Q w) (reesCover_surjective Q w)

@[simp] theorem reesParameter_val (Q : Ideal P) (w : σ → ℕ) :
    (reesParameter Q w).val = (Polynomial.X : Polynomial (P ⧸ Q)) :=
  reesMap_X Q w

theorem reesParameter_ne_zero (Q : Ideal P) [Q.IsPrime] (w : σ → ℕ) :
    reesParameter Q w ≠ 0 := by
  intro h
  have h' := congrArg Subtype.val h
  rw [reesParameter_val] at h'
  exact Polynomial.X_ne_zero h'

theorem reesParameter_not_isUnit (Q : Ideal P) [Q.IsPrime] (w : σ → ℕ) :
    ¬ IsUnit (reesParameter Q w) := by
  intro h
  have h' := h.map (reesAlgebra Q w).val.toMonoidHom
  change IsUnit (reesParameter Q w).val at h'
  rw [reesParameter_val] at h'
  exact Polynomial.not_isUnit_X h'

theorem ambient_parameter_algebraic (Q : Ideal P) [Q.IsPrime] (w : σ → ℕ) :
    IsAlgebraic (reesAlgebra Q w) (Polynomial.X : Polynomial (P ⧸ Q)) := by
  have h := isAlgebraic_algebraMap (A := Polynomial (P ⧸ Q)) (reesParameter Q w)
  simpa only [reesAmbient_algebraMap_apply,reesParameter_val] using h

/-- The denominator cleared relation is proved in the actual ambient algebra.
The coefficient `t^(w i)` is not asserted to be a unit or to give a monic equation. -/
theorem ambient_variable_algebraic (Q : Ideal P) [Q.IsPrime] (w : σ → ℕ) (i : σ) :
    IsAlgebraic (reesAlgebra Q w)
      (Polynomial.C (Ideal.Quotient.mkₐ K Q (MvPolynomial.X i))) := by
  have he : (reesParameter Q w) ^ w i •
      Polynomial.C (Ideal.Quotient.mkₐ K Q (MvPolynomial.X i)) =
      algebraMap (reesAlgebra Q w) (Polynomial (P ⧸ Q))
        (reesCover Q w (Polynomial.C (MvPolynomial.X i))) := by
    rw [Subalgebra.smul_def,smul_eq_mul]
    change (reesParameter Q w).val ^ w i *
      Polynomial.C (Ideal.Quotient.mkₐ K Q (MvPolynomial.X i)) =
        reesMap Q w (Polynomial.C (MvPolynomial.X i))
    rw [reesParameter_val,reesMap_C]
    rw [scaledQuotient_of_homogeneous Q w (MvPolynomial.X i) (w i)
      (MvPolynomial.isWeightedHomogeneous_X K w i)]
    exact mul_comm (Polynomial.X ^ w i : Polynomial (P ⧸ Q))
      (Polynomial.C (Ideal.Quotient.mkₐ K Q (MvPolynomial.X i)))
  apply IsAlgebraic.of_smul (y := (reesParameter Q w)^w i)
    (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero (w i) (reesParameter_ne_zero Q w)))
  rw [he]
  exact isAlgebraic_algebraMap _

theorem ambient_constant_algebraic (Q : Ideal P) [Q.IsPrime] (w : σ → ℕ) (p : P) :
    IsAlgebraic (reesAlgebra Q w) (Polynomial.C (Ideal.Quotient.mkₐ K Q p)) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have he : Polynomial.C (Ideal.Quotient.mkₐ K Q (MvPolynomial.C a)) =
          algebraMap (reesAlgebra Q w) (Polynomial (P ⧸ Q))
            (algebraMap K (reesAlgebra Q w) a) := by
        rw [←IsScalarTower.algebraMap_apply K (reesAlgebra Q w)
          (Polynomial (P ⧸ Q)),Polynomial.algebraMap_apply]
        exact congrArg Polynomial.C ((Ideal.Quotient.mkₐ K Q).commutes a)
      rw [he]
      exact isAlgebraic_algebraMap _
  | add p q hp hq =>
      rw [map_add,map_add]
      exact IsAlgebraic.add (R := reesAlgebra Q w)
        (S := Polynomial (P ⧸ Q)) hp hq
  | mul_X p i hp =>
      rw [map_mul,map_mul]
      exact IsAlgebraic.mul (R := reesAlgebra Q w)
        (S := Polynomial (P ⧸ Q)) hp (ambient_variable_algebraic Q w i)

set_option maxHeartbeats 800000 in
/-- The entire ambient polynomial domain is algebraic over the literal image
subalgebra, by the displayed denominator-cleared relations. -/
instance ambient_isAlgebraic (Q : Ideal P) [Q.IsPrime] (w : σ → ℕ) :
    Algebra.IsAlgebraic (reesAlgebra Q w) (Polynomial (P ⧸ Q)) := by
  constructor
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      exact IsAlgebraic.add (R := reesAlgebra Q w)
        (S := Polynomial (P ⧸ Q)) hp hq
  | monomial d a =>
      obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [←Polynomial.C_mul_X_pow_eq_monomial]
      change IsAlgebraic (reesAlgebra Q w)
        (Polynomial.C (Ideal.Quotient.mkₐ K Q f) *
          (Polynomial.X : Polynomial (P ⧸ Q)) ^ d)
      have hX : IsAlgebraic (reesAlgebra Q w)
          (Polynomial.X : Polynomial (P ⧸ Q)) := ambient_parameter_algebraic Q w
      have hp : IsAlgebraic (reesAlgebra Q w)
          ((Polynomial.X : Polynomial (P ⧸ Q)) ^ d) :=
        IsAlgebraic.pow (R := reesAlgebra Q w) (S := Polynomial (P ⧸ Q)) hX d
      exact IsAlgebraic.mul (R := reesAlgebra Q w) (S := Polynomial (P ⧸ Q))
        (ambient_constant_algebraic Q w f) hp

theorem reesAlgebra_dimension [Finite σ] (Q : Ideal P) [Q.IsPrime] (w : σ → ℕ) :
    ringKrullDim (reesAlgebra Q w) = ringKrullDim (P ⧸ Q)+1 := by
  rw [TauCeti.ringKrullDim_eq_of_isAlgebraic K (reesAlgebra Q w) (Polynomial (P ⧸ Q)),
    Polynomial.ringKrullDim_of_isNoetherianRing]

/-- The exact affine-domain height theorem is used here; regularity of `t`
alone would give only one of the two required dimension inequalities. -/
theorem zeroFiber_dimension_add_one [Finite σ] (Q : Ideal P) [Q.IsPrime]
    (w : σ → ℕ) :
    ringKrullDim (ZeroFiber Q w)+1 = ringKrullDim (reesAlgebra Q w) := by
  letI : IsNoetherianRing (reesAlgebra Q w) :=
    Algebra.FiniteType.isNoetherianRing K (reesAlgebra Q w)
  obtain ⟨M,hM,hsub⟩ := Ideal.exists_le_maximal
    (Ideal.span ({reesParameter Q w} : Set (reesAlgebra Q w)))
    (Ideal.span_singleton_ne_top (reesParameter_not_isUnit Q w))
  letI := hM
  apply Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero (reesParameter_ne_zero Q w))
    (TauCeti.height_eq_ringKrullDim_of_isMaximal K M)
  exact hsub (Ideal.mem_span_singleton_self _)

/-- Prime ideals retain their exact Krull dimension under arbitrary
nonnegative integer weights, including weights equal to zero. -/
theorem prime_initial_dimension [Finite σ] (Q : Ideal P) [Q.IsPrime] (w : σ → ℕ) :
    ringKrullDim (P ⧸ initialIdeal Q w) = ringKrullDim (P ⧸ Q) := by
  rw [ringKrullDim_eq_of_ringEquiv (initialQuotientEquiv Q w).toRingEquiv]
  apply ENat.WithBot.add_one_cancel.mp
  rw [zeroFiber_dimension_add_one,reesAlgebra_dimension]

/-- The dimension inequality needed for comparison with a prime candidate
initial ideal, proved for every ideal by actual prime chains. -/
theorem dimension_le_initial_dimension [Finite σ] (I : Ideal P) (w : σ → ℕ) :
    ringKrullDim (P ⧸ I) ≤ ringKrullDim (P ⧸ initialIdeal I w) := by
  rw [ringKrullDim_quotient I]
  refine iSup_le fun l => ?_
  let Q : Ideal P := l.head.val.asIdeal
  letI : Q.IsPrime := l.head.val.isPrime
  have hIQ : I≤Q := by
    simpa only [PrimeSpectrum.mem_zeroLocus,SetLike.coe_subset_coe] using l.head.property
  let q : LTSeries (PrimeSpectrum.zeroLocus (R := P) (Q : Set P)) :=
    .mk l.length (fun i => ⟨(l i).val,by
      rw [PrimeSpectrum.mem_zeroLocus,SetLike.coe_subset_coe]
      exact LTSeries.head_le l i⟩)
      (fun _ _ hij => Subtype.mk_lt_mk.mpr (l.strictMono hij))
  have hlen : (l.length : WithBot ℕ∞) ≤ ringKrullDim (P ⧸ Q) :=
    (Order.LTSeries.length_le_krullDim q).trans (ringKrullDim_quotient Q).symm.le
  rw [←prime_initial_dimension Q w] at hlen
  exact hlen.trans (ringKrullDim_le_of_surjective
    (Ideal.Quotient.factor (initialIdeal_mono w hIQ))
    (Ideal.Quotient.factor_surjective (initialIdeal_mono w hIQ)))

end PaperVerification.WeightedInitialFiber
