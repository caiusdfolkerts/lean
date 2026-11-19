module

public import PaperVerification.AlternatingFormsEvenOrbitBlocks
public import PaperVerification.AlternatingFormsOrbitPolynomial
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# The dominant polynomial family of even alternating pencils

Both block coefficient vectors remain independent parameters.  The remaining
parameters are the entries of the change-of-basis matrix.  The polynomial
coordinates are the literal selected entries of the two congruence transforms.
At the identity and at block coefficients (1, lam), the restriction of its
Jacobian to matrix variation and second-vector variation is the already solved
even-pencil differential.  Distinct lam therefore give a surjective Jacobian.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open Matrix MvPolynomial
open scoped BigOperators Classical Matrix

section DualCongruence

variable {K ν : Type*} [CommRing K] [Fintype ν] [DecidableEq ν]

theorem orbitCongruenceCoordinate_dual (A H : Matrix ν ν K) (u v : ν) :
    aeval (fun z : ν × ν =>
      TrivSqZeroExt.inl (orbitIdentityPoint (K := K) z) +
        TrivSqZeroExt.inr (H z.1 z.2) : (ν × ν) → TrivSqZeroExt K K)
      (orbitCongruenceCoordinate A u v) =
      TrivSqZeroExt.inl (A u v) +
        TrivSqZeroExt.inr ((H.transpose * A + A * H) u v) := by
  apply TrivSqZeroExt.ext
  · rw [MvPolynomial.aeval_inl_add_inr]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, add_zero, orbitCongruenceCoordinate_identity]
  · have h := congrFun (orbitCongruenceFamily_jacobian
      (fun _ : Unit => A) (fun _ => u) (fun _ => v)
      (fun z => H z.1 z.2)) ()
    rw [TauCeti.jacobiMatrixAt_mulVec_apply_eq_snd_aeval] at h
    change (aeval (fun z : ν × ν =>
      TrivSqZeroExt.inl (orbitIdentityPoint (K := K) z) +
        TrivSqZeroExt.inr (H z.1 z.2))
      (orbitCongruenceCoordinate A u v)).snd =
        ((H.transpose * A + A * H) u v) at h
    simpa only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, zero_add] using h

end DualCongruence

variable {K : Type*} [Field K]

abbrev EvenOrbitParameter (k : ℕ) :=
  (EvenOrbitMode k × EvenOrbitMode k) ⊕ (Bool × Fin k)

def evenOrbitSingleBlock (k : ℕ) (i : Fin k) :
    Matrix (EvenOrbitMode k) (EvenOrbitMode k) K :=
  evenOrbitSecond (Pi.single i 1)

theorem evenOrbitSecond_sum_single (k : ℕ) (lam : Fin k → K) :
    (∑ i, lam i • evenOrbitSingleBlock (K := K) k i) = evenOrbitSecond lam := by
  ext u v
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  rcases u with ⟨a, i⟩
  rcases v with ⟨b, j⟩
  by_cases hij : i = j
  · subst j
    simp [evenOrbitSingleBlock, evenOrbitSecond, Matrix.blockDiagonal_apply,
      Pi.single_apply, smul_eq_mul, mul_ite, ite_mul, apply_ite]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp only [if_neg (Ne.symm hji), Matrix.zero_apply, mul_zero]
    · simp
  · simp [evenOrbitSingleBlock, evenOrbitSecond, Matrix.blockDiagonal_apply, hij]

theorem evenOrbitSecond_one (k : ℕ) :
    evenOrbitSecond (fun _ : Fin k => (1 : K)) = evenOrbitFirst (K := K) k := by
  simp only [evenOrbitSecond, evenOrbitFirst, one_smul]

theorem evenOrbitSingleBlock_congruence_sum (k : ℕ) (lam : Fin k → K)
    (X : Matrix (EvenOrbitMode k) (EvenOrbitMode k) K) (u v : EvenOrbitMode k) :
    (∑ i, lam i * (X.transpose * evenOrbitSingleBlock (K := K) k i * X) u v) =
      (X.transpose * evenOrbitSecond lam * X) u v := by
  rw [← evenOrbitSecond_sum_single (K := K) k lam, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]

theorem evenOrbitSingleBlock_differential_sum (k : ℕ) (lam : Fin k → K)
    (H : Matrix (EvenOrbitMode k) (EvenOrbitMode k) K) (u v : EvenOrbitMode k) :
    (∑ i, lam i * (H.transpose * evenOrbitSingleBlock (K := K) k i +
      evenOrbitSingleBlock (K := K) k i * H) u v) =
      (H.transpose * evenOrbitSecond lam + evenOrbitSecond lam * H) u v := by
  rw [← evenOrbitSecond_sum_single (K := K) k lam, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, mul_add,
    Finset.sum_add_distrib]

def evenOrbitLiftedCongruence (k : ℕ)
    (A : Matrix (EvenOrbitMode k) (EvenOrbitMode k) K) (u v : EvenOrbitMode k) :
    MvPolynomial (EvenOrbitParameter k) K :=
  rename Sum.inl (orbitCongruenceCoordinate A u v)

def evenOrbitPolynomials (k : ℕ) (z : EvenOrbitPairSlot k) :
    MvPolynomial (EvenOrbitParameter k) K :=
  ∑ i, X (Sum.inr (z.1, i)) *
    evenOrbitLiftedCongruence k (evenOrbitSingleBlock (K := K) k i)
      (evenOrbitSlotRow k z.2) (evenOrbitSlotCol k z.2)

/-- This evaluation identity pins the polynomial map to the actual matrix
congruence action and both independent block coefficient vectors. -/
theorem evenOrbitPolynomials_eval (k : ℕ) (x : EvenOrbitParameter k → K)
    (z : EvenOrbitPairSlot k) :
    eval x (evenOrbitPolynomials k z) =
      ((Matrix.of fun i j => x (Sum.inl (i, j))).transpose *
        evenOrbitSecond (fun i => x (Sum.inr (z.1, i))) *
        (Matrix.of fun i j => x (Sum.inl (i, j))))
          (evenOrbitSlotRow k z.2) (evenOrbitSlotCol k z.2) := by
  simp only [evenOrbitPolynomials, map_sum, map_mul, eval_X,
    evenOrbitLiftedCongruence, eval_rename, orbitCongruenceCoordinate_eval,
    Function.comp_apply]
  exact evenOrbitSingleBlock_congruence_sum (K := K) k _ _ _ _

def evenOrbitBasePoint {k : ℕ} (lam : Fin k → K) : EvenOrbitParameter k → K :=
  Sum.elim orbitIdentityPoint (fun z => if z.1 then lam z.2 else 1)

def evenOrbitTangent {k : ℕ}
    (H : Matrix (EvenOrbitMode k) (EvenOrbitMode k) K) (μ : Fin k → K) :
    EvenOrbitParameter k → K :=
  Sum.elim (fun z => H z.1 z.2) (fun z => if z.1 then μ z.2 else 0)

theorem evenOrbitLiftedCongruence_dual {k : ℕ} (lam μ : Fin k → K)
    (A H : Matrix (EvenOrbitMode k) (EvenOrbitMode k) K) (u v : EvenOrbitMode k) :
    aeval (fun z => TrivSqZeroExt.inl (evenOrbitBasePoint lam z) +
      TrivSqZeroExt.inr (evenOrbitTangent H μ z) :
        EvenOrbitParameter k → TrivSqZeroExt K K)
      (evenOrbitLiftedCongruence k A u v) =
      TrivSqZeroExt.inl (A u v) +
        TrivSqZeroExt.inr ((H.transpose * A + A * H) u v) := by
  rw [evenOrbitLiftedCongruence, aeval_rename]
  exact orbitCongruenceCoordinate_dual A H u v

theorem evenOrbitPolynomials_jacobian {k : ℕ} (lam μ : Fin k → K)
    (H : Matrix (EvenOrbitMode k) (EvenOrbitMode k) K) :
    TauCeti.jacobiMatrixAt (evenOrbitPolynomials (K := K) k) (evenOrbitBasePoint lam) *ᵥ
        evenOrbitTangent H μ = evenOrbitDifferential lam H μ := by
  funext z
  rw [TauCeti.jacobiMatrixAt_mulVec_apply_eq_snd_aeval]
  simp only [evenOrbitPolynomials, map_sum, map_mul, aeval_X,
    evenOrbitLiftedCongruence_dual, TrivSqZeroExt.snd_sum,
    DualNumber.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, add_zero, zero_add]
  rcases z with ⟨b, s⟩
  cases b
  · simp only [evenOrbitBasePoint, evenOrbitTangent, Sum.elim_inr,
      Bool.false_eq_true, if_false, one_mul, zero_mul, add_zero,
      evenOrbitDifferential]
    simpa only [one_mul, evenOrbitSecond_one] using
      evenOrbitSingleBlock_differential_sum (K := K) k (fun _ => (1 : K)) H
        (evenOrbitSlotRow k s) (evenOrbitSlotCol k s)
  · simp only [evenOrbitBasePoint, evenOrbitTangent, Sum.elim_inr,
      if_true, Finset.sum_add_distrib, evenOrbitDifferential]
    rw [evenOrbitSingleBlock_differential_sum]
    have hμ := congrArg
      (fun A : Matrix (EvenOrbitMode k) (EvenOrbitMode k) K =>
        A (evenOrbitSlotRow k s) (evenOrbitSlotCol k s))
      (evenOrbitSecond_sum_single (K := K) k μ)
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hμ
    rw [hμ]
    rfl

/-- Matrix variation and variation of the second block vector already cover
all coefficients.  The first-vector parameters introduce no extra premise. -/
theorem evenOrbit_jacobian_surjective {k : ℕ} (lam : Fin k → K)
    (hlam : Function.Injective lam) :
    (TauCeti.jacobiMatrixAt (evenOrbitPolynomials (K := K) k)
      (evenOrbitBasePoint lam)).mulVec.Surjective := by
  intro y
  obtain ⟨⟨H, μ⟩, hy⟩ := evenOrbitDifferential_surjective lam hlam y
  refine ⟨evenOrbitTangent H μ, ?_⟩
  rw [evenOrbitPolynomials_jacobian]
  exact hy

theorem evenOrbit_natPoint_injective [CharZero K] (k : ℕ) :
    Function.Injective (fun i : Fin k => (i.val : K)) := by
  intro i j hij
  exact Fin.ext (Nat.cast_injective hij)

theorem evenOrbit_algebraicIndependent [CharZero K] (k : ℕ) :
    AlgebraicIndependent K (evenOrbitPolynomials (K := K) k) :=
  TauCeti.algebraicIndependent_of_mulVec_surjective_jacobiMatrixAt
    (evenOrbit_jacobian_surjective (fun i => (i.val : K)) (evenOrbit_natPoint_injective k))

def evenOrbitDeterminant (k : ℕ) : MvPolynomial (EvenOrbitParameter k) K :=
  rename Sum.inl (orbitDeterminant (K := K) (ν := EvenOrbitMode k))

theorem evenOrbitDeterminant_eval (k : ℕ) (x : EvenOrbitParameter k → K) :
    eval x (evenOrbitDeterminant (K := K) k) =
      (Matrix.of fun i j => x (Sum.inl (i, j))).det := by
  rw [evenOrbitDeterminant, eval_rename, orbitDeterminant_eval]
  rfl

theorem evenOrbitDeterminant_basePoint {k : ℕ} (lam : Fin k → K) :
    eval (evenOrbitBasePoint lam) (evenOrbitDeterminant (K := K) k) = 1 := by
  rw [evenOrbitDeterminant, eval_rename]
  exact orbitDeterminant_identity

theorem evenOrbitDeterminant_ne_zero (k : ℕ) :
    evenOrbitDeterminant (K := K) k ≠ 0 := by
  intro hz
  have h := evenOrbitDeterminant_basePoint (fun _ : Fin k => (0 : K))
  rw [hz, map_zero] at h
  exact zero_ne_one h

/-- Polynomial identities holding on all invertible block congruences hold on
the full space of pairs of alternating-form coefficients. -/
theorem evenOrbit_polynomial_eq_zero_of_vanish [CharZero K] (k : ℕ)
    {q : MvPolynomial (EvenOrbitPairSlot k) K}
    (hq : ∀ x : EvenOrbitParameter k → K,
      eval x (evenOrbitDeterminant (K := K) k) ≠ 0 →
        eval (fun i => eval x (evenOrbitPolynomials (K := K) k i)) q = 0) : q = 0 := by
  letI : Infinite K := Infinite.of_injective Nat.cast Nat.cast_injective
  exact polynomial_eq_zero_of_dominant_open_vanish
    (evenOrbit_jacobian_surjective (fun i => (i.val : K))
      (evenOrbit_natPoint_injective k)) (evenOrbitDeterminant_ne_zero k) hq

end PaperVerification.AlternatingForms
