module

public import PaperVerification.AlternatingFormsChernSeriesIdentity
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Descent of the actual Chern relations to elementary symmetric coordinates

The relations are first defined as genuine symmetric polynomials in roots.
The fundamental theorem of symmetric polynomials then gives their unique
expressions in the elementary symmetric coordinates.  Vieta surjectivity is
proved by factoring a polynomial with constant coefficient one, allowing its
degree to drop and padding the root tuple by zeros.  Consequently the isolated
common zero statement concerns arbitrary coefficient tuples, rather than only
tuples already supplied together with chosen roots.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open Finset

variable {K σ : Type*} [Field K] [CharZero K] [Fintype σ] [DecidableEq σ]

/-- Substitution of the squares of the root variables. -/
noncomputable def squareSubstitution :
    MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  MvPolynomial.aeval fun i => MvPolynomial.X i ^ 2

theorem rename_squareSubstitution (e : Equiv.Perm σ) (p : MvPolynomial σ K) :
    MvPolynomial.rename e (squareSubstitution p) =
      squareSubstitution (MvPolynomial.rename e p) := by
  simp only [squareSubstitution, MvPolynomial.comp_aeval_apply,
    MvPolynomial.aeval_rename, map_pow, MvPolynomial.rename_X, Function.comp_def]

/-- The actual root-coordinate relation polynomial from Section 4.3. -/
noncomputable def chernRootRelationPolynomial (n : ℕ) : MvPolynomial σ K :=
  if Even n then
    squareSubstitution (MvPolynomial.hsymm σ K (n / 2))
  else
    ∑ i, MvPolynomial.X i * squareSubstitution
      (MvPolynomial.pderiv i (MvPolynomial.hsymm σ K ((n + 1) / 2)))

theorem eval_squareSubstitution (x : σ → K) (p : MvPolynomial σ K) :
    MvPolynomial.eval x (squareSubstitution p) =
      MvPolynomial.eval (fun i => x i ^ 2) p := by
  change MvPolynomial.aeval x (MvPolynomial.aeval _ p) = MvPolynomial.aeval _ p
  simp only [MvPolynomial.comp_aeval_apply, map_pow, MvPolynomial.aeval_X]

@[simp] theorem eval_chernRootRelationPolynomial (x : σ → K) (n : ℕ) :
    MvPolynomial.eval x (chernRootRelationPolynomial (K := K) (σ := σ) n) =
      chernRootRelation x n := by
  unfold chernRootRelationPolynomial chernRootRelation
  split_ifs <;> simp [eval_squareSubstitution]

set_option maxHeartbeats 800000 in
theorem chernRootRelationPolynomial_isSymmetric (n : ℕ) :
    (chernRootRelationPolynomial (K := K) (σ := σ) n).IsSymmetric := by
  intro e
  unfold chernRootRelationPolynomial
  split_ifs
  · rw [rename_squareSubstitution, MvPolynomial.rename_hsymm]
  · simp only [map_sum, map_mul, MvPolynomial.rename_X, rename_squareSubstitution]
    calc
      _ = ∑ i, MvPolynomial.X (e i) * squareSubstitution
          (MvPolynomial.pderiv (e i) (MvPolynomial.hsymm σ K ((n + 1) / 2))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← MvPolynomial.pderiv_rename e.injective,
          MvPolynomial.rename_hsymm]
      _ = _ := Equiv.sum_comp e (fun i : σ => MvPolynomial.X i * squareSubstitution
        (MvPolynomial.pderiv i (MvPolynomial.hsymm σ K ((n + 1) / 2))))

/-- Coordinates `c₁,…,cₛ` have indices `0,…,s-1`.  This is the unique polynomial
whose substitution `cᵢ=eᵢ(x)` is the paper's root-coordinate relation. -/
noncomputable def chernCoefficientRelation (s n : ℕ) : MvPolynomial (Fin s) K :=
  (MvPolynomial.esymmAlgEquiv (Fin s) K (Fintype.card_fin s)).symm
    ⟨chernRootRelationPolynomial n, chernRootRelationPolynomial_isSymmetric n⟩

theorem chernCoefficientRelation_substitution (s n : ℕ) :
    MvPolynomial.aeval (fun i : Fin s => MvPolynomial.esymm (Fin s) K (i.val + 1))
        (chernCoefficientRelation (K := K) s n) =
      chernRootRelationPolynomial (K := K) (σ := Fin s) n := by
  have h := (MvPolynomial.esymmAlgEquiv (Fin s) K (Fintype.card_fin s)).apply_symm_apply
    ⟨chernRootRelationPolynomial n, chernRootRelationPolynomial_isSymmetric n⟩
  have hv := congrArg Subtype.val h
  change (MvPolynomial.esymmAlgHom (Fin s) K s (chernCoefficientRelation s n)).val = _ at hv
  simpa only [MvPolynomial.esymmAlgHom_apply] using hv

/-- The root-to-coefficient map used by the splitting principle. -/
noncomputable def chernCoefficientTuple {s : ℕ} (x : Fin s → K) : Fin s → K :=
  fun i => MvPolynomial.eval x (MvPolynomial.esymm (Fin s) K (i.val + 1))

theorem eval_chernCoefficientRelation {s : ℕ} (x : Fin s → K) (n : ℕ) :
    MvPolynomial.eval (chernCoefficientTuple x) (chernCoefficientRelation s n) =
      chernRootRelation x n := by
  have h := congrArg (MvPolynomial.aeval x)
    (chernCoefficientRelation_substitution (K := K) s n)
  rw [MvPolynomial.comp_aeval_apply] at h
  exact h.trans (eval_chernRootRelationPolynomial x n)

/-- The elementary symmetric coefficient formula, including degrees larger
than the number of roots and tuples containing zero roots. -/
theorem chernPolynomial_coeff (x : σ → K) (n : ℕ) :
    (chernPolynomial x).coeff n =
      (-1 : K) ^ n * MvPolynomial.eval x (MvPolynomial.esymm σ K n) := by
  have h := congrArg (PowerSeries.map (MvPolynomial.eval x))
    (TauCeti.mk_neg_one_pow_mul_esymm_eq_prod_one_sub_X (σ := σ) K)
  have hc := congrArg (PowerSeries.coeff n) h
  simp only [PowerSeries.coeff_map, map_mul, map_pow, map_neg, map_one,
    PowerSeries.coeff_mk, map_prod, map_sub, PowerSeries.map_C,
    MvPolynomial.eval_X, PowerSeries.map_X] at hc
  rw [← chernPolynomial_coe, Polynomial.coeff_coe] at hc
  exact hc.symm

/-- A constant-one polynomial factors into exactly `s` normalized linear
factors over an algebraically closed field; zero roots account for degree loss. -/
theorem exists_chernPolynomial [IsAlgClosed K] (s : ℕ) (P : Polynomial K)
    (hP0 : P.coeff 0 = 1) (hPs : P.natDegree ≤ s) :
    ∃ x : Fin s → K, chernPolynomial x = P := by
  induction s generalizing P with
  | zero =>
    have hP : P = 1 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hPs), hP0,
        map_one]
    exact ⟨Fin.elim0, by simp [chernPolynomial, hP]⟩
  | succ s ih =>
    by_cases hP : P = 1
    · exact ⟨fun _ => 0, by simp [chernPolynomial, hP]⟩
    have hdeg : P.natDegree ≠ 0 := by
      intro hzero
      apply hP
      rw [Polynomial.eq_C_of_natDegree_eq_zero hzero, hP0, map_one]
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root P
      (Polynomial.degree_ne_of_natDegree_ne hdeg)
    have hr0 : r ≠ 0 := by
      intro hz
      subst r
      have h : P.eval 0 = 0 := hr
      rw [← Polynomial.coeff_zero_eq_eval_zero, hP0] at h
      exact one_ne_zero h
    obtain ⟨D, hD⟩ := Polynomial.dvd_iff_isRoot.mpr hr
    let Q : Polynomial K := -Polynomial.C r * D
    have hab : Polynomial.C r⁻¹ * Polynomial.C r = (1 : Polynomial K) := by
      rw [← map_mul, inv_mul_cancel₀ hr0, map_one]
    have hfactor : P = (1 - Polynomial.C r⁻¹ * Polynomial.X) * Q := by
      rw [hD]
      dsimp [Q]
      calc
        _ = Polynomial.C r⁻¹ * Polynomial.C r * Polynomial.X * D - Polynomial.C r * D := by
          rw [hab]
          ring
        _ = _ := by ring
    have hQ0 : Q.coeff 0 = 1 := by
      have h := congrArg (fun p : Polynomial K => p.coeff 0) hfactor
      simpa [Polynomial.mul_coeff_zero, hP0] using h.symm
    have hQne : Q ≠ 0 := by
      intro h
      simpa [h] using hQ0
    have hlin : (1 - Polynomial.C r⁻¹ * Polynomial.X).natDegree = 1 := by
      rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt]
      · exact Polynomial.natDegree_C_mul_X _ (inv_ne_zero hr0)
      · simp [Polynomial.natDegree_C_mul_X _ (inv_ne_zero hr0)]
    have hlinne : (1 - Polynomial.C r⁻¹ * Polynomial.X : Polynomial K) ≠ 0 := by
      intro h
      simpa [h] using hlin
    have hQs : Q.natDegree ≤ s := by
      rw [hfactor, Polynomial.natDegree_mul hlinne hQne, hlin] at hPs
      omega
    obtain ⟨x, hx⟩ := ih Q hQ0 hQs
    refine ⟨Fin.cons r⁻¹ x, ?_⟩
    rw [chernPolynomial, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    change (1 - Polynomial.C r⁻¹ * Polynomial.X) * chernPolynomial x = P
    rw [hx]
    exact hfactor.symm

/-- A polynomial whose signed nonconstant coefficients are an arbitrary
coefficient tuple. -/
noncomputable def coefficientPolynomial {s : ℕ} (c : Fin s → K) : Polynomial K :=
  1 + ∑ i, Polynomial.C ((-1 : K) ^ (i.val + 1) * c i) * Polynomial.X ^ (i.val + 1)

@[simp] theorem coefficientPolynomial_coeff_zero {s : ℕ} (c : Fin s → K) :
    (coefficientPolynomial c).coeff 0 = 1 := by
  simp [coefficientPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]

theorem coefficientPolynomial_natDegree_le {s : ℕ} (c : Fin s → K) :
    (coefficientPolynomial c).natDegree ≤ s := by
  unfold coefficientPolynomial
  apply (Polynomial.natDegree_add_le _ _).trans
  refine max_le (by simp) ?_
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem coefficientPolynomial_coeff {s : ℕ} (c : Fin s → K) (i : Fin s) :
    (coefficientPolynomial c).coeff (i.val + 1) = (-1 : K) ^ (i.val + 1) * c i := by
  simp only [coefficientPolynomial, Polynomial.coeff_add, Polynomial.coeff_one,
    Nat.add_eq_zero, one_ne_zero, and_false, ite_false, zero_add,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have h : i.val ≠ j.val := by
      intro h
      exact hji (Fin.ext h.symm)
    simp [h]
  · simp

/-- Vieta surjectivity, with no assumption that the last coefficient is nonzero. -/
theorem chernCoefficientTuple_surjective [IsAlgClosed K] (s : ℕ) :
    Function.Surjective (chernCoefficientTuple (K := K) (s := s)) := by
  intro c
  obtain ⟨x, hx⟩ := exists_chernPolynomial s (coefficientPolynomial c)
    (coefficientPolynomial_coeff_zero c) (coefficientPolynomial_natDegree_le c)
  refine ⟨x, ?_⟩
  funext i
  have h := congrArg (fun p : Polynomial K => p.coeff (i.val + 1)) hx
  rw [chernPolynomial_coeff, coefficientPolynomial_coeff] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h

/-- The isolated common zero assertion in the abstract Chern coordinates.
This is the same polynomial system as the root system, by the proved
fundamental-theorem substitution and Vieta surjectivity. -/
theorem chernCoefficientRelation_common_zero [IsAlgClosed K] {s w : ℕ} (hw : 0 < w)
    (c : Fin s → K)
    (hwindow : ∀ m, w ≤ m → m < w + s →
      MvPolynomial.eval c (chernCoefficientRelation s m) = 0) :
    c = 0 := by
  obtain ⟨x, rfl⟩ := chernCoefficientTuple_surjective (K := K) s c
  have hx : ∀ i, x i = 0 := by
    apply chernRootRelation_common_zero hw
    intro m hwm hms
    rw [← eval_chernCoefficientRelation]
    exact hwindow m hwm (by simpa using hms)
  funext i
  have hcoeff := chernPolynomial_coeff x (i.val + 1)
  have hP : chernPolynomial x = 1 := by simp [chernPolynomial, hx]
  rw [hP] at hcoeff
  have hz : (-1 : K) ^ (i.val + 1) * chernCoefficientTuple x i = 0 := by
    simpa [chernCoefficientTuple, Polynomial.coeff_one] using hcoeff.symm
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

end PaperVerification.AlternatingForms
