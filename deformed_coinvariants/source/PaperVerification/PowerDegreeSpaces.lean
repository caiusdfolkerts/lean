module

public import PaperVerification.PowerComplex
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Finite homogeneous pieces of the power-tail complex

The shift is encoded by the exact equation `degree(a) + shift = total`.
Consequently negative would-be polynomial degrees give the zero space, with no
truncated-subtraction artifact. All exponent types are finite, uniformly in
the number of variables and the total degree.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Module
open scoped BigOperators

namespace PaperVerification.PowerOperators

def ShiftedExponent (n s d : ℕ) := {a : Fin n →₀ ℕ // a.degree+s=d}

instance shiftedExponent_finite (n s d : ℕ) : Finite (ShiftedExponent n s d) := by
  change Finite {a : Fin n →₀ ℕ // a.degree+s=d}
  have hset : Set.Finite {a : Fin n →₀ ℕ | a.degree+s=d} :=
    (Finsupp.finite_of_degree_le (σ := Fin n) d).subset (by
      intro a ha
      change a.degree ≤ d
      change a.degree+s=d at ha
      omega)
  exact hset.to_subtype

noncomputable instance shiftedExponent_fintype (n s d : ℕ) :
    Fintype (ShiftedExponent n s d) := Fintype.ofFinite _

variable (R : Type*) [CommRing R] (n s d : ℕ)

def shiftedPiece : Submodule R (MvPolynomial (Fin n) R) :=
  restrictSupport R {a | a.degree+s=d}

def shiftedPieceBasis : Basis (ShiftedExponent n s d) R (shiftedPiece R n s d) :=
  basisRestrictSupport R {a : Fin n →₀ ℕ | a.degree+s=d}

instance shiftedPiece_finite : Module.Finite R (shiftedPiece R n s d) :=
  Module.Finite.of_basis (shiftedPieceBasis R n s d)

variable {R n s d}

theorem mem_shiftedPiece (p : MvPolynomial (Fin n) R) :
    p ∈ shiftedPiece R n s d ↔ ∀ a, p.coeff a ≠ 0 → a.degree+s=d := by
  simp only [shiftedPiece, mem_restrictSupport_iff, Set.subset_def,
    Finset.mem_coe, MvPolynomial.mem_support_iff, Set.mem_setOf_eq]

theorem shiftedPiece_eq_homogeneous (hs : s ≤ d) :
    shiftedPiece R n s d = homogeneousSubmodule (Fin n) R (d-s) := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  unfold shiftedPiece restrictSupport
  congr 1
  ext a
  simp only [Set.mem_setOf_eq]
  omega

theorem shiftedPiece_eq_bot (hs : d < s) : shiftedPiece R n s d = ⊥ := by
  apply eq_bot_iff.mpr
  intro p hp
  change p = 0
  apply MvPolynomial.ext
  intro a
  have hz : p.coeff a = 0 := by
    by_contra hc
    have he := (mem_shiftedPiece p).mp hp a hc
    omega
  simpa using hz

def shiftedProjection (s d : ℕ) :
    MvPolynomial (Fin n) R →ₗ[R] MvPolynomial (Fin n) R :=
  if s ≤ d then homogeneousComponent (d-s) else 0

theorem shiftedProjection_mem (s d : ℕ) (p : MvPolynomial (Fin n) R) :
    shiftedProjection s d p ∈ shiftedPiece R n s d := by
  by_cases hs : s ≤ d
  · rw [shiftedProjection, if_pos hs, shiftedPiece_eq_homogeneous hs]
    exact homogeneousComponent_mem _ _
  · simp only [shiftedProjection, hs, ite_false, LinearMap.zero_apply,
      Submodule.zero_mem]

theorem shiftedProjection_of_mem {p : MvPolynomial (Fin n) R}
    (hp : p ∈ shiftedPiece R n s d) : shiftedProjection s d p = p := by
  by_cases hs : s ≤ d
  · rw [shiftedPiece_eq_homogeneous hs] at hp
    rw [shiftedProjection, if_pos hs, homogeneousComponent_eq_self hp]
  · rw [shiftedPiece_eq_bot (Nat.lt_of_not_ge hs), Submodule.mem_bot] at hp
    simp only [hp, map_zero]

theorem shiftedProjection_mul {q : MvPolynomial (Fin n) R} {j : ℕ}
    (hq : q.IsHomogeneous j) (s d : ℕ) (p : MvPolynomial (Fin n) R) :
    shiftedProjection s d (p*q) = shiftedProjection (s+j) d p * q := by
  by_cases hs : s ≤ d
  · rw [shiftedProjection, if_pos hs, hq.homogeneousComponent_mul_right]
    by_cases hj : j ≤ d-s
    · have hsj : s+j ≤ d := by omega
      simp only [hj, ite_true, shiftedProjection, hsj, Nat.sub_sub]
    · have hsj : ¬s+j ≤ d := by omega
      simp only [hj, ite_false, shiftedProjection, hsj, LinearMap.zero_apply, zero_mul]
  · have hsj : ¬s+j ≤ d := by omega
    simp only [shiftedProjection, hs, hsj, ite_false, LinearMap.zero_apply, zero_mul]

theorem shiftedProjection_euler (s d : ℕ) (i : Fin n) (p : MvPolynomial (Fin n) R) :
    shiftedProjection s d (euler i p) = euler i (shiftedProjection s d p) := by
  unfold shiftedProjection
  split_ifs
  · exact (euler_homogeneousComponent i p _).symm
  · simp only [LinearMap.zero_apply, map_zero]

theorem shiftedProjection_reversed (c : Fin n → R) (lam : R) (s d k : ℕ)
    (p : MvPolynomial (Fin n) R) :
    shiftedProjection s d (reversed c lam k p) =
      reversed c lam k (shiftedProjection (s+k) d p) := by
  simp only [reversed_eq_sum_postEuler, map_sum, postEuler_apply, map_add, map_smul,
    shiftedProjection_euler]
  apply Finset.sum_congr rfl
  intro i _
  have he : shiftedProjection s d (X i ^ k * p) =
      X i ^ k * shiftedProjection (s+k) d p := by
    rw [mul_comm (X i ^ k), shiftedProjection_mul (isHomogeneous_X_pow i k),
      mul_comm]
  rw [he]

theorem shiftedProjection_recurrence (m d : ℕ) (i j l : Fin n)
    (p : MvPolynomial (Fin n) R) :
    shiftedProjection (m+l.val) d (recurrenceVector m i j p l) =
      recurrenceVector m i j
        (shiftedProjection ((m+i.val)+(m+j.val)) d p) l := by
  simp only [recurrenceVector_apply]
  by_cases hl : l.val ≤ m+i.val+j.val
  · rw [mul_comm (homogeneousTailCoefficient _ l),
      shiftedProjection_mul (homogeneousTailCoefficient_isHomogeneous _ l)]
    have he : m+l.val+(m+i.val+j.val-l.val) = (m+i.val)+(m+j.val) := by omega
    rw [he, mul_comm]
  · rw [homogeneousTailCoefficient_eq_zero _ l (Nat.lt_of_not_ge hl)]
    simp only [zero_mul, map_zero]

theorem shiftedProjection_elementarySyzygy (c : Fin n → R) (lam : R) (m d : ℕ)
    (i j l : Fin n) (p : MvPolynomial (Fin n) R) :
    shiftedProjection (m+l.val) d (elementarySyzygy c lam m i j p l) =
      elementarySyzygy c lam m i j
        (shiftedProjection ((m+i.val)+(m+j.val)) d p) l := by
  classical
  have hs (j : Fin n) (u : MvPolynomial (Fin n) R) :
      shiftedProjection (R := R) (n := n) (m+l.val) d
          ((Pi.single j u : Fin n → MvPolynomial (Fin n) R) l) =
        (Pi.single j (shiftedProjection (R := R) (n := n) (m+j.val) d u) :
          Fin n → MvPolynomial (Fin n) R) l := by
    by_cases hlj : l = j
    · subst l
      simp only [Pi.single_eq_same]
    · simp only [Pi.single_eq_of_ne hlj, map_zero]
  simp only [elementarySyzygy_apply, Pi.sub_apply, Pi.smul_apply, map_sub,
    map_smul, shiftedProjection_recurrence, hs, shiftedProjection_reversed,
    Nat.add_comm (m+j.val) (m+i.val)]

/-- Every homogeneous relation in the exact fiber has a homogeneous Koszul
preimage with the correct shifts, including all low-degree zero terms. -/
theorem zero_slope_homogeneous_syzygies (c : Fin n → R) (m d : ℕ)
    (hf : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) R)
      (List.ofFn fun i : Fin n => weightedPower c (m+i.val)))
    (v : Fin n → MvPolynomial (Fin n) R)
    (hv : ∀ i, v i ∈ shiftedPiece R n (m+i.val) d)
    (hz : tailMap c 0 m v = 0) :
    ∃ A : Fin n → Fin n → MvPolynomial (Fin n) R,
      (∀ i j, A i j ∈ shiftedPiece R n ((m+i.val)+(m+j.val)) d) ∧
      syzygyMap c 0 m A = v := by
  have hmem : v ∈ LinearMap.range (syzygyMap c 0 m) := by
    rw [zero_slope_exact_of_regular c m hf]
    exact hz
  obtain ⟨B, hB⟩ := hmem
  let A := fun i j => shiftedProjection ((m+i.val)+(m+j.val)) d (B i j)
  refine ⟨A, fun i j => shiftedProjection_mem _ _ _, ?_⟩
  funext l
  calc
    syzygyMap c 0 m A l = shiftedProjection (m+l.val) d (syzygyMap c 0 m B l) := by
      simp only [syzygyMap_apply, Finset.sum_apply, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change elementarySyzygy c 0 m i j
          (shiftedProjection ((m+j.val)+(m+i.val)) d (B j i)) l =
        shiftedProjection (m+l.val) d (elementarySyzygy c 0 m i j (B j i) l)
      rw [shiftedProjection_elementarySyzygy, Nat.add_comm (m+j.val) (m+i.val)]
    _ = shiftedProjection (m+l.val) d (v l) := by rw [hB]
    _ = v l := shiftedProjection_of_mem (hv l)

end PaperVerification.PowerOperators
