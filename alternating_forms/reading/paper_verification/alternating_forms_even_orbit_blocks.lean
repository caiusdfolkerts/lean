module

public import PaperVerification.AlternatingFormsOrbitChart
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring.Basic

/-!
# Solving the differential of a generic even alternating pencil

The canonical pair consists of symplectic 2 by 2 blocks with coefficients 1 and λᵢ.
Changing both the basis and the λᵢ gives a surjective differential when the λᵢ are
pairwise distinct. The off-diagonal blocks are solved by a two-equation linear system.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open Matrix
open scoped BigOperators

variable {K : Type*} [Field K]

def evenOrbitJ : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

theorem evenOrbitJ_transpose : (evenOrbitJ (K := K)).transpose = -evenOrbitJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenOrbitJ]

theorem evenOrbitJ_square : evenOrbitJ (K := K) * evenOrbitJ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenOrbitJ, Matrix.mul_apply, Fin.sum_univ_two]

theorem evenOrbitJ_upper_cancel (V : Matrix (Fin 2) (Fin 2) K) :
    evenOrbitJ * (-evenOrbitJ * V) = V := by
  rw [← mul_assoc, mul_neg, evenOrbitJ_square, neg_neg, one_mul]

theorem evenOrbitJ_lower_cancel (U : Matrix (Fin 2) (Fin 2) K) :
    (evenOrbitJ * U.transpose).transpose * evenOrbitJ = U := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, evenOrbitJ_transpose,
    mul_assoc, neg_mul, evenOrbitJ_square, neg_neg, mul_one]

def evenOrbitSolveU (a b : K) (C D : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K :=
  (b - a)⁻¹ • (D - a • C)

def evenOrbitSolveV (a b : K) (C D : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K :=
  (b - a)⁻¹ • (b • C - D)

theorem evenOrbitSolve_add (a b : K) (h : b - a ≠ 0)
    (C D : Matrix (Fin 2) (Fin 2) K) :
    evenOrbitSolveU a b C D + evenOrbitSolveV a b C D = C := by
  ext i j
  simp only [evenOrbitSolveU, evenOrbitSolveV, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  field_simp [h] <;> ring

theorem evenOrbitSolve_weighted (a b : K) (h : b - a ≠ 0)
    (C D : Matrix (Fin 2) (Fin 2) K) :
    b • evenOrbitSolveU a b C D + a • evenOrbitSolveV a b C D = D := by
  ext i j
  simp only [evenOrbitSolveU, evenOrbitSolveV, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  field_simp [h] <;> ring

def evenOrbitUpper (a b : K) (C D : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K :=
  -evenOrbitJ * evenOrbitSolveV a b C D

def evenOrbitLower (a b : K) (C D : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K :=
  evenOrbitJ * (evenOrbitSolveU a b C D).transpose

theorem evenOrbit_offDiagonal_first (a b : K) (h : b - a ≠ 0)
    (C D : Matrix (Fin 2) (Fin 2) K) :
    (evenOrbitLower a b C D).transpose * evenOrbitJ +
      evenOrbitJ * evenOrbitUpper a b C D = C := by
  rw [evenOrbitLower, evenOrbitUpper, evenOrbitJ_lower_cancel, evenOrbitJ_upper_cancel]
  exact evenOrbitSolve_add a b h C D

theorem evenOrbit_offDiagonal_second (a b : K) (h : b - a ≠ 0)
    (C D : Matrix (Fin 2) (Fin 2) K) :
    b • ((evenOrbitLower a b C D).transpose * evenOrbitJ) +
      a • (evenOrbitJ * evenOrbitUpper a b C D) = D := by
  rw [evenOrbitLower, evenOrbitUpper, evenOrbitJ_lower_cancel, evenOrbitJ_upper_cancel]
  exact evenOrbitSolve_weighted a b h C D

def evenOrbitDiagonal (c : K) : Matrix (Fin 2) (Fin 2) K := !![c, 0; 0, 0]

theorem evenOrbit_diagonal_first (c : K) :
    (evenOrbitDiagonal c).transpose * evenOrbitJ + evenOrbitJ * evenOrbitDiagonal c =
      c • evenOrbitJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [evenOrbitDiagonal, evenOrbitJ, Matrix.mul_apply, Fin.sum_univ_two]

abbrev EvenOrbitMode (k : ℕ) := Fin 2 × Fin k
abbrev EvenOrbitSlot (k : ℕ) := Fin k ⊕ (Orbit.StrictPair k × (Fin 2 × Fin 2))
abbrev EvenOrbitPairSlot (k : ℕ) := Bool × EvenOrbitSlot k

def evenOrbitSlotRow (k : ℕ) : EvenOrbitSlot k → EvenOrbitMode k
  | Sum.inl i => (0, i)
  | Sum.inr p => (p.2.1, p.1.val.1)

def evenOrbitSlotCol (k : ℕ) : EvenOrbitSlot k → EvenOrbitMode k
  | Sum.inl i => (1, i)
  | Sum.inr p => (p.2.2, p.1.val.2)

def evenOrbitBlock {k : ℕ} (H : Matrix (EvenOrbitMode k) (EvenOrbitMode k) K)
    (i j : Fin k) : Matrix (Fin 2) (Fin 2) K :=
  H.submatrix (fun a ↦ (a, i)) (fun b ↦ (b, j))

theorem evenOrbitBlock_add {k : ℕ}
    (H G : Matrix (EvenOrbitMode k) (EvenOrbitMode k) K) (i j : Fin k) :
    evenOrbitBlock (H + G) i j = evenOrbitBlock H i j + evenOrbitBlock G i j := rfl

theorem evenOrbitBlock_transpose {k : ℕ}
    (H : Matrix (EvenOrbitMode k) (EvenOrbitMode k) K) (i j : Fin k) :
    evenOrbitBlock H.transpose i j = (evenOrbitBlock H j i).transpose := rfl

theorem evenOrbitBlock_mul_diagonal {k : ℕ}
    (H : Matrix (EvenOrbitMode k) (EvenOrbitMode k) K)
    (B : Fin k → Matrix (Fin 2) (Fin 2) K) (i j : Fin k) :
    evenOrbitBlock (H * Matrix.blockDiagonal B) i j = evenOrbitBlock H i j * B j := by
  ext a b
  simp [evenOrbitBlock, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.blockDiagonal_apply, mul_ite]

theorem evenOrbitBlock_diagonal_mul {k : ℕ}
    (B : Fin k → Matrix (Fin 2) (Fin 2) K)
    (H : Matrix (EvenOrbitMode k) (EvenOrbitMode k) K) (i j : Fin k) :
    evenOrbitBlock (Matrix.blockDiagonal B * H) i j = B i * evenOrbitBlock H i j := by
  ext a b
  simp [evenOrbitBlock, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.blockDiagonal_apply, ite_mul]

def evenOrbitFirst (k : ℕ) : Matrix (EvenOrbitMode k) (EvenOrbitMode k) K :=
  Matrix.blockDiagonal fun _ ↦ evenOrbitJ

def evenOrbitSecond {k : ℕ} (lam : Fin k → K) :
    Matrix (EvenOrbitMode k) (EvenOrbitMode k) K :=
  Matrix.blockDiagonal fun i ↦ lam i • evenOrbitJ

def evenOrbitDifferential {k : ℕ} (lam : Fin k → K)
    (H : Matrix (EvenOrbitMode k) (EvenOrbitMode k) K) (μ : Fin k → K) :
    EvenOrbitPairSlot k → K :=
  fun z ↦ if z.1 then
      (H.transpose * evenOrbitSecond lam + evenOrbitSecond lam * H + evenOrbitSecond μ)
        (evenOrbitSlotRow k z.2) (evenOrbitSlotCol k z.2)
    else
      (H.transpose * evenOrbitFirst (K := K) k + evenOrbitFirst (K := K) k * H)
        (evenOrbitSlotRow k z.2) (evenOrbitSlotCol k z.2)

/-- Assemble the diagonal and off-diagonal solutions into a single infinitesimal matrix. -/
def evenOrbitSolutionMatrix {k : ℕ} (lam c : Fin k → K)
    (C D : Orbit.StrictPair k → Matrix (Fin 2) (Fin 2) K) :
    Matrix (EvenOrbitMode k) (EvenOrbitMode k) K :=
  Matrix.of fun u v ↦
    if h : u.2 < v.2 then
      evenOrbitUpper (lam u.2) (lam v.2) (C ⟨(u.2, v.2), h⟩) (D ⟨(u.2, v.2), h⟩) u.1 v.1
    else if h' : v.2 < u.2 then
      evenOrbitLower (lam v.2) (lam u.2) (C ⟨(v.2, u.2), h'⟩) (D ⟨(v.2, u.2), h'⟩) u.1 v.1
    else evenOrbitDiagonal (c u.2) u.1 v.1

theorem evenOrbitSolutionMatrix_diagonal {k : ℕ} (lam c : Fin k → K)
    (C D : Orbit.StrictPair k → Matrix (Fin 2) (Fin 2) K) (i : Fin k) :
    evenOrbitBlock (evenOrbitSolutionMatrix lam c C D) i i = evenOrbitDiagonal (c i) := by
  ext a b
  simp [evenOrbitBlock, evenOrbitSolutionMatrix]

theorem evenOrbitSolutionMatrix_upper {k : ℕ} (lam c : Fin k → K)
    (C D : Orbit.StrictPair k → Matrix (Fin 2) (Fin 2) K) (p : Orbit.StrictPair k) :
    evenOrbitBlock (evenOrbitSolutionMatrix lam c C D) p.val.1 p.val.2 =
      evenOrbitUpper (lam p.val.1) (lam p.val.2) (C p) (D p) := by
  ext a b
  simp [evenOrbitBlock, evenOrbitSolutionMatrix, p.property]

theorem evenOrbitSolutionMatrix_lower {k : ℕ} (lam c : Fin k → K)
    (C D : Orbit.StrictPair k → Matrix (Fin 2) (Fin 2) K) (p : Orbit.StrictPair k) :
    evenOrbitBlock (evenOrbitSolutionMatrix lam c C D) p.val.2 p.val.1 =
      evenOrbitLower (lam p.val.1) (lam p.val.2) (C p) (D p) := by
  ext a b
  simp [evenOrbitBlock, evenOrbitSolutionMatrix, p.property, not_lt_of_ge p.property.le]

/-- The actual even-pencil differential, including eigenvalue variation, is onto. -/
theorem evenOrbitDifferential_surjective {k : ℕ} (lam : Fin k → K)
    (hlam : Function.Injective lam) :
    Function.Surjective (fun Hμ :
      Matrix (EvenOrbitMode k) (EvenOrbitMode k) K × (Fin k → K) ↦
        evenOrbitDifferential lam Hμ.1 Hμ.2) := by
  intro y
  let c : Fin k → K := fun i ↦ y (false, Sum.inl i)
  let d : Fin k → K := fun i ↦ y (true, Sum.inl i)
  let C : Orbit.StrictPair k → Matrix (Fin 2) (Fin 2) K :=
    fun p ↦ Matrix.of fun a b ↦ y (false, Sum.inr (p, (a, b)))
  let D : Orbit.StrictPair k → Matrix (Fin 2) (Fin 2) K :=
    fun p ↦ Matrix.of fun a b ↦ y (true, Sum.inr (p, (a, b)))
  let H := evenOrbitSolutionMatrix lam c C D
  let μ : Fin k → K := fun i ↦ d i - lam i * c i
  have hne (p : Orbit.StrictPair k) : lam p.val.2 - lam p.val.1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    exact p.property.ne (hlam h).symm
  have hfirst (i j : Fin k) :
      evenOrbitBlock (H.transpose * evenOrbitFirst (K := K) k + evenOrbitFirst (K := K) k * H) i j =
        (evenOrbitBlock H j i).transpose * evenOrbitJ +
          evenOrbitJ * evenOrbitBlock H i j := by
    rw [evenOrbitBlock_add, evenOrbitFirst, evenOrbitBlock_mul_diagonal,
      evenOrbitBlock_diagonal_mul, evenOrbitBlock_transpose]
  have hsecond (i j : Fin k) :
      evenOrbitBlock (H.transpose * evenOrbitSecond lam + evenOrbitSecond lam * H) i j =
        lam j • ((evenOrbitBlock H j i).transpose * evenOrbitJ) +
          lam i • (evenOrbitJ * evenOrbitBlock H i j) := by
    rw [evenOrbitBlock_add, evenOrbitSecond, evenOrbitBlock_mul_diagonal,
      evenOrbitBlock_diagonal_mul, evenOrbitBlock_transpose,
      mul_smul_comm, smul_mul_assoc]
  refine ⟨(H, μ), ?_⟩
  funext z
  rcases z with ⟨flag, slot⟩
  cases slot with
  | inl i =>
    have hdiag := evenOrbitSolutionMatrix_diagonal lam c C D i
    cases flag
    · change evenOrbitBlock
        (H.transpose * evenOrbitFirst (K := K) k + evenOrbitFirst (K := K) k * H) i i 0 1 = c i
      rw [hfirst, hdiag, evenOrbit_diagonal_first]
      simp [evenOrbitJ]
    · change (evenOrbitBlock
        (H.transpose * evenOrbitSecond lam + evenOrbitSecond lam * H) i i +
        evenOrbitBlock (evenOrbitSecond μ) i i) 0 1 = d i
      rw [hsecond, hdiag]
      rw [← smul_add, evenOrbit_diagonal_first]
      simp [evenOrbitBlock, evenOrbitSecond, evenOrbitJ, μ, smul_eq_mul, mul_assoc] <;> ring
  | inr p =>
    rcases p with ⟨p, u, v⟩
    have hu := evenOrbitSolutionMatrix_upper lam c C D p
    have hl := evenOrbitSolutionMatrix_lower lam c C D p
    cases flag
    · change evenOrbitBlock
        (H.transpose * evenOrbitFirst (K := K) k + evenOrbitFirst (K := K) k * H)
          p.val.1 p.val.2 u v = C p u v
      rw [hfirst, hl, hu, evenOrbit_offDiagonal_first _ _ (hne p)]
    · change (evenOrbitBlock
        (H.transpose * evenOrbitSecond lam + evenOrbitSecond lam * H)
          p.val.1 p.val.2 +
        evenOrbitBlock (evenOrbitSecond μ) p.val.1 p.val.2) u v = D p u v
      rw [hsecond, hl, hu, evenOrbit_offDiagonal_second _ _ (hne p)]
      have hzero : evenOrbitBlock (evenOrbitSecond μ) p.val.1 p.val.2 = 0 := by
        ext a b
        simp [evenOrbitBlock, evenOrbitSecond, Matrix.blockDiagonal_apply,
          p.property.ne]
      rw [hzero, add_zero]

end PaperVerification.AlternatingForms
