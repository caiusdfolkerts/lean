module

public import PaperVerification.AlternatingFormsOrbitBlocks
public import PaperVerification.AlternatingFormsOrbitPolynomial
public import Mathlib.Data.Matrix.Block
public import Mathlib.Tactic.Ring.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Dominance of the canonical odd alternating pencil

For V = K^(t+1) ⊕ K^(t+2), the two canonical alternating matrices have off-diagonal
incidence blocks for the embeddings i ↦ i+1 and i ↦ i. Their simultaneous congruence
map has a surjective Jacobian at the identity. The proof uses the explicit block
solutions, not a classification theorem.
-/

@[expose] public section
noncomputable section

namespace PaperVerification.AlternatingForms

open Matrix MvPolynomial
open scoped BigOperators Matrix

variable {K : Type*} [Field K]

abbrev OddOrbitMode (t : ℕ) := Fin (t + 1) ⊕ Fin (t + 2)
abbrev OddOrbitSlot (t : ℕ) :=
  Orbit.StrictPair (t + 1) ⊕
    (Orbit.StrictPair (t + 2) ⊕ (Fin (t + 1) × Fin (t + 2)))
abbrev OddOrbitPairSlot (t : ℕ) := Bool × OddOrbitSlot t

def oddOrbitSlotRow (t : ℕ) : OddOrbitSlot t → OddOrbitMode t
  | Sum.inl p => Sum.inl p.val.1
  | Sum.inr (Sum.inl p) => Sum.inr p.val.1
  | Sum.inr (Sum.inr p) => Sum.inl p.1

def oddOrbitSlotCol (t : ℕ) : OddOrbitSlot t → OddOrbitMode t
  | Sum.inl p => Sum.inl p.val.2
  | Sum.inr (Sum.inl p) => Sum.inr p.val.2
  | Sum.inr (Sum.inr p) => Sum.inr p.2

def orbitIncidence {a b : ℕ} (e : Fin a → Fin b) : Matrix (Fin a) (Fin b) K :=
  Matrix.of fun i j ↦ if j = e i then 1 else 0

def orbitSkewIncidence {a b : ℕ} (e : Fin a → Fin b) :
    Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) K :=
  Matrix.fromBlocks 0 (orbitIncidence e) (-(orbitIncidence e).transpose) 0

def oddOrbitMatrices (t : ℕ) (z : OddOrbitPairSlot t) :
    Matrix (OddOrbitMode t) (OddOrbitMode t) K :=
  if z.1 then orbitSkewIncidence (K := K) Fin.castSucc else orbitSkewIncidence (K := K) Fin.succ

def oddOrbitPolynomials (t : ℕ) :
    OddOrbitPairSlot t → MvPolynomial (OddOrbitMode t × OddOrbitMode t) K :=
  orbitCongruenceFamily (oddOrbitMatrices t)
    (fun z ↦ oddOrbitSlotRow t z.2) (fun z ↦ oddOrbitSlotCol t z.2)

/-- Rearrange the independent coefficients of the two alternating matrices into
the AA, BB and AB blocks. -/
def oddOrbitCoefficientBlocks (t : ℕ) (y : OddOrbitPairSlot t → K) :
    OddOrbitBlockOutput K t :=
  (Sum.elim (fun p ↦ y (false, Sum.inl p)) (fun p ↦ y (true, Sum.inl p)),
   (Sum.elim (fun p ↦ y (false, Sum.inr (Sum.inl p)))
      (fun p ↦ y (true, Sum.inr (Sum.inl p))),
    (Matrix.of fun i j ↦ y (false, Sum.inr (Sum.inr (i, j))),
     Matrix.of fun i j ↦ y (true, Sum.inr (Sum.inr (i, j))))))

theorem oddOrbitCoefficientBlocks_injective (t : ℕ) :
    Function.Injective (oddOrbitCoefficientBlocks (K := K) t) := by
  intro y z h
  funext w
  rcases w with ⟨b, p⟩
  cases p with
  | inl p =>
    cases b
    · exact congrFun (congrArg Prod.fst h) (Sum.inl p)
    · exact congrFun (congrArg Prod.fst h) (Sum.inr p)
  | inr p =>
    cases p with
    | inl p =>
      cases b
      · exact congrFun (congrArg (fun a ↦ a.2.1) h) (Sum.inl p)
      · exact congrFun (congrArg (fun a ↦ a.2.1) h) (Sum.inr p)
    | inr p =>
      cases b
      · exact congrFun (congrFun (congrArg (fun a ↦ a.2.2.1) h) p.1) p.2
      · exact congrFun (congrFun (congrArg (fun a ↦ a.2.2.2) h) p.1) p.2

section BlockCalculation

variable {a b : ℕ}
  (P : Matrix (Fin a) (Fin a) K) (Q : Matrix (Fin a) (Fin b) K)
  (R : Matrix (Fin b) (Fin a) K) (S : Matrix (Fin b) (Fin b) K)
  (e : Fin a → Fin b)

theorem orbitSkewIncidence_differential_AA (i j : Fin a) :
    ((Matrix.fromBlocks P Q R S).transpose * orbitSkewIncidence (K := K) e +
      orbitSkewIncidence (K := K) e * Matrix.fromBlocks P Q R S) (Sum.inl i) (Sum.inl j) =
      R (e i) j - R (e j) i := by
  simp [orbitSkewIncidence, orbitIncidence, Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_sum_type, mul_ite, ite_mul, sub_eq_add_neg, add_comm]

theorem orbitSkewIncidence_differential_BB (i j : Fin b) :
    ((Matrix.fromBlocks P Q R S).transpose * orbitSkewIncidence (K := K) e +
      orbitSkewIncidence (K := K) e * Matrix.fromBlocks P Q R S) (Sum.inr i) (Sum.inr j) =
      (∑ a, if j = e a then Q a i else 0) -
        (∑ a, if i = e a then Q a j else 0) := by
  simp [orbitSkewIncidence, orbitIncidence, Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_sum_type, mul_ite, ite_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem orbitSkewIncidence_differential_AB (i : Fin a) (j : Fin b) :
    ((Matrix.fromBlocks P Q R S).transpose * orbitSkewIncidence (K := K) e +
      orbitSkewIncidence (K := K) e * Matrix.fromBlocks P Q R S) (Sum.inl i) (Sum.inr j) =
      (∑ a, if j = e a then P a i else 0) + S (e i) j := by
  simp [orbitSkewIncidence, orbitIncidence, Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_sum_type, mul_ite, ite_mul]

end BlockCalculation

theorem sum_succ_eq_rectPad {k : ℕ}
    (Q : Matrix (Fin k) (Fin (k + 1)) K) (i j : Fin (k + 1)) :
    (∑ a, if i = a.succ then Q a j else 0) = Orbit.rectPad Q i.val j := by
  refine Fin.cases ?_ (fun a ↦ ?_) i
  · simp [eq_comm, Fin.succ_ne_zero]
  · simp [Fin.succ_inj]

theorem sum_castSucc_eq_rectPad {k : ℕ}
    (Q : Matrix (Fin k) (Fin (k + 1)) K) (i j : Fin (k + 1)) :
    (∑ a, if i = a.castSucc then Q a j else 0) = Orbit.rectPad Q (i.val + 1) j := by
  refine Fin.lastCases ?_ (fun a ↦ ?_) i
  · have hne (a : Fin k) : (Fin.last k : Fin (k + 1)) ≠ a.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      have ha := a.isLt
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      omega
    simp [hne]
  · simp [Fin.castSucc_inj]

theorem orbitSquarePad_succ_fin {t : ℕ}
    (P : Matrix (Fin (t + 1)) (Fin (t + 1)) K) (i j : Fin (t + 1)) :
    orbitSquarePad P (i.val + 1) j.val = P i j := by
  have hi : 0 < i.val + 1 := by omega
  have hi' : i.val + 1 ≤ t + 1 := by have := i.isLt; omega
  have hj : j.val ≤ t := by have := j.isLt; omega
  simp [orbitSquarePad, hi, hi', hj]

theorem sum_succ_eq_squarePad {t : ℕ}
    (P : Matrix (Fin (t + 1)) (Fin (t + 1)) K)
    (i : Fin (t + 2)) (j : Fin (t + 1)) :
    (∑ a, if i = a.succ then P a j else 0) = orbitSquarePad P i.val j.val := by
  refine Fin.cases ?_ (fun a ↦ ?_) i
  · simp [orbitSquarePad, eq_comm, Fin.succ_ne_zero]
  · simp [Fin.succ_inj, orbitSquarePad_succ_fin]

theorem sum_castSucc_eq_squarePad {t : ℕ}
    (P : Matrix (Fin (t + 1)) (Fin (t + 1)) K)
    (i : Fin (t + 2)) (j : Fin (t + 1)) :
    (∑ a, if i = a.castSucc then P a j else 0) =
      orbitSquarePad P (i.val + 1) j.val := by
  refine Fin.lastCases ?_ (fun a ↦ ?_) i
  · have hne (a : Fin (t + 1)) :
        (Fin.last (t + 1) : Fin (t + 2)) ≠ a.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      have ha := a.isLt
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      omega
    simp [hne, orbitSquarePad]
  · simp [Fin.castSucc_inj, orbitSquarePad_succ_fin]

/-- The previously solved blocks are the blocks of the actual congruence differential. -/
theorem oddOrbitDifferential_blocks (t : ℕ) (H : OddOrbitBlockInput K t) :
    oddOrbitCoefficientBlocks t
      (orbitCongruenceDifferential (oddOrbitMatrices t)
        (fun z ↦ oddOrbitSlotRow t z.2) (fun z ↦ oddOrbitSlotCol t z.2)
        (fun z ↦ oddOrbitBlockMatrix t H z.1 z.2)) =
      oddOrbitBlockMap t H := by
  apply Prod.ext
  · funext z
    cases z with
    | inl p =>
      change ((oddOrbitBlockMatrix t H).transpose * orbitSkewIncidence (K := K) (a := t+1) (b := t+2) Fin.succ +
        orbitSkewIncidence (K := K) (a := t+1) (b := t+2) Fin.succ * oddOrbitBlockMatrix t H)
          (Sum.inl p.val.1) (Sum.inl p.val.2) = _
      exact orbitSkewIncidence_differential_AA H.1.1 H.2.1 H.2.2 H.1.2
        Fin.succ p.val.1 p.val.2
    | inr p =>
      change ((oddOrbitBlockMatrix t H).transpose * orbitSkewIncidence (K := K) (a := t+1) (b := t+2) Fin.castSucc +
        orbitSkewIncidence (K := K) (a := t+1) (b := t+2) Fin.castSucc * oddOrbitBlockMatrix t H)
          (Sum.inl p.val.1) (Sum.inl p.val.2) = _
      exact orbitSkewIncidence_differential_AA H.1.1 H.2.1 H.2.2 H.1.2
        Fin.castSucc p.val.1 p.val.2
  · apply Prod.ext
    · funext z
      cases z with
      | inl p =>
        change ((oddOrbitBlockMatrix t H).transpose * orbitSkewIncidence (K := K) (a := t+1) (b := t+2) Fin.succ +
          orbitSkewIncidence (K := K) (a := t+1) (b := t+2) Fin.succ * oddOrbitBlockMatrix t H)
            (Sum.inr p.val.1) (Sum.inr p.val.2) =
          -(Orbit.rectPad H.2.1 p.val.1.val p.val.2 -
            Orbit.rectPad H.2.1 p.val.2.val p.val.1)
        rw [oddOrbitBlockMatrix, orbitSkewIncidence_differential_BB,
          sum_succ_eq_rectPad, sum_succ_eq_rectPad]
        ring
      | inr p =>
        change ((oddOrbitBlockMatrix t H).transpose * orbitSkewIncidence (K := K) (a := t+1) (b := t+2) Fin.castSucc +
          orbitSkewIncidence (K := K) (a := t+1) (b := t+2) Fin.castSucc * oddOrbitBlockMatrix t H)
            (Sum.inr p.val.1) (Sum.inr p.val.2) =
          -(Orbit.rectPad H.2.1 (p.val.1.val + 1) p.val.2 -
            Orbit.rectPad H.2.1 (p.val.2.val + 1) p.val.1)
        rw [oddOrbitBlockMatrix, orbitSkewIncidence_differential_BB,
          sum_castSucc_eq_rectPad, sum_castSucc_eq_rectPad]
        ring
    · apply Prod.ext
      · ext i j
        change ((oddOrbitBlockMatrix t H).transpose * orbitSkewIncidence (K := K) (a := t+1) (b := t+2) Fin.succ +
          orbitSkewIncidence (K := K) (a := t+1) (b := t+2) Fin.succ * oddOrbitBlockMatrix t H)
            (Sum.inl i) (Sum.inr j) =
          orbitSquarePad H.1.1 j.val i.val + H.1.2 i.succ j
        rw [oddOrbitBlockMatrix, orbitSkewIncidence_differential_AB,
          sum_succ_eq_squarePad]
      · ext i j
        change ((oddOrbitBlockMatrix t H).transpose * orbitSkewIncidence (K := K) (a := t+1) (b := t+2) Fin.castSucc +
          orbitSkewIncidence (K := K) (a := t+1) (b := t+2) Fin.castSucc * oddOrbitBlockMatrix t H)
            (Sum.inl i) (Sum.inr j) =
          orbitSquarePad H.1.1 (j.val + 1) i.val + H.1.2 i.castSucc j
        rw [oddOrbitBlockMatrix, orbitSkewIncidence_differential_AB,
          sum_castSucc_eq_squarePad]

/-- The canonical odd pencil has a surjective differential at the identity. -/
theorem oddOrbit_jacobian_surjective (t : ℕ) :
    (TauCeti.jacobiMatrixAt (oddOrbitPolynomials (K := K) t)
      (orbitIdentityPoint (K := K) (ν := OddOrbitMode t))).mulVec.Surjective := by
  intro y
  obtain ⟨H, hH⟩ := oddOrbitBlockMap_surjective (K := K) t (oddOrbitCoefficientBlocks t y)
  refine ⟨fun z ↦ oddOrbitBlockMatrix t H z.1 z.2, ?_⟩
  change TauCeti.jacobiMatrixAt
    (orbitCongruenceFamily (oddOrbitMatrices t)
      (fun z ↦ oddOrbitSlotRow t z.2) (fun z ↦ oddOrbitSlotCol t z.2))
    (orbitIdentityPoint (K := K) (ν := OddOrbitMode t)) *ᵥ
      (fun z ↦ oddOrbitBlockMatrix t H z.1 z.2) = y
  rw [orbitCongruenceFamily_jacobian]
  apply oddOrbitCoefficientBlocks_injective t
  rw [oddOrbitDifferential_blocks, hH]

theorem oddOrbit_algebraicIndependent (t : ℕ) :
    AlgebraicIndependent K (oddOrbitPolynomials (K := K) t) :=
  TauCeti.algebraicIndependent_of_mulVec_surjective_jacobiMatrixAt
    (oddOrbit_jacobian_surjective t)

/-- The invertible changes of basis already have polynomially dense image. -/
theorem oddOrbit_polynomial_eq_zero_of_vanish [Infinite K] (t : ℕ)
    {q : MvPolynomial (OddOrbitPairSlot t) K}
    (hq : ∀ X : (OddOrbitMode t × OddOrbitMode t) → K,
      eval X (orbitDeterminant (K := K) (ν := OddOrbitMode t)) ≠ 0 →
        eval (fun i ↦ eval X (oddOrbitPolynomials (K := K) t i)) q = 0) :
    q = 0 :=
  polynomial_eq_zero_of_dominant_open_vanish
    (oddOrbit_jacobian_surjective t) (orbitDeterminant_ne_zero (K := K)) hq

end PaperVerification.AlternatingForms
