module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.SplitIfs
public import Lean.Elab.Tactic.Omega

/-!
# The rectangular chart map used in the odd pencil orbit

A k by (k+1) matrix is determined by the alternating parts of its two consecutive
square paddings. The proof is elementary: the kernel recurrence moves every entry
toward the first row or last column, both of which vanish.
-/

@[expose] public section
noncomputable section

namespace PaperVerification.AlternatingForms.Orbit

open Matrix

abbrev StrictPair (n : ℕ) :=
  {p : Fin n × Fin n // p.1 < p.2}

/-- Two strict triangles have the same size as a k by (k+1) rectangle. -/
def rectanglePairEquiv (k : ℕ) :
    (Fin k × Fin (k + 1)) ≃ (StrictPair (k + 1) ⊕ StrictPair (k + 1)) where
  toFun z := if h : z.1.val < z.2.val then
      Sum.inl ⟨(z.1.castSucc, z.2), h⟩
    else Sum.inr ⟨(z.2, z.1.succ), by
      change z.2.val < z.1.val + 1
      omega⟩
  invFun z := match z with
    | Sum.inl p =>
      (⟨p.val.1.val, by have := p.property; have := p.val.2.isLt; omega⟩, p.val.2)
    | Sum.inr p =>
      (⟨p.val.2.val - 1, by have := p.property; have := p.val.2.isLt; omega⟩, p.val.1)
  left_inv z := by
    rcases z with ⟨i, j⟩
    dsimp
    split_ifs with h
    · apply Prod.ext
      · apply Fin.ext
        rfl
      · rfl
    · apply Prod.ext
      · apply Fin.ext
        simp
      · rfl
  right_inv z := by
    rcases z with p | p
    · rcases p with ⟨⟨i, j⟩, hij⟩
      change i.val < j.val at hij
      dsimp
      rw [dif_pos hij]
    · rcases p with ⟨⟨i, j⟩, hij⟩
      change i.val < j.val at hij
      have hj : 0 < j.val := by omega
      have h : ¬ j.val - 1 < i.val := by omega
      dsimp
      rw [dif_neg h]
      congr 1
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simp only [Fin.val_succ, Fin.val_mk]
        omega

variable {K : Type*} [Field K] {k : ℕ}

/-- One-based row padding, with zero rows at 0 and k+1. -/
def rectPad (Q : Matrix (Fin k) (Fin (k + 1)) K) (r : ℕ)
    (j : Fin (k + 1)) : K :=
  if h : 0 < r ∧ r ≤ k then Q ⟨r - 1, by omega⟩ j else 0

@[simp]
theorem rectPad_zero (Q : Matrix (Fin k) (Fin (k + 1)) K) (j : Fin (k + 1)) :
    rectPad Q 0 j = 0 := by
  simp [rectPad]

@[simp]
theorem rectPad_last (Q : Matrix (Fin k) (Fin (k + 1)) K) (j : Fin (k + 1)) :
    rectPad Q (k + 1) j = 0 := by
  simp [rectPad]

@[simp]
theorem rectPad_succ (Q : Matrix (Fin k) (Fin (k + 1)) K)
    (i : Fin k) (j : Fin (k + 1)) :
    rectPad Q (i.val + 1) j = Q i j := by
  have hi : 0 < i.val + 1 ∧ i.val + 1 ≤ k := by omega
  simp only [rectPad, dif_pos hi, Nat.add_sub_cancel]

theorem rectPad_add (Q T : Matrix (Fin k) (Fin (k + 1)) K)
    (r : ℕ) (j : Fin (k + 1)) :
    rectPad (Q + T) r j = rectPad Q r j + rectPad T r j := by
  by_cases h : 0 < r ∧ r ≤ k <;> simp [rectPad, h]

theorem rectPad_smul (a : K) (Q : Matrix (Fin k) (Fin (k + 1)) K)
    (r : ℕ) (j : Fin (k + 1)) :
    rectPad (a • Q) r j = a * rectPad Q r j := by
  by_cases h : 0 < r ∧ r ≤ k <;> simp [rectPad, h, smul_eq_mul]

/-- The alternating parts of the two consecutive square paddings. -/
def rectangleChart (k : ℕ) :
    Matrix (Fin k) (Fin (k + 1)) K →ₗ[K]
      ((StrictPair (k + 1) ⊕ StrictPair (k + 1)) → K) where
  toFun Q := Sum.elim
    (fun p ↦ rectPad Q p.val.1.val p.val.2 - rectPad Q p.val.2.val p.val.1)
    (fun p ↦ rectPad Q (p.val.1.val + 1) p.val.2 -
      rectPad Q (p.val.2.val + 1) p.val.1)
  map_add' Q T := by
    funext p
    cases p <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, rectPad_add] <;> ring
  map_smul' a Q := by
    funext p
    cases p <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, rectPad_smul] <;> ring

/-- No nonzero rectangle has both padded alternating parts zero. -/
theorem rectangleChart_eq_zero (Q : Matrix (Fin k) (Fin (k + 1)) K)
    (hQ : rectangleChart (K := K) k Q = 0) : Q = 0 := by
  have hfirst (i j : Fin (k + 1)) : rectPad Q i.val j = rectPad Q j.val i := by
    rcases lt_trichotomy i j with hij | hij | hji
    · have h := congrFun hQ (Sum.inl ⟨(i, j), hij⟩)
      exact sub_eq_zero.mp h
    · subst j
      rfl
    · have h := congrFun hQ (Sum.inl ⟨(j, i), hji⟩)
      exact (sub_eq_zero.mp h).symm
  have hsecond (i j : Fin (k + 1)) :
      rectPad Q (i.val + 1) j = rectPad Q (j.val + 1) i := by
    rcases lt_trichotomy i j with hij | hij | hji
    · have h := congrFun hQ (Sum.inr ⟨(i, j), hij⟩)
      exact sub_eq_zero.mp h
    · subst j
      rfl
    · have h := congrFun hQ (Sum.inr ⟨(j, i), hji⟩)
      exact (sub_eq_zero.mp h).symm
  have hzero : ∀ r : ℕ, r ≤ k → ∀ j : Fin (k + 1), rectPad Q r j = 0 := by
    intro r
    induction r with
    | zero =>
      intro _ j
      exact rectPad_zero Q j
    | succ r ih =>
      intro hr j
      let i : Fin (k + 1) := ⟨r, by omega⟩
      by_cases hj : j.val = k
      · calc
          rectPad Q (r + 1) j = rectPad Q (k + 1) i := by
            simpa only [i, Fin.val_mk, hj] using hsecond i j
          _ = 0 := rectPad_last Q i
      · let j' : Fin (k + 1) := ⟨j.val + 1, by have := j.isLt; omega⟩
        calc
          rectPad Q (r + 1) j = rectPad Q (j.val + 1) i := hsecond i j
          _ = rectPad Q r j' := hfirst j' i
          _ = 0 := ih (by omega) j'
  ext i j
  simpa only [rectPad_succ, Matrix.zero_apply] using
    hzero (i.val + 1) (by have := i.isLt; omega) j

theorem rectangleChart_injective (k : ℕ) :
    Function.Injective (rectangleChart (K := K) k) := by
  intro Q T h
  apply sub_eq_zero.mp
  apply rectangleChart_eq_zero
  rw [map_sub, h, sub_self]

/-- The chart map is an isomorphism in every size, over every field. -/
theorem rectangleChart_surjective (k : ℕ) :
    Function.Surjective (rectangleChart (K := K) k) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := rectangleChart (K := K) k) ?_).mp (rectangleChart_injective k)
  have hc := Fintype.card_congr (rectanglePairEquiv k)
  calc
    Module.finrank K (Matrix (Fin k) (Fin (k + 1)) K) = k * (k + 1) := by
      change Module.finrank K (Fin k → Fin (k + 1) → K) = _
      simp [Module.finrank_pi_fintype]
    _ = Fintype.card (StrictPair (k + 1) ⊕ StrictPair (k + 1)) := by
      simpa only [Fintype.card_prod, Fintype.card_fin] using hc
    _ = Module.finrank K ((StrictPair (k + 1) ⊕ StrictPair (k + 1)) → K) := by
      rw [Module.finrank_fintype_fun_eq_card]

def rectangleChartEquiv (k : ℕ) :
    Matrix (Fin k) (Fin (k + 1)) K ≃ₗ[K]
      ((StrictPair (k + 1) ⊕ StrictPair (k + 1)) → K) :=
  LinearEquiv.ofBijective (rectangleChart k)
    ⟨rectangleChart_injective k, rectangleChart_surjective k⟩

end PaperVerification.AlternatingForms.Orbit
