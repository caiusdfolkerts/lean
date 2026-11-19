module

public import VolumePolynomials.MixedVolumeMultilinearMap
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

set_option autoImplicit false
noncomputable section

/-! The exact ten-term cubic expansion of actual three-dimensional volume.
The factors three and six come from expanding the genuine multilinear map.
The planar seven-term specialization is a consequence of zero pure volumes. -/

open Set MeasureTheory Module
open scoped BigOperators Pointwise

namespace VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

def mixedVolume3 (A B C : ConvexBody E) : ℝ := mixedVolume μ ![A, B, C]

theorem mixedVolume3_swap_first (A B C : ConvexBody E) :
    mixedVolume3 μ B A C = mixedVolume3 μ A B C := by
  first
  | have h := mixedVolume_reindex μ (![A, B, C] : Fin 3 → ConvexBody E) (Equiv.swap 0 1)
    have heq : (fun i => (![A, B, C] : Fin 3 → ConvexBody E) ((Equiv.swap 0 1) i)) =
        ![B, A, C] := by
      funext i
      fin_cases i <;> simp [Equiv.swap_apply_def]
    simpa only [heq, mixedVolume3] using h

theorem mixedVolume3_swap_last (A B C : ConvexBody E) :
    mixedVolume3 μ A C B = mixedVolume3 μ A B C := by
  first
  | have h := mixedVolume_reindex μ (![A, B, C] : Fin 3 → ConvexBody E) (Equiv.swap 1 2)
    have heq : (fun i => (![A, B, C] : Fin 3 → ConvexBody E) ((Equiv.swap 1 2) i)) =
        ![A, C, B] := by
      funext i
      fin_cases i <;> simp [Equiv.swap_apply_def]
    simpa only [heq, mixedVolume3] using h

theorem mixedVolume3_cycle (A B C : ConvexBody E) :
    mixedVolume3 μ B C A = mixedVolume3 μ A B C := by
  first
  | rw [mixedVolume3_swap_last μ B A C, mixedVolume3_swap_first μ A B C]

theorem mixedVolume3_diagonal (hdim : finrank ℝ E = 3) (A : ConvexBody E) :
    mixedVolume3 μ A A A = μ.real (A : Set E) := by
  first
  | have heq : (![A, A, A] : Fin 3 → ConvexBody E) = fun _ => A := by
      funext i
      fin_cases i <;> rfl
    simpa only [mixedVolume3, heq] using mixedVolume_diagonal μ hdim A

def tripleTupleEquiv (ι : Type*) : (Fin 3 → ι) ≃ ι × (ι × ι) where
  toFun f := (f 0, f 1, f 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv p := by cases p; rfl

theorem sum_three_functions {ι : Type*} [Fintype ι] (f : (Fin 3 → ι) → ℝ) :
    (∑ p : Fin 3 → ι, f p) = ∑ a, ∑ b, ∑ c, f ![a, b, c] := by
  first
  | classical
    calc
      _ = ∑ p : ι × (ι × ι), f ![p.1, p.2.1, p.2.2] :=
        Fintype.sum_equiv (tripleTupleEquiv ι) _ _ (fun p =>
          congrArg f ((tripleTupleEquiv ι).left_inv p).symm)
      _ = _ := by simp only [Fintype.sum_prod_type]

theorem mixedVolume_weighted_sum_expansion {n d : ℕ}
    (K : Fin n → ConvexBody E) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) :
    mixedVolume μ (fun _ : Fin d => ∑ i, t i • K i) =
      ∑ p : Fin d → Fin n, (∏ j, t (p j)) * mixedVolume μ (fun j => K (p j)) := by
  first
  | have h := (mixedVolumeMultilinear μ d).map_sum (fun (_ : Fin d) (i : Fin n) => t i • K i)
    rw [mixedVolumeMultilinear_apply] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro p _
    exact mixedVolume_independent_smul μ (fun j => K (p j)) (fun j => t (p j)) (fun j => ht (p j))

theorem trivariate_volume_formula (hdim : finrank ℝ E = 3)
    (A B C : ConvexBody E) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    μ.real (a • A + b • B + c • C : Set E) =
      a ^ 3 * μ.real (A : Set E) + b ^ 3 * μ.real (B : Set E) + c ^ 3 * μ.real (C : Set E) +
      3 * a ^ 2 * b * mixedVolume3 μ A A B +
      3 * a ^ 2 * c * mixedVolume3 μ A A C +
      3 * a * b ^ 2 * mixedVolume3 μ B B A +
      3 * b ^ 2 * c * mixedVolume3 μ B B C +
      3 * a * c ^ 2 * mixedVolume3 μ C C A +
      3 * b * c ^ 2 * mixedVolume3 μ C C B +
      6 * a * b * c * mixedVolume3 μ A B C := by
  first
  | let K : Fin 3 → ConvexBody E := ![A, B, C]
    let t : Fin 3 → ℝ := ![a, b, c]
    have ht : ∀ i, 0 ≤ t i := by intro i; fin_cases i <;> assumption
    have h := mixedVolume_weighted_sum_expansion μ (d := 3) K t ht
    rw [mixedVolume_diagonal μ hdim] at h
    rw [sum_three_functions] at h
    have htuple (i j l : Fin 3) : (fun r => K (![i, j, l] r)) = ![K i, K j, K l] := by
      funext r
      fin_cases r <;> rfl
    simp only [Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, htuple] at h
    change μ.real (a • A + b • B + c • C : Set E) = _ at h
    have hAAA := mixedVolume3_diagonal μ hdim A
    have hBBB := mixedVolume3_diagonal μ hdim B
    have hCCC := mixedVolume3_diagonal μ hdim C
    have hABA := mixedVolume3_swap_last μ A A B
    have hBAA := (mixedVolume3_cycle μ A B A).trans hABA
    have hACA := mixedVolume3_swap_last μ A A C
    have hCAA := (mixedVolume3_cycle μ A C A).trans hACA
    have hBAB := mixedVolume3_swap_last μ B B A
    have hABB := (mixedVolume3_cycle μ B A B).trans hBAB
    have hBCB := mixedVolume3_swap_last μ B B C
    have hCBB := (mixedVolume3_cycle μ B C B).trans hBCB
    have hCAC := mixedVolume3_swap_last μ C C A
    have hACC := (mixedVolume3_cycle μ C A C).trans hCAC
    have hCBC := mixedVolume3_swap_last μ C C B
    have hBCC := (mixedVolume3_cycle μ C B C).trans hCBC
    have hACB := mixedVolume3_swap_last μ A B C
    have hBAC := mixedVolume3_swap_first μ A B C
    have hBCA := mixedVolume3_cycle μ A B C
    have hCAB : mixedVolume3 μ C A B = mixedVolume3 μ A B C :=
      (mixedVolume3_cycle μ B C A).trans hBCA
    have hCBA : mixedVolume3 μ C B A = mixedVolume3 μ A B C :=
      (mixedVolume3_swap_first μ B C A).trans hBCA
    change mixedVolume μ ![A, A, A] = μ.real (A : Set E) at hAAA
    dsimp only [mixedVolume3] at hBBB hCCC hABA hBAA hACA hCAA hBAB hABB hBCB hCBB
    dsimp only [mixedVolume3] at hCAC hACC hCBC hBCC hACB hBAC hBCA hCAB hCBA ⊢
    dsimp only [K, t, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h
    simp only [Matrix.head_cons, Matrix.tail_cons] at h
    rw [hAAA, hBBB, hCCC, hABA, hBAA, hACA, hCAA, hBAB, hABB, hBCB, hCBB,
      hCAC, hACC, hCBC, hBCC, hACB, hBAC, hBCA, hCAB, hCBA] at h
    rw [h]
    ring

theorem trivariate_volume_formula_planar (hdim : finrank ℝ E = 3)
    (A B C : ConvexBody E) (hA : μ.real (A : Set E) = 0)
    (hB : μ.real (B : Set E) = 0) (hC : μ.real (C : Set E) = 0)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    μ.real (a • A + b • B + c • C : Set E) =
      3 * a ^ 2 * b * mixedVolume3 μ A A B +
      3 * a ^ 2 * c * mixedVolume3 μ A A C +
      3 * a * b ^ 2 * mixedVolume3 μ B B A +
      3 * b ^ 2 * c * mixedVolume3 μ B B C +
      3 * a * c ^ 2 * mixedVolume3 μ C C A +
      3 * b * c ^ 2 * mixedVolume3 μ C C B +
      6 * a * b * c * mixedVolume3 μ A B C := by
  first
  | simpa only [hA, hB, hC, mul_zero, zero_add] using
      trivariate_volume_formula μ hdim A B C ha hb hc

end VolumePolynomials
