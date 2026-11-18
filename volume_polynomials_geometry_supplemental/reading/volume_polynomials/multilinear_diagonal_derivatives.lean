module

public import VolumePolynomials.SupportMultilinearVolume
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section
set_option autoImplicit false

/-! # The first two derivatives of a finite symmetric multilinear diagonal

Continuity is proved by an explicit finite coordinate expansion. The
derivative formula then follows from Mathlib's genuine derivative of a
continuous multilinear map. Symmetry identifies every summand, giving the
exact factors `n` and `n (n-1)` without an informal coefficient comparison.
-/

noncomputable section
open Set
open scoped BigOperators

namespace VolumePolynomials.MultilinearDiagonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem cons_const {V : Type*} (p : V) (n : ℕ) :
    Fin.cons p (fun _ : Fin n => p) = (fun _ : Fin (n + 1) => p) :=
  Fin.cons_self_tail (fun _ : Fin (n + 1) => p)

theorem coordinate_expansion {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin n => ι → ℝ) ℝ)
    (x : Fin n → ι → ℝ) :
    F x = ∑ r : Fin n → ι, (∏ i, x i (r i)) * F (fun i => Pi.single (r i) 1) := by
  first
  | calc
      F x = F (fun i => ∑ j, x i j • Pi.single j 1) := by
        congr 1
        funext i
        exact pi_eq_sum_univ' (x i)
      _ = ∑ r : Fin n → ι, F (fun i => x i (r i) • Pi.single (r i) 1) :=
        F.map_sum (fun i j => x i j • Pi.single j 1)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r _
        exact F.map_smul_univ (fun i => x i (r i)) (fun i => Pi.single (r i) 1)

theorem continuous {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin n => ι → ℝ) ℝ) : Continuous F := by
  first
  | have he : (F : (Fin n → ι → ℝ) → ℝ) =
        fun x => ∑ r : Fin n → ι, (∏ i, x i (r i)) * F (fun i => Pi.single (r i) 1) :=
      funext (coordinate_expansion F)
    rw [he]
    apply continuous_finsetSum
    intro r _
    apply Continuous.mul _ continuous_const
    exact continuous_finsetProd _ (fun i _ => (continuous_apply (r i)).comp (continuous_apply i))

def toContinuous {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin n => ι → ℝ) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => ι → ℝ) ℝ :=
  ⟨F, continuous F⟩

def PermutationSymmetric {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) : Prop :=
  ∀ x : Fin n → V, ∀ e : Equiv.Perm (Fin n), F (fun j => x (e j)) = F x

def liftPermutation {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.cons 0 (fun i => (e i).succ)
  invFun := Fin.cons 0 (fun i => (e.symm i).succ)
  left_inv i := by
    first
    | exact Fin.cases rfl (fun j => by simp only [Fin.cons_succ, Equiv.symm_apply_apply]) i
  right_inv i := by
    first
    | exact Fin.cases rfl (fun j => by simp only [Fin.cons_succ, Equiv.apply_symm_apply]) i

theorem PermutationSymmetric.curryLeft
    {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    {F : MultilinearMap ℝ (fun _ : Fin (n + 1) => V) ℝ}
    (hF : PermutationSymmetric F) (a : V) : PermutationSymmetric (F.curryLeft a) := by
  first
  | intro x e
    have he : (fun j : Fin (n + 1) =>
        (Fin.cons a x : Fin (n + 1) → V) (liftPermutation e j)) =
        (Fin.cons a (fun j : Fin n => x (e j)) : Fin (n + 1) → V) := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    have h := hF (Fin.cons a x) (liftPermutation e)
    rw [he] at h
    exact h

theorem PermutationSymmetric.update_const
    {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    {F : MultilinearMap ℝ (fun _ : Fin (n + 1) => V) ℝ}
    (hF : PermutationSymmetric F) (p x : V) (i : Fin (n + 1)) :
    F (Function.update (fun _ => p) i x) = F (Fin.cons x (fun _ => p)) := by
  first
  | have he := hF (Function.update (fun _ => p) i x) (Equiv.swap 0 i)
    change F ((Function.update (fun _ => p) i x) ∘ Equiv.swap 0 i) = _ at he
    rw [Function.update_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_right] at he
    have ht : Function.update ((fun _ : Fin (n + 1) => p) ∘ Equiv.swap 0 i) 0 x =
        Fin.cons x (fun _ : Fin n => p) := by
      funext j
      exact Fin.cases (by simp) (fun k => by simp [Function.comp_def]) j
    rw [ht] at he
    exact he.symm

theorem PermutationSymmetric.swap_first_two
    {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    {F : MultilinearMap ℝ (fun _ : Fin (n + 2) => V) ℝ}
    (hF : PermutationSymmetric F) (x y : V) (H : Fin n → V) :
    F (Fin.cons x (Fin.cons y H)) = F (Fin.cons y (Fin.cons x H)) := by
  first
  | have he := hF (Fin.cons x (Fin.cons y H)) (Equiv.swap 0 1)
    change F ((Matrix.vecCons x (Matrix.vecCons y H)) ∘ Equiv.swap 0 1) = _ at he
    rw [Matrix.cons_cons_comp_swap_zero_one] at he
    exact he.symm

theorem PermutationSymmetric.rotate_first_three
    {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    {F : MultilinearMap ℝ (fun _ : Fin (n + 3) => V) ℝ}
    (hF : PermutationSymmetric F) (x y h : V) (H : Fin n → V) :
    F (Fin.cons x (Fin.cons y (Fin.cons h H))) =
      F (Fin.cons h (Fin.cons x (Fin.cons y H))) := by
  first
  | calc
      _ = F (Fin.cons x (Fin.cons h (Fin.cons y H))) :=
        (hF.curryLeft x).swap_first_two y h H
      _ = _ := hF.swap_first_two x h (Fin.cons y H)

theorem hasDerivAt_diagonal {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (n + 1) => ι → ℝ) ℝ)
    (hF : PermutationSymmetric F) (p x : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (fun _ => p + s • x))
      (((n + 1 : ℕ) : ℝ) * F (Fin.cons x (fun _ => p + t • x))) t := by
  first
  | have hcurve : HasDerivAt (fun s : ℝ => (fun _ : Fin (n + 1) => p + s • x))
        (fun _ => x) t := by
      apply hasDerivAt_pi.mpr
      intro i
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const x).const_add p
    have hd := (toContinuous F).hasFDerivAt (fun _ => p + t • x)
    have he := hd.comp_hasDerivAt t hcurve
    simp only [Function.comp_def, ContinuousMultilinearMap.linearDeriv_apply] at he
    change HasDerivAt (fun s : ℝ => F (fun _ : Fin (n + 1) => p + s • x))
      (∑ i : Fin (n + 1), F (Function.update (fun _ => p + t • x) i x)) t at he
    simpa only [hF.update_const, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using he

theorem hasDerivAt_first_diagonal_derivative {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (n + 2) => ι → ℝ) ℝ)
    (hF : PermutationSymmetric F) (p x : ι → ℝ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => ((n + 2 : ℕ) : ℝ) * F (Fin.cons x (fun _ => p + s • x)))
      (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1) *
        F (Fin.cons x (Fin.cons x (fun _ => p + t • x)))) t := by
  first
  | have hd := HasDerivAt.const_mul (((n + 2 : ℕ) : ℝ))
      (hasDerivAt_diagonal (F.curryLeft x) (hF.curryLeft x) p x t)
    convert hd using 1 <;> simp only [MultilinearMap.curryLeft_apply]
    push_cast
    ring

end VolumePolynomials.MultilinearDiagonal
