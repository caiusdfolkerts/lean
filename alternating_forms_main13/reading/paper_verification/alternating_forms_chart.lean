module

public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Prod
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-!
# The linear kernel in the odd common-isotropic chart

Section 4.4 of the source paper identifies the chart map from `Hom(B,A)` to a
pair of alternating forms on `B`.  Its kernel is described by a rectangular
array, padded by zero rows, which is symmetric in two consecutive ways.  The
following theorem proves, for every size, that this kernel is zero.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

/-- The complete boundary-propagation argument for the kernel in Section 4.4.
It does not use division and is valid over every coefficient type with zero. -/
theorem chart_kernel_zero {K : Type*} [Zero K] (k : ℕ) (T : ℕ → ℕ → K)
    (hfirst : ∀ j ≤ k, T 0 j = 0)
    (hlast : ∀ j ≤ k, T (k + 1) j = 0)
    (hsymmetric : ∀ i ≤ k, ∀ j ≤ k, T i j = T j i)
    (hshifted : ∀ i ≤ k, ∀ j ≤ k, T (i + 1) j = T (j + 1) i) :
    ∀ i ≤ k + 1, ∀ j ≤ k, T i j = 0 := by
  intro i
  induction i with
  | zero =>
      intro _ j hj
      exact hfirst j hj
  | succ i ih =>
      intro hi j hj
      have hik : i ≤ k := by omega
      by_cases hjk : j < k
      · calc
          T (i + 1) j = T (j + 1) i := hshifted i hik j hj
          _ = T i (j + 1) := hsymmetric (j + 1) (by omega) i hik
          _ = 0 := ih (by omega) (j + 1) (by omega)
      · have hjeq : j = k := by omega
        subst j
        exact (hshifted i hik k le_rfl).trans (hlast i hik)

/-- Independent coordinates of an alternating form on `K^m`. -/
abbrev StrictPairs (m : ℕ) := {p : Fin m × Fin m // p.1 < p.2}

/-- Pad a `k` by `k+1` matrix by its two zero boundary rows. -/
def chartPad {K : Type*} [Zero K] {k : ℕ}
    (T : Fin k → Fin (k + 1) → K) (i j : ℕ) : K :=
  if h : 0 < i ∧ i ≤ k ∧ j ≤ k then
    T ⟨i - 1, by omega⟩ ⟨j, by omega⟩
  else 0

@[simp] theorem chartPad_first {K : Type*} [Zero K] {k : ℕ}
    (T : Fin k → Fin (k + 1) → K) (j : ℕ) : chartPad T 0 j = 0 := by
  simp [chartPad]

@[simp] theorem chartPad_last {K : Type*} [Zero K] {k : ℕ}
    (T : Fin k → Fin (k + 1) → K) (j : ℕ) : chartPad T (k + 1) j = 0 := by
  simp [chartPad]

@[simp] theorem chartPad_entry {K : Type*} [Zero K] {k : ℕ}
    (T : Fin k → Fin (k + 1) → K) (i : Fin k) (j : Fin (k + 1)) :
    chartPad T (i.val + 1) j.val = T i j := by
  have h : 0 < i.val + 1 ∧ i.val + 1 ≤ k ∧ j.val ≤ k := by
    have := i.isLt
    have := j.isLt
    omega
  simp [chartPad, h]

section LinearChart

variable {K : Type*} [Field K] {k : ℕ}

theorem chartPad_add (T U : Fin k → Fin (k + 1) → K) (i j : ℕ) :
    chartPad (T + U) i j = chartPad T i j + chartPad U i j := by
  simp only [chartPad]
  split_ifs <;> simp

theorem chartPad_smul (c : K) (T : Fin k → Fin (k + 1) → K) (i j : ℕ) :
    chartPad (c • T) i j = c • chartPad T i j := by
  simp only [chartPad]
  split_ifs <;> simp

/-- The explicit full-space chart map, in the independent upper-triangular
coordinates of its two alternating-form targets. -/
def chartMap (k : ℕ) : (Fin k → Fin (k + 1) → K) →ₗ[K]
    ((StrictPairs (k + 1) → K) × (StrictPairs (k + 1) → K)) where
  toFun T :=
    (fun p => chartPad T p.1.1.val p.1.2.val - chartPad T p.1.2.val p.1.1.val,
     fun p => chartPad T (p.1.1.val + 1) p.1.2.val -
       chartPad T (p.1.2.val + 1) p.1.1.val)
  map_add' T U := by
    apply Prod.ext <;> funext p <;> dsimp <;> rw [chartPad_add, chartPad_add] <;> abel
  map_smul' c T := by
    apply Prod.ext <;> funext p <;> dsimp <;> rw [chartPad_smul, chartPad_smul] <;>
      simp only [smul_eq_mul, mul_sub]

private theorem symmetric_of_strict_coordinates (m : ℕ) (A : Fin m → Fin m → K)
    (h : ∀ p : StrictPairs m, A p.1.1 p.1.2 - A p.1.2 p.1.1 = 0) :
    ∀ i j, A i j = A j i := by
  intro i j
  rcases lt_trichotomy i j with hij | hij | hij
  · exact sub_eq_zero.mp (h ⟨(i, j), hij⟩)
  · subst j
    rfl
  · exact (sub_eq_zero.mp (h ⟨(j, i), hij⟩)).symm

theorem chartMap_eq_zero (T : Fin k → Fin (k + 1) → K)
    (hT : chartMap k T = 0) : T = 0 := by
  have hfirst : ∀ i j : Fin (k + 1),
      chartPad T i.val j.val = chartPad T j.val i.val := by
    apply symmetric_of_strict_coordinates
    intro p
    exact congrArg (fun Z => Z.1 p) hT
  have hsecond : ∀ i j : Fin (k + 1),
      chartPad T (i.val + 1) j.val = chartPad T (j.val + 1) i.val := by
    apply symmetric_of_strict_coordinates
    intro p
    exact congrArg (fun Z => Z.2 p) hT
  have hz := chart_kernel_zero k (chartPad T)
    (fun j _ => chartPad_first T j) (fun j _ => chartPad_last T j)
    (fun i hi j hj => hfirst ⟨i, by omega⟩ ⟨j, by omega⟩)
    (fun i hi j hj => hsecond ⟨i, by omega⟩ ⟨j, by omega⟩)
  funext i j
  have h := hz (i.val + 1) (by have := i.isLt; omega) j.val
    (by have := j.isLt; omega)
  simpa only [chartPad_entry, Pi.zero_apply] using h

theorem chartMap_injective (k : ℕ) : Function.Injective (chartMap (K := K) k) := by
  intro T U hTU
  apply sub_eq_zero.mp
  apply chartMap_eq_zero
  rw [map_sub, hTU, sub_self]

theorem card_strictPairs (m : ℕ) : Fintype.card (StrictPairs m) = m.choose 2 := by
  classical
  simpa [StrictPairs, Fintype.subtype_card] using
    (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin m))))

theorem chartMap_dimensions (k : ℕ) :
    Module.finrank K (Fin k → Fin (k + 1) → K) =
      Module.finrank K ((StrictPairs (k + 1) → K) × (StrictPairs (k + 1) → K)) := by
  classical
  rw [Module.finrank_pi_fintype, Module.finrank_prod]
  simp only [Module.finrank_pi, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, card_strictPairs]
  simpa [Nat.choose_one_right, Nat.mul_comm, two_mul] using
    (Nat.add_one_mul_choose_eq k 1)

/-- The coordinate map of Section 4.4 is an isomorphism in every size, over an
arbitrary field.  In particular, the characteristic-zero statement is proved
without an assumption of full rank. -/
theorem chartMap_bijective (k : ℕ) : Function.Bijective (chartMap (K := K) k) :=
  ⟨chartMap_injective k,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (chartMap_dimensions (K := K) k)).mp (chartMap_injective k)⟩

noncomputable def chartEquiv (k : ℕ) :
    (Fin k → Fin (k + 1) → K) ≃ₗ[K]
      ((StrictPairs (k + 1) → K) × (StrictPairs (k + 1) → K)) :=
  LinearEquiv.ofBijective (chartMap k) (chartMap_bijective k)

end LinearChart

end PaperVerification.AlternatingForms
