module

public import Recovery.Unimodular.FlagKoszul.CoefficientModuleBar
public import Mathlib.Data.Finset.Card

/-!
# Exact coefficient maps and the Koszul-filtration induction

Surjections and exact kernels are proved to survive passage to finite word
vectors. The induction theorem is purely logical: its three premises are
subsequently discharged by the actual quotient-module bar construction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Unimodular.FlagKoszul.CoefficientModuleBar

open PaperVerification.NoncommutativeBar

variable {A I M N P : Type*} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P] [Module A P]

@[simp] theorem map_apply (f : M →ₗ[A] N) (z : Words I M) (L : List I) :
    map f z L = f (z L) := rfl

theorem map_injective (f : M →ₗ[A] N) (hf : Function.Injective f) :
    Function.Injective (map f (I := I)) := by
  intro x y h
  ext L
  exact hf (congrArg (fun z : Words I N => z L) h)

theorem map_surjective (f : M →ₗ[A] N) (hf : Function.Surjective f) :
    Function.Surjective (map f (I := I)) := by
  intro z
  induction z using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add z w hz hw =>
    obtain ⟨x, hx⟩ := hz
    obtain ⟨y, hy⟩ := hw
    exact ⟨x + y, by rw [map_add, hx, hy]⟩
  | single L n =>
    obtain ⟨m, hm⟩ := hf n
    exact ⟨Finsupp.single L m, by rw [map_single, hm]⟩

theorem map_kernel_preimage (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hfg : ∀ n, g n = 0 → ∃ m, f m = n)
    (z : Words I N) (hz : map g z = 0) : ∃ w, map f w = z := by
  classical
  apply LinearMap.mem_range.mp
  rw [← Finsupp.sum_single z, Finsupp.sum]
  apply Submodule.sum_mem
  intro L hL
  have hg : g (z L) = 0 := congrArg (fun x : Words I P => x L) hz
  obtain ⟨m, hm⟩ := hfg (z L) hg
  exact ⟨Finsupp.single L m, by rw [map_single, hm]⟩

theorem map_comp_zero (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hfg : ∀ m, g (f m) = 0) (z : Words I M) : map g (map f z) = 0 := by
  ext L
  exact hfg (z L)

#print axioms map_kernel_preimage

end Unimodular.FlagKoszul.CoefficientModuleBar

namespace Unimodular.FlagKoszul.KoszulFiltration

variable {E : Type*} [DecidableEq E]

/-- Lexicographic induction on bar degree and the number of variable generators.
The colon term may contain any finite set of variables; its lower bar degree
is what makes the induction well founded. -/
theorem induction
    (P : Finset E → ℕ → ℕ → Prop) (colon : Finset E → E → Finset E)
    (hzero : ∀ S N, 0 < N → P S 0 N)
    (hempty : ∀ r N, r < N → P ∅ r N)
    (hinsert : ∀ S j r N, j ∉ S → r + 1 < N →
      P S (r + 1) N → P (colon S j) r (N - 1) → P (insert j S) (r + 1) N) :
    ∀ S r N, r < N → P S r N := by
  intro S r
  induction r generalizing S with
  | zero => exact hzero S
  | succ r ih =>
    intro N hN
    induction S using Finset.induction_on with
    | empty => exact hempty (r + 1) N hN
    | @insert j S hj hS =>
      exact hinsert S j r N hj hN hS (ih (colon S j) (N - 1) (by omega))

#print axioms induction

end Unimodular.FlagKoszul.KoszulFiltration
