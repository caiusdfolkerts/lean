module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ext

@[expose] public section

/-!
The arbitrary-length coefficient propagation in §3.2. This module proves the
complete displayed homogeneous system has exactly one scalar of freedom; it does
not by itself assert the polytope theorem before the slack/coordinate bridge.
-/
noncomputable section
namespace GraphicalZonotopes
namespace Path

@[ext] structure Coordinates (n : ℕ) where
  edge1 : Fin (n - 1) → ℝ
  edge2 : Fin (n - 2) → ℝ
  edge3 : Fin (n - 3) → ℝ
  tri012 : Fin (n - 2) → ℝ
  tri013 : Fin (n - 3) → ℝ
  tri023 : Fin (n - 3) → ℝ
  tetra : Fin (n - 3) → ℝ

def scale (n : ℕ) (a : ℝ) : Coordinates n where
  edge1 := fun _ => 0
  edge2 := fun _ => 0
  edge3 := fun _ => 0
  tri012 := fun _ => a
  tri013 := fun _ => 0
  tri023 := fun _ => a
  tetra := fun _ => -a

def Tight (n : ℕ) (y : Coordinates n) : Prop :=
  (∀ i, y.edge1 i = 0) ∧ (∀ i, y.edge2 i = 0) ∧ (∀ i, y.edge3 i = 0) ∧
  ∀ i : Fin (n - 3),
    y.edge3 i + y.tri013 i = 0 ∧
    y.edge1 ⟨i.val, by omega⟩ + y.tri012 ⟨i.val, by omega⟩ + y.tri013 i + y.tetra i = 0 ∧
    y.edge2 ⟨i.val + 1, by omega⟩ + y.tri013 i + y.tri012 ⟨i.val + 1, by omega⟩ + y.tetra i = 0 ∧
    y.edge3 i + y.tri013 i + y.tri023 i + y.tetra i = 0

theorem scale_tight (n : ℕ) (a : ℝ) : Tight n (scale n a) := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_⟩
  intro i
  simp [scale]

/-- The displayed zero equations in the paper have a one-dimensional solution
space for every allowed path size, including both endpoints. -/
theorem tight_eq_scale {n : ℕ} (hn : 4 ≤ n) {y : Coordinates n} (hy : Tight n y) :
    y = scale n (y.tri012 ⟨0, by omega⟩) := by
  let a := y.tri012 ⟨0, by omega⟩
  have hu : ∀ i, y.tri013 i = 0 := by
    intro i
    have h := (hy.2.2.2 i).1
    rw [hy.2.2.1 i] at h
    linarith
  have htstep : ∀ i : Fin (n - 3),
      y.tri012 ⟨i.val, by omega⟩ = y.tri012 ⟨i.val + 1, by omega⟩ := by
    intro i
    have h1 := (hy.2.2.2 i).2.1
    have h2 := (hy.2.2.2 i).2.2.1
    rw [hy.1, hu] at h1
    rw [hy.2.1, hu] at h2
    linarith
  have ht : ∀ i : Fin (n - 2), y.tri012 i = a := by
    have aux : ∀ k : ℕ, ∀ hk : k < n - 2, y.tri012 ⟨k, hk⟩ = a := by
      intro k
      induction k with
      | zero => intro hk; rfl
      | succ k ih =>
        intro hk
        have hkn : k < n - 3 := by omega
        have hp := htstep ⟨k, hkn⟩
        have hi := ih (by omega)
        exact hp.symm.trans hi
    intro i
    exact aux i.val i.isLt
  have hh : ∀ i, y.tetra i = -a := by
    intro i
    have h := (hy.2.2.2 i).2.1
    rw [hy.1, ht, hu] at h
    linarith
  have hv : ∀ i, y.tri023 i = a := by
    intro i
    have h := (hy.2.2.2 i).2.2.2
    rw [hy.2.2.1, hu, hh] at h
    linarith
  apply Coordinates.ext
  · funext i; exact hy.1 i
  · funext i; exact hy.2.1 i
  · funext i; exact hy.2.2.1 i
  · funext i; exact ht i
  · funext i; exact hu i
  · funext i; exact hv i
  · funext i; exact hh i

theorem tight_iff_exists_scale {n : ℕ} (hn : 4 ≤ n) (y : Coordinates n) :
    Tight n y ↔ ∃ a : ℝ, y = scale n a := by
  constructor
  · intro hy
    exact ⟨_, tight_eq_scale hn hy⟩
  · rintro ⟨a, rfl⟩
    exact scale_tight n a

theorem scale_injective {n : ℕ} (hn : 4 ≤ n) : Function.Injective (scale n) := by
  intro a b hab
  have h := congrArg (fun y => y.tri012 ⟨0, by omega⟩) hab
  exact h

end Path
end GraphicalZonotopes
