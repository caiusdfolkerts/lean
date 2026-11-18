module

public import VolumePolynomials.HolonomyCoordinates
public import VolumePolynomials.HolonomySeries
public import Mathlib.Tactic.Abel

@[expose] public section
noncomputable section

open Set
open scoped Pointwise

namespace VolumePolynomials.Holonomy

/-- Linear maps carry actual translates to translates by the image vector. -/
theorem linear_image_vadd
    {E F T : Type*} [AddCommGroup E] [AddCommGroup F]
    [FunLike T E F] [AddMonoidHomClass T E F]
    (f : T) (v : E) (S : Set E) :
    f '' (v +ᵥ S) = f v +ᵥ f '' S := by
  first
  | simp only [← Set.image_vadd, Set.image_image, Function.comp_apply,
      vadd_eq_add, map_add]

def lastTransport (lam : ℝ) : Plane →L[ℝ] Plane :=
  lam • transport20.toContinuousLinearMap

@[simp] theorem lastTransport_apply (lam : ℝ) (p : Plane) :
    lastTransport lam p = lam • transport20 p := rfl

theorem image_transport_cycle (lam : ℝ) (A : Set Plane) :
    lastTransport lam '' (transport12 '' (transport01 '' A)) = scaledReturn lam '' A := by
  first
  | simp only [Set.image_image]
    congr 1
    funext p
    change lam • transport20 (transport12 (transport01 p)) = lam • returnMap p
    rw [transport_cycle]

/-- The three projected translation relations give exactly the affine return
equation, including all translation terms. -/
theorem projection_cycle_affine (lam : ℝ) (A B C S : Set Plane) (b c d : Plane)
    (hB : B = b +ᵥ transport01 '' A)
    (hC : C = c +ᵥ transport12 '' B)
    (hLast : A = d +ᵥ (S + lastTransport lam '' C)) :
    ∃ q : Plane, A = q +ᵥ (S + scaledReturn lam '' A) := by
  first
  | refine ⟨d + (lastTransport lam c + lastTransport lam (transport12 b)), ?_⟩
    rw [hC, hB] at hLast
    simpa only [linear_image_vadd, vadd_vadd, vadd_eq_add, add_vadd_comm,
      map_add, image_transport_cycle] using hLast

/-- Translating by the explicitly solved center removes the affine term. -/
theorem recenter_affine_equation (lam : ℝ) (A S : Set Plane) (q : Plane)
    (hA : A = q +ᵥ (S + scaledReturn lam '' A)) :
    -translationCenter lam q +ᵥ A =
      S + scaledReturn lam '' (-translationCenter lam q +ᵥ A) := by
  first
  | let c := translationCenter lam q
    have hc : -c + q = scaledReturn lam (-c) := by
      have ht := translationCenter_equation lam q
      change c - scaledReturn lam c = q at ht
      rw [← ht, map_neg]
      abel
    calc
      -c +ᵥ A = -c +ᵥ (q +ᵥ (S + scaledReturn lam '' A)) := congrArg (-c +ᵥ ·) hA
      _ = (-c + q) +ᵥ (S + scaledReturn lam '' A) := by
        simp only [vadd_vadd, vadd_eq_add]
      _ = scaledReturn lam (-c) +ᵥ (S + scaledReturn lam '' A) := by rw [hc]
      _ = S + (scaledReturn lam (-c) +ᵥ scaledReturn lam '' A) := by
        rw [add_vadd_comm]
      _ = S + scaledReturn lam '' (-c +ᵥ A) := by rw [linear_image_vadd]

/-- Every nonempty compact solution of the affine return equation is a translate
of the actual infinite Minkowski series. -/
theorem affine_solution_is_forced (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1)
    (A : Set Plane) (hAc : IsCompact A) (hAn : A.Nonempty)
    (q : Plane)
    (hA : A = q +ᵥ (centeredSegment (1, 0) + scaledReturn lam '' A)) :
    A = translationCenter lam q +ᵥ (forcedBody lam hlam₀ hlam₁ : Set Plane) := by
  first
  | have heq := forcedBody_unique lam hlam₀ hlam₁
      (-translationCenter lam q +ᵥ A)
      (hAc.vadd (-translationCenter lam q))
      hAn.vadd_set
      (recenter_affine_equation lam A (centeredSegment (1, 0)) q hA)
    rw [← heq]
    simp only [vadd_vadd, vadd_eq_add, add_neg_cancel, zero_vadd]

/-- Full three-plane conclusion after the projected equality cases have been
established: the three bodies are simultaneous translates of Kλ and its two
prescribed linear images. -/
theorem projection_cycle_forces_three_bodies
    (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1)
    (A B C : Set Plane) (hAc : IsCompact A) (hAn : A.Nonempty)
    (b c d : Plane)
    (hB : B = b +ᵥ transport01 '' A)
    (hC : C = c +ᵥ transport12 '' B)
    (hLast : A = d +ᵥ (centeredSegment (1, 0) + lastTransport lam '' C)) :
    ∃ a₀ b₀ c₀ : Plane,
      A = a₀ +ᵥ (forcedBody lam hlam₀ hlam₁ : Set Plane) ∧
      B = b₀ +ᵥ transport01 '' (forcedBody lam hlam₀ hlam₁ : Set Plane) ∧
      C = c₀ +ᵥ transport12 ''
        (transport01 '' (forcedBody lam hlam₀ hlam₁ : Set Plane)) := by
  first
  | obtain ⟨q, hq⟩ := projection_cycle_affine lam A B C (centeredSegment (1, 0))
      b c d hB hC hLast
    let a₀ := translationCenter lam q
    have hA := affine_solution_is_forced lam hlam₀ hlam₁ A hAc hAn q hq
    refine ⟨a₀, b + transport01 a₀, c + transport12 (b + transport01 a₀), hA, ?_, ?_⟩
    · rw [hB, hA]
      simp only [linear_image_vadd, vadd_vadd, vadd_eq_add, a₀]
    · rw [hC, hB, hA]
      simp only [linear_image_vadd, vadd_vadd, vadd_eq_add, a₀]


end VolumePolynomials.Holonomy
