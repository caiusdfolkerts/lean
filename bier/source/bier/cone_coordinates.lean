import bier.threshold
import bier.standard_coordinates
import Mathlib.Data.Finset.Option

/-! A faithful linear realization of Bier cones modulo the diagonal. -/

noncomputable section

namespace Bier

open Set

variable {V : Type*} [Fintype V] [DecidableEq V]

structure ConeCoordinates (face : Finset V → Prop) (w : Option (V ⊕ V) → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ w a
  total : ∑ a, w a = 1
  positive : face (Finset.univ.filter (fun v => 0 < w (some (.inl v))))
  negative : ¬ face (Finset.univ.filter (fun v => w (some (.inr v)) = 0))
  disjoint : ∀ v, w (some (.inl v)) = 0 ∨ w (some (.inr v)) = 0

def signedCoordinate (w : Option (V ⊕ V) → ℝ) (v : V) : ℝ :=
  w (some (.inl v)) - w (some (.inr v))

def coneProjection (v₀ : V) : (Option (V ⊕ V) → ℝ) →ₗ[ℝ] ({v : V // v ≠ v₀} → ℝ) where
  toFun w v := signedCoordinate w v - signedCoordinate w v₀
  map_add' := by intros; ext; simp [signedCoordinate]; ring
  map_smul' := by intros; ext; simp [signedCoordinate, mul_sub]

@[simp] theorem coneProjection_apply (v₀ : V) (w : Option (V ⊕ V) → ℝ)
    (v : {v : V // v ≠ v₀}) :
    coneProjection v₀ w v = signedCoordinate w v - signedCoordinate w v₀ := rfl

theorem ConeCoordinates.signed_positive {face : Finset V → Prop} {w : Option (V ⊕ V) → ℝ}
    (hw : ConeCoordinates face w) :
    face (Finset.univ.filter (fun v => 0 < signedCoordinate w v)) := by
  convert hw.positive using 1
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, signedCoordinate]
  have hl := hw.nonneg (some (.inl v))
  have hr := hw.nonneg (some (.inr v))
  rcases hw.disjoint v with h | h <;> rw [h] <;> constructor <;> intro h' <;> linarith

theorem ConeCoordinates.signed_nonnegative {face : Finset V → Prop}
    {w : Option (V ⊕ V) → ℝ} (hw : ConeCoordinates face w) :
    ¬ face (Finset.univ.filter (fun v => 0 ≤ signedCoordinate w v)) := by
  classical
  have heq : Finset.univ.filter (fun v => 0 ≤ signedCoordinate w v) =
      Finset.univ.filter (fun v => w (some (.inr v)) = 0) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change 0 ≤ w (some (.inl v)) - w (some (.inr v)) ↔ w (some (.inr v)) = 0
    have hl := hw.nonneg (some (.inl v))
    have hr := hw.nonneg (some (.inr v))
    rcases hw.disjoint v with h | h <;> rw [h] <;> constructor <;> intro h' <;> linarith
  rw [heq]
  exact hw.negative

theorem coneProjection_injective (face : Finset V → Prop)
    (hdown : ∀ {s t}, s ⊆ t → face t → face s) (v₀ : V) :
    Set.InjOn (coneProjection v₀) {w | ConeCoordinates face w} := by
  intro w hw z hz heq
  let c := signedCoordinate w v₀ - signedCoordinate z v₀
  have hdiff : ∀ v, signedCoordinate w v = signedCoordinate z v + c := by
    intro v
    by_cases hv : v = v₀
    · subst v
      simp [c]
    · have hh := congrFun heq ⟨v, hv⟩
      change signedCoordinate w v - signedCoordinate w v₀ =
        signedCoordinate z v - signedCoordinate z v₀ at hh
      dsimp [c]
      linarith
  have hc : c = 0 := diagonal_difference_eq_zero face hdown _ _ hw.signed_positive
    hw.signed_nonnegative hz.signed_positive hz.signed_nonnegative c hdiff
  have heqSigned : ∀ v, signedCoordinate w v = signedCoordinate z v := by
    intro v
    simpa only [hc, add_zero] using hdiff v
  have heqSome : ∀ a : V ⊕ V, w (some a) = z (some a) := by
    intro a
    cases a with
    | inl v =>
      have hh := heqSigned v
      dsimp [signedCoordinate] at hh
      have hlw := hw.nonneg (some (.inl v))
      have hrw := hw.nonneg (some (.inr v))
      have hlz := hz.nonneg (some (.inl v))
      have hrz := hz.nonneg (some (.inr v))
      rcases hw.disjoint v with hw' | hw' <;>
        rcases hz.disjoint v with hz' | hz' <;> linarith
    | inr v =>
      have hh := heqSigned v
      dsimp [signedCoordinate] at hh
      have hlw := hw.nonneg (some (.inl v))
      have hrw := hw.nonneg (some (.inr v))
      have hlz := hz.nonneg (some (.inl v))
      have hrz := hz.nonneg (some (.inr v))
      rcases hw.disjoint v with hw' | hw' <;>
        rcases hz.disjoint v with hz' | hz' <;> linarith
  funext a
  cases a with
  | some a => exact heqSome a
  | none =>
    have hwSum := hw.total
    have hzSum := hz.total
    simp only [Fintype.sum_option] at hwSum hzSum
    have hs : ∑ a, w (some a) = ∑ a, z (some a) := Finset.sum_congr rfl (fun a _ => heqSome a)
    linarith

end Bier
