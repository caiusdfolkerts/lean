module

public import Projection.SupportDensity
public import VolumePolynomials.ProjectionPairingEquality
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic.Module

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace RankThreeProjection
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Membership in the actual convex hull of two compact convex bodies. -/
theorem mem_joinBody_iff (A B : ConvexBody E) (x : E) :
    x ∈ joinBody A B ↔ ∃ t ∈ Icc (0 : ℝ) 1, ∃ a ∈ A, ∃ b ∈ B,
      x = (1 - t) • a + t • b := by
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, hx⟩ := mem_convexJoin.mp hx
    rw [segment_eq_image] at hx
    obtain ⟨t, ht, he⟩ := hx
    exact ⟨t, ht, a, ha, b, hb, he.symm⟩
  · rintro ⟨t, ht, a, ha, b, hb, rfl⟩
    apply mem_convexJoin.mpr
    refine ⟨a, ha, b, hb, ?_⟩
    rw [segment_eq_image]
    exact ⟨t, ht, rfl⟩

theorem le_joinBody_left (A B : ConvexBody E) : A ≤ joinBody A B :=
  subset_convexJoin_left B.nonempty

theorem le_joinBody_right (A B : ConvexBody E) : B ≤ joinBody A B :=
  subset_convexJoin_right A.nonempty

/-- The Cayley union identity, including an arbitrary common Minkowski
summand. Every body and sum in this identity has its usual set meaning. -/
theorem joinBody_cayley_union (A B R : ConvexBody E) :
    ((joinBody A B + A + R : ConvexBody E) : Set E) ∪
        ((joinBody A B + B + R : ConvexBody E) : Set E) =
      ((joinBody A B + joinBody A B + R : ConvexBody E) : Set E) := by
  let D := joinBody A B
  have hA : A ≤ D := le_joinBody_left A B
  have hB : B ≤ D := le_joinBody_right A B
  apply subset_antisymm
  · rintro x (hx | hx)
    · rcases hx with ⟨y, ⟨d, hd, a, ha, rfl⟩, r, hr, rfl⟩
      exact ⟨d + a, ⟨d, hd, a, hA ha, rfl⟩, r, hr, rfl⟩
    · rcases hx with ⟨y, ⟨d, hd, b, hb, rfl⟩, r, hr, rfl⟩
      exact ⟨d + b, ⟨d, hd, b, hB hb, rfl⟩, r, hr, rfl⟩
  · have hdouble : D + D = (2 : ℝ) • D := by
      simpa only [one_smul, one_add_one_eq_two] using
        (body_add_smul D (a := 1) (b := 1) zero_le_one zero_le_one).symm
    intro x hx
    change x ∈ ((D + D + R : ConvexBody E) : Set E) at hx
    rw [hdouble] at hx
    rcases hx with ⟨y, ⟨d, hd, rfl⟩, r, hr, rfl⟩
    obtain ⟨t, ht, a, ha, b, hb, rfl⟩ := (mem_joinBody_iff A B d).mp hd
    by_cases ht2 : t ≤ 1 / 2
    · left
      have hd' : (1 - 2 * t) • a + (2 * t) • b ∈ D :=
        D.convex (hA ha) (hB hb) (by linarith) (by linarith [ht.1]) (by ring)
      refine ⟨((1 - 2 * t) • a + (2 * t) • b) + a,
        ⟨_, hd', a, ha, rfl⟩, r, hr, ?_⟩
      module
    · right
      have hd' : (2 * (1 - t)) • a + (2 * t - 1) • b ∈ D :=
        D.convex (hA ha) (hB hb) (by linarith [ht.2]) (by linarith) (by ring)
      refine ⟨((2 * (1 - t)) • a + (2 * t - 1) • b) + b,
        ⟨_, hd', b, hb, rfl⟩, r, hr, ?_⟩
      module

/-- The Cayley intersection identity. The common summand may contribute
different points to the two representations; convexity combines them. -/
theorem joinBody_cayley_inter (A B R : ConvexBody E) :
    ((joinBody A B + A + R : ConvexBody E) : Set E) ∩
        ((joinBody A B + B + R : ConvexBody E) : Set E) =
      ((A + B + R : ConvexBody E) : Set E) := by
  let D := joinBody A B
  have hA : A ≤ D := le_joinBody_left A B
  have hB : B ≤ D := le_joinBody_right A B
  apply subset_antisymm
  · intro x hx
    rcases hx.1 with ⟨y₁, ⟨d₁, hd₁, a₀, ha₀, rfl⟩, r₁, hr₁, hx₁⟩
    rcases hx.2 with ⟨y₂, ⟨d₂, hd₂, b₀, hb₀, rfl⟩, r₂, hr₂, hx₂⟩
    obtain ⟨t, ht, a₁, ha₁, b₁, hb₁, hd₁'⟩ := (mem_joinBody_iff A B d₁).mp hd₁
    obtain ⟨s, hs, a₂, ha₂, b₂, hb₂, hd₂'⟩ := (mem_joinBody_iff A B d₂).mp hd₂
    obtain ⟨a, ha, hea⟩ := A.convex.exists_mem_add_smul_eq ha₀ ha₁
      (show (0 : ℝ) ≤ 1 from zero_le_one) (sub_nonneg.mpr ht.2)
    obtain ⟨b, hb, heb⟩ := B.convex.exists_mem_add_smul_eq hb₀ hb₂
      (show (0 : ℝ) ≤ 1 from zero_le_one) hs.1
    have hea' : (2 - t) • a = a₀ + (1 - t) • a₁ := by
      simpa only [one_smul, show (1 : ℝ) + (1 - t) = 2 - t by ring] using hea
    have heb' : (1 + s) • b = b₀ + s • b₂ := by
      simpa only [one_smul] using heb
    have hleft : ((2 - t) • a + t • b₁) + r₁ = x := by
      calc
        _ = (d₁ + a₀) + r₁ := by rw [hea', hd₁']; module
        _ = x := hx₁
    have hright : ((1 - s) • a₂ + (1 + s) • b) + r₂ = x := by
      calc
        _ = (d₂ + b₀) + r₂ := by rw [heb', hd₂']; module
        _ = x := hx₂
    by_cases hden : 1 - t + s = 0
    · have ht1 : t = 1 := by linarith [ht.2, hs.1]
      refine ⟨a + b₁, ⟨a, ha, b₁, hb₁, rfl⟩, r₁, hr₁, ?_⟩
      simpa only [ht1, sub_self, add_zero, one_smul,
        show (2 : ℝ) - 1 = 1 by ring] using hleft
    · have hdenpos : 0 < 1 - t + s :=
        lt_of_le_of_ne (by linarith [ht.2, hs.1]) (Ne.symm hden)
      let w : ℝ := s / (1 - t + s)
      have hw0 : 0 ≤ w := div_nonneg hs.1 hdenpos.le
      have hw1 : w ≤ 1 := (div_le_one hdenpos).mpr (by linarith [ht.2])
      have hw : w * (1 - t + s) = s := div_mul_cancel₀ _ hden
      let a' := (w * (2 - t)) • a + ((1 - w) * (1 - s)) • a₂
      let b' := (w * t) • b₁ + ((1 - w) * (1 + s)) • b
      let r' := w • r₁ + (1 - w) • r₂
      have ha' : a' ∈ A := A.convex ha ha₂
        (mul_nonneg hw0 (by linarith [ht.2]))
        (mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr hs.2)) (by nlinarith [hw])
      have hb' : b' ∈ B := B.convex hb₁ hb
        (mul_nonneg hw0 ht.1)
        (mul_nonneg (sub_nonneg.mpr hw1) (by linarith [hs.1])) (by nlinarith [hw])
      have hr' : r' ∈ R := R.convex hr₁ hr₂ hw0 (sub_nonneg.mpr hw1) (by ring)
      refine ⟨a' + b', ⟨a', ha', b', hb', rfl⟩, r', hr', ?_⟩
      calc
        _ = w • (((2 - t) • a + t • b₁) + r₁) +
            (1 - w) • (((1 - s) • a₂ + (1 + s) • b) + r₂) := by
              dsimp [a', b', r']
              module
        _ = w • x + (1 - w) • x := by rw [hleft, hright]
        _ = x := by module
  · rintro x ⟨y, ⟨a, ha, b, hb, rfl⟩, r, hr, rfl⟩
    constructor
    · refine ⟨b + a, ⟨b, hB hb, a, ha, rfl⟩, r, hr, ?_⟩
      rw [add_comm b a]
    · exact ⟨a + b, ⟨a, hA ha, b, hb, rfl⟩, r, hr, rfl⟩

theorem joinBody_smul (A B : ConvexBody E) {s : ℝ} (hs : 0 ≤ s) :
    joinBody (s • A) (s • B) = s • joinBody A B := by
  apply supportContinuous_injective
  ext u
  have hjoin := congrArg (fun f : C(NormalSphere E, ℝ) => f u)
    (supportContinuous_join A B)
  change BodySupport.support (joinBody A B) u.val =
    max (BodySupport.support A u.val) (BodySupport.support B u.val) at hjoin
  rw [supportContinuous_join]
  change max (BodySupport.support (s • A) u.val) (BodySupport.support (s • B) u.val) =
    BodySupport.support (s • joinBody A B) u.val
  rw [Support.smul_body A u.val hs, Support.smul_body B u.val hs,
    Support.smul_body (joinBody A B) u.val hs, hjoin]
  exact (mul_max_of_nonneg _ _ hs).symm

section Volume
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- Ordinary Haar volume inclusion–exclusion on the actual Cayley sets. -/
theorem joinBody_cayley_volume (A B R : ConvexBody E) :
    μ.real ((joinBody A B + joinBody A B + R : ConvexBody E) : Set E) +
        μ.real ((A + B + R : ConvexBody E) : Set E) =
      μ.real ((joinBody A B + A + R : ConvexBody E) : Set E) +
        μ.real ((joinBody A B + B + R : ConvexBody E) : Set E) := by
  have h := measureReal_union_add_inter (μ := μ)
    (s := ((joinBody A B + A + R : ConvexBody E) : Set E))
    (t := ((joinBody A B + B + R : ConvexBody E) : Set E))
    (joinBody A B + B + R).isCompact.measurableSet
    (joinBody A B + A + R).isCompact.measure_lt_top.ne
    (joinBody A B + B + R).isCompact.measure_lt_top.ne
  rw [joinBody_cayley_union, joinBody_cayley_inter] at h
  exact h

/-- The quadratic mixed-volume valuation identity for a convex hull. It is
proved by ordinary volume inclusion–exclusion and polynomial coefficient
uniqueness, without postulating a valuation property of mixed volume. -/
theorem mixedVolume_joinBody_identity {d : ℕ} (K : Fin d → ConvexBody E)
    (A B : ConvexBody E) :
    mixedVolume μ (Fin.cons (joinBody A B) (Fin.cons (joinBody A B) K)) +
        mixedVolume μ (Fin.cons A (Fin.cons B K)) =
      mixedVolume μ (Fin.cons (joinBody A B) (Fin.cons A K)) +
        mixedVolume μ (Fin.cons (joinBody A B) (Fin.cons B K)) := by
  let D := joinBody A B
  let p (L : ConvexBody E) := volumePolynomial μ (Fin.cons L (Fin.cons L K))
  have hpoly : p (D + D) + p (A + B) = p (D + A) + p (D + B) := by
    apply MvPolynomial.funext_set (fun _ => Ici (0 : ℝ)) (fun _ => Ici_infinite 0)
    intro t ht
    have ht' : ∀ i, 0 ≤ t i := fun i => ht i (mem_univ i)
    let s : ℝ := t 0 + t 1
    have hs : 0 ≤ s := add_nonneg (ht' 0) (ht' 1)
    let R : ConvexBody E := ∑ i : Fin d, t i.succ.succ • K i
    have hsum (L : ConvexBody E) :
        (∑ i, t i • (Fin.cons L (Fin.cons L K)) i) = s • L + R := by
      dsimp [s, R]
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one]
      rw [← add_assoc, ← body_add_smul L (ht' 0) (ht' 1)]
    simp only [MvPolynomial.eval_add, p, volumePolynomial_eval μ _ t ht', hsum]
    have h := joinBody_cayley_volume μ (s • A) (s • B) R
    rw [joinBody_smul A B hs] at h
    simpa only [← smul_add, D] using h
  have hcoeff := congrArg (fun P : MvPolynomial (Fin (d + 2)) ℝ =>
    P.coeff (squarefreeExponent (d + 2)) / (d + 2).factorial) hpoly
  have hquad :
      mixedVolume μ (Fin.cons (D + D) (Fin.cons (D + D) K)) +
          mixedVolume μ (Fin.cons (A + B) (Fin.cons (A + B) K)) =
        mixedVolume μ (Fin.cons (D + A) (Fin.cons (D + A) K)) +
          mixedVolume μ (Fin.cons (D + B) (Fin.cons (D + B) K)) := by
    simpa only [p, mixedVolume, MvPolynomial.coeff_add, add_div] using hcoeff
  let q : ConvexBody E → ConvexBody E → ℝ :=
    fun X Y => mixedVolume μ (Fin.cons X (Fin.cons Y K))
  have hadd (X Y T : ConvexBody E) : q (X + Y) T = q X T + q Y T :=
    PolyhedralSupport.mixedVolume_cons_add μ X Y (Fin.cons T K)
  have hsymm (X Y : ConvexBody E) : q X Y = q Y X :=
    PolyhedralSupport.mixedVolume_cons_cons_swap μ X Y K
  have hadd_right (X Y T : ConvexBody E) : q X (Y + T) = q X Y + q X T := by
    rw [hsymm, hadd, hsymm Y X, hsymm T X]
  change q (D + D) (D + D) + q (A + B) (A + B) =
    q (D + A) (D + A) + q (D + B) (D + B) at hquad
  simp only [hadd, hadd_right] at hquad
  rw [hsymm A D, hsymm B D, hsymm B A] at hquad
  change q D D + q A B = q D A + q D B
  linarith

end Volume
end RankThreeProjection
