module

public import Unimodular.FanProducts
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Linarith

@[expose] public section

open scoped Pointwise

namespace Unimodular.MinimalFaces

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The points of a cone dominated by a nonnegative multiple of `x`. This is a geometric
definition of its smallest face through `x`; it contains no face or completeness assumptions. -/
def dominatedCone (C : PointedCone ℝ V) (x : V) : PointedCone ℝ V where
  carrier := {y | y ∈ C ∧ ∃ a : ℝ, 0 ≤ a ∧ a • x - y ∈ C}
  zero_mem' := ⟨C.zero_mem, 0, le_rfl, by simpa using C.zero_mem⟩
  add_mem' := by
    rintro y z ⟨hy, a, ha, hay⟩ ⟨hz, b, hb, hbz⟩
    refine ⟨C.add_mem hy hz, a + b, add_nonneg ha hb, ?_⟩
    convert C.add_mem hay hbz using 1 <;> module
  smul_mem' := by
    rintro r y ⟨hy, a, ha, hay⟩
    refine ⟨PointedCone.smul_mem C r.2 hy, (r : ℝ) * a, mul_nonneg r.2 ha, ?_⟩
    change ((r : ℝ) * a) • x - (r : ℝ) • y ∈ C
    rw [mul_smul, ← smul_sub]
    exact PointedCone.smul_mem C r.2 hay

@[simp] theorem mem_dominatedCone (C : PointedCone ℝ V) (x y : V) :
    y ∈ dominatedCone C x ↔ y ∈ C ∧ ∃ a : ℝ, 0 ≤ a ∧ a • x - y ∈ C := Iff.rfl

theorem dominatedCone_isFaceOf (C : PointedCone ℝ V) (x : V) :
    (dominatedCone C x).IsFaceOf C := by
  apply PointedCone.IsFaceOf.of_mem_of_add_mem_left
  · exact fun _ hy => hy.1
  · rintro y z hy hz ⟨_, a, ha, hsum⟩
    refine ⟨hy, a, ha, ?_⟩
    convert C.add_mem hsum hz using 1 <;> abel

theorem self_mem_dominatedCone {C : PointedCone ℝ V} {x : V} (hx : x ∈ C) :
    x ∈ dominatedCone C x := ⟨hx, 1, zero_le_one, by simpa using C.zero_mem⟩

/-- Every face containing `x` contains the dominated cone. -/
theorem dominatedCone_le {C F : PointedCone ℝ V} {x : V}
    (hF : F.IsFaceOf C) (hxF : x ∈ F) : dominatedCone C x ≤ F := by
  rintro y ⟨hy, a, ha, hsub⟩
  apply hF.mem_of_add_mem_left hy hsub
  simpa using PointedCone.smul_mem F ha hxF

theorem dominatedCone_eq_of_face {C F : PointedCone ℝ V} {x : V}
    (hF : F.IsFaceOf C) (hxF : x ∈ F) : dominatedCone F x = dominatedCone C x := by
  apply le_antisymm
  · exact dominatedCone_le
      ((PointedCone.IsFaceOf.isFaceOf_iff_le (dominatedCone_isFaceOf C x) hF).2
        (dominatedCone_le hF hxF)) (self_mem_dominatedCone (hF.le hxF))
  · exact dominatedCone_le ((dominatedCone_isFaceOf F x).trans hF)
      (self_mem_dominatedCone hxF)

/-- The negative part of a dominating expression remains in the same minimal face. -/
theorem dominating_residual_mem {C : PointedCone ℝ V} {x y : V}
    (hx : x ∈ C) {a : ℝ} (ha : 0 ≤ a) (hy : y ∈ C) (hsub : a • x - y ∈ C) :
    a • x - y ∈ dominatedCone C x := by
  apply (dominatedCone_isFaceOf C x).mem_of_add_mem_right hy hsub
  simpa using PointedCone.smul_mem (dominatedCone C x) ha (self_mem_dominatedCone hx)

/-- Every vector in the span of the minimal face can be absorbed in its positive direction.
This is the local geometric step used in quotient-star gluing. -/
theorem absorb_span {C : PointedCone ℝ V} {x : V} (hx : x ∈ C)
    {v : V} (hv : v ∈ Submodule.span ℝ (dominatedCone C x : Set V)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 ≤ t → t ≤ δ → x + t • v ∈ dominatedCone C x := by
  obtain ⟨p, hp, q, hq, rfl⟩ := PointedCone.mem_span.mp hv
  obtain ⟨hqC, a, ha, haq⟩ := hq
  refine ⟨(a + 1)⁻¹, inv_pos.2 (by linarith), ?_⟩
  intro t ht htd
  have hta : t * a ≤ 1 := by
    have ht' : t * (a + 1) ≤ 1 := calc
      t * (a + 1) ≤ (a + 1)⁻¹ * (a + 1) :=
        mul_le_mul_of_nonneg_right htd (by linarith)
      _ = 1 := inv_mul_cancel₀ (by linarith)
    nlinarith
  have hres := dominating_residual_mem hx ha hqC haq
  have hm := (dominatedCone C x).add_mem
    ((dominatedCone C x).add_mem
      (PointedCone.smul_mem _ (sub_nonneg.2 hta) (self_mem_dominatedCone hx))
      (PointedCone.smul_mem _ ht hres))
    (PointedCone.smul_mem _ ht hp)
  convert hm using 1 <;> module

/-- The same absorption works in both directions along a line. -/
theorem absorb_span_two_sided {C : PointedCone ℝ V} {x : V} (hx : x ∈ C)
    {v : V} (hv : v ∈ Submodule.span ℝ (dominatedCone C x : Set V)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| ≤ δ → x + t • v ∈ dominatedCone C x := by
  obtain ⟨a, ha, hpa⟩ := absorb_span hx hv
  obtain ⟨b, hb, hnb⟩ := absorb_span hx (Submodule.neg_mem _ hv)
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro t ht
  by_cases ht0 : 0 ≤ t
  · exact hpa t ht0 ((le_abs_self t).trans (ht.trans (min_le_left _ _)))
  · have htn : 0 ≤ -t := by linarith
    have h := hnb (-t) htn ((neg_le_abs t).trans (ht.trans (min_le_right _ _)))
    simpa only [neg_smul, smul_neg, neg_neg] using h

/-- If two faces of one cone are both smallest faces through the same point, they agree.
No face-to-face property of a larger collection is assumed here. -/
theorem equal_of_common_supercone {C D S : PointedCone ℝ V} {x : V}
    (hxC : x ∈ C) (hxD : x ∈ D)
    (hCS : (dominatedCone C x).IsFaceOf S)
    (hDS : (dominatedCone D x).IsFaceOf S) :
    dominatedCone C x = dominatedCone D x := by
  have hC := dominatedCone_eq_of_face hCS (self_mem_dominatedCone hxC)
  have hD := dominatedCone_eq_of_face hDS (self_mem_dominatedCone hxD)
  have hCC := dominatedCone_eq_of_face (dominatedCone_isFaceOf C x)
    (self_mem_dominatedCone hxC)
  have hDD := dominatedCone_eq_of_face (dominatedCone_isFaceOf D x)
    (self_mem_dominatedCone hxD)
  exact hCC.symm.trans (hC.trans (hD.symm.trans hDD))

end Unimodular.MinimalFaces
