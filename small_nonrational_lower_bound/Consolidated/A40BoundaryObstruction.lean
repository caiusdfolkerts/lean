module
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Papers.FacetNormalization
public import Mathlib.Data.Fin.VecNotation
public import Papers.FiniteProjectionBoundary

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: Papers/A40SignObstruction.lean -/






@[expose] public section

/-!
# The cyclic sign obstruction for Appendix B type A40

This is the algebraic part of an exclusion, not yet the actual-polytope
application. In an actual A40 realization the positive supporting forms of
the ten bipyramids give the two equations and strict product below after
normalizing the five independent A-vertices. The actual geometric extraction
of these hypotheses is a separate obligation.

No assumption that a free coordinate is nonzero is needed here. The positive
plane coefficient and the strict product already exclude 0 and 1.
-/

namespace Papers.RationalWitnesses.A40

def next (i : Fin 5) : Fin 5 :=
  match i.val with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | _ => 0

def prev (i : Fin 5) : Fin 5 :=
  match i.val with
  | 0 => 4
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | _ => 3

@[simp] theorem next_prev : ∀ i : Fin 5, next (prev i) = i := by decide +kernel
@[simp] theorem prev_next : ∀ i : Fin 5, prev (next i) = i := by decide +kernel
theorem next_eq_add_one : ∀ i : Fin 5, next i = i + 1 := by decide +kernel
theorem prev_eq_add_four : ∀ i : Fin 5, prev i = i + 4 := by decide +kernel

/-- Two strictly positive evaluations with the same nonzero row scale force
the unscaled evaluations to have the same sign. -/
theorem same_sign_of_scaled_positives {r a b : ℝ}
    (ha : 0 < r * a) (hb : 0 < r * b) : 0 < a * b := by
  have h := mul_pos ha hb
  have heq : (r * a) * (r * b) = r ^ 2 * (a * b) := by ring
  rw [heq] at h
  rcases mul_pos_iff.mp h with h | h
  · exact h.2
  · exact False.elim ((not_lt_of_ge (sq_nonneg r)) h.1)

/-- Eliminate the factor shared by the two adjacent supporting planes.
Its square is nonnegative, so no additional nonvanishing hypothesis is
hidden in the reduction to the strict cyclic product. -/
theorem cyclic_product_of_shared_factor {x x' z c : ℝ}
    (hy : 0 < x' * (1 - z))
    (hleft : 0 < (x - 1) * (1 - z) * c)
    (hright : (x' - 1) * c < 0) :
    x' * (x - 1) * (x' - 1) < 0 := by
  have h := mul_neg_of_pos_of_neg (mul_pos hy hleft) hright
  have heq : (x' * (1 - z) * ((x - 1) * (1 - z) * c)) * ((x' - 1) * c) =
      (x' * (x - 1) * (x' - 1)) * ((1 - z) * c) ^ 2 := by ring
  rw [heq] at h
  by_contra hn
  exact (not_le_of_gt h) (mul_nonneg (le_of_not_gt hn) (sq_nonneg _))

private theorem preceding_gt_one {b c : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1)
    (hp : c * (b - 1) * (c - 1) < 0) : 1 < b := by
  by_contra hb
  have hb' : b - 1 ≤ 0 := sub_nonpos.mpr (le_of_not_gt hb)
  have hbc : c * (b - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc0.le hb'
  have hprod : 0 ≤ c * (b - 1) * (c - 1) :=
    mul_nonneg_of_nonpos_of_nonpos hbc (sub_nonpos.mpr hc1.le)
  exact (not_le_of_gt hp) hprod

private theorem plane_preceding_gt_one {a c y z : ℝ}
    (hy : 0 < y) (hz : 0 < z)
    (hleft : 1 = y + z * a) (hright : c = y + z * c)
    (hc0 : 0 < c) (hc1 : c < 1) : 1 < a := by
  have hz1 : z < 1 := by
    by_contra hz1
    have hz1' : 1 ≤ z := le_of_not_gt hz1
    have hmul := mul_le_mul_of_nonneg_right hz1' hc0.le
    nlinarith
  by_contra ha
  have ha' : a ≤ 1 := le_of_not_gt ha
  have hza : z * a ≤ z := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ha' hz.le
  have hstrict := mul_pos (sub_pos.mpr hz1) (sub_pos.mpr hc1)
  nlinarith

private theorem next_between_zero_one {a b : ℝ}
    (ha : 1 < a) (hp : b * (a - 1) * (b - 1) < 0) :
    0 < b ∧ b < 1 := by
  have ha' : 0 < a - 1 := sub_pos.mpr ha
  have hrewrite : b * (a - 1) * (b - 1) = (a - 1) * (b * (b - 1)) := by ring
  rw [hrewrite] at hp
  have hbb : b * (b - 1) < 0 := by
    rcases mul_neg_iff.mp hp with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_gt ha') h.1)
  rcases mul_neg_iff.mp hbb with h | h
  · exact ⟨h.1, sub_neg.mp h.2⟩
  · have : 1 < b := sub_pos.mp h.2
    linarith

/-- The normalized positive-plane equations and strict support signs for a
five-cycle cannot all hold. This contains no hypothesis about a realization
space, density, rationality, or a preclassified polytope. -/
theorem sign_obstruction
    (x y z : Fin 5 → ℝ)
    (hy : ∀ i, 0 < y i) (hz : ∀ i, 0 < z i)
    (hleft : ∀ i, 1 = y i + z i * x (prev i))
    (hright : ∀ i, x (next i) = y i + z i * x (next i))
    (hsign : ∀ i, x (next i) * (x i - 1) * (x (next i) - 1) < 0) :
    False := by
  have hnotmiddle : ∀ i, ¬ (0 < x i ∧ x i < 1) := by
    intro i hi
    have hprev : 1 < x (prev i) :=
      preceding_gt_one hi.1 hi.2 (by simpa only [next_prev] using hsign (prev i))
    have hprevprev : 1 < x (prev (prev i)) :=
      plane_preceding_gt_one (hy (prev i)) (hz (prev i)) (hleft (prev i))
        (by simpa only [next_prev] using hright (prev i)) hi.1 hi.2
    have hprod := hsign (prev (prev i))
    simp only [next_prev] at hprod
    have hpositive :
        0 < x (prev i) * (x (prev (prev i)) - 1) * (x (prev i) - 1) :=
      mul_pos (mul_pos (by linarith) (sub_pos.mpr hprevprev)) (sub_pos.mpr hprev)
    exact (not_lt_of_gt hpositive) hprod
  have hnotlarge : ∀ i, ¬ 1 < x i := by
    intro i hi
    exact hnotmiddle (next i) (next_between_zero_one hi (hsign i))
  have hnegative : ∀ i, x i < 0 := by
    intro i
    rcases lt_trichotomy (x i) 0 with h | h | h
    · exact h
    · have heq := hright (prev i)
      simp only [next_prev, h, mul_zero, add_zero] at heq
      have := hy (prev i)
      linarith
    · rcases lt_trichotomy (x i) 1 with h' | h' | h'
      · exact False.elim (hnotmiddle i ⟨h, h'⟩)
      · have hp := hsign (prev i)
        simp only [next_prev, h', sub_self, mul_zero] at hp
        exact False.elim (lt_irrefl _ hp)
      · exact False.elim (hnotlarge i h')
  have hcycle : ∀ i, x (next i) < x (prev i) := by
    intro i
    by_contra h
    have hle : x (prev i) ≤ x (next i) := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_left hle (hz i).le
    have hl := hleft i
    have hr := hright i
    have hn := hnegative (next i)
    linarith
  have h0 := hcycle 0
  have h1 := hcycle 1
  have h2 := hcycle 2
  have h3 := hcycle 3
  have h4 := hcycle 4
  change x 1 < x 4 at h0
  change x 2 < x 0 at h1
  change x 3 < x 1 at h2
  change x 4 < x 2 at h3
  change x 0 < x 3 at h4
  linarith

private theorem shift_one_three : ∀ i : Fin 5, (i + 1) + 3 = i + 4 := by decide +kernel
private theorem shift_four_three : ∀ i : Fin 5, (i + 4) + 3 = i + 2 := by decide +kernel
private theorem shift_one_four : ∀ i : Fin 5, (i + 1) + 4 = i := by decide +kernel
private theorem shift_one_one : ∀ i : Fin 5, (i + 1) + 1 = i + 2 := by decide +kernel

/-- The exact scalar equations extracted from the ten positive bipyramid
supporting forms are inconsistent. The row scales may have either sign;
their nonvanishing follows from the strict evaluations and is not an input.

The normalization uses only the positive coefficients `a`. The shared
factor for adjacent rows is `1 + a (i+2) * s i * s (i+1)`, so a global
product of the five `a` coefficients is unnecessary in the formal proof. -/
theorem normalized_support_obstruction
    (a s lam R u t : Fin 5 → ℝ)
    (ha : ∀ i, 0 < a i) (hu : ∀ i, 0 < u i) (ht : ∀ i, 0 < t i)
    (hleft : ∀ i, a (i + 4) = u i + t i * s (i + 4))
    (hright : ∀ i, s (i + 1) = a (i + 1) * u i + a (i + 2) * s (i + 1) * t i)
    (hlam : ∀ i, lam i = u i * a (i + 1) * s i - t i)
    (hF2 : ∀ i, 0 < R i * (1 + a (i + 2) * lam i))
    (hF3 : ∀ i, 0 < R i * (s i - a i * a (i + 3)))
    (hF4 : ∀ i, 0 < R i * (lam i - a (i + 4) * a (i + 1) * s i)) :
    False := by
  let x : Fin 5 → ℝ := fun i => s i / (a i * a (i + 3))
  let y : Fin 5 → ℝ := fun i => u i / a (i + 4)
  let z : Fin 5 → ℝ := fun i => t i * a (i + 2)
  have han : ∀ i, a i ≠ 0 := fun i => ne_of_gt (ha i)
  have hy : ∀ i, 0 < y i := fun i => div_pos (hu i) (ha (i + 4))
  have hz : ∀ i, 0 < z i := fun i => mul_pos (ht i) (ha (i + 2))
  have heqleft : ∀ i, 1 = y i + z i * x (i + 4) := by
    intro i
    dsimp [x, y, z]
    rw [shift_four_three]
    calc
      1 = (u i + t i * s (i + 4)) / a (i + 4) := by
        rw [← hleft i, div_self (han (i + 4))]
      _ = u i / a (i + 4) +
          (t i * a (i + 2)) * (s (i + 4) / (a (i + 4) * a (i + 2))) := by
        field_simp [han] <;> ring
  have heqright : ∀ i, x (i + 1) = y i + z i * x (i + 1) := by
    intro i
    dsimp [x, y, z]
    rw [shift_one_three]
    calc
      s (i + 1) / (a (i + 1) * a (i + 4)) =
          (a (i + 1) * u i + a (i + 2) * s (i + 1) * t i) /
            (a (i + 1) * a (i + 4)) := by
        exact congrArg (fun v : ℝ => v / (a (i + 1) * a (i + 4))) (hright i)
      _ = u i / a (i + 4) +
          (t i * a (i + 2)) * (s (i + 1) / (a (i + 1) * a (i + 4))) := by
        field_simp [han] <;> ring
  have hmiddle : ∀ i, 0 < R i * (x i - 1) := by
    intro i
    have h := hF3 i
    have heq : s i - a i * a (i + 3) = (x i - 1) * (a i * a (i + 3)) := by
      dsimp [x]
      rw [sub_mul, div_mul_cancel₀ _ (mul_ne_zero (han i) (han (i + 3))), one_mul]
    rw [heq, ← mul_assoc] at h
    exact (mul_pos_iff_of_pos_right (mul_pos (ha i) (ha (i + 3)))).mp h
  have hminus : ∀ i, lam i - a (i + 4) * a (i + 1) * s i =
      -t i * (1 + a (i + 1) * s i * s (i + 4)) := by
    intro i
    have hu' : u i = a (i + 4) - t i * s (i + 4) := by linarith [hleft i]
    rw [hlam i, hu']
    ring
  have hplus : ∀ i, 1 + a (i + 2) * lam i =
      (1 - z i) * (1 + a (i + 2) * s i * s (i + 1)) := by
    intro i
    have hg : a (i + 1) * u i =
        s (i + 1) - a (i + 2) * s (i + 1) * t i := by linarith [hright i]
    calc
      1 + a (i + 2) * lam i =
          1 - a (i + 2) * t i + a (i + 2) * s i * (a (i + 1) * u i) := by
        rw [hlam i]
        ring
      _ = (1 - z i) * (1 + a (i + 2) * s i * s (i + 1)) := by
        rw [hg]
        dsimp [z]
        ring
  have hproduct : ∀ i, x (i + 1) * (x i - 1) * (x (i + 1) - 1) < 0 := by
    intro i
    let c := 1 + a (i + 2) * s i * s (i + 1)
    have hpositive : 0 < x (i + 1) * (1 - z i) := by
      have heq : x (i + 1) * (1 - z i) = y i := by nlinarith [heqright i]
      rw [heq]
      exact hy i
    have hfirst : 0 < (x i - 1) * (1 - z i) * c := by
      have h := hF2 i
      rw [hplus i] at h
      have hsign := same_sign_of_scaled_positives (hmiddle i) h
      simpa only [c, mul_assoc] using hsign
    have hlast : (x (i + 1) - 1) * c < 0 := by
      have h := hF4 (i + 1)
      rw [hminus, shift_one_one, shift_one_four] at h
      have heq : 1 + a (i + 2) * s (i + 1) * s i = c := by dsimp [c]; ring
      rw [heq] at h
      have hsign := same_sign_of_scaled_positives (hmiddle (i + 1)) h
      have hring : (x (i + 1) - 1) * (-t (i + 1) * c) =
          -(t (i + 1) * ((x (i + 1) - 1) * c)) := by ring
      rw [hring] at hsign
      have hn := neg_pos.mp hsign
      rcases mul_neg_iff.mp hn with hh | hh
      · exact hh.2
      · exact False.elim ((not_lt_of_gt (ht (i + 1))) hh.1)
    exact cyclic_product_of_shared_factor hpositive hfirst hlast
  apply sign_obstruction x y z hy hz
  · intro i
    simpa only [prev_eq_add_four] using heqleft i
  · intro i
    simpa only [next_eq_add_one] using heqright i
  · intro i
    simpa only [next_eq_add_one] using hproduct i

end Papers.RationalWitnesses.A40

end
end BundlePart0

section BundlePart1
/- Source: Papers/A40SupportGeometry.lean -/







@[expose] public section

/-!
# Supporting forms exclude the cyclic A40 incidence pattern

The five distinguished vertices are proved independent from the positive
support matrix. Thus the coordinate chart used in the sign obstruction is
available in every actual realization; it is not a genericity hypothesis.
This file first treats linear supporting forms in an arbitrary real vector
space of dimension five. The actual affine-polytope application is separate.

Prepared proof source. A kernel check of this new file is still required.
-/

noncomputable section

namespace Papers.RationalWitnesses.A40

open Module
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The normalized evaluations of the ten supporting forms that matter for
A40. The five tetrahedral facets are not needed for this obstruction. -/
structure NormalizedSupportSystem (V : Type*) [AddCommGroup V] [Module ℝ V] where
  A : Fin 5 → V
  B : Fin 5 → V
  F : Fin 5 → V →ₗ[ℝ] ℝ
  G : Fin 5 → V →ₗ[ℝ] ℝ
  a : Fin 5 → ℝ
  u : Fin 5 → ℝ
  t : Fin 5 → ℝ
  a_pos : ∀ i, 0 < a i
  u_pos : ∀ i, 0 < u i
  t_pos : ∀ i, 0 < t i
  F_A : ∀ i j, F i (A j) =
    (if j = i + 2 then 1 else 0) + (if j = i + 4 then a i else 0)
  G_A : ∀ i j, G i (A j) =
    (if j = i + 1 then 1 else 0) + (if j = i + 3 then u i else 0) +
      (if j = i + 4 then t i else 0)
  F_B_zero : ∀ i, F i (B i) = 0 ∧ F (i + 1) (B i) = 0
  G_B_zero : ∀ i, G i (B (i + 4)) = 0 ∧ G i (B i) = 0 ∧
    G i (B (i + 1)) = 0
  F_B_pos : ∀ i, 0 < F (i + 2) (B i) ∧ 0 < F (i + 3) (B i) ∧
    0 < F (i + 4) (B i)

namespace NormalizedSupportSystem

variable (S : NormalizedSupportSystem V)

theorem F_sum (i : Fin 5) (c : Fin 5 → ℝ) :
    S.F i (∑ j, c j • S.A j) = c (i + 2) + S.a i * c (i + 4) := by
  simp only [map_sum, map_smul, smul_eq_mul, S.F_A, mul_add,
    mul_ite, mul_one, mul_zero, Finset.sum_add_distrib]
  simp [mul_comm]

theorem G_sum (i : Fin 5) (c : Fin 5 → ℝ) :
    S.G i (∑ j, c j • S.A j) =
      c (i + 1) + S.u i * c (i + 3) + S.t i * c (i + 4) := by
  simp only [map_sum, map_smul, smul_eq_mul, S.G_A, mul_add,
    mul_ite, mul_one, mul_zero, Finset.sum_add_distrib]
  simp [mul_comm]

/-- The sparse positive support matrix has determinant
`1 + a₀a₁a₂a₃a₄`. The proof uses its kernel recurrence, so it does not
rely on a determinant computation or on a presumed projective frame. -/
theorem A_linearIndependent : LinearIndependent ℝ S.A := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have he (j : Fin 5) : c (j + 2) + S.a j * c (j + 4) = 0 := by
    rw [← S.F_sum j c, hc, map_zero]
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have h3 := he 3
  have h4 := he 4
  norm_num at h0 h1 h2 h3 h4
  have hc0 : c 0 = -(S.a 3 * S.a 0 * S.a 2 * S.a 4 * S.a 1) * c 0 := by
    calc
      c 0 = -S.a 3 * c 2 := by linarith only [h3]
      _ = S.a 3 * S.a 0 * c 4 := by
        rw [show c 2 = -S.a 0 * c 4 by linarith only [h0]]
        ring
      _ = -(S.a 3 * S.a 0 * S.a 2) * c 1 := by
        rw [show c 4 = -S.a 2 * c 1 by linarith only [h2]]
        ring
      _ = S.a 3 * S.a 0 * S.a 2 * S.a 4 * c 3 := by
        rw [show c 1 = -S.a 4 * c 3 by linarith only [h4]]
        ring
      _ = -(S.a 3 * S.a 0 * S.a 2 * S.a 4 * S.a 1) * c 0 := by
        rw [show c 3 = -S.a 1 * c 0 by linarith only [h1]]
        ring
  have hpositive : 0 < 1 + S.a 3 * S.a 0 * S.a 2 * S.a 4 * S.a 1 := by
    have hp := mul_pos (mul_pos (mul_pos (mul_pos (S.a_pos 3) (S.a_pos 0))
      (S.a_pos 2)) (S.a_pos 4)) (S.a_pos 1)
    linarith
  have hz : (1 + S.a 3 * S.a 0 * S.a 2 * S.a 4 * S.a 1) * c 0 = 0 := by
    linear_combination hc0
  have hz0 : c 0 = 0 := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hpositive)
  have hz3 : c 3 = 0 := by simpa only [hz0, mul_zero, add_zero] using h1
  have hz1 : c 1 = 0 := by simpa only [hz3, mul_zero, add_zero] using h4
  have hz4 : c 4 = 0 := by simpa only [hz1, mul_zero, add_zero] using h2
  have hz2 : c 2 = 0 := by simpa only [hz4, mul_zero, add_zero] using h0
  fin_cases i <;> assumption

variable [FiniteDimensional ℝ V]

include S in
/-- All line parameters and positive coefficients used by the algebraic
obstruction are extracted from the supporting forms of the system. -/
theorem impossible (hdim : Module.finrank ℝ V = 5) : False := by
  let b : Basis (Fin 5) ℝ V := Basis.mk S.A_linearIndependent
    (S.A_linearIndependent.span_eq_top_of_card_eq_finrank'
      (by simpa using hdim.symm)).ge
  have hb : ∀ i, b i = S.A i := fun i => Basis.mk_apply _ _ i
  let X : Fin 5 → Fin 5 → ℝ := fun i => b.repr (S.B i)
  have hF (i j : Fin 5) : S.F i (S.B j) =
      X j (i + 2) + S.a i * X j (i + 4) := by
    have he : ∑ k, X j k • S.A k = S.B j := by
      simpa only [X, hb] using b.sum_repr (S.B j)
    rw [← he, S.F_sum]
  have hG (i j : Fin 5) : S.G i (S.B j) =
      X j (i + 1) + S.u i * X j (i + 3) + S.t i * X j (i + 4) := by
    have he : ∑ k, X j k • S.A k = S.B j := by
      simpa only [X, hb] using b.sum_repr (S.B j)
    rw [← he, S.G_sum]
  have hX2 (j : Fin 5) : X j (j + 2) = -S.a j * X j (j + 4) := by
    have h := (S.F_B_zero j).1
    rw [hF] at h
    linarith only [h]
  have hX3 (j : Fin 5) : X j (j + 3) = -S.a (j + 1) * X j j := by
    have h := (S.F_B_zero j).2
    rw [hF] at h
    norm_num [add_assoc] at h
    linarith only [h]
  let R : Fin 5 → ℝ := fun j => X j (j + 4)
  have hR : ∀ j, R j ≠ 0 := by
    intro j hj
    have hj' : X j (j + 4) = 0 := hj
    have h2 : X j (j + 2) = 0 := by simpa only [hj', mul_zero] using hX2 j
    have hg := (S.G_B_zero (j + 1)).1
    norm_num [add_assoc] at hg
    rw [hG] at hg
    norm_num [add_assoc] at hg
    rw [h2, hj', mul_zero, zero_add, zero_add] at hg
    have hS : X j j = 0 := (mul_eq_zero.mp hg).resolve_left
      (ne_of_gt (S.t_pos (j + 1)))
    have h3 : X j (j + 3) = 0 := by simpa only [hS, mul_zero] using hX3 j
    have hg0 := (S.G_B_zero j).2.1
    rw [hG, h3, hj', mul_zero, mul_zero, add_zero, add_zero] at hg0
    have hp := (S.F_B_pos j).1
    rw [hF] at hp
    norm_num [add_assoc] at hp
    rw [hj', hg0, mul_zero, zero_add] at hp
    exact (lt_irrefl 0) hp
  let s : Fin 5 → ℝ := fun j => X j j / R j
  let lam : Fin 5 → ℝ := fun j => X j (j + 1) / R j
  have hs (j : Fin 5) : R j * s j = X j j := by
    dsimp only [s]
    field_simp [hR j] <;> ring
  have hl (j : Fin 5) : R j * lam j = X j (j + 1) := by
    dsimp only [lam]
    field_simp [hR j] <;> ring
  have hleft (j : Fin 5) : S.a (j + 4) = S.u j + S.t j * s (j + 4) := by
    have h := (S.G_B_zero j).1
    rw [hG] at h
    have h2 := hX2 (j + 4)
    norm_num [add_assoc] at h2
    rw [h2] at h
    have hr : X (j + 4) (j + 3) = R (j + 4) := by
      norm_num [R, add_assoc]
    rw [hr] at h
    change -(S.a (j + 4) * R (j + 4)) + S.u j * R (j + 4) +
      S.t j * X (j + 4) (j + 4) = 0 at h
    rw [← hs (j + 4)] at h
    have he : R (j + 4) *
        (-S.a (j + 4) + S.u j + S.t j * s (j + 4)) = 0 := by
      linear_combination h
    have hz := (mul_eq_zero.mp he).resolve_left (hR (j + 4))
    linarith only [hz]
  have hright (j : Fin 5) : s (j + 1) = S.a (j + 1) * S.u j +
      S.a (j + 2) * s (j + 1) * S.t j := by
    have h := (S.G_B_zero j).2.2
    rw [hG] at h
    have h2 := hX2 (j + 1)
    have h3 := hX3 (j + 1)
    norm_num [add_assoc] at h2 h3
    rw [h2, h3] at h
    have hr : X (j + 1) j = R (j + 1) := by
      norm_num [R, add_assoc]
    rw [hr] at h
    change X (j + 1) (j + 1) + S.u j * -(S.a (j + 1) * R (j + 1)) +
      S.t j * -(S.a (j + 2) * X (j + 1) (j + 1)) = 0 at h
    rw [← hs (j + 1)] at h
    have he : R (j + 1) * (s (j + 1) - S.a (j + 1) * S.u j -
        S.a (j + 2) * s (j + 1) * S.t j) = 0 := by
      linear_combination h
    have hz := (mul_eq_zero.mp he).resolve_left (hR (j + 1))
    linarith only [hz]
  have hlam (j : Fin 5) : lam j = S.u j * S.a (j + 1) * s j - S.t j := by
    have h := (S.G_B_zero j).2.1
    rw [hG, hX3, ← hs j, ← hl j] at h
    change R j * lam j + S.u j * (-S.a (j + 1) * (R j * s j)) +
      S.t j * R j = 0 at h
    have he : R j * (lam j - S.u j * S.a (j + 1) * s j + S.t j) = 0 := by
      linear_combination h
    have hz := (mul_eq_zero.mp he).resolve_left (hR j)
    linarith only [hz]
  have hF2 (j : Fin 5) : 0 < R j * (1 + S.a (j + 2) * lam j) := by
    have h := (S.F_B_pos j).1
    rw [hF] at h
    norm_num [add_assoc] at h
    rw [← hl j] at h
    change 0 < R j + S.a (j + 2) * (R j * lam j) at h
    nlinarith only [h]
  have hF3 (j : Fin 5) : 0 < R j * (s j - S.a j * S.a (j + 3)) := by
    have h := (S.F_B_pos j).2.1
    rw [hF] at h
    norm_num [add_assoc] at h
    rw [hX2, ← hs j] at h
    change 0 < R j * s j + S.a (j + 3) * (-S.a j * R j) at h
    nlinarith only [h]
  have hF4 (j : Fin 5) : 0 < R j *
      (lam j - S.a (j + 4) * S.a (j + 1) * s j) := by
    have h := (S.F_B_pos j).2.2
    rw [hF] at h
    norm_num [add_assoc] at h
    rw [hX3, ← hs j, ← hl j] at h
    change 0 < R j * lam j + S.a (j + 4) * (-S.a (j + 1) * (R j * s j)) at h
    nlinarith only [h]
  exact normalized_support_obstruction S.a s lam R S.u S.t
    S.a_pos S.u_pos S.t_pos hleft hright hlam hF2 hF3 hF4

end NormalizedSupportSystem

end Papers.RationalWitnesses.A40

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/A40ActualObstruction.lean -/





@[expose] public section

/-!
# The A40 boundary has no actual real four-polytope realization

The ten bipyramidal facet masks below are those of Appendix B's A40 pattern,
written with `A = (0,1,3,2,9)` and `B = (4,6,7,5,8)`. The argument needs only
these ten exact supporting faces. Positivity at every omitted vertex is
derived from the actual supporting affine form of the face.

No chart, frame, sign pattern, or rationality hypothesis is supplied by the
caller. In particular, the five A-points are proved to be a homogeneous
basis by the preceding support-geometry theorem.


-/

noncomputable section

namespace Papers.RationalWitnesses.A40

open Module Set
open scoped Classical
open Papers.Polytopes Papers.Coordinates Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

def ALabel : Fin 5 → Fin 10 := ![0, 1, 3, 2, 9]
def BLabel : Fin 5 → Fin 10 := ![4, 6, 7, 5, 8]

def FMask (i : Fin 5) : Finset (Fin 10) :=
  {ALabel i, ALabel (i + 1), ALabel (i + 3), BLabel i, BLabel (i + 4)}

/-- This is the paper's `G_(i+2)`; the shift makes its nonzero A-evaluations
occur at cyclic positions `i+1`, `i+3`, `i+4`. -/
def GMask (i : Fin 5) : Finset (Fin 10) :=
  {ALabel i, ALabel (i + 2), BLabel (i + 4), BLabel i, BLabel (i + 1)}

theorem mem_FMask_A : ∀ i j : Fin 5,
    ALabel j ∈ FMask i ↔ j ≠ i + 2 ∧ j ≠ i + 4 := by decide +kernel

theorem mem_GMask_A : ∀ i j : Fin 5,
    ALabel j ∈ GMask i ↔ j ≠ i + 1 ∧ j ≠ i + 3 ∧ j ≠ i + 4 := by decide +kernel

theorem FMask_B_zero : ∀ i : Fin 5,
    BLabel i ∈ FMask i ∧ BLabel i ∈ FMask (i + 1) := by decide +kernel

theorem FMask_B_pos : ∀ i : Fin 5,
    BLabel i ∉ FMask (i + 2) ∧ BLabel i ∉ FMask (i + 3) ∧
      BLabel i ∉ FMask (i + 4) := by decide +kernel

theorem GMask_B_zero : ∀ i : Fin 5,
    BLabel (i + 4) ∈ GMask i ∧ BLabel i ∈ GMask i ∧
      BLabel (i + 1) ∈ GMask i := by decide +kernel

private theorem distinct_F_positions : ∀ i : Fin 5, i + 2 ≠ i + 4 := by decide +kernel
private theorem distinct_G_positions : ∀ i : Fin 5,
    i + 1 ≠ i + 3 ∧ i + 1 ≠ i + 4 ∧ i + 3 ≠ i + 4 := by decide +kernel

/-- An exact inclusion of the ten cyclic supporting facets into the actual
polytope face lattice. A complete facet-list correspondence implies this
predicate, but completeness is not required for the exclusion. -/
structure ActualFacetPattern (P : ConvexPolytope 4) (lab : Fin 10 → VertexType P) where
  F : Fin 5 → FacetType P
  G : Fin 5 → FacetType P
  F_mem : ∀ i j, (lab j).val ∈ (F i).val.val ↔ j ∈ FMask i
  G_mem : ∀ i j, (lab j).val ∈ (G i).val.val ↔ j ∈ GMask i

private theorem support_positive_of_vertex_not_mem
    (P : ConvexPolytope 4) (F : FacetType P) (v : VertexType P)
    (hv : v.val ∉ F.val.val) : 0 < chosenFacetForm P F v.val := by
  have hf := chosenFacetForm_supports P F
  have hbody := vertex_mem_body P v.property
  have hn := hf.1 v.val hbody
  have hne : chosenFacetForm P F v.val ≠ 0 := by
    intro hz
    exact hv ((hf.mem_iff v.val).mpr ⟨hbody, hz⟩)
  exact lt_of_le_of_ne hn (Ne.symm hne)

/-- The ten actual supporting faces already contradict the cyclic sign
obstruction. No assumption of full dimension, or even injectivity of the
given labels, is added: any such realization supplies the impossible
normalized support system. -/
theorem no_actual_facet_pattern (P : ConvexPolytope 4)
    (lab : Fin 10 → VertexType P) (H : ActualFacetPattern P lab) : False := by
  let A : Fin 5 → E 4 × ℝ := fun i => ((lab (ALabel i)).val, 1)
  let B : Fin 5 → E 4 × ℝ := fun i => ((lab (BLabel i)).val, 1)
  let f : Fin 5 → (E 4 × ℝ) →ₗ[ℝ] ℝ :=
    fun i => affineLift (chosenFacetForm P (H.F i))
  let g : Fin 5 → (E 4 × ℝ) →ₗ[ℝ] ℝ :=
    fun i => affineLift (chosenFacetForm P (H.G i))
  have hf_eval (i : Fin 5) (j : Fin 10) :
      f i ((lab j).val, 1) = chosenFacetForm P (H.F i) (lab j).val := by
    simp only [f, affineLift_apply, homogeneousEvaluation_homogenize]
  have hg_eval (i : Fin 5) (j : Fin 10) :
      g i ((lab j).val, 1) = chosenFacetForm P (H.G i) (lab j).val := by
    simp only [g, affineLift_apply, homogeneousEvaluation_homogenize]
  have hf_zero (i : Fin 5) (j : Fin 10) (hj : j ∈ FMask i) :
      f i ((lab j).val, 1) = 0 := by
    rw [hf_eval]
    exact (chosenFacetForm_supports P (H.F i)).eq_zero ((H.F_mem i j).mpr hj)
  have hg_zero (i : Fin 5) (j : Fin 10) (hj : j ∈ GMask i) :
      g i ((lab j).val, 1) = 0 := by
    rw [hg_eval]
    exact (chosenFacetForm_supports P (H.G i)).eq_zero ((H.G_mem i j).mpr hj)
  have hf_pos (i : Fin 5) (j : Fin 10) (hj : j ∉ FMask i) :
      0 < f i ((lab j).val, 1) := by
    rw [hf_eval]
    apply support_positive_of_vertex_not_mem P (H.F i) (lab j)
    exact fun h => hj ((H.F_mem i j).mp h)
  have hg_pos (i : Fin 5) (j : Fin 10) (hj : j ∉ GMask i) :
      0 < g i ((lab j).val, 1) := by
    rw [hg_eval]
    apply support_positive_of_vertex_not_mem P (H.G i) (lab j)
    exact fun h => hj ((H.G_mem i j).mp h)
  have hfa2 (i : Fin 5) : 0 < f i (A (i + 2)) := by
    apply hf_pos
    rw [mem_FMask_A]
    simp
  have hfa4 (i : Fin 5) : 0 < f i (A (i + 4)) := by
    apply hf_pos
    rw [mem_FMask_A]
    simp
  have hga1 (i : Fin 5) : 0 < g i (A (i + 1)) := by
    apply hg_pos
    rw [mem_GMask_A]
    simp
  have hga3 (i : Fin 5) : 0 < g i (A (i + 3)) := by
    apply hg_pos
    rw [mem_GMask_A]
    simp
  have hga4 (i : Fin 5) : 0 < g i (A (i + 4)) := by
    apply hg_pos
    rw [mem_GMask_A]
    simp
  let F : Fin 5 → (E 4 × ℝ) →ₗ[ℝ] ℝ := fun i => (f i (A (i + 2)))⁻¹ • f i
  let G : Fin 5 → (E 4 × ℝ) →ₗ[ℝ] ℝ := fun i => (g i (A (i + 1)))⁻¹ • g i
  let a : Fin 5 → ℝ := fun i => f i (A (i + 4)) / f i (A (i + 2))
  let u : Fin 5 → ℝ := fun i => g i (A (i + 3)) / g i (A (i + 1))
  let t : Fin 5 → ℝ := fun i => g i (A (i + 4)) / g i (A (i + 1))
  have hFa (i : Fin 5) (v : E 4 × ℝ) : F i v = f i v / f i (A (i + 2)) := by
    simp only [F, LinearMap.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hGa (i : Fin 5) (v : E 4 × ℝ) : G i v = g i v / g i (A (i + 1)) := by
    simp only [G, LinearMap.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hFA (i j : Fin 5) : F i (A j) =
      (if j = i + 2 then 1 else 0) + (if j = i + 4 then a i else 0) := by
    rw [hFa]
    by_cases h2 : j = i + 2
    · subst j
      simp [distinct_F_positions i, ne_of_gt (hfa2 i)]
    by_cases h4 : j = i + 4
    · subst j
      simp [Ne.symm (distinct_F_positions i), a]
    have hz : f i (A j) = 0 :=
      hf_zero i (ALabel j) ((mem_FMask_A i j).mpr ⟨h2, h4⟩)
    simp [hz, h2, h4]
  have hGA (i j : Fin 5) : G i (A j) =
      (if j = i + 1 then 1 else 0) + (if j = i + 3 then u i else 0) +
        (if j = i + 4 then t i else 0) := by
    rw [hGa]
    by_cases h1 : j = i + 1
    · subst j
      simp [(distinct_G_positions i).1, (distinct_G_positions i).2.1,
        ne_of_gt (hga1 i)]
    by_cases h3 : j = i + 3
    · subst j
      simp [Ne.symm (distinct_G_positions i).1, (distinct_G_positions i).2.2, u]
    by_cases h4 : j = i + 4
    · subst j
      simp [Ne.symm (distinct_G_positions i).2.1, Ne.symm (distinct_G_positions i).2.2, t]
    have hz : g i (A j) = 0 :=
      hg_zero i (ALabel j) ((mem_GMask_A i j).mpr ⟨h1, h3, h4⟩)
    simp [hz, h1, h3, h4]
  let S : NormalizedSupportSystem (E 4 × ℝ) := {
    A := A, B := B, F := F, G := G, a := a, u := u, t := t
    a_pos := fun i => div_pos (hfa4 i) (hfa2 i)
    u_pos := fun i => div_pos (hga3 i) (hga1 i)
    t_pos := fun i => div_pos (hga4 i) (hga1 i)
    F_A := hFA, G_A := hGA
    F_B_zero := by
      intro i
      constructor
      · rw [hFa, hf_zero i (BLabel i) (FMask_B_zero i).1, zero_div]
      · rw [hFa, hf_zero (i + 1) (BLabel i) (FMask_B_zero i).2, zero_div]
    G_B_zero := by
      intro i
      refine ⟨?_, ?_, ?_⟩
      · rw [hGa, hg_zero i (BLabel (i + 4)) (GMask_B_zero i).1, zero_div]
      · rw [hGa, hg_zero i (BLabel i) (GMask_B_zero i).2.1, zero_div]
      · rw [hGa, hg_zero i (BLabel (i + 1)) (GMask_B_zero i).2.2, zero_div]
    F_B_pos := by
      intro i
      refine ⟨?_, ?_, ?_⟩
      · rw [hFa]
        exact div_pos (hf_pos (i + 2) (BLabel i) (FMask_B_pos i).1) (hfa2 (i + 2))
      · rw [hFa]
        exact div_pos (hf_pos (i + 3) (BLabel i) (FMask_B_pos i).2.1) (hfa2 (i + 3))
      · rw [hFa]
        exact div_pos (hf_pos (i + 4) (BLabel i) (FMask_B_pos i).2.2) (hfa2 (i + 4)) }
  exact S.impossible (by simp [Module.finrank_prod, finrank_euclideanSpace_fin])

end Papers.RationalWitnesses.A40

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/A40BoundaryExclusion.lean -/




@[expose] public section

/-!
# Finite-boundary interface for the A40 exclusion

The exact complete-boundary predicate comes from actual polytope geometry.
The finite check below only identifies the ten required facet masks inside
the literal family printed in Appendix B.2.


-/

noncomputable section
namespace Papers.RationalWitnesses.A40

open scoped Classical
open Papers.Polytopes
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

def TMask (i : Fin 5) : Finset (Fin 10) :=
  {ALabel i, ALabel (i + 3), BLabel i, BLabel (i + 1)}

def paperFacetFamily : Finset (Finset (Fin 10)) :=
  Finset.univ.image FMask ∪ Finset.univ.image GMask ∪ Finset.univ.image TMask

theorem FMask_mem_paperFacetFamily (i : Fin 5) : FMask i ∈ paperFacetFamily := by
  exact Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))

theorem GMask_mem_paperFacetFamily (i : Fin 5) : GMask i ∈ paperFacetFamily := by
  exact Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))

theorem paperFacetFamily_card : paperFacetFamily.card = 15 := by decide +kernel

/-- It suffices that the exact actual facet family contains the ten cyclic
facets. In particular this applies to the complete A40 family. -/
theorem no_realizes_boundary_containing_A40
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (B : Boundary 9)
    (hB : RealizesBoundary P lab B)
    (hF : ∀ i, FMask i ∈ B.facets) (hG : ∀ i, GMask i ∈ B.facets) : False := by
  apply no_actual_facet_pattern P lab
  exact {
    F := fun i => hB.facetFor ⟨FMask i, hF i⟩
    G := fun i => hB.facetFor ⟨GMask i, hG i⟩
    F_mem := fun i j => hB.facetFor_mem ⟨FMask i, hF i⟩ j
    G_mem := fun i j => hB.facetFor_mem ⟨GMask i, hG i⟩ j }

theorem no_realizes_A40_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (B : Boundary 9)
    (hB : RealizesBoundary P lab B) (hfacets : B.facets = paperFacetFamily) : False := by
  apply no_realizes_boundary_containing_A40 P lab B hB
  · intro i
    rw [hfacets]
    exact FMask_mem_paperFacetFamily i
  · intro i
    rw [hfacets]
    exact GMask_mem_paperFacetFamily i

end Papers.RationalWitnesses.A40

end
end
end BundlePart3
