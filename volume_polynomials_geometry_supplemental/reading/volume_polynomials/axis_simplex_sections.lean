module

public import VolumePolynomials.AxisSimplex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Sections of a sum of two ordered axis simplices

When the first axis of the second simplex is its shortest, a section of
`t Δ + s Λ` allocates as much first-coordinate height as possible to Δ.
The proof is a literal set equality. Moving height from Λ to Δ enlarges
the remaining section because the shortest-axis multiple of Δ is
contained in the tail simplex.
-/

open Set
open scoped Pointwise BigOperators

namespace VolumePolynomials.AxisSimplex

open SimplexCoordinates

theorem add_body_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B C D : ConvexBody E} (hAB : A ≤ B) (hCD : C ≤ D) : A + C ≤ B + D := by
  first
  | rintro _ ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hAB hx, y, hCD hy, rfl⟩

theorem smul_body_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : ConvexBody E} (hAB : A ≤ B) (r : ℝ) : r • A ≤ r • B := by
  first
  | rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hAB hx, rfl⟩

theorem transfer_summand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P Q : ConvexBody E) {c : ℝ} (hc : 0 < c) (hPQ : c • P ≤ Q)
    {a b δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hδb : δ / c ≤ b) :
    (a + δ) • P + (b - δ / c) • Q ≤ a • P + b • Q := by
  first
  | have hd : 0 ≤ δ / c := div_nonneg hδ hc.le
    have hrest : 0 ≤ b - δ / c := sub_nonneg.mpr hδb
    have hdelta : δ • P ≤ (δ / c) • Q := by
      first
      | have heq : δ • P = (δ / c) • (c • P) := by
          rw [smul_smul, div_mul_cancel₀ δ hc.ne']
        rw [heq]
        exact smul_body_mono hPQ _
    calc
      (a + δ) • P + (b - δ / c) • Q =
          (a • P + δ • P) + (b - δ / c) • Q := by rw [body_add_smul P ha hδ]
      _ ≤ (a • P + (δ / c) • Q) + (b - δ / c) • Q :=
        add_body_mono (add_body_mono le_rfl hdelta) le_rfl
      _ = a • P + b • Q := by
        first
        | rw [add_assoc, ← body_add_smul Q hd hrest]
          congr 2
          ring

def firstSection {n : ℕ} (K : Body (n + 1)) (z : ℝ) : Set (Space n) :=
  {x | Fin.cons z x ∈ K}

theorem firstSection_sum_support {n : ℕ} {lam : Fin (n + 1) → ℝ}
    (hlam : ∀ i, 0 < lam i) {t s z : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hne : (firstSection (t • body (n + 1) + s • axisBody lam) z).Nonempty) :
    0 ≤ z ∧ z ≤ t + s * lam 0 := by
  first
  | obtain ⟨x, u, hu, v, hv, heq⟩ := hne
    have hu' : u ∈ t • axisBody (fun _ : Fin (n + 1) => 1) := by
      first
      | rwa [axisBody_one]
    have h0 : u 0 + v 0 = z := congrArg (fun w : Space (n + 1) => w 0) heq
    have hu0 := coordinate_nonnegative (fun _ => zero_lt_one) ht hu' 0
    have hv0 := coordinate_nonnegative hlam hs hv 0
    have hut := coordinate_upper_bound (fun _ => zero_lt_one) ht hu' 0
    have hvs := coordinate_upper_bound hlam hs hv 0
    constructor <;> nlinarith

theorem firstSection_sum_empty {n : ℕ} {lam : Fin (n + 1) → ℝ}
    (hlam : ∀ i, 0 < lam i) {t s z : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hz : z ∉ Icc (0 : ℝ) (t + s * lam 0)) :
    firstSection (t • body (n + 1) + s • axisBody lam) z = ∅ := by
  first
  | apply Set.not_nonempty_iff_eq_empty.mp
    intro hne
    exact hz (firstSection_sum_support hlam ht hs hne)

theorem firstSection_sum_lower {n : ℕ} {lam : Fin (n + 1) → ℝ}
    (hlam : ∀ i, 0 < lam i) (hmin : ∀ i : Fin n, lam 0 ≤ lam i.succ)
    {t s z : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hz0 : 0 ≤ z) (hzt : z ≤ t) :
    firstSection (t • body (n + 1) + s • axisBody lam) z =
      ((t - z) • body n + s • axisBody (Fin.tail lam) : Body n) := by
  first
  | have hcontain : lam 0 • body n ≤ axisBody (Fin.tail lam) :=
      scaled_simplex_subset_axisBody (fun i => hlam i.succ) (hlam 0).le hmin
    ext x
    constructor
    · rintro ⟨u, hu, v, hv, heq⟩
      have hu' : u ∈ t • axisBody (fun _ : Fin (n + 1) => 1) := by
        first
        | rwa [axisBody_one]
      have hu0 := coordinate_nonnegative (fun _ => zero_lt_one) ht hu' 0
      have hv0 := coordinate_nonnegative hlam hs hv 0
      have hut : u 0 ≤ t := by
        first
        | simpa only [mul_one] using coordinate_upper_bound (fun _ => zero_lt_one) ht hu' 0
      have hvs := coordinate_upper_bound hlam hs hv 0
      have h0 : u 0 + v 0 = z := congrArg (fun w : Space (n + 1) => w 0) heq
      have htail : Fin.tail u + Fin.tail v = x := by
        first
        | funext i
          exact congrArg (fun w : Space (n + 1) => w i.succ) heq
      have husection : Fin.tail u ∈ (t - u 0) • body n := by
        first
        | have h := Set.ext_iff.mp (section_smul_axisBody (fun _ => zero_lt_one) ht hu0
            (by simpa only [mul_one] using hut)) (Fin.tail u)
          have hone : Fin.tail (fun _ : Fin (n + 1) => (1 : ℝ)) =
              (fun _ : Fin n => (1 : ℝ)) := rfl
          simp only [hone, axisBody_one, div_one, Set.mem_setOf_eq,
            ← ConvexBody.coe_smul] at h
          apply Iff.mp h
          simpa only [axisBody_one, Fin.cons_self_tail] using hu'
      have hvsection : Fin.tail v ∈ (s - v 0 / lam 0) • axisBody (Fin.tail lam) := by
        first
        | apply (Set.ext_iff.mp (section_smul_axisBody hlam hs hv0 hvs) (Fin.tail v)).mp
          change Fin.cons (v 0) (Fin.tail v) ∈
            ((s • axisBody lam : Body (n + 1)) : Set (Space (n + 1)))
          rw [Fin.cons_self_tail]
          exact hv
      have htransfer := transfer_summand (body n) (axisBody (Fin.tail lam))
        (hlam 0) hcontain (sub_nonneg.mpr hzt) hv0
        ((div_le_iff₀ (hlam 0)).mpr hvs)
      have harith : (t - z) + v 0 = t - u 0 := by linarith
      rw [harith] at htransfer
      exact htransfer ⟨Fin.tail u, husection, Fin.tail v, hvsection, htail⟩
    · rintro ⟨u, hu, v, hv, huv⟩
      have hu' : Fin.cons z u ∈ t • body (n + 1) := by
        first
        | have h := Set.ext_iff.mp (section_smul_axisBody (fun _ : Fin (n + 1) => zero_lt_one)
            ht hz0 (by simpa only [mul_one] using hzt)) u
          have hone : Fin.tail (fun _ : Fin (n + 1) => (1 : ℝ)) =
              (fun _ : Fin n => (1 : ℝ)) := rfl
          simp only [hone, axisBody_one, div_one, Set.mem_setOf_eq,
            ← ConvexBody.coe_smul] at h
          apply Iff.mpr h
          change u ∈ (t - z) • body n
          exact hu
      have hv' : Fin.cons 0 v ∈ s • axisBody lam := by
        first
        | apply (Set.ext_iff.mp (section_smul_axisBody hlam hs le_rfl
            (mul_nonneg hs (hlam 0).le)) v).mpr
          simp only [zero_div, sub_zero]
          change v ∈ s • axisBody (Fin.tail lam)
          exact hv
      refine ⟨Fin.cons z u, hu', Fin.cons 0 v, hv', ?_⟩
      funext i
      cases i using Fin.cases with
      | zero => simp
      | succ i => exact congrFun huv i

theorem firstSection_sum_upper {n : ℕ} {lam : Fin (n + 1) → ℝ}
    (hlam : ∀ i, 0 < lam i) (hmin : ∀ i : Fin n, lam 0 ≤ lam i.succ)
    {t s z : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (htz : t ≤ z)
    (hzs : z ≤ t + s * lam 0) :
    firstSection (t • body (n + 1) + s • axisBody lam) z =
      (s - (z - t) / lam 0) • (axisBody (Fin.tail lam) : Set (Space n)) := by
  first
  | have hcontain : lam 0 • body n ≤ axisBody (Fin.tail lam) :=
      scaled_simplex_subset_axisBody (fun i => hlam i.succ) (hlam 0).le hmin
    have hr : 0 ≤ s - (z - t) / lam 0 :=
      sub_nonneg.mpr ((div_le_iff₀ (hlam 0)).mpr (by linarith))
    ext x
    constructor
    · rintro ⟨u, hu, v, hv, heq⟩
      have hu' : u ∈ t • axisBody (fun _ : Fin (n + 1) => 1) := by
        first
        | rwa [axisBody_one]
      have hu0 := coordinate_nonnegative (fun _ => zero_lt_one) ht hu' 0
      have hv0 := coordinate_nonnegative hlam hs hv 0
      have hut : u 0 ≤ t := by
        first
        | simpa only [mul_one] using coordinate_upper_bound (fun _ => zero_lt_one) ht hu' 0
      have hvs := coordinate_upper_bound hlam hs hv 0
      have h0 : u 0 + v 0 = z := congrArg (fun w : Space (n + 1) => w 0) heq
      have htail : Fin.tail u + Fin.tail v = x := by
        first
        | funext i
          exact congrArg (fun w : Space (n + 1) => w i.succ) heq
      have husection : Fin.tail u ∈ (t - u 0) • body n := by
        first
        | have h := Set.ext_iff.mp (section_smul_axisBody (fun _ => zero_lt_one) ht hu0
            (by simpa only [mul_one] using hut)) (Fin.tail u)
          have hone : Fin.tail (fun _ : Fin (n + 1) => (1 : ℝ)) =
              (fun _ : Fin n => (1 : ℝ)) := rfl
          simp only [hone, axisBody_one, div_one, Set.mem_setOf_eq,
            ← ConvexBody.coe_smul] at h
          apply Iff.mp h
          simpa only [axisBody_one, Fin.cons_self_tail] using hu'
      have hvsection : Fin.tail v ∈ (s - v 0 / lam 0) • axisBody (Fin.tail lam) := by
        first
        | apply (Set.ext_iff.mp (section_smul_axisBody hlam hs hv0 hvs) (Fin.tail v)).mp
          change Fin.cons (v 0) (Fin.tail v) ∈
            ((s • axisBody lam : Body (n + 1)) : Set (Space (n + 1)))
          rw [Fin.cons_self_tail]
          exact hv
      have hδb : (t - u 0) / lam 0 ≤ s - (z - t) / lam 0 := by
        first
        | have hvs' := (div_le_iff₀ (hlam 0)).mpr hvs
          have hid : (t - u 0) / lam 0 + (z - t) / lam 0 = v 0 / lam 0 := by
            rw [← add_div]
            congr 1
            linarith
          linarith
      have htransfer := transfer_summand (body n) (axisBody (Fin.tail lam))
        (hlam 0) hcontain (a := 0) le_rfl (sub_nonneg.mpr hut) hδb
      have harith : s - (z - t) / lam 0 - (t - u 0) / lam 0 = s - v 0 / lam 0 := by
        first
        | rw [sub_sub, ← add_div]
          congr 2
          linarith
      simp only [zero_add, body_zero_smul, harith] at htransfer
      exact htransfer ⟨Fin.tail u, husection, Fin.tail v, hvsection, htail⟩
    · intro hx
      have hu : Fin.cons t (0 : Space n) ∈ t • body (n + 1) := by
        first
        | refine ⟨Pi.single (0 : Fin (n + 1)) 1, coordinate_mem_simplex 0, ?_⟩
          funext i
          cases i using Fin.cases <;> simp [Pi.single_apply]
      have hv : Fin.cons (z - t) x ∈ s • axisBody lam := by
        first
        | apply (Set.ext_iff.mp (section_smul_axisBody hlam hs (sub_nonneg.mpr htz)
            (by linarith)) x).mpr
          exact hx
      refine ⟨Fin.cons t 0, hu, Fin.cons (z - t) x, hv, ?_⟩
      funext i
      cases i using Fin.cases <;> simp

end VolumePolynomials.AxisSimplex
