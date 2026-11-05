module

public import mixed_volume.general.indexed_series

/-! Word directions and the exact stochastic weights used by the general
mixed-volume reduction.  Words include the empty word. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.AutomatonWords

open Set Matrix
open scoped BigOperators

abbrev Plane := ℝ × ℝ
abbrev Word (s : ℕ) := List (Fin s)

def base (s : ℕ) : ℝ := (s : ℝ) + 1
def rho (s : ℕ) : ℝ := 1 / (4 * (s : ℝ))

theorem base_pos (s : ℕ) : 0 < base s := by
  dsimp [base]
  positivity

theorem rho_pos {s : ℕ} (hs : 0 < s) : 0 < rho s := by
  dsimp [rho]
  positivity

theorem card_mul_rho {s : ℕ} (hs : 0 < s) : (s : ℝ) * rho s = 1 / 4 := by
  have h : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  dsimp [rho]
  field_simp

def tag {s : ℕ} : Word s → ℝ
  | [] => 0
  | a :: w => ((a.val : ℝ) + 1 + tag w) / base s

@[simp] theorem tag_nil {s : ℕ} : tag ([] : Word s) = 0 := rfl
@[simp] theorem tag_cons {s : ℕ} (a : Fin s) (w : Word s) :
    tag (a :: w) = ((a.val : ℝ) + 1 + tag w) / base s := rfl

theorem tag_nonneg {s : ℕ} (w : Word s) : 0 ≤ tag w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [tag_cons]
    exact div_nonneg (by positivity) (base_pos s).le

theorem tag_lt_one {s : ℕ} (w : Word s) : tag w < 1 := by
  induction w with
  | nil => norm_num
  | cons a w ih =>
    rw [tag_cons, div_lt_one (base_pos s)]
    have ha : (a.val : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast a.isLt
    dsimp [base]
    linarith

theorem tag_cons_pos {s : ℕ} (a : Fin s) (w : Word s) : 0 < tag (a :: w) := by
  rw [tag_cons]
  exact div_pos (by have := tag_nonneg w; positivity) (base_pos s)

theorem tag_cons_lt_of_head_lt {s : ℕ} {a b : Fin s}
    (hab : a < b) (u v : Word s) : tag (a :: u) < tag (b :: v) := by
  rw [tag_cons, tag_cons, div_lt_div_iff_of_pos_right (base_pos s)]
  have hab' : (a.val : ℝ) + 1 ≤ (b.val : ℝ) := by exact_mod_cast hab
  have hu := tag_lt_one u
  have hv := tag_nonneg v
  linarith

theorem tag_injective {s : ℕ} : Function.Injective (@tag s) := by
  intro u
  induction u with
  | nil =>
    intro v h
    cases v with
    | nil => rfl
    | cons b v =>
      have hb := tag_cons_pos b v
      simp only [tag_nil] at h
      linarith
  | cons a u ih =>
    intro v h
    cases v with
    | nil =>
      have ha := tag_cons_pos a u
      simp only [tag_nil] at h
      linarith
    | cons b v =>
      have hab : a = b := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have := tag_cons_lt_of_head_lt hlt u v
          linarith
        · have := tag_cons_lt_of_head_lt hgt v u
          linarith
      subst b
      have huv : tag u = tag v := by
        rw [tag_cons, tag_cons] at h
        have hh := (div_left_inj' (base_pos s).ne').mp h
        linarith
      exact congrArg (List.cons a) (ih huv)

def transition {s : ℕ} (a : Fin s) : Plane →L[ℝ] Plane where
  toFun p := (rho s / base s * (p.1 + ((a.val : ℝ) + 1) * p.2), rho s * p.2)
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' r p := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply] <;> ring
  cont := by fun_prop

@[simp] theorem transition_apply {s : ℕ} (a : Fin s) (p : Plane) :
    transition a p =
      (rho s / base s * (p.1 + ((a.val : ℝ) + 1) * p.2), rho s * p.2) := rfl

def generator {s : ℕ} (w : Word s) : Plane :=
  (rho s) ^ w.length • (tag w, 1)

@[simp] theorem generator_nil {s : ℕ} : generator ([] : Word s) = (0, 1) := by
  simp [generator]

theorem generator_cons {s : ℕ} (a : Fin s) (w : Word s) :
    generator (a :: w) = transition a (generator w) := by
  ext <;> simp only [generator, List.length_cons, tag_cons, transition_apply,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul, pow_succ] <;> ring

theorem generator_norm {s : ℕ} (hs : 0 < s) (w : Word s) :
    ‖generator w‖ = rho s ^ w.length := by
  rw [generator, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (rho_pos hs).le _)]
  have ht : ‖(tag w, (1 : ℝ))‖ = 1 := by
    change max ‖tag w‖ ‖(1 : ℝ)‖ = 1
    rw [Real.norm_eq_abs, abs_of_nonneg (tag_nonneg w), norm_one,
      max_eq_right (tag_lt_one w).le]
  rw [ht, mul_one]

/-- Counting by word length proves absolute convergence for every finite alphabet. -/
theorem summable_pow_length (s : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hcontract : (s : ℝ) * r < 1) :
    Summable (fun w : Word s => r ^ w.length) := by
  let e : (Σ n : ℕ, List.Vector (Fin s) n) ≃ Word s :=
    { toFun := fun p => p.2.1
      invFun := fun w => ⟨w.length, ⟨w, rfl⟩⟩
      left_inv := by rintro ⟨n, w, hw⟩; cases hw; rfl
      right_inv := by intro w; rfl }
  have hnonneg : ∀ p : (Σ n : ℕ, List.Vector (Fin s) n), 0 ≤ r ^ p.1 :=
    fun p => pow_nonneg hr _
  have hsum : Summable (fun p : (Σ n : ℕ, List.Vector (Fin s) n) => r ^ p.1) := by
    apply (summable_sigma_of_nonneg hnonneg).2
    refine ⟨fun n => Summable.of_finite, ?_⟩
    have hg := summable_geometric_of_lt_one (mul_nonneg (Nat.cast_nonneg s) hr) hcontract
    simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, card_vector,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, mul_pow] using hg
  apply e.summable_iff.mp
  change Summable (fun p : (Σ n : ℕ, List.Vector (Fin s) n) => r ^ p.2.1.length)
  simpa only [List.Vector.length_val] using hsum

theorem generator_summable {s : ℕ} (hs : 0 < s) :
    Summable (fun w : Word s => ‖generator w‖) := by
  simp only [generator_norm hs]
  apply summable_pow_length s (rho s) (rho_pos hs).le
  rw [card_mul_rho hs]
  norm_num

def tagNormal {s : ℕ} (w : Word s) : Plane →L[ℝ] ℝ where
  toFun p := p.1 - tag w * p.2
  map_add' p q := by dsimp; ring
  map_smul' r p := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ring
  cont := by fun_prop

theorem tagNormal_generator {s : ℕ} (w v : Word s) :
    tagNormal w (generator v) = rho s ^ v.length * (tag v - tag w) := by
  simp only [generator, map_smul, smul_eq_mul]
  change rho s ^ v.length * (tag v - tag w * 1) = _
  ring

theorem tagNormal_generator_ne {s : ℕ} (hs : 0 < s) (w v : Word s) (hvw : v ≠ w) :
    tagNormal w (generator v) ≠ 0 := by
  rw [tagNormal_generator]
  exact mul_ne_zero (pow_ne_zero _ (rho_pos hs).ne')
    (sub_ne_zero.mpr (tag_injective.ne hvw))

/-- A probability row has its literal nonnegative entries and unit sum. -/
def ProbabilityRow {m : ℕ} (p : Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1

/-- The input data for the geometric theorem, before rationality is imposed. -/
structure Data (s m : ℕ) where
  P : Fin s → Matrix (Fin m) (Fin m) ℝ
  P_nonneg : ∀ a j k, 0 ≤ P a j k
  P_sum : ∀ a j, ∑ k, P a j k = 1
  f : Fin m → ℝ
  f_nonneg : ∀ j, 0 ≤ f j
  f_le_one : ∀ j, f j ≤ 1
  stationary : Fin m → ℝ
  stationary_probability : ProbabilityRow stationary
  stationary_fixed : ∀ a, stationary ᵥ* P a = stationary

namespace Data

variable {s m : ℕ} (A : Data s m)

def wordMatrix (A : Data s m) : Word s → Matrix (Fin m) (Fin m) ℝ
  | [] => 1
  | a :: w => A.P a * wordMatrix A w

@[simp] theorem wordMatrix_nil : A.wordMatrix [] = 1 := rfl
@[simp] theorem wordMatrix_cons (a : Fin s) (w : Word s) :
    A.wordMatrix (a :: w) = A.P a * A.wordMatrix w := rfl

theorem wordMatrix_nonneg (w : Word s) (j k : Fin m) : 0 ≤ A.wordMatrix w j k := by
  induction w generalizing j with
  | nil => simp only [wordMatrix_nil, Matrix.one_apply]; split <;> positivity
  | cons a w ih =>
    rw [wordMatrix_cons, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (A.P_nonneg a j l) (ih l))

theorem wordMatrix_sum (w : Word s) (j : Fin m) : ∑ k, A.wordMatrix w j k = 1 := by
  induction w generalizing j with
  | nil => simp [wordMatrix_nil, Matrix.one_apply]
  | cons a w ih =>
    simp only [wordMatrix_cons, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ih, mul_one]
    exact A.P_sum a j

def value (w : Word s) (j : Fin m) : ℝ := (A.wordMatrix w *ᵥ A.f) j

theorem value_nonneg (w : Word s) (j : Fin m) : 0 ≤ A.value w j := by
  unfold value Matrix.mulVec dotProduct
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (A.wordMatrix_nonneg w j k) (A.f_nonneg k))

theorem value_le_one (w : Word s) (j : Fin m) : A.value w j ≤ 1 := by
  calc
    A.value w j = ∑ k, A.wordMatrix w j k * A.f k := rfl
    _ ≤ ∑ k, A.wordMatrix w j k * 1 :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (A.f_le_one k) (A.wordMatrix_nonneg w j k)
    _ = 1 := by simpa only [mul_one] using A.wordMatrix_sum w j

@[simp] theorem value_nil (j : Fin m) : A.value [] j = A.f j := by
  simp [value]

theorem value_cons (a : Fin s) (w : Word s) (j : Fin m) :
    A.value (a :: w) j = ∑ k, A.P a j k * A.value w k := by
  rw [value, wordMatrix_cons, ← Matrix.mulVec_mulVec]
  rfl

def weight (w : Word s) (j : Fin m) : ℝ := 1 + A.value w j

theorem weight_pos (w : Word s) (j : Fin m) : 0 < A.weight w j := by
  dsimp [weight]
  linarith [A.value_nonneg w j]

theorem weight_le_two (w : Word s) (j : Fin m) : A.weight w j ≤ 2 := by
  dsimp [weight]
  linarith [A.value_le_one w j]

@[simp] theorem weight_nil (j : Fin m) : A.weight [] j = 1 + A.f j := by
  simp [weight]

theorem weight_cons (a : Fin s) (w : Word s) (j : Fin m) :
    A.weight (a :: w) j = ∑ k, A.P a j k * A.weight w k := by
  simp only [weight, value_cons, mul_add, mul_one, Finset.sum_add_distrib, A.P_sum]

theorem stationary_word (w : Word s) : A.stationary ᵥ* A.wordMatrix w = A.stationary := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [wordMatrix_cons, ← Matrix.vecMul_vecMul, A.stationary_fixed, ih]

def gamma : ℝ := A.stationary ⬝ᵥ A.f

theorem stationary_value (w : Word s) :
    A.stationary ⬝ᵥ A.value w = A.gamma := by
  unfold value gamma
  rw [Matrix.dotProduct_mulVec, A.stationary_word]

theorem stationary_weight (w : Word s) :
    (∑ j, A.stationary j * A.weight w j) = 1 + A.gamma := by
  simp only [weight, mul_add, mul_one, Finset.sum_add_distrib,
    A.stationary_probability.2]
  exact congrArg (1 + ·) (A.stationary_value w)

def acceptance (p : Fin m → ℝ) (w : Word s) : ℝ := p ⬝ᵥ A.value w

theorem acceptance_nonneg (p : Fin m → ℝ) (hp : ProbabilityRow p) (w : Word s) :
    0 ≤ A.acceptance p w := by
  unfold acceptance dotProduct
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hp.1 j) (A.value_nonneg w j))

theorem acceptance_le_one (p : Fin m → ℝ) (hp : ProbabilityRow p) (w : Word s) :
    A.acceptance p w ≤ 1 := by
  calc
    A.acceptance p w = ∑ j, p j * A.value w j := rfl
    _ ≤ ∑ j, p j * 1 :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (A.value_le_one w j) (hp.1 j)
    _ = 1 := by simpa only [mul_one] using hp.2

theorem probability_weight (p : Fin m → ℝ) (hp : ProbabilityRow p) (w : Word s) :
    (∑ j, p j * A.weight w j) = 1 + A.acceptance p w := by
  simp only [weight, mul_add, mul_one, Finset.sum_add_distrib, hp.2]
  rfl

def UniversalCutpoint (p : Fin m → ℝ) (theta : ℝ) : Prop :=
  ∀ w : Word s, A.acceptance p w ≤ theta

end Data

end MixedVolume.AutomatonWords

end
