module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# The height-space argument for identified parameters

The space below is the literal rational linear space (9) in the manuscript.
No assertion about its dimension is built into its definition. Classes may be
arbitrary nonempty inverse-stable parts, rather than automorphism orbits.
-/

@[expose] public section
noncomputable section

namespace Sunlet.OrbitHeight

variable {G C : Type*} [AddCommGroup G] [Fintype G] [Fintype C]
  [LinearOrder C]

structure InverseStablePartition (G C : Type*) [AddCommGroup G] where
  classOf : G → C
  surjective : Function.Surjective classOf
  zeroClass : C
  zero_iff : ∀ a, classOf a = zeroClass ↔ a = 0
  neg_class : ∀ a, classOf (-a) = classOf a

namespace InverseStablePartition

variable (P : InverseStablePartition G C)

@[simp] theorem zero_class : P.classOf 0 = P.zeroClass := (P.zero_iff 0).mpr rfl

/-- The unnormalized rational height space, with its zero coordinate included. -/
def heightSpace : Submodule ℚ (C → ℚ) where
  carrier := {x | x P.zeroClass = 0 ∧
    ∀ b c, P.classOf b < P.classOf c →
      x (P.classOf c) = x (P.classOf b) + x (P.classOf (c - b))}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    constructor
    · simp [hx0, hy0]
    · intro b c h
      simp only [Pi.add_apply, hx b c h, hy b c h]
      ring
  smul_mem' := by
    rintro r x ⟨hx0, hx⟩
    constructor
    · simp [hx0]
    · intro b c h
      simp only [Pi.smul_apply, smul_eq_mul, hx b c h]
      ring

theorem neg_value (x : C → ℚ) (a : G) :
    x (P.classOf (-a)) = x (P.classOf a) := by rw [P.neg_class]

/-- Mixed signs contradict the relation between a maximum and a minimum. -/
theorem one_sign {x : C → ℚ} (hx : x ∈ P.heightSpace) :
    (∀ i, 0 ≤ x i) ∨ (∀ i, x i ≤ 0) := by
  classical
  by_cases hn : ∀ i, 0 ≤ x i
  · exact Or.inl hn
  right
  obtain ⟨i, hi⟩ : ∃ i, x i < 0 := by simpa using hn
  intro j
  by_contra hj
  have hj' : 0 < x j := lt_of_not_ge hj
  obtain ⟨a, ha⟩ := P.surjective j
  obtain ⟨b, hb⟩ := P.surjective i
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image (Finset.univ : Finset G)
    (fun g => x (P.classOf g)) ⟨0, Finset.mem_univ 0⟩
  obtain ⟨q, _, hq⟩ := Finset.exists_min_image (Finset.univ : Finset G)
    (fun g => x (P.classOf g)) ⟨0, Finset.mem_univ 0⟩
  have hp0 : 0 < x (P.classOf p) := by
    have := hp a (Finset.mem_univ _)
    rw [ha] at this
    linarith
  have hq0 : x (P.classOf q) < 0 := by
    have := hq b (Finset.mem_univ _)
    rw [hb] at this
    linarith
  have hne : P.classOf p ≠ P.classOf q := by
    intro h
    rw [h] at hp0
    linarith
  rcases lt_or_gt_of_ne hne with h | h
  · have he := hx.2 p q h
    have hm := hq (q - p) (Finset.mem_univ _)
    linarith
  · have he := hx.2 q p h
    have hm := hp (p - q) (Finset.mem_univ _)
    linarith

/-- A linear subspace of rational functions whose every element has one sign
has dimension at most one. This is the linear-algebra step in Lemma 7.3. -/
theorem finrank_le_one_of_one_sign (S : Submodule ℚ (C → ℚ))
    (hS : ∀ x ∈ S, (∀ i, 0 ≤ x i) ∨ (∀ i, x i ≤ 0)) :
    Module.finrank ℚ S ≤ 1 := by
  classical
  by_cases hbot : S = ⊥
  · subst S
    rw [Module.finrank_eq_zero_of_subsingleton]
    exact Nat.zero_le _
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨c, hc⟩ : ∃ c, v c ≠ 0 := by
    by_contra h
    apply hv0
    ext c
    simpa using not_exists.mp h c
  let ev : S →ₗ[ℚ] ℚ :=
    { toFun := fun w => w.val c
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hev : Function.Injective ev := by
    apply (LinearMap.ker_eq_bot).mp
    apply (Submodule.eq_bot_iff _).mpr
    intro w hw
    have hwc : w.val c = 0 := by simpa [ev] using hw
    apply Subtype.ext
    funext b
    by_contra hwb
    have hwb' : w.val b ≠ 0 := by simpa using hwb
    let t : ℚ := (-v c - v b) / w.val b
    have hz : v + t • w.val ∈ S := S.add_mem hv (S.smul_mem t w.property)
    have hzc : (v + t • w.val) c = v c := by simp [hwc]
    have hzb : (v + t • w.val) b = -v c := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, t]
      field_simp [hwb']
      ring
    rcases hS _ hz with hp | hn
    · have h1 := hp c
      have h2 := hp b
      rw [hzc] at h1
      rw [hzb] at h2
      exact hc (by linarith)
    · have h1 := hn c
      have h2 := hn b
      rw [hzc] at h1
      rw [hzb] at h2
      exact hc (by linarith)
  have h := LinearMap.finrank_le_finrank_of_injective hev
  simpa using h

/-- The first assertion of Lemma 7.3, for the literal space (9). -/
theorem heightSpace_finrank_le_one : Module.finrank ℚ P.heightSpace ≤ 1 :=
  finrank_le_one_of_one_sign P.heightSpace (fun _ hx => P.one_sign hx)

theorem monotone_of_nonnegative {x : C → ℚ} (hx : x ∈ P.heightSpace)
    (hn : ∀ i, 0 ≤ x i) : Monotone x := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | h
  · exact le_rfl
  obtain ⟨b, rfl⟩ := P.surjective i
  obtain ⟨c, rfl⟩ := P.surjective j
  have he := hx.2 b c h
  have hd := hn (P.classOf (c - b))
  linarith

theorem difference_absolute {x : C → ℚ} (hx : x ∈ P.heightSpace)
    (hn : ∀ i, 0 ≤ x i) (b c : G) (hne : P.classOf b ≠ P.classOf c) :
    x (P.classOf (c - b)) = |x (P.classOf c) - x (P.classOf b)| := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (P.monotone_of_nonnegative hx hn h.le))]
    linarith [hx.2 b c h]
  · rw [abs_of_nonpos (sub_nonpos.mpr (P.monotone_of_nonnegative hx hn h.le))]
    have he := hx.2 c b h
    have hd : x (P.classOf (b - c)) = x (P.classOf (c - b)) := by
      rw [← neg_sub c b, P.neg_class]
    rw [hd] at he
    linarith

/-- Two distinct positive heights necessarily have ratio two. -/
theorem larger_positive_eq_twice {x : C → ℚ} (hx : x ∈ P.heightSpace)
    (hn : ∀ i, 0 ≤ x i) (b c : G)
    (hb : 0 < x (P.classOf b)) (hbc : x (P.classOf b) < x (P.classOf c)) :
    x (P.classOf c) = 2 * x (P.classOf b) ∧
      P.classOf (c - b) = P.classOf (-b) := by
  have hne : P.classOf b ≠ P.classOf c := by intro h; rw [h] at hbc; exact hbc.false
  have hd := P.difference_absolute hx hn b c hne
  rw [abs_of_pos (sub_pos.mpr hbc)] at hd
  have heq : P.classOf (c - b) = P.classOf (-b) := by
    by_contra h
    have hh := P.difference_absolute hx hn (-b) (c - b) (Ne.symm h)
    have hg : c - b - -b = c := by abel
    rw [hg, P.neg_class, hd] at hh
    rcases le_total 0 (x (P.classOf c) - x (P.classOf b) - x (P.classOf b)) with hp | hp
    · rw [abs_of_nonneg hp] at hh
      linarith
    · rw [abs_of_nonpos hp] at hh
      linarith
  have hv : x (P.classOf (c - b)) = x (P.classOf b) := by rw [heq, P.neg_class]
  exact ⟨by linarith, heq⟩

/-- Translation by a zero-height element preserves every height, including zero. -/
theorem zero_translation {x : C → ℚ} (hx : x ∈ P.heightSpace)
    (hn : ∀ i, 0 ≤ x i) (z : G) (hz : x (P.classOf z) = 0) (a : G) :
    x (P.classOf (a - z)) = x (P.classOf a) := by
  by_cases ha : x (P.classOf a) = 0
  · by_contra hh
    have hh' : 0 < x (P.classOf (a - z)) := by
      have := hn (P.classOf (a - z))
      rw [ha] at hh
      exact lt_of_le_of_ne this (Ne.symm hh)
    have hclass : P.classOf (-z) ≠ P.classOf (a - z) := by
      intro h
      rw [← h, P.neg_class, hz] at hh'
      exact hh'.false
    have he := P.difference_absolute hx hn (-z) (a - z) hclass
    have hg : a - z - -z = a := by abel
    rw [hg, P.neg_class, hz, sub_zero, abs_of_pos hh', ha] at he
    linarith
  · have hap : 0 < x (P.classOf a) := lt_of_le_of_ne (hn _) (Ne.symm ha)
    have hclass : P.classOf z ≠ P.classOf a := by intro h; rw [← h, hz] at hap; exact hap.false
    simpa [hz, abs_of_pos hap] using P.difference_absolute hx hn z a hclass

/-- The zero set in Lemma 7.3 is an actual additive subgroup of the given group. -/
def zeroSubgroup (x : C → ℚ) (hx : x ∈ P.heightSpace) (hn : ∀ i, 0 ≤ x i) :
    AddSubgroup G where
  carrier := {a | x (P.classOf a) = 0}
  zero_mem' := by simpa using hx.1
  add_mem' := by
    intro a b ha hb
    have hz : x (P.classOf (-b)) = 0 := by simpa [P.neg_class] using hb
    change x (P.classOf (a + b)) = 0
    calc
      x (P.classOf (a + b)) = x (P.classOf a) := by
        simpa using P.zero_translation hx hn (-b) hz a
      _ = 0 := ha
  neg_mem' := by intro a ha; simpa [P.neg_class] using ha

/-- A class admitting a same-class difference, exactly the set `R` in §7.1. -/
def sameClassDifference (i : C) : Prop :=
  i ≠ P.zeroClass ∧
    ∃ b c : G, P.classOf b = P.classOf c ∧ P.classOf b ≠ P.zeroClass ∧
      P.classOf (c - b) = i

/-- There are at most two positive levels, with the second twice the first. -/
theorem positive_levels {x : C → ℚ} (hx : x ∈ P.heightSpace)
    (hn : ∀ i, 0 ≤ x i) (hzero : x ≠ 0) :
    ∃ a : G, 0 < x (P.classOf a) ∧
      ∀ i, x i = 0 ∨ x i = x (P.classOf a) ∨ x i = 2 * x (P.classOf a) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, 0 < x i := by
    by_contra h
    apply hzero
    funext i
    have hle : x i ≤ 0 := not_lt.mp (not_exists.mp h i)
    exact le_antisymm hle (hn i)
  let S : Finset C := Finset.univ.filter fun i => 0 < x i
  have hS : S.Nonempty := ⟨i, by simp [S, hi]⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image S x hS
  have hjp : 0 < x j := (Finset.mem_filter.mp hj).2
  obtain ⟨a, ha⟩ := P.surjective j
  refine ⟨a, by simpa [ha] using hjp, ?_⟩
  intro k
  by_cases hk : x k = 0
  · exact Or.inl hk
  right
  have hkp : 0 < x k := lt_of_le_of_ne (hn k) (Ne.symm hk)
  have hjk := hmin k (by simp [S, hkp])
  rcases eq_or_lt_of_le hjk with h | h
  · exact Or.inl (by simpa [ha] using h.symm)
  · obtain ⟨b, hb⟩ := P.surjective k
    exact Or.inr (by
      simpa [hb] using (P.larger_positive_eq_twice hx hn a b
        (by simpa [ha] using hjp) (by simpa [ha, hb] using h)).1)

/-- Every class at the upper positive level supplies one of the same-class rows. -/
theorem upper_level_mem_sameClassDifference {x : C → ℚ} (hx : x ∈ P.heightSpace)
    (hn : ∀ i, 0 ≤ x i) (a c : G) (ha : 0 < x (P.classOf a))
    (hc : x (P.classOf c) = 2 * x (P.classOf a)) :
    P.sameClassDifference (P.classOf c) := by
  have hlt : x (P.classOf a) < x (P.classOf c) := by linarith
  have he := (P.larger_positive_eq_twice hx hn a c ha hlt).2
  have hc0 : P.classOf c ≠ P.zeroClass := by
    intro h
    rw [h, hx.1] at hc
    linarith
  refine ⟨hc0, -a, c - a, he.symm, ?_, ?_⟩
  · intro h
    rw [P.neg_class] at h
    rw [h, hx.1] at ha
    exact ha.false
  · congr 1
    abel

end InverseStablePartition

end Sunlet.OrbitHeight
