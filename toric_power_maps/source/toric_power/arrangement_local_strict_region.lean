module

public import ToricPower.ArrangementStrictRegion
public import ToricPower.LocalMorseCone

/-! # The actual excluded half-neighborhood of strict integral support

Inside the integral local star, an inequality which is already strict
at the center stays strict. Thus only the active boundary inequalities
occur in the excluded set. Separation from their negative cone supplies
a common star center in every chosen open convex local neighborhood.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set

namespace ToricPower.IntegralArrangement

section General

variable {E J : Type*} [AddCommGroup E] [Module ℝ E] [Finite J]
  (f : J → E →ₗ[ℝ] ℝ) (lower : J → ℤ) (selected : Set J)

/-- The actual inequalities attaining their integer boundary value. -/
def strictActive (x : E) : Set J :=
  {j | j ∈ selected ∧ f j x = (lower j : ℝ)}

theorem localStar_strict_integral {x y : E} (inside : y ∈ localStar f x)
    (j : J) (strict : (lower j : ℝ) < f j x) : (lower j : ℝ) < f j y := by
  have ceiling : lower j < ⌈f j x⌉ := Int.lt_ceil.mpr strict
  have integerBound : lower j + 1 ≤ ⌈f j x⌉ := by omega
  have bound : (lower j : ℝ) + 1 ≤ (⌈f j x⌉ : ℝ) := by exact_mod_cast integerBound
  have localBound := (inside j).1
  linarith

/-- The complement in the local star is exactly the union of weak
opposite half-spaces for the active inequalities. -/
theorem localStar_not_strictCellRegion_iff {x y : E}
    (weak : ∀ j ∈ selected, (lower j : ℝ) ≤ f j x)
    (inside : y ∈ localStar f x) :
    y ∉ strictCellRegion f lower selected ↔
      ∃ j : strictActive f lower selected x, f j.val y ≤ f j.val x := by
  classical
  constructor
  · intro outside
    simp only [strictCellRegion,mem_setOf_eq] at outside
    push_neg at outside
    obtain ⟨j,hj,bound⟩ := outside
    have active : f j x = (lower j : ℝ) := by
      by_contra unequal
      have strict : (lower j : ℝ) < f j x :=
        lt_of_le_of_ne (weak j hj) (Ne.symm unequal)
      exact (not_lt_of_ge bound) (localStar_strict_integral f lower inside j strict)
    exact ⟨⟨j,hj,active⟩,by simpa only [active] using bound⟩
  · rintro ⟨j,bound⟩ supported
    have strict := supported j.val j.property.1
    rw [j.property.2] at bound
    exact (not_lt_of_ge bound) strict

def shiftedNegativeHalf (B : Set E) (x : E) (ξ : Module.Dual ℝ E) : Set E :=
  B ∩ {y | ξ (y-x) < 0}

theorem shiftedNegativeHalf_convex {B : Set E} (convex : Convex ℝ B)
    (x : E) (ξ : Module.Dual ℝ E) : Convex ℝ (shiftedNegativeHalf B x ξ) := by
  have same : shiftedNegativeHalf B x ξ = B ∩ ξ ⁻¹' Iio (ξ x) := by
    ext y
    simp only [shiftedNegativeHalf,mem_inter_iff,mem_setOf_eq,mem_preimage,mem_Iio,
      map_sub,sub_lt_zero]
  rw [same]
  exact convex.inter ((convex_Iio (ξ x)).linear_preimage ξ)

theorem shiftedNegativeHalf_excluded_eq {B : Set E} (x : E) (ξ : Module.Dual ℝ E)
    (inside : B ⊆ localStar f x)
    (weak : ∀ j ∈ selected, (lower j : ℝ) ≤ f j x) :
    shiftedNegativeHalf B x ξ ∩ (strictCellRegion f lower selected)ᶜ =
      shiftedNegativeHalf B x ξ ∩
        ⋃ j : strictActive f lower selected x, {y | f j.val y ≤ f j.val x} := by
  ext y
  constructor
  · rintro ⟨hy,outside⟩
    obtain ⟨j,hj⟩ := (localStar_not_strictCellRegion_iff f lower selected weak
      (inside hy.1)).mp outside
    exact ⟨hy,mem_iUnion.mpr ⟨j,hj⟩⟩
  · rintro ⟨hy,excluded⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp excluded
    exact ⟨hy,(localStar_not_strictCellRegion_iff f lower selected weak
      (inside hy.1)).mpr ⟨j,hj⟩⟩

end General

section Topology

variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite J]
  (f : J → E →ₗ[ℝ] ℝ) (lower : J → ℤ) (selected : Set J)

/-- Outside the negative active cone, the literal negative half of
every open neighborhood is nonempty, including when no inequality is active. -/
theorem shiftedNegativeHalf_nonempty_of_outsideActiveCone
    {B : Set E} (x : E) (ξ : Module.Dual ℝ E)
    (openB : IsOpen B) (center : x ∈ B)
    (feasible : ∃ w : E, ∀ j : strictActive f lower selected x, 0 < f j.val w)
    (outsideCone : -ξ ∉ PointedCone.hull ℝ
      (Set.range (fun j : strictActive f lower selected x => f j.val))) :
    (shiftedNegativeHalf B x ξ).Nonempty := by
  classical
  letI : Fintype (strictActive f lower selected x) := Fintype.ofFinite _
  obtain ⟨v,_,hξv⟩ := LocalMorse.exists_common_positive_direction
    (fun j : strictActive f lower selected x => f j.val) ξ feasible outsideCone
  let B₀ : Set E := {w | x+w ∈ B}
  have openB₀ : IsOpen B₀ := openB.preimage (continuous_const.add continuous_id)
  have zeroB₀ : (0 : E) ∈ B₀ := by simpa only [B₀,mem_setOf_eq,add_zero] using center
  obtain ⟨t,ht,htB⟩ := LocalMorse.exists_negative_smul_mem openB₀ zeroB₀ v
  refine ⟨x+(-t) • v,htB,?_⟩
  change ξ (x+(-t) • v-x) < 0
  simp only [add_sub_cancel_left,map_smul,smul_eq_mul]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr ht) hξv

/-- Separation supplies a real star center of the literal excluded
negative half-neighborhood. The normal cone consists only of active forms. -/
theorem shiftedNegativeHalf_excluded_starConvex
    {B : Set E} (x : E) (ξ : Module.Dual ℝ E)
    (convex : Convex ℝ B) (openB : IsOpen B) (center : x ∈ B)
    (inside : B ⊆ localStar f x)
    (weak : ∀ j ∈ selected, (lower j : ℝ) ≤ f j x)
    (activeNonempty : (strictActive f lower selected x).Nonempty)
    (feasible : ∃ w : E, ∀ j : strictActive f lower selected x, 0 < f j.val w)
    (outsideCone : -ξ ∉ PointedCone.hull ℝ
      (Set.range (fun j : strictActive f lower selected x => f j.val))) :
    ∃ p : E,
      StarConvex ℝ p
        (shiftedNegativeHalf B x ξ ∩ (strictCellRegion f lower selected)ᶜ) ∧
      p ∈ shiftedNegativeHalf B x ξ ∩ (strictCellRegion f lower selected)ᶜ := by
  classical
  letI : Fintype (strictActive f lower selected x) := Fintype.ofFinite _
  obtain ⟨v,hv,hξv⟩ := LocalMorse.exists_common_positive_direction
    (fun j : strictActive f lower selected x => f j.val) ξ feasible outsideCone
  let B₀ : Set E := {w | x + w ∈ B}
  have openB₀ : IsOpen B₀ := openB.preimage (continuous_const.add continuous_id)
  have zeroB₀ : (0 : E) ∈ B₀ := by simpa only [B₀,mem_setOf_eq,add_zero] using center
  obtain ⟨t,ht,htB⟩ := LocalMorse.exists_negative_smul_mem openB₀ zeroB₀ v
  let p : E := x + (-t) • v
  have hpB : p ∈ B := htB
  have hpξ : ξ (p-x) < 0 := by
    simp only [p,add_sub_cancel_left,map_smul,smul_eq_mul]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr ht) hξv
  have hpf (j : strictActive f lower selected x) : f j.val p ≤ f j.val x := by
    have negative := mul_neg_of_neg_of_pos (neg_lt_zero.mpr ht) (hv j)
    simp only [p,map_add,map_smul,smul_eq_mul]
    linarith
  have star : StarConvex ℝ p (shiftedNegativeHalf B x ξ ∩
      ⋃ j : strictActive f lower selected x, {y | f j.val y ≤ f j.val x}) :=
    ((shiftedNegativeHalf_convex convex x ξ).starConvex ⟨hpB,hpξ⟩).inter
      (starConvex_iUnion fun j =>
        ((convex_Iic (f j.val x)).linear_preimage (f j.val)).starConvex (hpf j))
  obtain ⟨j,hj⟩ := activeNonempty
  have hp : p ∈ shiftedNegativeHalf B x ξ ∩
      ⋃ j : strictActive f lower selected x, {y | f j.val y ≤ f j.val x} :=
    ⟨⟨hpB,hpξ⟩,mem_iUnion.mpr ⟨⟨j,hj⟩,hpf ⟨j,hj⟩⟩⟩
  rw [← shiftedNegativeHalf_excluded_eq f lower selected x ξ inside weak] at star hp
  exact ⟨p,star,hp⟩

end Topology

end ToricPower.IntegralArrangement

end
