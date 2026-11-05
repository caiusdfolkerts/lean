module
public import PaperVerification.ToricEffectiveCone
public import Mathlib.Algebra.Order.Floor.Ring
public import Lean.Elab.Tactic.Omega
@[expose] public section

/-!
# Terminating primitive reductions

A nonnegative integral ray combination with noncone support can be reduced by
one genuine primitive relation. Integral strict support gives a decreasing
integer cost bounded below by a global supporting linear function. Thus the
reduction terminates in a cone, while every coefficient function nonnegative
on primitive relations has nonincreasing cost.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

def countSupport (c : Lattice n → ℕ) : Finset (Lattice n) :=
  «Σ».rays.filter (fun v => 0 < c v)

def countVector (c : Lattice n → ℕ) : Lattice n :=
  ∑ v ∈ «Σ».rays, (c v : ℤ) • v

def countCost (a : Lattice n → ℝ) (c : Lattice n → ℕ) : ℝ :=
  ∑ v ∈ «Σ».rays, (c v : ℝ) * a v

def countIntegerCost (H : Lattice n → ℤ) (c : Lattice n → ℕ) : ℤ :=
  ∑ v ∈ «Σ».rays, (c v : ℤ) * H v

theorem cast_countIntegerCost (H : Lattice n → ℤ) (c : Lattice n → ℕ) :
    («Σ».countIntegerCost H c : ℝ) = «Σ».countCost (fun v => (H v : ℝ)) c := by
  simp only [countIntegerCost, countCost, Int.cast_sum, Int.cast_mul, Int.cast_natCast]

/-- A globally supporting linear function gives a lower bound on the cost of
every nonnegative integral representation of a fixed lattice vector. -/
theorem countCost_lower_bound (a : Lattice n → ℝ)
    (ℓ : Ambient n →ₗ[ℝ] ℝ) (hℓ : ∀ v ∈ «Σ».rays, ℓ (embed n v) ≤ a v)
    (c : Lattice n → ℕ) :
    ℓ (embed n («Σ».countVector c)) ≤ «Σ».countCost a c := by
  have he : ℓ (embed n («Σ».countVector c)) =
      ∑ v ∈ «Σ».rays, (c v : ℝ) * ℓ (embed n v) := by
    simp only [countVector, map_sum, embed_int_smul, Int.cast_natCast,
      map_smul, smul_eq_mul]
  rw [he]
  exact Finset.sum_le_sum (fun v hv =>
    mul_le_mul_of_nonneg_left (hℓ v hv) (Nat.cast_nonneg _))

namespace PrimitiveRelation

variable {«Σ»} (R : «Σ».PrimitiveRelation)

/-- Replace one copy of each positive ray by its integral focus expansion. -/
def reduceCounts (c : Lattice n → ℕ) (v : Lattice n) : ℕ :=
  c v - (if v ∈ R.positive then 1 else 0) +
    if v ∈ R.negative then R.coefficient v else 0

theorem cast_reduceCounts {A : Type*} [Ring A] (c : Lattice n → ℕ)
    (hc : ∀ v ∈ R.positive, 0 < c v) (v : Lattice n) :
    (R.reduceCounts c v : A) = (c v : A) -
      (if v ∈ R.positive then 1 else 0) +
      if v ∈ R.negative then (R.coefficient v : A) else 0 := by
  have hsub : (if v ∈ R.positive then 1 else 0) ≤ c v := by
    split_ifs with hv
    · exact Nat.succ_le_of_lt (hc v hv)
    · exact Nat.zero_le _
  simp only [reduceCounts, Nat.cast_add, Nat.cast_sub hsub, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

/-- A primitive reduction preserves the actual lattice vector. -/
theorem countVector_reduceCounts (c : Lattice n → ℕ)
    (hc : ∀ v ∈ R.positive, 0 < c v) :
    «Σ».countVector (R.reduceCounts c) = «Σ».countVector c := by
  unfold countVector
  simp only [R.cast_reduceCounts c hc, add_smul, sub_smul, ite_smul,
    one_smul, zero_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_indicator_of_subset R.primitive.1,
    sum_indicator_of_subset (fun v hv => «Σ».ray_mem_of_mem_cone R.negative_cone hv)]
  rw [R.equation]
  abel

/-- The cost drops by exactly the primitive relation degree. -/
theorem countCost_reduceCounts (a : Lattice n → ℝ) (c : Lattice n → ℕ)
    (hc : ∀ v ∈ R.positive, 0 < c v) :
    «Σ».countCost a (R.reduceCounts c) = «Σ».countCost a c - R.degree a := by
  unfold countCost degree
  simp only [R.cast_reduceCounts c hc, add_mul, sub_mul, ite_mul,
    one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_indicator_of_subset R.primitive.1,
    sum_indicator_of_subset (fun v hv => «Σ».ray_mem_of_mem_cone R.negative_cone hv)]
  ring

theorem countIntegerCost_reduceCounts_lt (H : Lattice n → ℤ)
    (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ))) (c : Lattice n → ℕ)
    (hc : ∀ v ∈ R.positive, 0 < c v) :
    «Σ».countIntegerCost H (R.reduceCounts c) < «Σ».countIntegerCost H c := by
  have he := R.countCost_reduceCounts (fun v => (H v : ℝ)) c hc
  have hp := R.degree_pos_of_strictSupport hH
  rw [← «Σ».cast_countIntegerCost H (R.reduceCounts c),
    ← «Σ».cast_countIntegerCost H c] at he
  have hreal : («Σ».countIntegerCost H (R.reduceCounts c) : ℝ) <
      («Σ».countIntegerCost H c : ℝ) := by linarith
  exact_mod_cast hreal

end PrimitiveRelation

/-- Integral strict support makes all primitive reductions terminate. The
terminal cone representation is no more expensive for any coefficient
function nonnegative on every primitive relation. -/
theorem exists_cone_reduction (H : Lattice n → ℤ)
    (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (a : Lattice n → ℝ) (ha : ∀ R : «Σ».PrimitiveRelation, 0 ≤ R.degree a)
    (c : Lattice n → ℕ) :
    ∃ d : Lattice n → ℕ, «Σ».countVector d = «Σ».countVector c ∧
      «Σ».countSupport d ∈ «Σ».cones ∧ «Σ».countCost a d ≤ «Σ».countCost a c := by
  let z := «Σ».countVector c
  obtain ⟨ℓ, hzero, hℓ⟩ :=
    IsStrictSupport.isNef «Σ» hH ∅ «Σ».empty_mem
  let lower : ℤ := ⌊ℓ (embed n z)⌋
  let measure (d : Lattice n → ℕ) : ℕ := («Σ».countIntegerCost H d - lower).toNat
  have hbounded (d : Lattice n → ℕ) (hd : «Σ».countVector d = z) :
      lower ≤ «Σ».countIntegerCost H d := by
    have hb := «Σ».countCost_lower_bound (fun v => (H v : ℝ)) ℓ hℓ d
    rw [hd, ← «Σ».cast_countIntegerCost H d] at hb
    have hf : (lower : ℝ) ≤ («Σ».countIntegerCost H d : ℝ) :=
      (Int.floor_le (ℓ (embed n z))).trans hb
    exact_mod_cast hf
  have hrec : ∀ k : ℕ, ∀ d : Lattice n → ℕ,
      «Σ».countVector d = z → measure d = k →
      ∃ e : Lattice n → ℕ, «Σ».countVector e = «Σ».countVector d ∧
        «Σ».countSupport e ∈ «Σ».cones ∧ «Σ».countCost a e ≤ «Σ».countCost a d := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro d hd hmeasure
      by_cases hs : «Σ».countSupport d ∈ «Σ».cones
      · exact ⟨d, rfl, hs, le_rfl⟩
      · obtain ⟨Q, hQsub, hQ⟩ := «Σ».exists_primitiveCollection_subset
          (Finset.filter_subset _ _) hs
        obtain ⟨R, hRpos⟩ := «Σ».exists_primitiveRelation hQ
        have hpositive : ∀ v ∈ R.positive, 0 < d v := by
          intro v hv
          rw [hRpos] at hv
          exact (Finset.mem_filter.mp (hQsub hv)).2
        let d' := R.reduceCounts d
        have hvector : «Σ».countVector d' = «Σ».countVector d :=
          R.countVector_reduceCounts d hpositive
        have hd'z : «Σ».countVector d' = z := hvector.trans hd
        have hless : «Σ».countIntegerCost H d' < «Σ».countIntegerCost H d :=
          R.countIntegerCost_reduceCounts_lt H hH d hpositive
        have hmeasure' : measure d' < k := by
          rw [← hmeasure]
          change («Σ».countIntegerCost H d' - lower).toNat <
            («Σ».countIntegerCost H d - lower).toNat
          have hlow := hbounded d' hd'z
          exact (Int.toNat_lt_toNat (by omega)).mpr (by omega)
        obtain ⟨e, hevec, hecone, hecost⟩ := ih (measure d') hmeasure' d' hd'z rfl
        refine ⟨e, hevec.trans hvector, hecone, hecost.trans ?_⟩
        have hcost := R.countCost_reduceCounts a d hpositive
        change «Σ».countCost a (R.reduceCounts d) ≤ «Σ».countCost a d
        rw [hcost]
        exact sub_le_self _ (ha R)
  exact hrec (measure c) c rfl rfl

end SmoothCompleteFan

end PaperVerification.ToricGeometry
