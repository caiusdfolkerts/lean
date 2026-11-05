module
public import PaperVerification.ToricSimplexParity
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
@[expose] public section
/-!
# Geometric correspondence for the simplex allocation theorem

Standard simplices are defined by their usual real coordinate inequalities.
Their actual topological interiors and integer points are related here to
`simplex_parity_integer`; in particular, no interior hypothesis is replaced
by an unexplained arithmetic proxy.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped BigOperators Pointwise

/-- The standard degree-`k` simplex in real affine coordinates. -/
def RealSimplex (d : ℕ) (k : ℝ) : Set (Fin d → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ k}

/-- The coordinate simplex is precisely the convex hull of the origin and scaled
standard basis vectors. This identifies `RealSimplex d k` with the paper's `k Δ_d`. -/
theorem realSimplex_eq_convexHull {d : ℕ} {k : ℝ} (hk : 0 < k) :
    RealSimplex d k =
      convexHull ℝ (insert (0 : Fin d → ℝ) (Set.range fun i => Pi.single i k)) := by
  have hconv : Convex ℝ (RealSimplex d k) := by
    intro x hx y hy a b ha hb hab
    refine ⟨fun i => add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)), ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have hx' := mul_le_mul_of_nonneg_left hx.2 ha
    have hy' := mul_le_mul_of_nonneg_left hy.2 hb
    nlinarith
  have hverts : insert (0 : Fin d → ℝ) (Set.range fun i => Pi.single i k) ⊆
      RealSimplex d k := by
    rintro x (rfl | ⟨i, rfl⟩)
    · exact ⟨fun _ => le_rfl, by simpa using hk.le⟩
    · refine ⟨?_, ?_⟩
      · intro j
        simp only [Pi.single_apply]
        split_ifs <;> positivity
      · simp
  refine Set.Subset.antisymm ?_ (convexHull_min hverts hconv)
  intro x hx
  let w : Fin (d + 1) → ℝ := Fin.cons (1 - (∑ i, x i) / k) (fun i => x i / k)
  let v : Fin (d + 1) → (Fin d → ℝ) := Fin.cons 0 (fun i => Pi.single i k)
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change 0 ≤ 1 - (∑ i, x i) / k
      exact sub_nonneg.mpr ((div_le_one hk).mpr hx.2)
    · change 0 ≤ x j / k
      exact div_nonneg (hx.1 j) hk.le
  have hwsum : ∑ i, w i = 1 := by
    simp only [Fin.sum_univ_succ, w, Fin.cons_zero, Fin.cons_succ,
      ← Finset.sum_div]
    ring
  have hv : ∀ i, v i ∈ insert (0 : Fin d → ℝ) (Set.range fun i => Pi.single i k) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Set.mem_insert 0 _
    · exact Set.mem_insert_of_mem _ (Set.mem_range_self j)
  have hwv : ∑ i, w i • v i = x := by
    ext j
    simp [Fin.sum_univ_succ, w, v, Pi.single_apply, Finset.sum_apply, hk.ne']
  exact mem_convexHull_of_exists_fintype w v hw hwsum hv hwv

private def coordinateSum (d : ℕ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ i, ContinuousLinearMap.proj i

@[simp] private theorem coordinateSum_apply {d : ℕ} (x : Fin d → ℝ) :
    coordinateSum d x = ∑ i, x i := by
  simp [coordinateSum]

/-- Topological interior of the positive-dimensional standard simplex. -/
theorem interior_realSimplex (d : ℕ) (k : ℝ) :
    interior (RealSimplex (d + 1) k) =
      {x | (∀ i, 0 < x i) ∧ ∑ i, x i < k} := by
  have hcoord (i : Fin (d + 1)) :
      interior {x : Fin (d + 1) → ℝ | 0 ≤ x i} = {x | 0 < x i} := by
    have h :=
      ((isOpenMap_eval (X := fun _ : Fin (d + 1) => ℝ) i).preimage_interior_eq_interior_preimage
        (continuous_apply i) (Set.Ici (0 : ℝ))).symm
    rw [interior_Ici] at h
    simpa only [Set.preimage, Set.Ici, Set.Ioi, Function.eval, Set.mem_setOf_eq] using h
  have hsurj : Function.Surjective (coordinateSum (d + 1)) := by
    intro y
    exact ⟨Pi.single 0 y, by simp⟩
  have hsum :
      interior {x : Fin (d + 1) → ℝ | ∑ i, x i ≤ k} = {x | ∑ i, x i < k} := by
    have h :=
      ((coordinateSum (d + 1)).isOpenMap hsurj).preimage_interior_eq_interior_preimage
        (coordinateSum (d + 1)).continuous (Set.Iic k) |>.symm
    rw [interior_Iic] at h
    simpa only [Set.preimage, Set.Iic, Set.Iio, coordinateSum_apply, Set.mem_setOf_eq] using h
  have hset : RealSimplex (d + 1) k =
      (⋂ i, {x : Fin (d + 1) → ℝ | 0 ≤ x i}) ∩ {x | ∑ i, x i ≤ k} := by
    ext x
    simp [RealSimplex]
  rw [hset, interior_inter, interior_iInter_of_finite]
  simp_rw [hcoord, hsum]
  ext x
  simp

/-- Every point of the Minkowski sum satisfies the combined simplex inequalities. -/
theorem add_realSimplex_subset (d : ℕ) (k l : ℝ) :
    RealSimplex d k + RealSimplex d l ⊆ RealSimplex d (k + l) := by
  rintro x ⟨a, ha, b, hb, rfl⟩
  refine ⟨fun i => add_nonneg (ha.1 i) (hb.1 i), ?_⟩
  simpa only [Pi.add_apply, Finset.sum_add_distrib] using add_le_add ha.2 hb.2

/-- The integer and real coordinate definitions agree under the canonical embedding. -/
theorem integerSimplex_iff_realSimplex {d k : ℕ} (a : Fin d → ℤ) :
    IntegerSimplex k a ↔ (fun i => (a i : ℝ)) ∈ RealSimplex d k := by
  constructor
  · rintro ⟨ha, hs⟩
    refine ⟨fun i => Int.cast_nonneg_iff.mpr (ha i), ?_⟩
    have h : ((∑ i, a i : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) := Int.cast_le.mpr hs
    simpa only [Int.cast_sum, Int.cast_natCast] using h
  · rintro ⟨ha, hs⟩
    refine ⟨fun i => Int.cast_nonneg_iff.mp (ha i), ?_⟩
    have h : ((∑ i, a i : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) := by
      simpa only [Int.cast_sum, Int.cast_natCast] using hs
    exact Int.cast_le.mp h

/-- Lemma 4.4 stated with actual real simplices, topological interior of their
Minkowski sum, and the full integer lattice in every positive dimension. -/
theorem simplex_parity_topological {d k l : ℕ}
    (hd : 0 < d) (hdk : d ≤ k) (hdl : d ≤ l)
    (m α : Fin d → ℤ)
    (hm : (fun i => (m i : ℝ)) ∈
      interior (RealSimplex d k + RealSimplex d l)) :
    ∃ a b : Fin d → ℤ,
      (fun i => (a i : ℝ)) ∈ RealSimplex d k ∧
      (fun i => (b i : ℝ)) ∈ RealSimplex d l ∧
      (∀ i, a i + b i = m i) ∧
      (∀ i, (a i - α i) % 2 = 0) := by
  cases d with
  | zero => omega
  | succ d =>
      have hm' := interior_mono (add_realSimplex_subset (d + 1) k l) hm
      rw [interior_realSimplex] at hm'
      have hmpos : ∀ i, 0 < m i := by
        intro i
        have h : (0 : ℝ) < (m i : ℝ) := hm'.1 i
        exact Int.cast_pos.mp h
      have hmsum : (∑ i, m i) < (k + l : ℕ) := by
        have h := hm'.2
        push_cast at h ⊢
        exact_mod_cast h
      obtain ⟨a, b, ha, hb, hab, hpar⟩ :=
        simplex_parity_integer hdk hdl m α hmpos hmsum
      exact ⟨a, b, (integerSimplex_iff_realSimplex a).mp ha,
        (integerSimplex_iff_realSimplex b).mp hb, hab, hpar⟩

end PaperVerification.Toric
