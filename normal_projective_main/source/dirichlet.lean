module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Ring

/-! Candidate for the remaining Corollary 2 dependency chain. This file is not
part of the verified library until an ordinary pinned Lean check has passed.
It proves the finite weighted Dirichlet problem directly from the maximum
principle. The planar embedding and convex-cap reconstruction are separate,
unproved obligations; this file does not assert Corollary 2. -/

@[expose] public section

namespace NormalProjective.Dirichlet

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weighted harmonic equation at an interior vertex. -/
def Harmonic (w : V → V → ℝ) (x : V → ℝ) (i : V) : Prop :=
  ∑ j, w i j * (x i - x j) = 0

/-- Maximum principle on any finite connected graph. Positive weights are
required on graph edges; all weights are nonnegative. Symmetry is unnecessary. -/
theorem maximum_principle (G : SimpleGraph V) (hG : G.Connected)
    (B : Set V) (hB : B.Nonempty) (w : V → V → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (he : ∀ i j, G.Adj i j → 0 < w i j)
    (x : V → ℝ) (hx : ∀ i, i ∉ B → Harmonic w x i)
    (c : ℝ) (hb : ∀ i ∈ B, x i ≤ c) : ∀ i, x i ≤ c := by
  intro i
  by_contra hi
  have hci : c < x i := lt_of_not_ge hi
  obtain ⟨u, _, hu⟩ := Finset.exists_max_image Finset.univ x
    ⟨i, Finset.mem_univ i⟩
  have hmax : ∀ v, x v ≤ x u := fun v => hu v (Finset.mem_univ v)
  have hcu : c < x u := hci.trans_le (hmax i)
  have hstep : ∀ v z, G.Adj v z → x v = x u → x z = x u := by
    intro v z hvz hv
    have hvB : v ∉ B := by
      intro hvB
      exact (not_lt_of_ge (hb v hvB)) (by simpa only [hv] using hcu)
    have hsum := hx v hvB
    have hnonneg : ∀ j ∈ (Finset.univ : Finset V),
        0 ≤ w v j * (x v - x j) := by
      intro j _
      exact mul_nonneg (hw v j) (sub_nonneg.mpr (by simpa only [hv] using hmax j))
    have hz : w v z * (x v - x z) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum z (Finset.mem_univ z)
    have heq : x v = x z := sub_eq_zero.mp
      ((mul_eq_zero.mp hz).resolve_left (ne_of_gt (he v z hvz)))
    exact heq.symm.trans hv
  have hwalk : ∀ {v z}, G.Walk v z → x v = x u → x z = x u := by
    intro v z p
    induction p with
    | nil => exact id
    | @cons v z t hvz p ih => exact fun hv => ih (hstep v z hvz hv)
  obtain ⟨b, hbB⟩ := hB
  obtain ⟨p⟩ := hG u b
  have hbu : x b = x u := hwalk p rfl
  exact (not_lt_of_ge (hb b hbB)) (by simpa only [hbu] using hcu)

theorem minimum_principle (G : SimpleGraph V) (hG : G.Connected)
    (B : Set V) (hB : B.Nonempty) (w : V → V → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (he : ∀ i j, G.Adj i j → 0 < w i j)
    (x : V → ℝ) (hx : ∀ i, i ∉ B → Harmonic w x i)
    (c : ℝ) (hb : ∀ i ∈ B, c ≤ x i) : ∀ i, c ≤ x i := by
  have hneg : ∀ i, i ∉ B → Harmonic w (fun j => -x j) i := by
    intro i hi
    unfold Harmonic at hx ⊢
    simp only [show ∀ j, -x i - -x j = -(x i - x j) by intro j; ring,
      mul_neg, Finset.sum_neg_distrib, hx i hi, neg_zero]
  have h := maximum_principle G hG B hB w hw he (fun j => -x j) hneg (-c)
    (fun i hi => neg_le_neg (hb i hi))
  intro i
  exact neg_le_neg_iff.mp (h i)

/-- Zero boundary data have only the zero harmonic extension. -/
theorem zero_of_harmonic_zero_boundary (G : SimpleGraph V) (hG : G.Connected)
    (B : Set V) (hB : B.Nonempty) (w : V → V → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (he : ∀ i j, G.Adj i j → 0 < w i j)
    (x : V → ℝ) (hx : ∀ i, i ∉ B → Harmonic w x i)
    (hb : ∀ i ∈ B, x i = 0) : x = 0 := by
  funext i
  exact le_antisymm
    (maximum_principle G hG B hB w hw he x hx 0 (fun j hj => (hb j hj).le) i)
    (minimum_principle G hG B hB w hw he x hx 0 (fun j hj => (hb j hj).ge) i)

/-- Boundary rows are identities; interior rows encode the weighted equation.
This full square matrix avoids selecting an ordering of the interior vertices. -/
noncomputable def matrix (B : Set V) (w : V → V → ℝ) : Matrix V V ℝ := by
  classical
  exact fun i j => if i ∈ B then if i = j then 1 else 0
    else (if i = j then ∑ k, w i k else 0) - w i j

theorem matrix_mulVec_boundary (B : Set V) (w : V → V → ℝ)
    (x : V → ℝ) {i : V} (hi : i ∈ B) : (matrix B w *ᵥ x) i = x i := by
  classical
  simp [matrix, Matrix.mulVec, dotProduct, hi]

theorem matrix_mulVec_interior (B : Set V) (w : V → V → ℝ)
    (x : V → ℝ) {i : V} (hi : i ∉ B) :
    (matrix B w *ᵥ x) i = ∑ j, w i j * (x i - x j) := by
  classical
  simp only [matrix, Matrix.mulVec, dotProduct, hi, ↓reduceIte, sub_mul,
    Finset.sum_sub_distrib, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [Finset.sum_mul]
  simp_rw [mul_sub, Finset.sum_sub_distrib]

theorem matrix_isUnit (G : SimpleGraph V) (hG : G.Connected)
    (B : Set V) (hB : B.Nonempty) (w : V → V → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (he : ∀ i j, G.Adj i j → 0 < w i j) :
    IsUnit (matrix B w) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hzero : matrix B w *ᵥ (x-y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hd : x-y = 0 := zero_of_harmonic_zero_boundary G hG B hB w hw he (x-y)
    (by
      intro i hi
      unfold Harmonic
      rw [← matrix_mulVec_interior B w (x-y) hi]
      exact congrFun hzero i)
    (by
      intro i hi
      rw [← matrix_mulVec_boundary B w (x-y) hi]
      exact congrFun hzero i)
  exact sub_eq_zero.mp hd

/-- Existence and uniqueness for arbitrary prescribed real boundary values. -/
theorem existsUnique_extension (G : SimpleGraph V) (hG : G.Connected)
    (B : Set V) (hB : B.Nonempty) (w : V → V → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (he : ∀ i j, G.Adj i j → 0 < w i j)
    (b : V → ℝ) :
    ∃! x : V → ℝ, (∀ i ∈ B, x i = b i) ∧ ∀ i, i ∉ B → Harmonic w x i := by
  classical
  have hu := matrix_isUnit G hG B hB w hw he
  let rhs : V → ℝ := fun i => if i ∈ B then b i else 0
  obtain ⟨x, hx⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hu rhs
  refine ⟨x, ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    have h := congrFun hx i
    simpa [matrix_mulVec_boundary B w x hi, rhs, hi] using h
  · intro i hi
    have h := congrFun hx i
    simpa [matrix_mulVec_interior B w x hi, rhs, hi, Harmonic] using h
  · intro y hy
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hu)
    rw [hx]
    funext i
    by_cases hi : i ∈ B
    · simpa [rhs, hi, matrix_mulVec_boundary B w y hi] using hy.1 i hi
    · simpa [rhs, hi, matrix_mulVec_interior B w y hi, Harmonic] using hy.2 i hi

noncomputable def solution (B : Set V) (w : V → V → ℝ) (b : V → ℝ) : V → ℝ := by
  classical
  exact (matrix B w)⁻¹ *ᵥ (fun i => if i ∈ B then b i else 0)

theorem solution_spec (G : SimpleGraph V) (hG : G.Connected)
    (B : Set V) (hB : B.Nonempty) (w : V → V → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (he : ∀ i j, G.Adj i j → 0 < w i j)
    (b : V → ℝ) :
    (∀ i ∈ B, solution B w b i = b i) ∧
      ∀ i, i ∉ B → Harmonic w (solution B w b) i := by
  classical
  have hd : IsUnit (matrix B w).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (matrix_isUnit G hG B hB w hw he)
  have heq : matrix B w *ᵥ solution B w b = (fun i => if i ∈ B then b i else 0) := by
    rw [solution, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]
  constructor
  · intro i hi
    simpa [matrix_mulVec_boundary B w (solution B w b) hi, hi] using congrFun heq i
  · intro i hi
    simpa [matrix_mulVec_interior B w (solution B w b) hi, hi, Harmonic] using congrFun heq i

theorem continuous_matrix {T : Type*} [TopologicalSpace T]
    (B : Set V) (w : T → V → V → ℝ) (hw : Continuous w) :
    Continuous (fun t => matrix B (w t)) := by
  classical
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hi : i ∈ B
  · simp only [matrix, hi, ↓reduceIte]
    exact continuous_const
  · simp only [matrix, hi, ↓reduceIte]
    apply Continuous.sub
    · by_cases hij : i = j
      · simp only [hij, ↓reduceIte]
        exact continuous_finsetSum _ (fun k _ => ((continuous_apply j).comp hw |> (continuous_apply k).comp))
      · simp only [hij, ↓reduceIte]
        exact continuous_const
    · exact ((continuous_apply i).comp hw |> (continuous_apply j).comp)

/-- The actual coordinate solution varies continuously with any continuous
positive edge-weight family, with no nonvanishing determinant hypothesis left
unproved. This supplies the linear-algebra stage of a Tutte path. -/
theorem continuous_solution {T : Type*} [TopologicalSpace T]
    (G : SimpleGraph V) (hG : G.Connected) (B : Set V) (hB : B.Nonempty)
    (w : T → V → V → ℝ) (hwc : Continuous w)
    (hw : ∀ t i j, 0 ≤ w t i j)
    (he : ∀ t i j, G.Adj i j → 0 < w t i j) (b : V → ℝ) :
    Continuous (fun t => solution B (w t) b) := by
  classical
  have hmc := continuous_matrix B w hwc
  have hd : ∀ t, (matrix B (w t)).det ≠ 0 := by
    intro t
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (matrix_isUnit G hG B hB (w t) (hw t) (he t))).ne_zero
  have hmi : Continuous (fun t => (matrix B (w t))⁻¹) := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv]
    exact (hmc.matrix_det.inv₀ hd).smul hmc.matrix_adjugate
  exact hmi.matrix_mulVec continuous_const

end NormalProjective.Dirichlet
