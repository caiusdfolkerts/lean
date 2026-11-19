module

public import VolumePolynomials.RationalBoxVolume
public import VolumePolynomials.RationalInterpolation
public import VolumePolynomials.BodyOperations
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.List.FinRange

@[expose] public section
set_option autoImplicit false

/-!
# Executable samples for rational vertex lists

All lists used in the algorithm have explicit order. In particular no
noncomputable conversion from a finset to a list is used. Actual finite
Minkowski sums are represented by all finite choices of one listed vertex
from each summand; their volume samples are computed with the certified
box-counting search.
-/

open Set Finset MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.RationalHulls

abbrev RationalPoint (d : ℕ) := Fin d → ℚ

def realPoint {d : ℕ} (x : RationalPoint d) : Space d := fun i => (x i : ℝ)

theorem realPoint_zero (d : ℕ) : realPoint (0 : RationalPoint d) = (0 : Space d) := by
  first
  | funext i
    change ((0 : ℚ) : ℝ) = 0
    exact Rat.cast_zero

def vertices {d : ℕ} (L : List (RationalPoint d)) : Set (Space d) :=
  realPoint '' {x | x ∈ L}

def hull {d : ℕ} (L : List (RationalPoint d)) : Set (Space d) := convexHull ℝ (vertices L)

theorem vertices_finite {d : ℕ} (L : List (RationalPoint d)) : (vertices L).Finite := by
  first
  | simpa only [vertices, List.coe_toFinset] using L.toFinset.finite_toSet.image realPoint

theorem vertices_eq_range {d : ℕ} (L : List (RationalPoint d)) :
    vertices L = range (fun i : Fin L.length => realPoint (L.get i)) := by
  first
  | ext x
    simp only [vertices, Set.mem_image, Set.mem_setOf_eq, List.mem_iff_get, Set.mem_range]
    constructor
    · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨L.get i, ⟨i, rfl⟩, rfl⟩

noncomputable def body {d : ℕ} (L : List (RationalPoint d)) (hL : 0 ∈ L) : Body d where
  carrier := hull L
  convex' := convex_convexHull ℝ _
  isCompact' := (vertices_finite L).isCompact_convexHull ℝ
  nonempty' := ⟨(0 : Space d),
    subset_convexHull ℝ _ ⟨(0 : RationalPoint d), hL, realPoint_zero d⟩⟩

theorem zero_mem_body {d : ℕ} (L : List (RationalPoint d)) (hL : 0 ∈ L) :
    (0 : Space d) ∈ body L hL :=
  subset_convexHull ℝ _ ⟨(0 : RationalPoint d), hL, realPoint_zero d⟩

theorem body_subset_box {d : ℕ} (L : List (RationalPoint d)) (hL : 0 ∈ L)
    (R : ℚ) (hbox : ∀ v ∈ L, ∀ i, |v i| ≤ R) :
    (body L hL : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)) := by
  first
  | apply convexHull_min _ (convex_Icc _ _)
    rintro x ⟨v, hv, rfl⟩
    constructor
    · intro i
      have h := (abs_le.mp (hbox v hv i)).1
      change -(R : ℝ) ≤ (v i : ℝ)
      exact_mod_cast h
    · intro i
      have h := (abs_le.mp (hbox v hv i)).2
      change (v i : ℝ) ≤ (R : ℝ)
      exact_mod_cast h

def radiusBound {d : ℕ} (L : List (RationalPoint d)) : ℚ :=
  (L.map (fun v => ∑ i, |v i|)).sum

def integerRadius {d : ℕ} (L : List (RationalPoint d)) : ℕ := ⌈radiusBound L⌉₊

theorem abs_le_radiusBound {d : ℕ} (L : List (RationalPoint d))
    {v : RationalPoint d} (hv : v ∈ L) (i : Fin d) : |v i| ≤ radiusBound L := by
  first
  | apply (Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)).trans
    exact List.single_le_sum (by
      intro q hq
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
      exact Finset.sum_nonneg (fun j _ => abs_nonneg (w j))) _ (List.mem_map.mpr ⟨v, hv, rfl⟩)

theorem hull_subset_ambient {d : ℕ} (L : List (RationalPoint d)) :
    hull L ⊆ RationalElimination.ambientBox d (integerRadius L) := by
  first
  | have hclosed : hull L ⊆ Icc (fun _ : Fin d => -(integerRadius L : ℝ))
        (fun _ => (integerRadius L : ℝ)) := by
      apply convexHull_min _ (convex_Icc _ _)
      rintro x ⟨v, hv, rfl⟩
      have hcoord (i : Fin d) : |realPoint v i| ≤ (integerRadius L : ℝ) := by
        have h := (abs_le_radiusBound L hv i).trans (Nat.le_ceil (radiusBound L))
        change |(v i : ℝ)| ≤ (integerRadius L : ℝ)
        rw [← Rat.cast_abs]
        exact_mod_cast h
      exact ⟨fun i => (abs_le.mp (hcoord i)).1, fun i => (abs_le.mp (hcoord i)).2⟩
    intro x hx i
    have h := hclosed hx
    exact ⟨by change -((integerRadius L : ℝ) + 1) < x i; linarith [h.1 i],
      by change x i ≤ (integerRadius L : ℝ) + 1; linarith [h.2 i]⟩

theorem halfspaces_solution_eq_hull {d : ℕ} (L : List (RationalPoint d)) :
    RationalElimination.solutionSet (RationalElimination.hullHalfspaces L.get) = hull L := by
  first
  | ext x
    rw [RationalElimination.solutionSet, Set.mem_setOf_eq,
      RationalElimination.hullHalfspaces_correct, hull, vertices_eq_range]
    rfl

/-- The radius and every halfspace are computed from the given finite list. -/
def approximateHullVolume {d : ℕ} (L : List (RationalPoint d)) (ε : ℚ) (hε : 0 < ε) : ℚ :=
  RationalElimination.approximateVolume (RationalElimination.hullHalfspaces L.get)
    (integerRadius L) (by rw [halfspaces_solution_eq_hull]; exact hull_subset_ambient L) ε hε

theorem approximateHullVolume_correct {d : ℕ} (L : List (RationalPoint d))
    (ε : ℚ) (hε : 0 < ε) :
    |(approximateHullVolume L ε hε : ℝ) - volume.real (hull L)| < (ε : ℝ) := by
  first
  | unfold approximateHullVolume
    simpa only [halfspaces_solution_eq_hull] using
      RationalElimination.approximateVolume_correct
        (RationalElimination.hullHalfspaces L.get) (integerRadius L)
        (by rw [halfspaces_solution_eq_hull]; exact hull_subset_ambient L) ε hε

/-- Ordered finite Cartesian products. -/
def selections {α : Type*} : {n : ℕ} → (Fin n → List α) → List (Fin n → α)
  | 0, _ => [Fin.elim0]
  | n + 1, L => (L 0).flatMap (fun a => (selections (Fin.tail L)).map (Fin.cons a))

theorem mem_selections {α : Type*} {n : ℕ} (L : Fin n → List α) (f : Fin n → α) :
    f ∈ selections L ↔ ∀ i, f i ∈ L i := by
  first
  | induction n with
    | zero =>
        simp only [selections, List.mem_singleton]
        constructor
        · intro _ i
          exact Fin.elim0 i
        · intro _
          funext i
          exact Fin.elim0 i
    | succ n ih =>
        simp only [selections, List.mem_flatMap, List.mem_map]
        constructor
        · rintro ⟨a, ha, g, hg, rfl⟩ i
          cases i using Fin.cases with
          | zero => exact ha
          | succ i => exact (ih (Fin.tail L) g).mp hg i
        · intro h
          exact ⟨f 0, h 0, Fin.tail f, (ih (Fin.tail L) (Fin.tail f)).mpr (fun i => h i.succ),
            Fin.cons_self_tail f⟩

def weightedVertices {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (t : Fin n → ℚ) : List (RationalPoint d) :=
  (selections L).map (fun f => ∑ i, t i • f i)

theorem mem_weightedVertices {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (t : Fin n → ℚ) (v : RationalPoint d) :
    v ∈ weightedVertices L t ↔ ∃ f : Fin n → RationalPoint d,
      (∀ i, f i ∈ L i) ∧ ∑ i, t i • f i = v := by
  first
  | simp only [weightedVertices, List.mem_map, mem_selections]

theorem zero_mem_weightedVertices {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (hL : ∀ i, 0 ∈ L i) (t : Fin n → ℚ) : 0 ∈ weightedVertices L t := by
  first
  | exact Iff.mpr (mem_weightedVertices L t 0) ⟨fun _ => 0, hL, by simp⟩

theorem vertices_weightedVertices {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (t : Fin n → ℚ) :
    vertices (weightedVertices L t) = ∑ i, (t i : ℝ) • vertices (L i) := by
  first
  | classical
    ext x
    rw [Set.mem_fintype_sum]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨f, hf, rfl⟩ := Iff.mp (mem_weightedVertices L t v) hv
      refine ⟨fun i => (t i : ℝ) • realPoint (f i), ?_, ?_⟩
      · intro i
        exact ⟨realPoint (f i), ⟨f i, hf i, rfl⟩, rfl⟩
      · ext j
        simp [realPoint]
    · rintro ⟨a, ha, rfl⟩
      have hpoints : ∀ i, ∃ q ∈ L i, (t i : ℝ) • realPoint q = a i := by
        intro i
        obtain ⟨y, ⟨q, hq, rfl⟩, hqy⟩ := ha i
        exact ⟨q, hq, hqy⟩
      choose q hq hqa using hpoints
      refine ⟨∑ i, t i • q i, Iff.mpr (mem_weightedVertices L t _) ⟨q, hq, rfl⟩, ?_⟩
      rw [show (∑ i, a i) = ∑ i, (t i : ℝ) • realPoint (q i) by simp only [hqa]]
      ext j
      simp [realPoint]

theorem hull_weightedVertices {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (t : Fin n → ℚ) :
    hull (weightedVertices L t) = ∑ i, (t i : ℝ) • hull (L i) := by
  first
  | rw [hull, vertices_weightedVertices, convexHull_sum]
    simp only [convexHull_smul, hull]

theorem weightedSum_body {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (hL : ∀ i, 0 ∈ L i) (t : Fin n → ℚ) :
    (weightedSum (fun i => body (L i) (hL i)) (fun i => (t i : ℝ)) : Set (Space d)) =
      hull (weightedVertices L t) := by
  first
  | rw [weightedSum, coe_sum_body, hull_weightedVertices]
    rfl

/-- Pure rational approximate coefficient vector recovered from all prescribed
positive rational samples. -/
def approximateCoefficients {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (ε : ℚ) (hε : 0 < ε) : MultiIndex n d → ℚ :=
  fun α => ∑ j : Fin (interpolationSize n d), coefficientExtractionWeight α j *
    approximateHullVolume (weightedVertices L (interpolationWeight j)) ε hε

theorem approximateCoefficients_correct {n d : ℕ} (L : Fin n → List (RationalPoint d))
    (hL : ∀ i, 0 ∈ L i) {c : Coefficients n d}
    (hc : Realizes (fun i => body (L i) (hL i)) c) (ε : ℚ) (hε : 0 < ε)
    (α : MultiIndex n d) :
    |(approximateCoefficients L ε hε α : ℝ) - c α| ≤
      (coefficientExtractionBound n d : ℝ) * (ε : ℝ) := by
  first
  | rw [coefficient_eq_rational_samples c α]
    simp only [approximateCoefficients, Rat.cast_sum, Rat.cast_mul, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j : Fin (interpolationSize n d),
          |(coefficientExtractionWeight α j : ℝ)| * (ε : ℝ) := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j _
        rw [← mul_sub, abs_mul, hc _ (fun i => by exact_mod_cast (interpolationWeight_pos j i).le)]
        change |(coefficientExtractionWeight α j : ℝ)| *
          |(approximateHullVolume _ ε hε : ℝ) - volume.real
            (weightedSum (fun i => body (L i) (hL i))
              (fun i => (interpolationWeight j i : ℝ)) : Set (Space d))| ≤ _
        rw [weightedSum_body]
        exact mul_le_mul_of_nonneg_left (approximateHullVolume_correct _ ε hε).le (abs_nonneg _)
      _ = (∑ j : Fin (interpolationSize n d), |(coefficientExtractionWeight α j : ℝ)|) * (ε : ℝ) :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ (coefficientExtractionBound n d : ℝ) * (ε : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by exact_mod_cast hε.le)
        simp only [coefficientExtractionBound, Rat.cast_sum, Rat.cast_abs]
        exact Finset.single_le_sum
          (fun β _ => Finset.sum_nonneg (fun j _ => abs_nonneg (coefficientExtractionWeight β j : ℝ)))
          (Finset.mem_univ α)

end VolumePolynomials.RationalHulls
