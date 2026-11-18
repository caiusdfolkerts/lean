module

public import triangulation
public import dirichlet_strong
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Tactic.FinCases

/-!
# Triangular boundary and strict interior of a harmonic drawing

The boundary has exactly three labelled corners. Its source triangulation is an
actual geometric triangulation of the standard closed triangle. The strict
interiority conclusion below is derived from the harmonic equations and the
proved half-plane connectivity; it is not included as a drawing hypothesis.
-/

@[expose] public section

noncomputable section

namespace NormalProjective.Planar

open Set Finset Complex

def basePoint : Fin 3 → ℂ := ![0,1,Complex.I]

def triangleCoordinate (j : Fin 3) (z : ℂ) : ℝ :=
  ![1-z.re-z.im,z.re,z.im] j

def baseTriangle : Set ℂ := {z | ∀ j, 0 ≤ triangleCoordinate j z}

theorem coordinate_basePoint (i j : Fin 3) :
    triangleCoordinate i (basePoint j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [triangleCoordinate,basePoint]

theorem coordinate_sum (z : ℂ) : ∑ j : Fin 3, triangleCoordinate j z = 1 := by
  simp [triangleCoordinate,Fin.sum_univ_succ]

theorem coordinate_reconstruct (z : ℂ) :
    ∑ j : Fin 3, triangleCoordinate j z • basePoint j = z := by
  apply Complex.ext <;> simp [triangleCoordinate,basePoint,Fin.sum_univ_succ]

def coordinateLinear : Fin 3 → (ℂ →L[ℝ] ℝ) :=
  ![-(Complex.reCLM + Complex.imCLM),Complex.reCLM,Complex.imCLM]

def coordinateThreshold : Fin 3 → ℝ := ![-1,0,0]

theorem coordinate_eq_linear (j : Fin 3) (z : ℂ) :
    triangleCoordinate j z = coordinateLinear j z - coordinateThreshold j := by
  fin_cases j <;> simp [triangleCoordinate,coordinateLinear,coordinateThreshold] <;> ring

theorem baseTriangle_convex : Convex ℝ baseTriangle := by
  have heq : baseTriangle = ⋂ j : Fin 3,
      {z | coordinateThreshold j ≤ coordinateLinear j z} := by
    ext z
    simp only [baseTriangle,mem_setOf_eq,mem_iInter,coordinate_eq_linear,sub_nonneg]
  rw [heq]
  exact convex_iInter (fun j => convex_halfSpace_ge (coordinateLinear j).toLinearMap.isLinear _)

theorem baseTriangle_eq_convexHull : baseTriangle = convexHull ℝ (range basePoint) := by
  apply Set.Subset.antisymm
  · intro z hz
    rw [← coordinate_reconstruct z]
    exact (convex_convexHull ℝ (range basePoint)).sum_mem
      (fun i _ => hz i) (coordinate_sum z)
      (fun i _ => subset_convexHull ℝ _ ⟨i,rfl⟩)
  · apply convexHull_min _ baseTriangle_convex
    rintro _ ⟨i,rfl⟩ j
    rw [coordinate_basePoint]
    split_ifs <;> norm_num

theorem coordinate_continuous (j : Fin 3) : Continuous (triangleCoordinate j) := by
  change Continuous (fun z => triangleCoordinate j z)
  simp_rw [coordinate_eq_linear]
  exact (coordinateLinear j).continuous.sub continuous_const

theorem mem_interior_baseTriangle_of_coordinates {z : ℂ}
    (hz : ∀ j, 0 < triangleCoordinate j z) : z ∈ interior baseTriangle := by
  let U : Set ℂ := {z | ∀ j, 0 < triangleCoordinate j z}
  have hU : IsOpen U := by
    have heq : U = ⋂ j : Fin 3, {z | 0 < triangleCoordinate j z} := by
      ext z
      simp [U]
    rw [heq]
    exact isOpen_iInter_of_finite (fun j => isOpen_lt continuous_const (coordinate_continuous j))
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hU.mem_nhds hz) (fun z hz j => (hz j).le))

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A genuine geometric triangulation of a triangle with exactly its three
corners as boundary vertices. The strict inequalities express the remaining
vertices' membership in the ordinary triangle interior. -/
structure TriangularDisk (V : Type*) [Fintype V] [DecidableEq V]
    extends Triangulation V where
  corner : Fin 3 ↪ V
  corner_point : ∀ j, point (corner j) = basePoint j
  domain_eq : toTriangulation.domain = baseTriangle
  interior_vertex : ∀ v, v ∉ Set.range corner →
    ∀ j, 0 < triangleCoordinate j (point v)

namespace TriangularDisk

variable (D : TriangularDisk V)

def boundary : Set V := range D.corner

theorem boundary_nonempty : D.boundary.Nonempty := ⟨D.corner 0,0,rfl⟩

theorem graph_connected : D.toTriangulation.graph.Connected := by
  letI : Nonempty V := ⟨D.corner 0⟩
  apply D.toTriangulation.graph_connected
  rw [D.domain_eq]
  exact baseTriangle_convex.isPreconnected

theorem positive_coordinate_vertices (j : Fin 3) :
    {v | coordinateThreshold j < coordinateLinear j (D.point v)} =
      {v | v ∉ D.boundary ∨ v = D.corner j} := by
  ext v
  change (coordinateThreshold j < coordinateLinear j (D.point v)) ↔
    (v ∉ D.boundary ∨ v = D.corner j)
  rw [← sub_pos,← coordinate_eq_linear]
  by_cases hv : v ∈ D.boundary
  · obtain ⟨k,rfl⟩ := hv
    rw [D.corner_point,coordinate_basePoint]
    by_cases hjk : j = k
    · subst k
      simp
    · have hkj : D.corner k ≠ D.corner j := fun h => hjk (D.corner.injective h).symm
      simp [hjk,hkj,show D.corner k ∈ D.boundary from ⟨k,rfl⟩]
  · simp only [hv,not_false_eq_true,true_or,iff_true]
    exact D.interior_vertex v hv j

theorem corner_accessible (j : Fin 3) (v : V) (hv : v ∉ D.boundary) :
    (D.toTriangulation.graph.induce {u | u ∉ D.boundary ∨ u = D.corner j}).Reachable
      ⟨v,Or.inl hv⟩ ⟨D.corner j,Or.inr rfl⟩ := by
  have hconvex : Convex ℝ D.toTriangulation.domain := D.domain_eq ▸ baseTriangle_convex
  have hcorner : coordinateThreshold j < coordinateLinear j (D.point (D.corner j)) := by
    rw [← sub_pos,← coordinate_eq_linear,D.corner_point,coordinate_basePoint]
    simp
  have hconn := D.toTriangulation.positive_induce_connected hconvex
    (coordinateLinear j) (coordinateThreshold j) ⟨D.corner j,hcorner⟩
  rw [D.positive_coordinate_vertices j] at hconn
  exact hconn _ _

theorem coordinates_nonneg_of_harmonic
    (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (he : ∀ i j, D.toTriangulation.graph.Adj i j → 0 < w i j)
    (q : V → ℂ) (hqB : ∀ j, q (D.corner j) = basePoint j)
    (hq : ∀ v, v ∉ D.boundary → ∀ j,
      Dirichlet.Harmonic w (fun v => triangleCoordinate j (q v)) v) :
    ∀ v j, 0 ≤ triangleCoordinate j (q v) := by
  intro v j
  apply Dirichlet.minimum_principle D.toTriangulation.graph D.graph_connected
    D.boundary D.boundary_nonempty w hw he
    (fun v => triangleCoordinate j (q v)) (fun v hv => hq v hv j) 0 _ v
  rintro b ⟨k,rfl⟩
  rw [hqB,coordinate_basePoint]
  split_ifs <;> norm_num

/-- Every interior vertex of the actual harmonic drawing lies strictly inside
the base triangle. The accessibility premise of the strong principle is proved
from the source triangulation, not assumed. -/
theorem interior_of_harmonic
    (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (he : ∀ i j, D.toTriangulation.graph.Adj i j → 0 < w i j)
    (q : V → ℂ) (hqB : ∀ j, q (D.corner j) = basePoint j)
    (hq : ∀ v, v ∉ D.boundary → ∀ j,
      Dirichlet.Harmonic w (fun v => triangleCoordinate j (q v)) v)
    (v : V) (hv : v ∉ D.boundary) : q v ∈ interior baseTriangle := by
  apply mem_interior_baseTriangle_of_coordinates
  intro j
  apply Dirichlet.strict_minimum_of_accessible D.toTriangulation.graph D.graph_connected
    D.boundary w hw he (fun v => triangleCoordinate j (q v))
    (fun v hv => hq v hv j) 0 _ (D.corner j) ⟨j,rfl⟩ _ v hv (D.corner_accessible j v hv)
  · rintro b ⟨k,rfl⟩
    rw [hqB,coordinate_basePoint]
    split_ifs <;> norm_num
  · rw [hqB,coordinate_basePoint]
    simp

end TriangularDisk

end NormalProjective.Planar
