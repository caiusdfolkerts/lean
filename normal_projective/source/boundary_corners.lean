module

public import triangular_disk
public import Mathlib.Data.Finset.Max

/-!
# The three boundary sides are actual graph edges

This fact is derived from the geometric triangulation. A sufficiently narrow
open half-plane around a side contains precisely its two corners among the
finite vertex set. Connectivity of the induced graph then supplies the edge.
No boundary-edge incidence is added as an assumption on a drawing.
-/

@[expose] public section

namespace NormalProjective.Planar.TriangularDisk

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (D : TriangularDisk V)

theorem source_coordinates_nonnegative (v : V) (j : Fin 3) :
    0 ≤ triangleCoordinate j (D.point v) := by
  have h := D.toTriangulation.point_mem_domain v
  rw [D.domain_eq] at h
  exact h j

theorem coordinate_zero_iff (j : Fin 3) (v : V) :
    triangleCoordinate j (D.point v) = 0 ↔
      ∃ k : Fin 3, k ≠ j ∧ v = D.corner k := by
  constructor
  · intro hv
    by_cases hB : v ∈ D.boundary
    · obtain ⟨k,rfl⟩ := hB
      refine ⟨k,?_,rfl⟩
      intro hkj
      subst k
      simpa [D.corner_point,coordinate_basePoint] using hv
    · exact False.elim ((D.interior_vertex v hB j).ne' hv)
  · rintro ⟨k,hkj,rfl⟩
    rw [D.corner_point,coordinate_basePoint]
    simp [Ne.symm hkj]

theorem coordinate_lt_one_of_ne_corner (j : Fin 3) (v : V)
    (hv : v ≠ D.corner j) : triangleCoordinate j (D.point v) < 1 := by
  by_cases hB : v ∈ D.boundary
  · obtain ⟨k,rfl⟩ := hB
    have hjk : j ≠ k := fun h => hv (congrArg D.corner h.symm)
    simp [D.corner_point,coordinate_basePoint,hjk]
  · have h0 := D.interior_vertex v hB 0
    have h1 := D.interior_vertex v hB 1
    have h2 := D.interior_vertex v hB 2
    fin_cases j <;> simp [triangleCoordinate] at h0 h1 h2 ⊢ <;> linarith

/-- The induced subgraph on the vertices lying on a side is connected. The
finite minimum below only separates zero coordinate values from positive ones;
it does not assume any combinatorial incidence of the side. -/
theorem zero_coordinate_induce_connected (j : Fin 3) :
    (D.toTriangulation.graph.induce
      {v | triangleCoordinate j (D.point v) = 0}).Connected := by
  classical
  let f : V → ℝ := fun v => triangleCoordinate j (D.point v)
  let S : Finset V := univ.filter (fun v => 0 < f v)
  have hjS : D.corner j ∈ S := by
    simp [S,f,D.corner_point,coordinate_basePoint]
  obtain ⟨v,hv,hmin⟩ := Finset.exists_min_image S f ⟨D.corner j,hjS⟩
  have hδ : 0 < f v := (mem_filter.mp hv).2
  have hzero : ∀ u, f u < f v ↔ f u = 0 := by
    intro u
    constructor
    · intro hu
      have hn := D.source_coordinates_nonnegative u j
      by_contra hne
      have hup : 0 < f u := lt_of_le_of_ne hn (Ne.symm hne)
      exact (not_lt_of_ge (hmin u (mem_filter.mpr ⟨mem_univ _,hup⟩))) hu
    · intro hu
      rwa [hu]
  let l : ℂ →L[ℝ] ℝ := -coordinateLinear j
  let c : ℝ := -(f v) - coordinateThreshold j
  have heq : {u | c < l (D.point u)} = {u | f u = 0} := by
    ext u
    have hf := coordinate_eq_linear j (D.point u)
    change -f v - coordinateThreshold j < -coordinateLinear j (D.point u) ↔ f u = 0
    rw [← hzero u]
    dsimp [f] at *
    constructor <;> intro h <;> linarith
  have hne : ∃ u, c < l (D.point u) := by
    have hk : ∃ k : Fin 3, k ≠ j := by
      fin_cases j
      · exact ⟨1,by decide⟩
      · exact ⟨0,by decide⟩
      · exact ⟨0,by decide⟩
    obtain ⟨k,hkj⟩ := hk
    have hfk : f (D.corner k) = 0 := by
      simp [f,D.corner_point,coordinate_basePoint,Ne.symm hkj]
    have hm : D.corner k ∈ {u | c < l (D.point u)} := by
      rw [heq]
      exact hfk
    exact ⟨D.corner k,hm⟩
  have hconv : Convex ℝ D.toTriangulation.domain := by
    rw [D.domain_eq]
    exact baseTriangle_convex
  have hc := D.toTriangulation.positive_induce_connected hconv l c hne
  rw [heq] at hc
  exact hc

theorem boundary_edge_of_third_corner (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hcover : ∀ l : Fin 3, l = i ∨ l = j ∨ l = k) :
    D.toTriangulation.graph.Adj (D.corner i) (D.corner j) := by
  let S : Set V := {v | triangleCoordinate k (D.point v) = 0}
  have hi : D.corner i ∈ S := (D.coordinate_zero_iff k _).mpr ⟨i,hik,rfl⟩
  have hj : D.corner j ∈ S := (D.coordinate_zero_iff k _).mpr ⟨j,hjk,rfl⟩
  have hne : (⟨D.corner i,hi⟩ : S) ≠ ⟨D.corner j,hj⟩ := by
    intro h
    exact hij (D.corner.injective (congrArg Subtype.val h))
  have hc := D.zero_coordinate_induce_connected k
  obtain ⟨z,hiz⟩ := SimpleGraph.Reachable.nonempty_neighborSet_left hne
    (hc ⟨D.corner i,hi⟩ ⟨D.corner j,hj⟩)
  have hadj : D.toTriangulation.graph.Adj (D.corner i) z.val := hiz
  obtain ⟨l,hl,hel⟩ := (D.coordinate_zero_iff k z.val).mp z.property
  rcases hcover l with rfl | rfl | rfl
  · exact False.elim (hadj.ne hel.symm)
  · simpa only [hel] using hadj
  · exact False.elim (hl rfl)

theorem boundary_edge (i j : Fin 3) (hij : i ≠ j) :
    D.toTriangulation.graph.Adj (D.corner i) (D.corner j) := by
  have hex : ∃ k : Fin 3, i ≠ k ∧ j ≠ k ∧
      ∀ l : Fin 3, l = i ∨ l = j ∨ l = k := by
    fin_cases i <;> fin_cases j <;> simp_all
    all_goals decide
  obtain ⟨k,hik,hjk,hcover⟩ := hex
  exact D.boundary_edge_of_third_corner i j k hij hik hjk hcover

end NormalProjective.Planar.TriangularDisk
