module

public import stress_flex

@[expose] public section

noncomputable section

open Matrix
open scoped BigOperators

namespace StressFlex.Torus

/-- The three lower-ring vertices \(A_k\) in the paper, indexed from zero. -/
def lowerA : Fin 3 → FrameworkVertex := ![1, 2, 3]

/-- The three middle-ring vertices \(B_k\) in the paper, indexed from zero. -/
def lowerB : Fin 3 → FrameworkVertex := ![4, 5, 6]

/-- The current lower face traverses \(A_kB_k\); its predecessor traverses it backwards. -/
theorem lower_face_corners (k : Fin 3) :
    faceVertex (faceIndex k 0) 0 = lowerA k ∧
    faceVertex (faceIndex k 0) 1 = lowerB k ∧
    faceVertex (faceIndex (k + 2) 0) 2 = lowerB k ∧
    faceVertex (faceIndex (k + 2) 0) 3 = lowerA k := by
  fin_cases k <;> decide

theorem lower_faces_distinct (k : Fin 3) :
    faceIndex k 0 ≠ faceIndex (k + 2) 0 := by
  fin_cases k <;> decide

theorem lower_edge_endpoints_distinct (k : Fin 3) :
    position (lowerA k) ≠ position (lowerB k) := by
  apply position_injective.ne
  fin_cases k <;> decide

/-- Adjacent base-triangle sides meet at the initial endpoint of the current side. -/
theorem lower_base_parameter (k : Fin 3) (s t : I)
    (h : baseEdge (k + 2) s = baseEdge k t) : t = i0 := by
  have hr := congrArg (fun z : baseGauge.Boundary => (z : ℂ).re) h
  have hi := congrArg (fun z : baseGauge.Boundary => (z : ℂ).im) h
  apply Subtype.ext
  change (t : ℝ) = 0
  fin_cases k <;>
    norm_num [baseEdge, baseEdgeCoord] at hr hi <;> linarith

theorem lower_edge_param (k : Fin 3) (t : I) :
    cellParam k 0 (i0, t) =
      (1 - (t : ℝ)) • position (lowerA k) + (t : ℝ) • position (lowerB k) := by
  have h := cellParam_squareEdge k 0 0 t
  simpa only [squareEdge, Matrix.cons_val_zero, zero_add,
    (lower_face_corners k).1, (lower_face_corners k).2.1] using h

/-- The lower dual-cycle adjacency is geometric: the two closed quadrilateral faces meet
in exactly the nondegenerate straight edge \(A_kB_k\). -/
theorem lower_faces_intersection (k : Fin 3) :
    faceSet (k + 2) 0 ∩ faceSet k 0 =
      segment ℝ (position (lowerA k)) (position (lowerB k)) := by
  apply Set.Subset.antisymm
  · rintro p ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have heq : cellParam (k + 2) 0 s = cellParam k 0 t := hs.trans ht.symm
    have hbase := congrArg Prod.fst (param_injective heq)
    have ht0 : t.1 = i0 := lower_base_parameter k s.1 t.1 hbase
    have hp : p = cellParam k 0 (i0, t.2) := by
      rw [← ht, ← ht0]
    rw [hp, lower_edge_param, segment_eq_image]
    exact ⟨(t.2 : ℝ), t.2.2, rfl⟩
  · intro p hp
    have hcorner (a : Fin 3) (j : Fin 4) :
        position (faceVertex (faceIndex a 0) j) ∈ faceSet a 0 :=
      ⟨squareCorner j, cellParam_corner a 0 j⟩
    have hA : position (lowerA k) ∈ faceSet k 0 := by
      simpa only [(lower_face_corners k).1] using hcorner k 0
    have hB : position (lowerB k) ∈ faceSet k 0 := by
      simpa only [(lower_face_corners k).2.1] using hcorner k 1
    have hAprev : position (lowerA k) ∈ faceSet (k + 2) 0 := by
      simpa only [(lower_face_corners k).2.2.2] using hcorner (k + 2) 3
    have hBprev : position (lowerB k) ∈ faceSet (k + 2) 0 := by
      simpa only [(lower_face_corners k).2.2.1] using hcorner (k + 2) 2
    exact ⟨(faceSet_convex (k + 2) 0).segment_subset hAprev hBprev hp,
      (faceSet_convex k 0).segment_subset hA hB hp⟩

/-- The exact vector period printed in the paper; only the first summand is nonzero. -/
theorem lower_cycle_period :
    ∑ k : Fin 3, stress (lowerA k) (lowerB k) •
      (position (lowerA k) ⨯₃ position (lowerB k)) = ![0, -4, 0] := by
  ext j
  fin_cases j <;>
    norm_num [lowerA, lowerB, stress, affineDependence, position, cross_apply,
      Fin.sum_univ_succ]

theorem lower_cycle_period_ne_zero :
    (∑ k : Fin 3, stress (lowerA k) (lowerB k) •
      (position (lowerA k) ⨯₃ position (lowerB k))) ≠ 0 := by
  rw [lower_cycle_period]
  intro h
  have hcoord := congrArg (fun v : FrameworkVector => v 1) h
  norm_num at hcoord

/-- Every genuine face-potential difference has zero period on the three-face cycle. -/
theorem lower_cycle_coboundary_sum (a : Fin 9 → FrameworkVector) :
    ∑ k : Fin 3, (a (faceIndex k 0) - a (faceIndex (k + 2) 0)) = 0 := by
  norm_num [Fin.sum_univ_succ, faceIndex]
  abel

/-- There is no assignment of vectors to all nine faces that realizes even the three
required differences along this actual geometric dual cycle. -/
theorem no_lower_cycle_face_potentials :
    ¬ ∃ a : Fin 9 → FrameworkVector, ∀ k : Fin 3,
      a (faceIndex k 0) - a (faceIndex (k + 2) 0) =
        stress (lowerA k) (lowerB k) •
          (position (lowerA k) ⨯₃ position (lowerB k)) := by
  rintro ⟨a, ha⟩
  have hsum :
      (∑ k : Fin 3, (a (faceIndex k 0) - a (faceIndex (k + 2) 0))) =
        ∑ k : Fin 3, stress (lowerA k) (lowerB k) •
          (position (lowerA k) ⨯₃ position (lowerB k)) :=
    Finset.sum_congr rfl (fun k _ => ha k)
  rw [lower_cycle_coboundary_sum] at hsum
  exact lower_cycle_period_ne_zero hsum.symm

/-- A global potential would in particular give the prescribed difference across each
oriented edge shared by two of the nine printed face cycles. -/
def RealizesFaceDifferences (a : Fin 9 → FrameworkVector) : Prop :=
  ∀ (f g : Fin 9) (j l : Fin 4), f ≠ g →
    faceVertex f j = faceVertex g (l + 1) →
    faceVertex f (j + 1) = faceVertex g l →
    a f - a g =
      stress (faceVertex f j) (faceVertex f (j + 1)) •
        (position (faceVertex f j) ⨯₃ position (faceVertex f (j + 1)))

theorem no_global_face_potentials :
    ¬ ∃ a : Fin 9 → FrameworkVector, RealizesFaceDifferences a := by
  rintro ⟨a, ha⟩
  apply no_lower_cycle_face_potentials
  refine ⟨a, fun k => ?_⟩
  have h :=
    ha (faceIndex k 0) (faceIndex (k + 2) 0) 0 2 (lower_faces_distinct k)
      (by simpa only [show (2 : Fin 4) + 1 = 3 by decide,
          (lower_face_corners k).1, (lower_face_corners k).2.2.2])
      (by simpa only [zero_add, (lower_face_corners k).2.1,
          (lower_face_corners k).2.2.1])
  simpa only [zero_add, (lower_face_corners k).1, (lower_face_corners k).2.1] using h

#print axioms lower_faces_intersection
#print axioms lower_cycle_period
#print axioms no_lower_cycle_face_potentials
#print axioms no_global_face_potentials

end StressFlex.Torus

