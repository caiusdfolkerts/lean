module

public import Recovery.Unimodular.NativePort.A3Geometry
public import Recovery.Unimodular.PriorExtensions.SquareSubdivision
public import Mathlib.Tactic.Tauto

@[expose] public section

/-! UNVERIFIED until the exact native compiler result is successful.
This aggregate includes all actual polygon/chart/facet compatibility
proofs and restricts the actual fan equivalence by lattice regularity.
It contains no projectivity classification. See the body manifest. -/

/- Exact current draft body: SquareSubdivisionClassify. -/
section Enumeration_SquareSubdivisionClassify



/-!
UNVERIFIED EXTENSION DRAFT. Intended module path in the separately pinned rc2
project: SquareSubdivisionClassify. This file develops the actual geometric
classification, not merely a count of abstract diagonal assignments.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set
open scoped BigOperators

namespace Unimodular.SquareSubdivision

/-- Every actual face of a square-vertex polytope has an exact original-vertex
key, including empty and lower-dimensional faces. -/
theorem face_has_key {s : Key} {F : Set Plane}
    (hF : Convex ℝ F) (hface : IsExtreme ℝ (hull s) F) :
    ∃ t : Key, t ⊆ s ∧ F = hull t ∧ FaceKey s t := by
  classical
  let t := s.filter (fun i => vertex i ∈ F)
  have himage : (vertex '' (s : Set (Fin 4))) ∩ F = vertex '' (t : Set (Fin 4)) := by
    ext x
    constructor
    · rintro ⟨⟨i,hi,rfl⟩,hx⟩
      exact ⟨i,Finset.mem_filter.mpr ⟨hi,hx⟩,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,(Finset.mem_filter.mp hi).1,rfl⟩,(Finset.mem_filter.mp hi).2⟩
  have heq : F = hull t := by
    rw [face_eq_convexHull_inter (vertex '' (s : Set (Fin 4))) F hF hface,himage]
    rfl
  refine ⟨t,Finset.filter_subset _ _,heq,?_⟩
  rw [heq] at hface
  exact isExtreme_iff_faceKey.mp hface

/-- Subdivision cells are encoded using all genuine geometric vertices, and
no code is assumed as part of the subdivision structure. -/
theorem cell_has_key {r : Key} (D : VertexSubdivision (hull r))
    {F : Set Plane} (hF : F ∈ D.cells) :
    ∃ s : Key, s ⊆ r ∧ F = hull s := by
  classical
  obtain ⟨T,hFT,hT⟩ := D.vertices F hF
  let s := r.filter (fun i => vertex i ∈ T)
  have hgen : (T : Set Plane) ⊆ vertex '' (r : Set (Fin 4)) :=
    hT.trans extremePoints_convexHull_subset
  have himage : vertex '' (s : Set (Fin 4)) = (T : Set Plane) := by
    ext x
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact (Finset.mem_filter.mp hi).2
    · intro hx
      obtain ⟨i,hi,rfl⟩ := hgen hx
      exact ⟨i,Finset.mem_filter.mpr ⟨hi,hx⟩,rfl⟩
  refine ⟨s,Finset.filter_subset _ _,?_⟩
  rw [hFT,hull,himage]

/-- Actual subdivisions with the same sets of geometric cells coincide. -/
theorem subdivision_ext {P : Set Plane} {D E : VertexSubdivision P}
    (h : D.cells = E.cells) : D = E := by
  cases D
  cases E
  cases h
  rfl

def triangle (i : Fin 4) : Key := Finset.univ.erase i

@[simp] theorem mem_triangle (i j : Fin 4) : j ∈ triangle i ↔ j ≠ i := by
  simp [triangle]

theorem triangle_ne_univ (i : Fin 4) : triangle i ≠ Finset.univ := by
  intro h
  have hi : i ∈ triangle i := h.symm ▸ Finset.mem_univ i
  simpa using hi

theorem triangle0_subset : ∀ s : Key,
    triangle 0 ⊆ s ↔ 1 ∈ s ∧ 2 ∈ s ∧ 3 ∈ s := by decide

theorem triangle1_subset : ∀ s : Key,
    triangle 1 ⊆ s ↔ 0 ∈ s ∧ 2 ∈ s ∧ 3 ∈ s := by decide

theorem triangle2_subset : ∀ s : Key,
    triangle 2 ⊆ s ↔ 0 ∈ s ∧ 1 ∈ s ∧ 3 ∈ s := by decide

theorem triangle3_subset : ∀ s : Key,
    triangle 3 ⊆ s ↔ 0 ∈ s ∧ 1 ∈ s ∧ 2 ∈ s := by decide

/-- A set of square corners containing a triangle is that triangle or all four
corners. This finite statement is used only after actual geometric coverage. -/
theorem superset_triangle : ∀ (i : Fin 4) (s : Key), triangle i ⊆ s →
    s = triangle i ∨ s = Finset.univ := by decide

def probe : Fin 4 → Plane :=
  ![![(1/2 : ℝ),1/4],![3/4,1/2],![1/2,3/4],![1/4,1/2]]

def probeWeights : Fin 4 → Fin 4 → ℝ :=
  ![![1/2,1/4,1/4,0],![0,1/2,1/4,1/4],
    ![1/4,0,1/2,1/4],![1/2,0,1/4,1/4]]

def probeMissing : Fin 4 → Fin 4 × Fin 4 := ![(2,3),(0,3),(0,1),(1,2)]

theorem probe_mem_square (i : Fin 4) : probe i ∈ square := by
  apply mem_hull_iff.mpr
  refine ⟨probeWeights i,?_,?_,?_,?_⟩
  · intro j
    fin_cases i <;> fin_cases j <;> norm_num [probeWeights]
  · intro j hj
    exact (hj (Finset.mem_univ j)).elim
  · fin_cases i <;> norm_num [probeWeights,Fin.sum_univ_succ]
  · ext j
    fin_cases i <;> fin_cases j <;>
      norm_num [probeWeights,probe,vertex,Fin.sum_univ_succ,Finset.sum_apply]

/-- Each interior probe forces one of the two triangles whose interiors
contain it. The proof uses real barycentric coordinates, not an oracle for
convex-hull membership. -/
theorem probe_forces_triangle {s : Key} (i : Fin 4) (hi : probe i ∈ hull s) :
    triangle (probeMissing i).1 ⊆ s ∨ triangle (probeMissing i).2 ⊆ s := by
  obtain ⟨a,ha,hz,hs,hpoint⟩ := mem_hull_iff.mp hi
  obtain ⟨h0,h1⟩ := weights_coordinates a
  rw [hpoint] at h0 h1
  rw [weights_sum] at hs
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have ha3 := ha 3
  have hz0 := hz 0
  have hz1 := hz 1
  have hz2 := hz 2
  have hz3 := hz 3
  fin_cases i
  all_goals first
    | change triangle 2 ⊆ s ∨ triangle 3 ⊆ s
    | change triangle 0 ⊆ s ∨ triangle 3 ⊆ s
    | change triangle 0 ⊆ s ∨ triangle 1 ⊆ s
    | change triangle 1 ⊆ s ∨ triangle 2 ⊆ s
  all_goals
    simp only [triangle0_subset,triangle1_subset,triangle2_subset,triangle3_subset]
    norm_num [probe] at h0 h1
    by_cases hm0 : (0 : Fin 4) ∈ s <;>
      by_cases hm1 : (1 : Fin 4) ∈ s <;>
      by_cases hm2 : (2 : Fin 4) ∈ s <;>
      by_cases hm3 : (3 : Fin 4) ∈ s <;>
      simp only [hm0,hm1,hm2,hm3,not_true_eq_false,not_false_eq_true,
        false_implies,true_implies,true_and,and_true,false_and,and_false,
        true_or,or_true,false_or,or_false] at hz0 hz1 hz2 hz3 ⊢
  all_goals linarith only [ha0,ha1,ha2,ha3,h0,h1,hs,hz0,hz1,hz2,hz3]

/-- Coverage by genuine cells forces one of the three possible maximal-cell
patterns. No restriction on the number of cells is a premise. -/
theorem subdivision_contains_maximal_pattern (D : VertexSubdivision square) :
    square ∈ D.cells ∨
      (hull (triangle 0) ∈ D.cells ∧ hull (triangle 2) ∈ D.cells) ∨
      (hull (triangle 1) ∈ D.cells ∧ hull (triangle 3) ∈ D.cells) := by
  classical
  by_cases hwhole : square ∈ D.cells
  · exact Or.inl hwhole
  have hprobe (i : Fin 4) :
      hull (triangle (probeMissing i).1) ∈ D.cells ∨
        hull (triangle (probeMissing i).2) ∈ D.cells := by
    have hp := probe_mem_square i
    rw [← D.cover] at hp
    obtain ⟨F,hF,hp⟩ := hp
    obtain ⟨s,hs,heq⟩ := cell_has_key D hF
    rw [heq] at hp hF
    have hns : s ≠ Finset.univ := by
      intro h
      apply hwhole
      simpa only [h,square] using hF
    rcases probe_forces_triangle i hp with h | h
    · rcases superset_triangle _ s h with he | he
      · exact Or.inl (he ▸ hF)
      · exact (hns he).elim
    · rcases superset_triangle _ s h with he | he
      · exact Or.inr (he ▸ hF)
      · exact (hns he).elim
  have h0 := hprobe 0
  have h1 := hprobe 1
  have h2 := hprobe 2
  have h3 := hprobe 3
  simp only [probeMissing,Matrix.cons_val_zero,Matrix.cons_val_succ] at h0 h1 h2 h3
  exact Or.inr (by tauto)

/-- If the square itself is a cell, the face axioms force precisely all its
ordinary faces and permit no diagonal or extra triangle. -/
theorem cells_of_whole (D : VertexSubdivision square) (hwhole : square ∈ D.cells) :
    D.cells = hull '' {s : Key | FaceKey Finset.univ s} := by
  ext F
  constructor
  · intro hF
    obtain ⟨s,hs,rfl⟩ := cell_has_key D hF
    refine ⟨s,?_,rfl⟩
    apply isExtreme_iff_faceKey.mp
    have h := (D.intersection_faces square hwhole (hull s) hF).1
    have hsub : hull s ⊆ square := hull_mono hs
    rw [Set.inter_eq_right.mpr hsub] at h
    change IsExtreme ℝ square (hull s)
    exact h
  · rintro ⟨s,hs,rfl⟩
    exact D.face_closed square hwhole (hull s) (convex_convexHull ℝ _)
      (faceKey_isExtreme hs)

/-- A cell crossing a diagonal would meet its neighbouring triangle in a
non-face. The midpoint of the two opposite diagonals witnesses the failure. -/
theorem no_crossing_02 (D : VertexSubdivision square)
    (htri : hull (triangle 0) ∈ D.cells) {s : Key} (hs : hull s ∈ D.cells) :
    ¬(0 ∈ s ∧ 2 ∈ s) := by
  rintro ⟨h0,h2⟩
  have hc : center ∈ hull s := by
    rw [center_diag02]
    exact (convex_convexHull ℝ _) ((vertex_mem_hull 0).mpr h0)
      ((vertex_mem_hull 2).mpr h2) (by norm_num) (by norm_num) (by norm_num)
  have hct : center ∈ hull (triangle 0) := by
    rw [center_diag13]
    exact (convex_convexHull ℝ _) ((vertex_mem_hull 1).mpr (by decide))
      ((vertex_mem_hull 3).mpr (by decide)) (by norm_num) (by norm_num) (by norm_num)
  have he := (D.intersection_faces (hull s) hs (hull (triangle 0)) htri).1
  have hp := he.left_mem_of_mem_openSegment ((vertex_mem_hull 0).mpr h0)
    ((vertex_mem_hull 2).mpr h2) ⟨hc,hct⟩
    ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,center_diag02.symm⟩
  have hz := (vertex_mem_hull 0).mp hp.2
  simpa using hz

theorem no_crossing_13 (D : VertexSubdivision square)
    (htri : hull (triangle 1) ∈ D.cells) {s : Key} (hs : hull s ∈ D.cells) :
    ¬(1 ∈ s ∧ 3 ∈ s) := by
  rintro ⟨h1,h3⟩
  have hc : center ∈ hull s := by
    rw [center_diag13]
    exact (convex_convexHull ℝ _) ((vertex_mem_hull 1).mpr h1)
      ((vertex_mem_hull 3).mpr h3) (by norm_num) (by norm_num) (by norm_num)
  have hct : center ∈ hull (triangle 1) := by
    rw [center_diag02]
    exact (convex_convexHull ℝ _) ((vertex_mem_hull 0).mpr (by decide))
      ((vertex_mem_hull 2).mpr (by decide)) (by norm_num) (by norm_num) (by norm_num)
  have he := (D.intersection_faces (hull s) hs (hull (triangle 1)) htri).1
  have hp := he.left_mem_of_mem_openSegment ((vertex_mem_hull 1).mpr h1)
    ((vertex_mem_hull 3).mpr h3) ⟨hc,hct⟩
    ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,center_diag13.symm⟩
  have hz := (vertex_mem_hull 1).mp hp.2
  simpa using hz

theorem no_crossing_02_iff : ∀ s : Key,
    ¬(0 ∈ s ∧ 2 ∈ s) ↔ s ⊆ triangle 0 ∨ s ⊆ triangle 2 := by decide

theorem no_crossing_13_iff : ∀ s : Key,
    ¬(1 ∈ s ∧ 3 ∈ s) ↔ s ⊆ triangle 1 ∨ s ⊆ triangle 3 := by decide

theorem cells_of_split_02 (D : VertexSubdivision square)
    (h0 : hull (triangle 0) ∈ D.cells) (h2 : hull (triangle 2) ∈ D.cells) :
    D.cells = hull '' {s : Key | s ⊆ triangle 0 ∨ s ⊆ triangle 2} := by
  ext F
  constructor
  · intro hF
    obtain ⟨s,hs,rfl⟩ := cell_has_key D hF
    exact ⟨s,(no_crossing_02_iff s).mp (no_crossing_02 D h0 hF),rfl⟩
  · rintro ⟨s,hs,rfl⟩
    rcases hs with hs | hs
    · exact D.face_closed _ h0 _ (convex_convexHull ℝ _)
        (faceKey_isExtreme ⟨hs,Or.inl (triangle_ne_univ 0)⟩)
    · exact D.face_closed _ h2 _ (convex_convexHull ℝ _)
        (faceKey_isExtreme ⟨hs,Or.inl (triangle_ne_univ 2)⟩)

theorem cells_of_split_13 (D : VertexSubdivision square)
    (h1 : hull (triangle 1) ∈ D.cells) (h3 : hull (triangle 3) ∈ D.cells) :
    D.cells = hull '' {s : Key | s ⊆ triangle 1 ∨ s ⊆ triangle 3} := by
  ext F
  constructor
  · intro hF
    obtain ⟨s,hs,rfl⟩ := cell_has_key D hF
    exact ⟨s,(no_crossing_13_iff s).mp (no_crossing_13 D h1 hF),rfl⟩
  · rintro ⟨s,hs,rfl⟩
    rcases hs with hs | hs
    · exact D.face_closed _ h1 _ (convex_convexHull ℝ _)
        (faceKey_isExtreme ⟨hs,Or.inl (triangle_ne_univ 1)⟩)
    · exact D.face_closed _ h3 _ (convex_convexHull ℝ _)
        (faceKey_isExtreme ⟨hs,Or.inl (triangle_ne_univ 3)⟩)

/-- Classification of every actual four-vertex square subdivision. The
converse constructions, and hence the exact cardinality, are separate. -/
theorem square_subdivision_three_forms (D : VertexSubdivision square) :
    D.cells = hull '' {s : Key | FaceKey Finset.univ s} ∨
      D.cells = hull '' {s : Key | s ⊆ triangle 0 ∨ s ⊆ triangle 2} ∨
      D.cells = hull '' {s : Key | s ⊆ triangle 1 ∨ s ⊆ triangle 3} := by
  rcases subdivision_contains_maximal_pattern D with h | ⟨h0,h2⟩ | ⟨h1,h3⟩
  · exact Or.inl (cells_of_whole D h)
  · exact Or.inr (Or.inl (cells_of_split_02 D h0 h2))
  · exact Or.inr (Or.inr (cells_of_split_13 D h1 h3))

#print axioms face_has_key
#print axioms cell_has_key
#print axioms probe_forces_triangle
#print axioms subdivision_contains_maximal_pattern
#print axioms square_subdivision_three_forms

end Unimodular.SquareSubdivision

end

end Enumeration_SquareSubdivisionClassify

/- Exact current draft body: SquareSubdivisionConstruct. -/
section Enumeration_SquareSubdivisionConstruct



/-!
UNVERIFIED EXTENSION DRAFT. Actual inverse constructions for the three square
subdivisions. The final equivalence concerns VertexSubdivision of the genuine
geometric square, not a newly defined type of combinatorial choices.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set
open scoped BigOperators

namespace Unimodular.SquareSubdivision

theorem square_eq_triangle02_union : square = hull (triangle 0) ∪ hull (triangle 2) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨a,ha,hz,hs,hpoint⟩ := mem_hull_iff.mp hx
    have ha0 := ha 0
    have ha1 := ha 1
    have ha2 := ha 2
    have ha3 := ha 3
    rw [weights_sum] at hs
    by_cases hle : a 0 ≤ a 2
    · left
      apply mem_hull_iff.mpr
      refine ⟨![0,a 1 + a 0,a 2 - a 0,a 3 + a 0],?_,?_,?_,?_⟩
      · intro i
        fin_cases i <;> simp <;> linarith
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst i
        simp
      · rw [weights_sum]
        simp
        linarith
      · rw [← hpoint]
        ext j
        fin_cases j <;> simp [Fin.sum_univ_succ,vertex,Finset.sum_apply] <;> ring
    · right
      apply mem_hull_iff.mpr
      refine ⟨![a 0 - a 2,a 1 + a 2,0,a 3 + a 2],?_,?_,?_,?_⟩
      · intro i
        fin_cases i <;> simp <;> linarith
      · intro i hi
        have hi2 : i = 2 := by simpa using hi
        subst i
        simp
      · rw [weights_sum]
        simp
        linarith
      · rw [← hpoint]
        ext j
        fin_cases j <;> simp [Fin.sum_univ_succ,vertex,Finset.sum_apply] <;> ring
  · rintro x (hx | hx)
    · exact hull_mono (Finset.subset_univ _) hx
    · exact hull_mono (Finset.subset_univ _) hx

theorem square_eq_triangle13_union : square = hull (triangle 1) ∪ hull (triangle 3) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨a,ha,hz,hs,hpoint⟩ := mem_hull_iff.mp hx
    have ha0 := ha 0
    have ha1 := ha 1
    have ha2 := ha 2
    have ha3 := ha 3
    rw [weights_sum] at hs
    by_cases hle : a 1 ≤ a 3
    · left
      apply mem_hull_iff.mpr
      refine ⟨![a 0 + a 1,0,a 2 + a 1,a 3 - a 1],?_,?_,?_,?_⟩
      · intro i
        fin_cases i <;> simp <;> linarith
      · intro i hi
        have hi1 : i = 1 := by simpa using hi
        subst i
        simp
      · rw [weights_sum]
        simp
        linarith
      · rw [← hpoint]
        ext j
        fin_cases j <;> simp [Fin.sum_univ_succ,vertex,Finset.sum_apply] <;> ring
    · right
      apply mem_hull_iff.mpr
      refine ⟨![a 0 + a 3,a 1 - a 3,a 2 + a 3,0],?_,?_,?_,?_⟩
      · intro i
        fin_cases i <;> simp <;> linarith
      · intro i hi
        have hi3 : i = 3 := by simpa using hi
        subst i
        simp
      · rw [weights_sum]
        simp
        linarith
      · rw [← hpoint]
        ext j
        fin_cases j <;> simp [Fin.sum_univ_succ,vertex,Finset.sum_apply] <;> ring
  · rintro x (hx | hx)
    · exact hull_mono (Finset.subset_univ _) hx
    · exact hull_mono (Finset.subset_univ _) hx

theorem triangle02_inter :
    hull (triangle 0) ∩ hull (triangle 2) = hull ({1,3} : Key) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx,hy⟩
    obtain ⟨a,ha,haz,has,hap⟩ := mem_hull_iff.mp hx
    obtain ⟨b,hb,hbz,hbs,hbp⟩ := mem_hull_iff.mp hy
    have ha0 : a 0 = 0 := haz 0 (by simp)
    have hb2 : b 2 = 0 := hbz 2 (by simp)
    obtain ⟨haX,haY⟩ := weights_coordinates a
    obtain ⟨hbX,hbY⟩ := weights_coordinates b
    rw [hap] at haX haY
    rw [hbp] at hbX hbY
    rw [weights_sum] at has hbs
    have ha2 : a 2 = 0 := by linarith [ha 2,hb 0]
    apply mem_hull_iff.mpr
    refine ⟨a,ha,?_,?_,hap⟩
    · intro i hi
      fin_cases i <;> simp_all
    · rwa [weights_sum]
  · intro x hx
    exact ⟨hull_mono (by decide) hx,hull_mono (by decide) hx⟩

theorem triangle13_inter :
    hull (triangle 1) ∩ hull (triangle 3) = hull ({0,2} : Key) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx,hy⟩
    obtain ⟨a,ha,haz,has,hap⟩ := mem_hull_iff.mp hx
    obtain ⟨b,hb,hbz,hbs,hbp⟩ := mem_hull_iff.mp hy
    have ha1 : a 1 = 0 := haz 1 (by simp)
    have hb3 : b 3 = 0 := hbz 3 (by simp)
    obtain ⟨haX,haY⟩ := weights_coordinates a
    obtain ⟨hbX,hbY⟩ := weights_coordinates b
    rw [hap] at haX haY
    rw [hbp] at hbX hbY
    rw [weights_sum] at has hbs
    have ha3 : a 3 = 0 := by linarith [ha 3,hb 1]
    apply mem_hull_iff.mpr
    refine ⟨a,ha,?_,?_,hap⟩
    · intro i hi
      fin_cases i <;> simp_all
    · rwa [weights_sum]
  · intro x hx
    exact ⟨hull_mono (by decide) hx,hull_mono (by decide) hx⟩

/-- The common-face condition descends from maximal cells to all their actual
faces. The proof uses the defining open-segment property directly. -/
theorem inherited_common_faces {V : Type*} [AddCommGroup V] [Module ℝ V]
    {A B S T : Set V} (hS : IsExtreme ℝ A S) (hT : IsExtreme ℝ B T)
    (hA : IsExtreme ℝ A (A ∩ B)) (hB : IsExtreme ℝ B (A ∩ B)) :
    IsExtreme ℝ S (S ∩ T) ∧ IsExtreme ℝ T (S ∩ T) := by
  constructor
  · refine ⟨Set.inter_subset_left,?_⟩
    intro x hx y hy z hz hseg
    have hxB := (hA.left_mem_of_mem_openSegment (hS.subset hx) (hS.subset hy)
      ⟨hS.subset hz.1,hT.subset hz.2⟩ hseg).2
    have hyB := (hA.right_mem_of_mem_openSegment (hS.subset hx) (hS.subset hy)
      ⟨hS.subset hz.1,hT.subset hz.2⟩ hseg).2
    exact ⟨hx,hT.left_mem_of_mem_openSegment hxB hyB hz.2 hseg⟩
  · refine ⟨Set.inter_subset_right,?_⟩
    intro x hx y hy z hz hseg
    have hxA := (hB.left_mem_of_mem_openSegment (hT.subset hx) (hT.subset hy)
      ⟨hS.subset hz.1,hT.subset hz.2⟩ hseg).1
    have hyA := (hB.right_mem_of_mem_openSegment (hT.subset hx) (hT.subset hy)
      ⟨hS.subset hz.1,hT.subset hz.2⟩ hseg).1
    exact ⟨hS.left_mem_of_mem_openSegment hxA hyA hz.1 hseg,hx⟩

def maximalKeys : Option Bool → Finset Key
  | none => {Finset.univ}
  | some false => {triangle 0,triangle 2}
  | some true => {triangle 1,triangle 3}

def catalogue (c : Option Bool) : Set Key :=
  {s | ∃ t ∈ maximalKeys c, FaceKey t s}

instance (c : Option Bool) (s : Key) : Decidable (s ∈ catalogue c) := by
  change Decidable (∃ t ∈ maximalKeys c, FaceKey t s)
  infer_instance

theorem faceKey_refl : ∀ s : Key, FaceKey s s := by decide

theorem maximalKeys_cover (c : Option Bool) {x : Plane} (hx : x ∈ square) :
    ∃ s ∈ maximalKeys c, x ∈ hull s := by
  cases c with
  | none => exact ⟨Finset.univ,by simp [maximalKeys],hx⟩
  | some b =>
    cases b
    · rw [square_eq_triangle02_union] at hx
      rcases hx with hx | hx
      · exact ⟨triangle 0,by simp [maximalKeys],hx⟩
      · exact ⟨triangle 2,by simp [maximalKeys],hx⟩
    · rw [square_eq_triangle13_union] at hx
      rcases hx with hx | hx
      · exact ⟨triangle 1,by simp [maximalKeys],hx⟩
      · exact ⟨triangle 3,by simp [maximalKeys],hx⟩

theorem maximalKeys_common_faces (c : Option Bool) {s t : Key}
    (hs : s ∈ maximalKeys c) (ht : t ∈ maximalKeys c) :
    IsExtreme ℝ (hull s) (hull s ∩ hull t) ∧
      IsExtreme ℝ (hull t) (hull s ∩ hull t) := by
  have hrefl (s : Key) :
      IsExtreme ℝ (hull s) (hull s ∩ hull s) ∧
      IsExtreme ℝ (hull s) (hull s ∩ hull s) := by
    simpa only [Set.inter_self] using
      (show IsExtreme ℝ (hull s) (hull s) ∧ IsExtreme ℝ (hull s) (hull s) from
        ⟨IsExtreme.rfl,IsExtreme.rfl⟩)
  have h02 : IsExtreme ℝ (hull (triangle 0))
        (hull (triangle 0) ∩ hull (triangle 2)) ∧
      IsExtreme ℝ (hull (triangle 2))
        (hull (triangle 0) ∩ hull (triangle 2)) := by
    rw [triangle02_inter]
    exact ⟨faceKey_isExtreme (by decide),faceKey_isExtreme (by decide)⟩
  have h13 : IsExtreme ℝ (hull (triangle 1))
        (hull (triangle 1) ∩ hull (triangle 3)) ∧
      IsExtreme ℝ (hull (triangle 3))
        (hull (triangle 1) ∩ hull (triangle 3)) := by
    rw [triangle13_inter]
    exact ⟨faceKey_isExtreme (by decide),faceKey_isExtreme (by decide)⟩
  cases c with
  | none =>
    simp only [maximalKeys,Finset.mem_singleton] at hs ht
    subst s
    subst t
    exact hrefl _
  | some b =>
    cases b
    · simp only [maximalKeys,Finset.mem_insert,Finset.mem_singleton] at hs ht
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
      · exact hrefl _
      · exact h02
      · simpa only [Set.inter_comm] using h02.symm
      · exact hrefl _
    · simp only [maximalKeys,Finset.mem_insert,Finset.mem_singleton] at hs ht
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
      · exact hrefl _
      · exact h13
      · simpa only [Set.inter_comm] using h13.symm
      · exact hrefl _

/-- Each of the three choices constructs an actual finite face-to-face
subdivision using precisely the geometric square's vertices. -/
def canonicalSubdivision (c : Option Bool) : VertexSubdivision square where
  cells := hull '' catalogue c
  finite_cells := (Set.toFinite (catalogue c)).image hull
  vertices := by
    classical
    rintro F ⟨s,hs,rfl⟩
    refine ⟨s.image vertex,?_,?_⟩
    · simp only [hull,Finset.coe_image]
    · rw [square_extremePoints]
      rintro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i,rfl⟩
  cover := by
    apply Set.Subset.antisymm
    · rintro x ⟨F,⟨s,hs,rfl⟩,hx⟩
      exact hull_mono (Finset.subset_univ _) hx
    · intro x hx
      obtain ⟨s,hs,hx⟩ := maximalKeys_cover c hx
      exact ⟨hull s,⟨s,⟨s,hs,faceKey_refl s⟩,rfl⟩,hx⟩
  face_closed := by
    rintro F ⟨s,⟨m,hm,hms⟩,rfl⟩ G hGc hG
    obtain ⟨t,ht,rfl,hst⟩ := face_has_key hGc hG
    refine ⟨t,⟨m,hm,?_⟩,rfl⟩
    exact isExtreme_iff_faceKey.mp
      ((faceKey_isExtreme hms).trans (faceKey_isExtreme hst))
  intersection_faces := by
    rintro F ⟨s,⟨m,hm,hms⟩,rfl⟩ G ⟨t,⟨n,hn,hnt⟩,rfl⟩
    obtain ⟨hM,hN⟩ := maximalKeys_common_faces c hm hn
    exact inherited_common_faces (faceKey_isExtreme hms) (faceKey_isExtreme hnt) hM hN

theorem catalogue_none : catalogue none = {s : Key | FaceKey Finset.univ s} := by
  ext s
  simp [catalogue,maximalKeys]

theorem catalogue_false : catalogue (some false) =
    {s : Key | s ⊆ triangle 0 ∨ s ⊆ triangle 2} := by
  ext s
  simp [catalogue,maximalKeys,FaceKey,triangle_ne_univ]

theorem catalogue_true : catalogue (some true) =
    {s : Key | s ⊆ triangle 1 ∨ s ⊆ triangle 3} := by
  ext s
  simp [catalogue,maximalKeys,FaceKey,triangle_ne_univ]

theorem canonicalSubdivision_surjective : Function.Surjective canonicalSubdivision := by
  intro D
  rcases square_subdivision_three_forms D with h | h | h
  · refine ⟨none,subdivision_ext ?_⟩
    change hull '' catalogue none = D.cells
    rw [catalogue_none]
    exact h.symm
  · refine ⟨some false,subdivision_ext ?_⟩
    change hull '' catalogue (some false) = D.cells
    rw [catalogue_false]
    exact h.symm
  · refine ⟨some true,subdivision_ext ?_⟩
    change hull '' catalogue (some true) = D.cells
    rw [catalogue_true]
    exact h.symm

@[simp] theorem hull_mem_canonical (c : Option Bool) (s : Key) :
    hull s ∈ (canonicalSubdivision c).cells ↔ s ∈ catalogue c := by
  constructor
  · rintro ⟨t,ht,h⟩
    have he : t = s := hull_injective h
    simpa only [he] using ht
  · intro hs
    exact ⟨s,hs,rfl⟩

theorem catalogue_distinct : ∀ c d : Option Bool,
    (∀ s : Key, s ∈ catalogue c ↔ s ∈ catalogue d) → c = d := by decide

theorem canonicalSubdivision_injective : Function.Injective canonicalSubdivision := by
  intro c d h
  apply catalogue_distinct c d
  intro s
  rw [← hull_mem_canonical c s,← hull_mem_canonical d s,h]

/-- The full geometric classification, with both inverse laws. -/
def squareSubdivisionEquiv : VertexSubdivision square ≃ Option Bool :=
  (Equiv.ofBijective canonicalSubdivision
    ⟨canonicalSubdivision_injective,canonicalSubdivision_surjective⟩).symm

theorem square_subdivision_card : Nat.card (VertexSubdivision square) = 3 := by
  rw [Nat.card_congr squareSubdivisionEquiv]
  simp [Nat.card_eq_fintype_card]

#print axioms square_eq_triangle02_union
#print axioms triangle02_inter
#print axioms inherited_common_faces
#print axioms canonicalSubdivision
#print axioms squareSubdivisionEquiv
#print axioms square_subdivision_card

end Unimodular.SquareSubdivision

end

end Enumeration_SquareSubdivisionConstruct

/- Exact current draft body: TriangleSubdivision. -/
section Enumeration_TriangleSubdivision



/-!
UNVERIFIED EXTENSION DRAFT. Uniqueness of a subdivision of an actual triangle
using only its original vertices. This is the fixed-triangular-facet part of
Section 7.1, prior to transport to the actual type-A cut facets.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set
open scoped BigOperators

namespace Unimodular.SquareSubdivision

theorem hull_extremePoints (s : Key) :
    (hull s).extremePoints ℝ = vertex '' (s : Set (Fin 4)) := by
  apply Set.Subset.antisymm
  · exact extremePoints_convexHull_subset
  · rintro x ⟨i,hi,rfl⟩
    apply inter_extremePoints_subset_extremePoints_of_subset
      (hull_mono (Finset.subset_univ s))
    refine ⟨(vertex_mem_hull i).mpr hi,?_⟩
    change vertex i ∈ square.extremePoints ℝ
    rw [square_extremePoints]
    exact ⟨i,rfl⟩

/-- The unsplit face complex of any square-vertex polytope is an actual
VertexSubdivision, including all proper and empty faces. -/
def trivialSubdivision (r : Key) : VertexSubdivision (hull r) where
  cells := hull '' {s : Key | FaceKey r s}
  finite_cells := (Set.toFinite _).image hull
  vertices := by
    classical
    rintro F ⟨s,hs,rfl⟩
    refine ⟨s.image vertex,?_,?_⟩
    · simp only [hull,Finset.coe_image]
    · rw [hull_extremePoints]
      rintro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i,hs.1 hi,rfl⟩
  cover := by
    apply Set.Subset.antisymm
    · rintro x ⟨F,⟨s,hs,rfl⟩,hx⟩
      exact hull_mono hs.1 hx
    · intro x hx
      exact ⟨hull r,⟨r,faceKey_refl r,rfl⟩,hx⟩
  face_closed := by
    rintro F ⟨s,hs,rfl⟩ G hGc hG
    obtain ⟨t,ht,rfl,hst⟩ := face_has_key hGc hG
    refine ⟨t,?_,rfl⟩
    exact isExtreme_iff_faceKey.mp
      ((faceKey_isExtreme hs).trans (faceKey_isExtreme hst))
  intersection_faces := by
    rintro F ⟨s,hs,rfl⟩ G ⟨t,ht,rfl⟩
    have hcommon : IsExtreme ℝ (hull r) (hull r ∩ hull r) := by
      simpa only [Set.inter_self] using (IsExtreme.refl ℝ (hull r))
    exact inherited_common_faces (faceKey_isExtreme hs) (faceKey_isExtreme ht)
      hcommon hcommon

theorem subdivision_eq_trivial_of_whole {r : Key} (D : VertexSubdivision (hull r))
    (hwhole : hull r ∈ D.cells) : D = trivialSubdivision r := by
  apply subdivision_ext
  ext F
  constructor
  · intro hF
    obtain ⟨s,hs,rfl⟩ := cell_has_key D hF
    refine ⟨s,?_,rfl⟩
    apply isExtreme_iff_faceKey.mp
    have h := (D.intersection_faces (hull r) hwhole (hull s) hF).1
    simpa only [Set.inter_eq_right.mpr (hull_mono hs)] using h
  · rintro ⟨s,hs,rfl⟩
    exact D.face_closed (hull r) hwhole (hull s) (convex_convexHull ℝ _)
      (faceKey_isExtreme hs)

def triangleBarycenter (i : Fin 4) : Plane :=
  ∑ j : Fin 4, (if j = i then 0 else (1/3 : ℝ)) • vertex j

theorem triangleBarycenter_mem (i : Fin 4) :
    triangleBarycenter i ∈ hull (triangle i) := by
  apply mem_hull_iff.mpr
  refine ⟨fun j => if j = i then 0 else (1/3 : ℝ),?_,?_,?_,rfl⟩
  · intro j
    change 0 ≤ if j = i then 0 else (1/3 : ℝ)
    split_ifs <;> norm_num
  · intro j hj
    have hji : j = i := by simpa using hj
    simp [hji]
  · fin_cases i <;> norm_num [Fin.sum_univ_succ]

/-- A point with three strictly positive barycentric coordinates cannot lie
in the hull of a proper subset of the triangle's three original vertices. -/
theorem triangleBarycenter_forces_full (i : Fin 4) {s : Key}
    (hs : s ⊆ triangle i) (hx : triangleBarycenter i ∈ hull s) : s = triangle i := by
  apply Finset.Subset.antisymm hs
  intro j hj
  obtain ⟨a,ha,hz,has,hap⟩ := mem_hull_iff.mp hx
  have hni : i ∉ s := fun hi => by simpa using hs hi
  have hai := hz i hni
  have hji : j ≠ i := (mem_triangle i j).mp hj
  by_contra hnj
  have haj := hz j hnj
  obtain ⟨haX,haY⟩ := weights_coordinates a
  rw [hap] at haX haY
  rw [weights_sum] at has
  fin_cases i <;> fin_cases j <;>
    norm_num [triangleBarycenter,Fin.sum_univ_succ,vertex,Finset.sum_apply] at hai haj haX haY hji <;>
      linarith

/-- Every actual triangle subdivision is its unsplit face complex. -/
theorem triangle_subdivision_unique (i : Fin 4)
    (D : VertexSubdivision (hull (triangle i))) : D = trivialSubdivision (triangle i) := by
  apply subdivision_eq_trivial_of_whole D
  have hx := triangleBarycenter_mem i
  rw [← D.cover] at hx
  obtain ⟨F,hF,hx⟩ := hx
  obtain ⟨s,hs,heq⟩ := cell_has_key D hF
  rw [heq] at hx hF
  have he := triangleBarycenter_forces_full i hs hx
  simpa only [he] using hF

def triangleSubdivisionEquiv (i : Fin 4) :
    VertexSubdivision (hull (triangle i)) ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := trivialSubdivision (triangle i)
  left_inv D := (triangle_subdivision_unique i D).symm
  right_inv u := by cases u; rfl

theorem triangle_subdivision_card (i : Fin 4) :
    Nat.card (VertexSubdivision (hull (triangle i))) = 1 := by
  rw [Nat.card_congr (triangleSubdivisionEquiv i)]
  simp [Nat.card_eq_fintype_card]

#print axioms hull_extremePoints
#print axioms trivialSubdivision
#print axioms triangleBarycenter_forces_full
#print axioms triangle_subdivision_unique
#print axioms triangleSubdivisionEquiv

end Unimodular.SquareSubdivision

end

end Enumeration_TriangleSubdivision

/- Exact current draft body: SubdivisionTransport. -/
section Enumeration_SubdivisionTransport



/-!
UNVERIFIED EXTENSION DRAFT. Actual geometric subdivision transport along an
injective affine map, including maps into a higher-dimensional ambient space.
This is needed to carry the planar square/triangle classifications to the
actual type-A facets. There is no fan or subdivision-equivalence assumption.
-/

set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set

namespace Unimodular.VertexSubdivisionTransport

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- Injective affine maps preserve actual convex extreme subsets. -/
theorem affine_image_isExtreme (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {A F : Set V} (h : IsExtreme ℝ A F) : IsExtreme ℝ (f '' A) (f '' F) := by
  refine ⟨Set.image_mono h.subset,?_⟩
  rintro x ⟨u,hu,rfl⟩ y ⟨v,hv,rfl⟩ z ⟨w,hw,rfl⟩ hseg
  have hseg' : f w ∈ f '' openSegment ℝ u v := by
    rw [image_openSegment ℝ f u v]
    exact hseg
  obtain ⟨q,hq,heq⟩ := hseg'
  have he : q = w := hf heq
  subst q
  exact ⟨u,h.left_mem_of_mem_openSegment hu hv hw hq,rfl⟩

/-- Pulling back an extreme subset along any affine map preserves extremity. -/
theorem affine_preimage_isExtreme (f : V →ᵃ[ℝ] W)
    {A F : Set W} (h : IsExtreme ℝ A F) :
    IsExtreme ℝ (f ⁻¹' A) (f ⁻¹' F) := by
  refine ⟨fun _ hx => h.subset hx,?_⟩
  intro x hx y hy z hz hseg
  apply h.left_mem_of_mem_openSegment hx hy hz
  rw [← image_openSegment ℝ f x y]
  exact ⟨z,hseg,rfl⟩

/-- The extreme-point equality is proved for affine embeddings, so a planar
facet model need not be an equivalence of its surrounding vector spaces. -/
theorem affine_image_extremePoints (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    (P : Set V) : f '' P.extremePoints ℝ = (f '' P).extremePoints ℝ := by
  apply Set.Subset.antisymm
  · rintro x ⟨u,hu,rfl⟩
    refine ⟨⟨u,hu.1,rfl⟩,?_⟩
    rintro y ⟨v,hv,rfl⟩ z ⟨w,hw,rfl⟩ hseg
    have hseg' : f u ∈ f '' openSegment ℝ v w := by
      rw [image_openSegment ℝ f v w]
      exact hseg
    obtain ⟨q,hq,heq⟩ := hseg'
    have he : q = u := hf heq
    subst q
    exact congrArg f (hu.2 hv hw hq)
  · intro x hx
    obtain ⟨u,hu,rfl⟩ := hx.1
    refine ⟨u,⟨hu,?_⟩,rfl⟩
    intro v hv w hw hseg
    apply hf
    apply hx.2 ⟨v,hv,rfl⟩ ⟨w,hw,rfl⟩
    rw [← image_openSegment ℝ f v w]
    exact ⟨u,hseg,rfl⟩

theorem subdivision_extensionality {P : Set V} {D E : VertexSubdivision P}
    (h : D.cells = E.cells) : D = E := by
  cases D
  cases E
  cases h
  rfl

/-- Push forward all actual cells and all actual faces. -/
def map (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {P : Set V} (D : VertexSubdivision P) : VertexSubdivision (f '' P) where
  cells := (fun F => f '' F) '' D.cells
  finite_cells := D.finite_cells.image _
  vertices := by
    classical
    rintro F ⟨G,hG,rfl⟩
    obtain ⟨s,hs,hsp⟩ := D.vertices G hG
    refine ⟨s.image f,?_,?_⟩
    · change f '' G = convexHull ℝ (↑(s.image f) : Set W)
      rw [hs,f.image_convexHull]
      simp only [Finset.coe_image]
    · rw [← affine_image_extremePoints f hf P]
      rintro x hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact ⟨y,hsp hy,rfl⟩
  cover := by
    ext x
    constructor
    · rintro ⟨F,⟨G,hG,rfl⟩,⟨y,hy,rfl⟩⟩
      exact ⟨y,D.cell_subset hG hy,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      rw [← D.cover] at hy
      obtain ⟨G,hG,hy⟩ := hy
      exact ⟨f '' G,⟨G,hG,rfl⟩,⟨y,hy,rfl⟩⟩
  face_closed := by
    rintro F ⟨G,hG,rfl⟩ H hHc hH
    have hpre : IsExtreme ℝ G (f ⁻¹' H) := by
      have h := affine_preimage_isExtreme f hH
      rwa [Set.preimage_image_eq G hf] at h
    have hcell : f ⁻¹' H ∈ D.cells :=
      D.face_closed G hG (f ⁻¹' H) (hHc.affine_preimage f) hpre
    refine ⟨f ⁻¹' H,hcell,?_⟩
    apply Set.image_preimage_eq_iff.mpr
    exact hH.subset.trans (Set.image_subset_range f G)
  intersection_faces := by
    rintro F ⟨A,hA,rfl⟩ G ⟨B,hB,rfl⟩
    rw [← Set.image_inter hf]
    exact ⟨affine_image_isExtreme f hf (D.intersection_faces A hA B hB).1,
      affine_image_isExtreme f hf (D.intersection_faces A hA B hB).2⟩

/-- Pull back all cells. Their finite vertex sets are derived from finite
preimages; no chosen inverse map or ambient surjectivity is assumed. -/
def pullback (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {P : Set V} (D : VertexSubdivision (f '' P)) : VertexSubdivision P where
  cells := (fun F => f ⁻¹' F) '' D.cells
  finite_cells := D.finite_cells.image _
  vertices := by
    classical
    rintro F ⟨G,hG,rfl⟩
    obtain ⟨t,ht,htP⟩ := D.vertices G hG
    have hpre : (f ⁻¹' (t : Set W)).Finite :=
      Set.Finite.preimage (fun _ _ _ _ h => hf h) t.finite_toSet
    let s := hpre.toFinset
    have hs : (s : Set V) = f ⁻¹' (t : Set W) := hpre.coe_toFinset
    have htrange : (t : Set W) ⊆ Set.range f :=
      fun x hx => Set.image_subset_range f P (htP hx).1
    have himage : f '' (s : Set V) = (t : Set W) := by
      rw [hs]
      exact Set.image_preimage_eq_iff.mpr htrange
    have hhull : f '' convexHull ℝ (s : Set V) = convexHull ℝ (t : Set W) := by
      rw [f.image_convexHull,himage]
    refine ⟨s,?_,?_⟩
    · change f ⁻¹' G = convexHull ℝ (s : Set V)
      rw [ht,← hhull,Set.preimage_image_eq _ hf]
    · intro x hx
      have hxt : x ∈ f ⁻¹' (t : Set W) := by
        rw [← hs]
        exact hx
      have hx' : f x ∈ (f '' P).extremePoints ℝ := htP hxt
      rw [← affine_image_extremePoints f hf P] at hx'
      obtain ⟨y,hy,he⟩ := hx'
      have hyx : y = x := hf he
      simpa only [hyx] using hy
  cover := by
    ext x
    constructor
    · rintro ⟨F,⟨G,hG,rfl⟩,hx⟩
      have hxp : f x ∈ f '' P := D.cell_subset hG hx
      obtain ⟨y,hy,he⟩ := hxp
      have hyx : y = x := hf he
      simpa only [hyx] using hy
    · intro hx
      have hfx : f x ∈ f '' P := ⟨x,hx,rfl⟩
      rw [← D.cover] at hfx
      obtain ⟨G,hG,hx⟩ := hfx
      exact ⟨f ⁻¹' G,⟨G,hG,rfl⟩,hx⟩
  face_closed := by
    rintro F ⟨G,hG,rfl⟩ H hHc hH
    have hGrange : G ⊆ Set.range f :=
      (D.cell_subset hG).trans (Set.image_subset_range f P)
    have himage : f '' (f ⁻¹' G) = G := Set.image_preimage_eq_iff.mpr hGrange
    have hface : IsExtreme ℝ G (f '' H) := by
      have h := affine_image_isExtreme f hf hH
      rwa [himage] at h
    have hcell : f '' H ∈ D.cells :=
      D.face_closed G hG (f '' H) (hHc.affine_image f) hface
    exact ⟨f '' H,hcell,Set.preimage_image_eq H hf⟩
  intersection_faces := by
    rintro F ⟨A,hA,rfl⟩ G ⟨B,hB,rfl⟩
    exact ⟨affine_preimage_isExtreme f (D.intersection_faces A hA B hB).1,
      affine_preimage_isExtreme f (D.intersection_faces A hA B hB).2⟩

theorem pullback_map (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {P : Set V} (D : VertexSubdivision P) : pullback f hf (map f hf D) = D := by
  apply subdivision_extensionality
  ext F
  constructor
  · rintro ⟨G,⟨H,hH,rfl⟩,hF⟩
    change f ⁻¹' (f '' H) = F at hF
    rw [Set.preimage_image_eq H hf] at hF
    simpa only [hF] using hH
  · intro hF
    exact ⟨f '' F,⟨F,hF,rfl⟩,Set.preimage_image_eq F hf⟩

theorem map_pullback (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {P : Set V} (D : VertexSubdivision (f '' P)) : map f hf (pullback f hf D) = D := by
  apply subdivision_extensionality
  ext F
  constructor
  · rintro ⟨G,⟨H,hH,rfl⟩,hF⟩
    change f '' (f ⁻¹' H) = F at hF
    have he : f '' (f ⁻¹' H) = H := Set.image_preimage_eq_iff.mpr
      ((D.cell_subset hH).trans (Set.image_subset_range f P))
    rw [he] at hF
    simpa only [hF] using hH
  · intro hF
    refine ⟨f ⁻¹' F,⟨F,hF,rfl⟩,?_⟩
    exact Set.image_preimage_eq_iff.mpr
      ((D.cell_subset hF).trans (Set.image_subset_range f P))

/-- Exact geometric equivalence of subdivision spaces under an affine
embedding, with every original vertex, face and intersection retained. -/
def affineEmbeddingEquiv (f : V →ᵃ[ℝ] W) (hf : Function.Injective f) (P : Set V) :
    VertexSubdivision P ≃ VertexSubdivision (f '' P) where
  toFun := map f hf
  invFun := pullback f hf
  left_inv := pullback_map f hf
  right_inv := map_pullback f hf

#print axioms affine_image_isExtreme
#print axioms affine_image_extremePoints
#print axioms map
#print axioms pullback
#print axioms affineEmbeddingEquiv

end Unimodular.VertexSubdivisionTransport

end

end Enumeration_SubdivisionTransport

/- Exact current draft body: A3FacetCharts. -/
section Enumeration_A3FacetCharts



/-!
UNVERIFIED EXTENSION DRAFT. Explicit affine embeddings of the ordinary square
and triangle onto the actual exposed A3 cut facets. The equations identify
actual convex hulls and preserve all cells, vertices, and faces. The resulting
subdivision equivalences make no assumption about the form of a subdivision.
-/

set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set

namespace Unimodular.A3FacetCharts

open TypeAFanGeometry SquareSubdivision VertexSubdivisionTransport

abbrev Labels := Fin 4 ≃ Vertex 3

/-- Injectivity of the genuine zero-sum-coordinate embedding. -/
theorem augmented_injective (n : ℕ) : Function.Injective (augmented n) := by
  intro x y h
  funext i
  exact congrFun h (some i)

def planeLinear (u v : Ambient 3) : Plane →ₗ[ℝ] Ambient 3 where
  toFun x := x 0 • u + x 1 • v
  map_add' x y := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' a x := by simp [Pi.smul_apply, smul_eq_mul, smul_add, mul_smul]

def squareCut (e : Labels) : Finset (Vertex 3) := {e 0, e 1}
def singletonCut (e : Labels) : Finset (Vertex 3) := {e 0}
def tripleCut (e : Labels) : Finset (Vertex 3) := {e 0, e 1, e 2}

/-- The four corners are the roots ac, bc, bd, ad, in that order. -/
def squareChart (e : Labels) : Plane →ᵃ[ℝ] Ambient 3 where
  toFun x := realRoot (e 0) (e 2) + x 0 • realRoot (e 1) (e 0) +
    x 1 • realRoot (e 2) (e 3)
  linear := planeLinear (realRoot (e 1) (e 0)) (realRoot (e 2) (e 3))
  map_vadd' p v := by
    dsimp [planeLinear]
    simp only [vadd_eq_add, Pi.add_apply, add_smul]
    abel

/-- The triangle with corners (0,0), (1,0), (0,1) maps to ab, ac, ad. -/
def singletonChart (e : Labels) : Plane →ᵃ[ℝ] Ambient 3 where
  toFun x := realRoot (e 0) (e 1) + x 0 • realRoot (e 1) (e 2) +
    x 1 • realRoot (e 1) (e 3)
  linear := planeLinear (realRoot (e 1) (e 2)) (realRoot (e 1) (e 3))
  map_vadd' p v := by
    dsimp [planeLinear]
    simp only [vadd_eq_add, Pi.add_apply, add_smul]
    abel

/-- The same triangle maps to ad, bd, cd for a three-element source cut. -/
def tripleChart (e : Labels) : Plane →ᵃ[ℝ] Ambient 3 where
  toFun x := realRoot (e 0) (e 3) + x 0 • realRoot (e 1) (e 0) +
    x 1 • realRoot (e 2) (e 0)
  linear := planeLinear (realRoot (e 1) (e 0)) (realRoot (e 2) (e 0))
  map_vadd' p v := by
    dsimp [planeLinear]
    simp only [vadd_eq_add, Pi.add_apply, add_smul]
    abel

@[simp] theorem augmented_squareChart (e : Labels) (x : Plane) (i : Fin 4) :
    augmented 3 (squareChart e x) (e i) = ![1-x 0,x 0,x 1-1,-x 1] i := by
  fin_cases i <;>
    simp [squareChart, map_add, map_smul, Pi.single_apply, e.injective.eq_iff] <;> ring

@[simp] theorem augmented_singletonChart (e : Labels) (x : Plane) (i : Fin 4) :
    augmented 3 (singletonChart e x) (e i) = ![1,x 0+x 1-1,-x 0,-x 1] i := by
  fin_cases i <;>
    simp [singletonChart, map_add, map_smul, Pi.single_apply, e.injective.eq_iff] <;> ring

@[simp] theorem augmented_tripleChart (e : Labels) (x : Plane) (i : Fin 4) :
    augmented 3 (tripleChart e x) (e i) = ![1-x 0-x 1,x 0,x 1,-1] i := by
  fin_cases i <;>
    simp [tripleChart, map_add, map_smul, Pi.single_apply, e.injective.eq_iff] <;> ring

theorem squareChart_injective (e : Labels) : Function.Injective (squareChart e) := by
  intro x y h
  have h0 := congrArg (fun z => augmented 3 z (e 1)) h
  have h1 := congrArg (fun z => augmented 3 z (e 3)) h
  simp only [augmented_squareChart] at h0 h1
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1

theorem singletonChart_injective (e : Labels) : Function.Injective (singletonChart e) := by
  intro x y h
  have h0 := congrArg (fun z => augmented 3 z (e 2)) h
  have h1 := congrArg (fun z => augmented 3 z (e 3)) h
  simp only [augmented_singletonChart] at h0 h1
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1

theorem tripleChart_injective (e : Labels) : Function.Injective (tripleChart e) := by
  intro x y h
  have h0 := congrArg (fun z => augmented 3 z (e 1)) h
  have h1 := congrArg (fun z => augmented 3 z (e 2)) h
  simp only [augmented_tripleChart] at h0 h1
  funext i
  fin_cases i <;> first | simpa using h0 | simpa using h1

def squarePairs : Fin 4 → Fin 4 × Fin 4 := ![(0,2),(1,2),(1,3),(0,3)]
def singletonTargets : Fin 4 → Fin 4 := ![1,2,1,3]
def tripleSources : Fin 4 → Fin 4 := ![0,1,0,2]

theorem squareChart_vertex (e : Labels) (i : Fin 4) :
    squareChart e (vertex i) =
      realRoot (e (squarePairs i).1) (e (squarePairs i).2) := by
  apply augmented_injective 3
  funext p
  obtain ⟨j,rfl⟩ := e.surjective p
  fin_cases i <;> fin_cases j <;>
    simp [augmented_squareChart, vertex, squarePairs, Pi.single_apply, e.injective.eq_iff]

theorem singletonChart_vertex (e : Labels) (i : Fin 4) (hi : i ∈ triangle 2) :
    singletonChart e (vertex i) = realRoot (e 0) (e (singletonTargets i)) := by
  apply augmented_injective 3
  funext p
  obtain ⟨j,rfl⟩ := e.surjective p
  fin_cases i <;> fin_cases j <;>
    simp_all [triangle, augmented_singletonChart, vertex, singletonTargets,
      Pi.single_apply, e.injective.eq_iff]

theorem tripleChart_vertex (e : Labels) (i : Fin 4) (hi : i ∈ triangle 2) :
    tripleChart e (vertex i) = realRoot (e (tripleSources i)) (e 3) := by
  apply augmented_injective 3
  funext p
  obtain ⟨j,rfl⟩ := e.surjective p
  fin_cases i <;> fin_cases j <;>
    simp_all [triangle, augmented_tripleChart, vertex, tripleSources,
      Pi.single_apply, e.injective.eq_iff]

theorem squareChart_vertices (e : Labels) :
    squareChart e '' Set.range vertex = embed '' cutRoots (squareCut e) := by
  ext x
  constructor
  · rintro ⟨p,⟨i,rfl⟩,rfl⟩
    rw [squareChart_vertex]
    refine ⟨latticeRoot (e (squarePairs i).1) (e (squarePairs i).2),
      ⟨e (squarePairs i).1,?_,e (squarePairs i).2,?_,rfl⟩,rfl⟩
    all_goals fin_cases i <;> simp [squarePairs,squareCut,e.injective.eq_iff]
  · rintro ⟨u,⟨p,hp,q,hq,rfl⟩,rfl⟩
    obtain ⟨i,rfl⟩ := e.surjective p
    obtain ⟨j,rfl⟩ := e.surjective q
    fin_cases i <;> fin_cases j <;>
      norm_num [squareCut,e.injective.eq_iff] at hp <;>
      norm_num [squareCut,e.injective.eq_iff] at hq
    all_goals first
      | exact ⟨vertex 0,⟨0,rfl⟩,squareChart_vertex e 0⟩
      | exact ⟨vertex 1,⟨1,rfl⟩,squareChart_vertex e 1⟩
      | exact ⟨vertex 2,⟨2,rfl⟩,squareChart_vertex e 2⟩
      | exact ⟨vertex 3,⟨3,rfl⟩,squareChart_vertex e 3⟩

theorem singletonChart_vertices (e : Labels) :
    singletonChart e '' (vertex '' (triangle 2 : Set (Fin 4))) =
      embed '' cutRoots (singletonCut e) := by
  ext x
  constructor
  · rintro ⟨p,⟨i,hi,rfl⟩,rfl⟩
    rw [singletonChart_vertex e i hi]
    refine ⟨latticeRoot (e 0) (e (singletonTargets i)),
      ⟨e 0,?_,e (singletonTargets i),?_,rfl⟩,rfl⟩
    · simp [singletonCut]
    · fin_cases i <;> simp_all [triangle,singletonTargets,singletonCut,e.injective.eq_iff]
  · rintro ⟨u,⟨p,hp,q,hq,rfl⟩,rfl⟩
    obtain ⟨i,rfl⟩ := e.surjective p
    obtain ⟨j,rfl⟩ := e.surjective q
    fin_cases i <;> fin_cases j <;>
      norm_num [singletonCut,e.injective.eq_iff] at hp <;>
      norm_num [singletonCut,e.injective.eq_iff] at hq
    all_goals first
      | exact ⟨vertex 0,⟨0,by decide,rfl⟩,singletonChart_vertex e 0 (by decide)⟩
      | exact ⟨vertex 1,⟨1,by decide,rfl⟩,singletonChart_vertex e 1 (by decide)⟩
      | exact ⟨vertex 3,⟨3,by decide,rfl⟩,singletonChart_vertex e 3 (by decide)⟩

theorem tripleChart_vertices (e : Labels) :
    tripleChart e '' (vertex '' (triangle 2 : Set (Fin 4))) =
      embed '' cutRoots (tripleCut e) := by
  ext x
  constructor
  · rintro ⟨p,⟨i,hi,rfl⟩,rfl⟩
    rw [tripleChart_vertex e i hi]
    refine ⟨latticeRoot (e (tripleSources i)) (e 3),
      ⟨e (tripleSources i),?_,e 3,?_,rfl⟩,rfl⟩
    · fin_cases i <;> simp_all [triangle,tripleSources,tripleCut,e.injective.eq_iff]
    · simp [tripleCut,e.injective.eq_iff]
  · rintro ⟨u,⟨p,hp,q,hq,rfl⟩,rfl⟩
    obtain ⟨i,rfl⟩ := e.surjective p
    obtain ⟨j,rfl⟩ := e.surjective q
    fin_cases i <;> fin_cases j <;>
      norm_num [tripleCut,e.injective.eq_iff] at hp <;>
      norm_num [tripleCut,e.injective.eq_iff] at hq
    all_goals first
      | exact ⟨vertex 0,⟨0,by decide,rfl⟩,tripleChart_vertex e 0 (by decide)⟩
      | exact ⟨vertex 1,⟨1,by decide,rfl⟩,tripleChart_vertex e 1 (by decide)⟩
      | exact ⟨vertex 3,⟨3,by decide,rfl⟩,tripleChart_vertex e 3 (by decide)⟩

/-- The affine square model is exactly the actual exposed four-root facet. -/
theorem squareChart_image (e : Labels) :
    squareChart e '' square = cutFace (squareCut e) := by
  rw [square,hull,(squareChart e).image_convexHull,cutFace_eq_convexHull]
  congr 1
  simpa only [Finset.coe_univ,Set.image_univ] using squareChart_vertices e

theorem singletonChart_image (e : Labels) :
    singletonChart e '' hull (triangle 2) = cutFace (singletonCut e) := by
  rw [hull,(singletonChart e).image_convexHull,cutFace_eq_convexHull,
    singletonChart_vertices]

theorem tripleChart_image (e : Labels) :
    tripleChart e '' hull (triangle 2) = cutFace (tripleCut e) := by
  rw [hull,(tripleChart e).image_convexHull,cutFace_eq_convexHull,tripleChart_vertices]

/-- Every actual vertex subdivision of this actual A3 square facet is one
of exactly three subdivisions, with no extra finiteness or shape hypothesis. -/
def squareFacetSubdivisionEquiv (e : Labels) :
    VertexSubdivision (cutFace (squareCut e)) ≃ Option Bool :=
  (Equiv.cast (congrArg (fun P : Set (Ambient 3) => VertexSubdivision P)
    (squareChart_image e).symm)).trans
    ((affineEmbeddingEquiv (squareChart e) (squareChart_injective e) square).symm.trans
      squareSubdivisionEquiv)

def singletonFacetSubdivisionEquiv (e : Labels) :
    VertexSubdivision (cutFace (singletonCut e)) ≃ PUnit.{1} :=
  (Equiv.cast (congrArg (fun P : Set (Ambient 3) => VertexSubdivision P)
    (singletonChart_image e).symm)).trans
    ((affineEmbeddingEquiv (singletonChart e) (singletonChart_injective e)
      (hull (triangle 2))).symm.trans (triangleSubdivisionEquiv 2))

def tripleFacetSubdivisionEquiv (e : Labels) :
    VertexSubdivision (cutFace (tripleCut e)) ≃ PUnit.{1} :=
  (Equiv.cast (congrArg (fun P : Set (Ambient 3) => VertexSubdivision P)
    (tripleChart_image e).symm)).trans
    ((affineEmbeddingEquiv (tripleChart e) (tripleChart_injective e)
      (hull (triangle 2))).symm.trans (triangleSubdivisionEquiv 2))

#print axioms squareChart_image
#print axioms singletonChart_image
#print axioms tripleChart_image
#print axioms squareFacetSubdivisionEquiv
#print axioms singletonFacetSubdivisionEquiv
#print axioms tripleFacetSubdivisionEquiv

end Unimodular.A3FacetCharts
end

end Enumeration_A3FacetCharts

/- Exact current draft body: SubdivisionBoundary. -/
section Enumeration_SubdivisionBoundary



/-!
UNVERIFIED EXTENSION DRAFT. A square or triangle cannot have its ordinary
boundary subdivided using only its original vertices. The statement is about
all actual convex faces and all actual cells. It includes the empty face,
whose restriction is the singleton family containing the empty cell.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set

namespace Unimodular.SubdivisionBoundary

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- The full family of ordinary convex faces, including the empty face. -/
def faceFamily (F : Set V) : Set (Set V) := {G | Convex ℝ G ∧ IsExtreme ℝ F G}

/-- Every vertex subdivision induces the unsplit face complex on each proper
convex face. This property does not restrict the interior subdivision. -/
def BoundaryRigid (P : Set V) : Prop :=
  ∀ (D : VertexSubdivision P) (F : Set V), Convex ℝ F → IsExtreme ℝ P F →
    F ≠ P → (fun G => G ∩ F) '' D.cells = faceFamily F

/-- Intersecting with a face remains a face of every subset of the parent. -/
theorem extreme_inter_of_subset {P F C : Set V}
    (hF : IsExtreme ℝ P F) (hC : C ⊆ P) : IsExtreme ℝ C (C ∩ F) := by
  refine ⟨Set.inter_subset_left,?_⟩
  intro x hx y hy z hz hseg
  exact ⟨hx,hF.left_mem_of_mem_openSegment (hC hx) (hC hy) hz.2 hseg⟩

open SquareSubdivision

/-- Intersections with genuine original faces retain precisely the original
vertices lying in the intersection; no geometric intersection oracle is used. -/
theorem hull_inter_face {r s t : Key} (hs : s ⊆ r) (ht : FaceKey r t) :
    hull s ∩ hull t = hull (s ∩ t) := by
  have he : IsExtreme ℝ (hull s) (hull s ∩ hull t) :=
    extreme_inter_of_subset (faceKey_isExtreme ht) (hull_mono hs)
  rw [face_eq_convexHull_inter (vertex '' (s : Set (Fin 4))) (hull s ∩ hull t)
    ((convex_convexHull ℝ _).inter (convex_convexHull ℝ _)) he]
  change convexHull ℝ _ = convexHull ℝ _
  congr 1
  ext x
  constructor
  · rintro ⟨⟨i,hi,rfl⟩,hsi,hti⟩
    exact ⟨i,Finset.mem_inter.mpr ⟨hi,(vertex_mem_hull i).mp hti⟩,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    obtain ⟨his,hit⟩ := Finset.mem_inter.mp hi
    exact ⟨⟨i,his,rfl⟩,(vertex_mem_hull i).mpr his,(vertex_mem_hull i).mpr hit⟩

theorem faceFamily_hull (s : Key) :
    faceFamily (hull s) = hull '' {t : Key | FaceKey s t} := by
  ext F
  constructor
  · rintro ⟨hFc,hF⟩
    obtain ⟨t,ht,rfl,htf⟩ := face_has_key hFc hF
    exact ⟨t,htf,rfl⟩
  · rintro ⟨t,ht,rfl⟩
    exact ⟨convex_convexHull ℝ _,faceKey_isExtreme ht⟩

/-- Finite bookkeeping only, after the actual geometric face classification. -/
theorem boundary_faces_in_catalogue : ∀ (c : Option Bool) (t s : Key),
    FaceKey Finset.univ t → t ≠ Finset.univ → FaceKey t s → s ∈ catalogue c := by
  decide

theorem canonical_boundary_restriction (c : Option Bool) {t : Key}
    (ht : FaceKey Finset.univ t) (htn : t ≠ Finset.univ) :
    (fun G => G ∩ hull t) '' (canonicalSubdivision c).cells = faceFamily (hull t) := by
  rw [faceFamily_hull]
  ext F
  constructor
  · rintro ⟨G,⟨s,hs,rfl⟩,rfl⟩
    refine ⟨s ∩ t,⟨Finset.inter_subset_right,Or.inl htn⟩,?_⟩
    exact (hull_inter_face (Finset.subset_univ s) ht).symm
  · rintro ⟨s,hs,rfl⟩
    refine ⟨hull s,⟨s,boundary_faces_in_catalogue c t s ht htn hs,rfl⟩,?_⟩
    exact Set.inter_eq_left.mpr (hull_mono hs.1)

/-- Arbitrary subdivisions of the square have the same full boundary complex. -/
theorem square_boundary_rigid : BoundaryRigid square := by
  intro D F hFc hF hne
  obtain ⟨t,ht,rfl,htf⟩ := face_has_key hFc hF
  have htn : t ≠ Finset.univ := by
    intro he
    exact hne (by simpa only [he,square])
  obtain ⟨c,rfl⟩ := canonicalSubdivision_surjective D
  exact canonical_boundary_restriction c htf htn

theorem trivial_boundary_restriction {r t : Key} (hr : r ≠ Finset.univ)
    (ht : FaceKey r t) :
    (fun G => G ∩ hull t) '' (trivialSubdivision r).cells = faceFamily (hull t) := by
  have htn : t ≠ Finset.univ := by
    intro he
    exact hr (Finset.eq_univ_of_forall fun i => ht.1 (he.symm ▸ Finset.mem_univ i))
  rw [faceFamily_hull]
  ext F
  constructor
  · rintro ⟨G,⟨s,hs,rfl⟩,rfl⟩
    exact ⟨s ∩ t,⟨Finset.inter_subset_right,Or.inl htn⟩,
      (hull_inter_face hs.1 ht).symm⟩
  · rintro ⟨s,hs,rfl⟩
    refine ⟨hull s,⟨s,⟨hs.1.trans ht.1,Or.inl hr⟩,rfl⟩,?_⟩
    exact Set.inter_eq_left.mpr (hull_mono hs.1)

/-- The triangular-facet statement includes every proper face and every
possible vertex subdivision, not just a selected triangulation. -/
theorem triangle_boundary_rigid (i : Fin 4) : BoundaryRigid (hull (triangle i)) := by
  intro D F hFc hF hne
  obtain ⟨t,ht,rfl,htf⟩ := face_has_key hFc hF
  rw [triangle_subdivision_unique i D]
  exact trivial_boundary_restriction (triangle_ne_univ i) htf

open VertexSubdivisionTransport

/-- Boundary rigidity is invariant under an actual affine embedding, even
when the ambient dimensions differ. -/
theorem affine_image_boundary_rigid (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {P : Set V} (hP : BoundaryRigid P) : BoundaryRigid (f '' P) := by
  intro D F hFc hF hne
  let D' := pullback f hf D
  let F' := f ⁻¹' F
  have hFrange : F ⊆ Set.range f := hF.subset.trans (Set.image_subset_range f P)
  have himF : f '' F' = F := Set.image_preimage_eq_iff.mpr hFrange
  have hF' : IsExtreme ℝ P F' := by
    have h := affine_preimage_isExtreme f hF
    rwa [Set.preimage_image_eq P hf] at h
  have hneq : F' ≠ P := by
    intro h
    apply hne
    rw [← himF,h]
  have hrestriction := hP D' F' (hFc.affine_preimage f) hF' hneq
  ext H
  constructor
  · rintro ⟨C,hC,rfl⟩
    have hpre : f ⁻¹' (C ∩ F) ∈ (fun G => G ∩ F') '' D'.cells :=
      ⟨f ⁻¹' C,⟨C,hC,rfl⟩,rfl⟩
    rw [hrestriction] at hpre
    have hCrange : C ∩ F ⊆ Set.range f := fun x hx => hFrange hx.2
    have himC : f '' (f ⁻¹' (C ∩ F)) = C ∩ F :=
      Set.image_preimage_eq_iff.mpr hCrange
    have hc := hpre.1.affine_image f
    have he := affine_image_isExtreme f hf hpre.2
    rw [himC] at hc
    rw [himF,himC] at he
    exact ⟨hc,he⟩
  · rintro ⟨hHc,hH⟩
    have hpre : f ⁻¹' H ∈ faceFamily F' :=
      ⟨hHc.affine_preimage f,affine_preimage_isExtreme f hH⟩
    rw [← hrestriction] at hpre
    obtain ⟨G,⟨C,hC,rfl⟩,hG⟩ := hpre
    refine ⟨C,hC,?_⟩
    have hCrange : C ∩ F ⊆ Set.range f := fun x hx => hFrange hx.2
    have hHrange : H ⊆ Set.range f := hH.subset.trans hFrange
    calc
      C ∩ F = f '' (f ⁻¹' (C ∩ F)) :=
        (Set.image_preimage_eq_iff.mpr hCrange).symm
      _ = f '' (f ⁻¹' H) := congrArg (fun U : Set V => f '' U) hG
      _ = H := Set.image_preimage_eq_iff.mpr hHrange

/-- Restriction to another set is the same as restriction to its intersection
with the parent polytope; the inclusion is derived from actual coverage. -/
theorem restriction_inter_parent {P : Set V} (D : VertexSubdivision P) (B : Set V) :
    (fun F => F ∩ B) '' D.cells = (fun F => F ∩ (P ∩ B)) '' D.cells := by
  apply Set.image_congr
  intro F hF
  ext x
  constructor
  · rintro ⟨hx,hb⟩
    exact ⟨hx,D.cell_subset hF hx,hb⟩
  · rintro ⟨hx,hp,hb⟩
    exact ⟨hx,hb⟩

#print axioms hull_inter_face
#print axioms square_boundary_rigid
#print axioms triangle_boundary_rigid
#print axioms affine_image_boundary_rigid

end Unimodular.SubdivisionBoundary
end

end Enumeration_SubdivisionBoundary

/- Exact current draft body: A3FanChoices. -/
section Enumeration_A3FanChoices



/-!
UNVERIFIED EXTENSION DRAFT. All choices of subdivisions of the actual A3 cut
facets are automatically compatible, because the genuine proper boundary
faces are unchanged. Composition with the recovered checked slicing/coning
bijection gives a bijection for actual fans, not an abstract enumeration of
six ternary parameters. No projectivity conclusion is made in this module.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set

namespace Unimodular.A3FanChoices

open TypeAFanGeometry A3FacetCharts SquareSubdivision SubdivisionBoundary
open TauCeti.Toric

/-- A finite catalogue of all nonempty proper source cuts on four labels.
The witnesses are actual bijections of labels, not assumptions on a facet. -/
theorem properCut_forms : ∀ S : Finset (Vertex 3), S.Nonempty → S ≠ Finset.univ →
    (∃ e : Labels, S = squareCut e) ∨
      (∃ e : Labels, S = singletonCut e) ∨ (∃ e : Labels, S = tripleCut e) := by
  decide

theorem pairCut_form : ∀ S : Finset (Vertex 3), S.card = 2 →
    ∃ e : Labels, S = squareCut e := by decide

theorem nonpairCut_forms : ∀ S : Finset (Vertex 3), S.Nonempty → S ≠ Finset.univ →
    S.card ≠ 2 → (∃ e : Labels, S = singletonCut e) ∨
      (∃ e : Labels, S = tripleCut e) := by decide

/-- Every actual A3 cut facet has invariant boundary under arbitrary
subdivisions using its own genuine vertices. -/
theorem cut_boundary_rigid (S : ProperCut 3) : BoundaryRigid (cutFace S.val) := by
  rcases properCut_forms S.val S.property.1 S.property.2 with
    ⟨e,he⟩ | ⟨e,he⟩ | ⟨e,he⟩
  · rw [he,← squareChart_image e]
    exact affine_image_boundary_rigid (squareChart e) (squareChart_injective e)
      square_boundary_rigid
  · rw [he,← singletonChart_image e]
    exact affine_image_boundary_rigid (singletonChart e) (singletonChart_injective e)
      (triangle_boundary_rigid 2)
  · rw [he,← tripleChart_image e]
    exact affine_image_boundary_rigid (tripleChart e) (tripleChart_injective e)
      (triangle_boundary_rigid 2)

/-- The compatibility field from the general type-A theorem is derived from
the actual geometry, for every independently chosen facet subdivision. -/
theorem all_cut_subdivisions_compatible
    (D : ∀ S : ProperCut 3, VertexSubdivision (cutFace S.val)) (S T : ProperCut 3) :
    (fun F => F ∩ cutFace T.val) '' (D S).cells =
      (fun F => F ∩ cutFace S.val) '' (D T).cells := by
  by_cases he : S = T
  · subst T
    rfl
  have hst : S.val ≠ T.val := fun h => he (Subtype.ext h)
  have hts : T.val ≠ S.val := Ne.symm hst
  have hsproper : cutFace S.val ∩ cutFace T.val ≠ cutFace S.val := by
    intro h
    apply hst
    apply (cutFace_subset_iff S.property.1 S.property.2).mp
    intro x hx
    have hx' : x ∈ cutFace S.val ∩ cutFace T.val := h.symm ▸ hx
    exact hx'.2
  have htproper : cutFace T.val ∩ cutFace S.val ≠ cutFace T.val := by
    intro h
    apply hts
    apply (cutFace_subset_iff T.property.1 T.property.2).mp
    intro x hx
    have hx' : x ∈ cutFace T.val ∩ cutFace S.val := h.symm ▸ hx
    exact hx'.2
  have hsface : IsExtreme ℝ (cutFace S.val) (cutFace S.val ∩ cutFace T.val) :=
    extreme_inter_of_subset (cutFace_extreme T.val) (cutFace_extreme S.val).subset
  have htface : IsExtreme ℝ (cutFace T.val) (cutFace T.val ∩ cutFace S.val) :=
    extreme_inter_of_subset (cutFace_extreme S.val) (cutFace_extreme T.val).subset
  calc
    (fun F => F ∩ cutFace T.val) '' (D S).cells =
        faceFamily (cutFace S.val ∩ cutFace T.val) := by
      rw [restriction_inter_parent]
      exact cut_boundary_rigid S (D S) _
        ((cutFace_convex S.val).inter (cutFace_convex T.val)) hsface hsproper
    _ = faceFamily (cutFace T.val ∩ cutFace S.val) := by rw [Set.inter_comm]
    _ = (fun F => F ∩ cutFace S.val) '' (D T).cells := by
      rw [restriction_inter_parent]
      exact (cut_boundary_rigid T (D T) _
        ((cutFace_convex T.val).inter (cutFace_convex S.val)) htface htproper).symm

/-- Compatibility carries no extra restriction in rank three, as a proved
equivalence of the actual geometric data structures. -/
def independentCutSubdivisionsEquiv : CompatibleCutSubdivisions 3 ≃
    (∀ S : ProperCut 3, VertexSubdivision (cutFace S.val)) where
  toFun D := D.subdivision
  invFun D := ⟨D,all_cut_subdivisions_compatible D⟩
  left_inv D := by cases D; rfl
  right_inv D := rfl

/-- Square facets have three choices; all eight triangular facets have one. -/
def CutChoice (S : ProperCut 3) : Type := if S.val.card = 2 then Option Bool else PUnit

instance (S : ProperCut 3) : Fintype (CutChoice S) := by
  unfold CutChoice
  split <;> infer_instance

instance (S : ProperCut 3) : DecidableEq (CutChoice S) := by
  unfold CutChoice
  split <;> infer_instance

/-- The equivalence for each facet is transported from an actual affine chart.
A chart is chosen only after its existence has been proved for that cut. -/
def cutSubdivisionEquiv (S : ProperCut 3) :
    VertexSubdivision (cutFace S.val) ≃ CutChoice S := by
  classical
  by_cases hs : S.val.card = 2
  · let e := Classical.choose (pairCut_form S.val hs)
    have he : S.val = squareCut e := Classical.choose_spec (pairCut_form S.val hs)
    exact ((Equiv.cast (congrArg (fun T => VertexSubdivision (cutFace T)) he)).trans
      (squareFacetSubdivisionEquiv e)).trans
        (Equiv.cast (by simp only [CutChoice,if_pos hs]))
  · by_cases hsingle : ∃ e : Labels, S.val = singletonCut e
    · let e := Classical.choose hsingle
      have he : S.val = singletonCut e := Classical.choose_spec hsingle
      exact ((Equiv.cast (congrArg (fun T => VertexSubdivision (cutFace T)) he)).trans
        (singletonFacetSubdivisionEquiv e)).trans
          (Equiv.cast (by simp only [CutChoice,if_neg hs]))
    · have htriple : ∃ e : Labels, S.val = tripleCut e :=
        (nonpairCut_forms S.val S.property.1 S.property.2 hs).resolve_left hsingle
      let e := Classical.choose htriple
      have he : S.val = tripleCut e := Classical.choose_spec htriple
      exact ((Equiv.cast (congrArg (fun T => VertexSubdivision (cutFace T)) he)).trans
        (tripleFacetSubdivisionEquiv e)).trans
          (Equiv.cast (by simp only [CutChoice,if_neg hs]))

/-- A literal bijection from complete fans with all twelve prescribed A3 rays
to the independent choices on the actual six square and eight triangular facets. -/
def a3FanChoicesEquiv :
    {Φ : Fan (FanBridge.standardEmbedding 3) // Φ.IsComplete ∧
      AllowedBlocks.HasRays (FanBridge.standardEmbedding 3) (rootFamily 3) Φ} ≃
        (∀ S : ProperCut 3, CutChoice S) :=
  (fanSubdivisionEquiv (n := 3) (by decide)).trans
    (independentCutSubdivisionsEquiv.trans (Equiv.piCongrRight cutSubdivisionEquiv))

theorem six_square_facets :
    Fintype.card {S : ProperCut 3 // S.val.card = 2} = 6 := by decide

theorem eight_triangular_facets :
    Fintype.card {S : ProperCut 3 // S.val.card ≠ 2} = 8 := by decide

/-- This finite count is used only after the full geometric bijection. -/
theorem cut_choice_count : Fintype.card (∀ S : ProperCut 3, CutChoice S) = 729 := by
  decide

/-- The full labelled-fan count asserted in Section 7.1. No simpliciality,
projectivity, chosen maximal cone list, or compatibility premise is added. -/
theorem a3_complete_fan_count :
    Nat.card {Φ : Fan (FanBridge.standardEmbedding 3) // Φ.IsComplete ∧
      AllowedBlocks.HasRays (FanBridge.standardEmbedding 3) (rootFamily 3) Φ} = 729 := by
  rw [Nat.card_congr a3FanChoicesEquiv,Nat.card_eq_fintype_card]
  exact cut_choice_count

#print axioms cut_boundary_rigid
#print axioms all_cut_subdivisions_compatible
#print axioms independentCutSubdivisionsEquiv
#print axioms cutSubdivisionEquiv
#print axioms a3FanChoicesEquiv
#print axioms a3_complete_fan_count

end Unimodular.A3FanChoices
end

end Enumeration_A3FanChoices

/- Exact current draft body: SubdivisionTriangulations. -/
section Enumeration_SubdivisionTriangulations



/-!
UNVERIFIED EXTENSION DRAFT. Genuine affine independence of the geometric cell
vertices identifies the two split square subdivisions as triangulations. The
property is preserved by the actual injective affine facet charts. These are
the geometric inputs to the smooth-fan count; the count is not assumed here.
-/

set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped BigOperators

namespace Unimodular.SubdivisionTriangulations

open SquareSubdivision VertexSubdivisionTransport A3FacetCharts

def triangleVertices (i : Fin 4) (j : Fin 3) : Plane := vertex (i.succAbove j)

theorem triangle_index_range : ∀ (i j : Fin 4),
    j ∈ triangle i ↔ ∃ k : Fin 3, i.succAbove k = j := by decide

theorem triangleVertices_range (i : Fin 4) :
    Set.range (triangleVertices i) = vertex '' (triangle i : Set (Fin 4)) := by
  ext x
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨i.succAbove j,(triangle_index_range i _).mpr ⟨j,rfl⟩,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    obtain ⟨k,rfl⟩ := (triangle_index_range i j).mp hj
    exact ⟨k,rfl⟩

/-- Every three-corner subset is an actual affine simplex in the plane. -/
theorem triangleVertices_affineIndependent (i : Fin 4) :
    AffineIndependent ℝ (triangleVertices i) := by
  apply (affineIndependent_iff_of_fintype ℝ _).mpr
  intro w hw hz j
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hz
  have hx := congrFun hz 0
  have hy := congrFun hz 1
  fin_cases i <;> fin_cases j <;>
    norm_num [triangleVertices,vertex,Fin.succAbove,Fin.sum_univ_succ,Finset.sum_apply] at hw hx hy ⊢ <;>
    linarith

theorem proper_hull_affineIndependent {s : Key} (hs : s ≠ Finset.univ) :
    AffineIndependent ℝ (Subtype.val : (hull s).extremePoints ℝ → Plane) := by
  classical
  have hi : ∃ i : Fin 4, i ∉ s := by
    by_contra h
    push_neg at h
    exact hs (Finset.eq_univ_iff_forall.mpr h)
  obtain ⟨i,hi⟩ := hi
  have hsub : s ⊆ triangle i := by
    intro j hj
    apply (mem_triangle i j).mpr
    intro he
    exact hi (he ▸ hj)
  rw [hull_extremePoints]
  have htri := (triangleVertices_affineIndependent i).range
  rw [triangleVertices_range] at htri
  exact htri.mono (Set.image_mono hsub)

/-- The square is not a simplex: the alternating affine dependence of its
four literal corners has coefficients 1,-1,1,-1. -/
theorem square_not_affineIndependent :
    ¬AffineIndependent ℝ (Subtype.val : square.extremePoints ℝ → Plane) := by
  intro h
  rw [square_extremePoints] at h
  have hv : AffineIndependent ℝ vertex := h.of_set_of_injective vertex_injective
  let w : Fin 4 → ℝ := ![1,-1,1,-1]
  have hs : ∑ i : Fin 4, w i = 0 := by norm_num [w,Fin.sum_univ_succ]
  have hz : ∑ i : Fin 4, w i • vertex i = 0 := by
    ext j
    fin_cases j <;> norm_num [w,vertex,Fin.sum_univ_succ,Finset.sum_apply]
  have hbad := hv.eq_zero_of_sum_eq_zero hs hz 0 (Finset.mem_univ 0)
  norm_num [w] at hbad

theorem split_catalogue_proper : ∀ (b : Bool) (s : Key),
    s ∈ catalogue (some b) → s ≠ Finset.univ := by decide

/-- The three actual square subdivisions are triangulations precisely for
the two diagonal choices. -/
theorem canonical_isTriangulation_iff (c : Option Bool) :
    (canonicalSubdivision c).IsTriangulation ↔ c ≠ none := by
  cases c with
  | none =>
    constructor
    · intro h
      have hcell : square ∈ (canonicalSubdivision none).cells := by
        apply (hull_mem_canonical none Finset.univ).mpr
        exact ⟨Finset.univ,by simp [maximalKeys],faceKey_refl _⟩
      exact (square_not_affineIndependent (h square hcell)).elim
    · intro h
      exact (h rfl).elim
  | some b =>
    constructor
    · intro h
      simp
    · intro h F hF
      obtain ⟨s,hs,rfl⟩ := hF
      exact proper_hull_affineIndependent (split_catalogue_proper b s hs)

theorem square_isTriangulation_iff (D : VertexSubdivision square) :
    D.IsTriangulation ↔ squareSubdivisionEquiv D ≠ none := by
  obtain ⟨c,rfl⟩ := canonicalSubdivision_surjective D
  have hc : squareSubdivisionEquiv.symm c = canonicalSubdivision c := rfl
  rw [← hc,squareSubdivisionEquiv.apply_symm_apply]
  exact canonical_isTriangulation_iff c

theorem triangle_isTriangulation (i : Fin 4)
    (D : VertexSubdivision (hull (triangle i))) : D.IsTriangulation := by
  intro F hF
  obtain ⟨s,hs,rfl⟩ := cell_has_key D hF
  apply proper_hull_affineIndependent
  intro he
  have hi : i ∈ triangle i := hs (he.symm ▸ Finset.mem_univ i)
  simpa using hi

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

theorem affineIndependent_image_iff (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    (A : Set V) :
    AffineIndependent ℝ (Subtype.val : (f '' A) → W) ↔
      AffineIndependent ℝ (Subtype.val : A → V) := by
  rw [← affineIndependent_equiv (Equiv.Set.image f A hf)]
  exact f.affineIndependent_iff hf

/-- Geometric triangulation is preserved and reflected by affine embeddings. -/
theorem map_isTriangulation_iff (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {P : Set V} (D : VertexSubdivision P) :
    (map f hf D).IsTriangulation ↔ D.IsTriangulation := by
  constructor
  · intro h F hF
    have hi := h (f '' F) ⟨F,hF,rfl⟩
    rw [← affine_image_extremePoints f hf F] at hi
    exact (affineIndependent_image_iff f hf _).mp hi
  · rintro h F ⟨G,hG,rfl⟩
    rw [← affine_image_extremePoints f hf G]
    exact (affineIndependent_image_iff f hf _).mpr (h G hG)

theorem pullback_isTriangulation_iff (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {P : Set V} (D : VertexSubdivision (f '' P)) :
    (pullback f hf D).IsTriangulation ↔ D.IsTriangulation := by
  rw [← map_isTriangulation_iff f hf (pullback f hf D),map_pullback]

theorem chart_isTriangulation_iff (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {P : Set V} {Q : Set W} (h : f '' P = Q) (D : VertexSubdivision Q) :
    ((affineEmbeddingEquiv f hf P).symm
      (Equiv.cast (congrArg (fun A : Set W => VertexSubdivision A) h.symm) D)).IsTriangulation ↔
      D.IsTriangulation := by
  cases h
  exact pullback_isTriangulation_iff f hf D

theorem cast_isTriangulation_iff {P Q : Set V} (h : P = Q)
    (D : VertexSubdivision P) :
    (Equiv.cast (congrArg (fun A : Set V => VertexSubdivision A) h) D).IsTriangulation ↔
      D.IsTriangulation := by
  subst Q
  rfl

theorem square_facet_isTriangulation_iff (e : Labels)
    (D : VertexSubdivision (TypeAFanGeometry.cutFace (squareCut e))) :
    D.IsTriangulation ↔ squareFacetSubdivisionEquiv e D ≠ none := by
  rw [← chart_isTriangulation_iff (squareChart e) (squareChart_injective e)
    (squareChart_image e) D]
  exact square_isTriangulation_iff _

theorem singleton_facet_isTriangulation (e : Labels)
    (D : VertexSubdivision (TypeAFanGeometry.cutFace (singletonCut e))) :
    D.IsTriangulation := by
  rw [← chart_isTriangulation_iff (singletonChart e) (singletonChart_injective e)
    (singletonChart_image e) D]
  exact triangle_isTriangulation 2 _

theorem triple_facet_isTriangulation (e : Labels)
    (D : VertexSubdivision (TypeAFanGeometry.cutFace (tripleCut e))) :
    D.IsTriangulation := by
  rw [← chart_isTriangulation_iff (tripleChart e) (tripleChart_injective e)
    (tripleChart_image e) D]
  exact triangle_isTriangulation 2 _

#print axioms triangleVertices_affineIndependent
#print axioms square_not_affineIndependent
#print axioms square_isTriangulation_iff
#print axioms map_isTriangulation_iff
#print axioms square_facet_isTriangulation_iff

end Unimodular.SubdivisionTriangulations
end

end Enumeration_SubdivisionTriangulations

/- Exact current draft body: A3RegularFanCount. -/
section Enumeration_A3RegularFanCount



/-!
UNVERIFIED EXTENSION DRAFT. This restricts the actual complete-fan equivalence
using genuine lattice regularity. Square cells must be split into triangles;
the eight triangular facets impose no choices. No simpliciality, basis, or
triangulation hypothesis is added to the type of complete fans being counted.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Unimodular.A3RegularFanCount

open TypeAFanGeometry A3FanChoices A3FacetCharts SubdivisionTriangulations
open TauCeti.Toric

/-- On a square facet this says that a diagonal is chosen. On a triangular
facet it imposes no condition. It is a predicate on the already established
coordinates for actual geometric subdivisions. -/
def choiceOption (S : ProperCut 3) (c : CutChoice S) : Option Bool :=
  if hs : S.val.card = 2 then
    (Equiv.cast (by simp only [CutChoice,if_pos hs])) c
  else some false

def ChoiceIsSplit (S : ProperCut 3) (c : CutChoice S) : Prop := choiceOption S c ≠ none

instance (S : ProperCut 3) (c : CutChoice S) : Decidable (ChoiceIsSplit S c) :=
  inferInstanceAs (Decidable (choiceOption S c ≠ none))

/-- The coordinate predicate is exactly affine independence of every actual
cell's extreme points, including all lower-dimensional cells. -/
theorem cut_isTriangulation_iff (S : ProperCut 3)
    (D : VertexSubdivision (cutFace S.val)) :
    D.IsTriangulation ↔ ChoiceIsSplit S (cutSubdivisionEquiv S D) := by
  classical
  by_cases hs : S.val.card = 2
  · let e := Classical.choose (pairCut_form S.val hs)
    have he : S.val = squareCut e := Classical.choose_spec (pairCut_form S.val hs)
    have h := square_facet_isTriangulation_iff e
      (Equiv.cast (congrArg (fun K => VertexSubdivision (cutFace K)) he) D)
    have hcast := cast_isTriangulation_iff (congrArg cutFace he) D
    simpa [cutSubdivisionEquiv,ChoiceIsSplit,choiceOption,hs,e] using hcast.symm.trans h
  · by_cases hsingle : ∃ e : Labels, S.val = singletonCut e
    · let e := Classical.choose hsingle
      have he : S.val = singletonCut e := Classical.choose_spec hsingle
      have h := singleton_facet_isTriangulation e
        (Equiv.cast (congrArg (fun K => VertexSubdivision (cutFace K)) he) D)
      have hD : D.IsTriangulation :=
        (cast_isTriangulation_iff (congrArg cutFace he) D).mp h
      simpa [ChoiceIsSplit,choiceOption,hs] using hD
    · have htriple : ∃ e : Labels, S.val = tripleCut e :=
        (nonpairCut_forms S.val S.property.1 S.property.2 hs).resolve_left hsingle
      let e := Classical.choose htriple
      have he : S.val = tripleCut e := Classical.choose_spec htriple
      have h := triple_facet_isTriangulation e
        (Equiv.cast (congrArg (fun K => VertexSubdivision (cutFace K)) he) D)
      have hD : D.IsTriangulation :=
        (cast_isTriangulation_iff (congrArg cutFace he) D).mp h
      simpa [ChoiceIsSplit,choiceOption,hs] using hD

abbrev CompleteRootFan :=
  {Φ : Fan (FanBridge.standardEmbedding 3) // Φ.IsComplete ∧
    AllowedBlocks.HasRays (FanBridge.standardEmbedding 3) (rootFamily 3) Φ}

/-- Actual lattice regularity, with its primitive-generator basis condition,
is transported through the complete geometric fan equivalence. -/
theorem fan_isRegular_iff_choices (Φ : CompleteRootFan) :
    Φ.val.IsRegular ↔ ∀ S : ProperCut 3,
      ChoiceIsSplit S (a3FanChoicesEquiv Φ S) := by
  rw [fan_isRegular_iff_cut_triangulations (by decide) Φ.val Φ.property.1 Φ.property.2]
  apply forall_congr'
  intro S
  exact cut_isTriangulation_iff S
    ((fanCutSubdivisions Φ.val Φ.property.1 Φ.property.2).subdivision S)

/-- The restriction is a bijection on actual fans; its inverse retains
completeness, all twelve rays, and the proved regularity property. -/
def regularFanChoicesEquiv :
    {Φ : CompleteRootFan // Φ.val.IsRegular} ≃
      {c : ∀ S : ProperCut 3, CutChoice S // ∀ S, ChoiceIsSplit S (c S)} :=
  Equiv.subtypeEquiv a3FanChoicesEquiv fan_isRegular_iff_choices

theorem regular_choice_count :
    Fintype.card {c : ∀ S : ProperCut 3, CutChoice S //
      ∀ S, ChoiceIsSplit S (c S)} = 64 := by
  decide

/-- There are exactly sixty-four actual regular complete fans on the twelve
labelled A3 rays, without quotienting by coordinate or root symmetries. -/
theorem a3_regular_complete_fan_count :
    Nat.card {Φ : CompleteRootFan // Φ.val.IsRegular} = 64 := by
  rw [Nat.card_congr regularFanChoicesEquiv,Nat.card_eq_fintype_card]
  exact regular_choice_count

/-- The same count with every geometric hypothesis visible in one subtype. -/
theorem a3_regular_complete_fan_count_explicit :
    Nat.card {Φ : Fan (FanBridge.standardEmbedding 3) // Φ.IsComplete ∧
      AllowedBlocks.HasRays (FanBridge.standardEmbedding 3) (rootFamily 3) Φ ∧
        Φ.IsRegular} = 64 := by
  let e : {Φ : Fan (FanBridge.standardEmbedding 3) // Φ.IsComplete ∧
      AllowedBlocks.HasRays (FanBridge.standardEmbedding 3) (rootFamily 3) Φ ∧
        Φ.IsRegular} ≃ {Φ : CompleteRootFan // Φ.val.IsRegular} :=
    { toFun := fun Φ => ⟨⟨Φ.val,Φ.property.1,Φ.property.2.1⟩,Φ.property.2.2⟩
      invFun := fun Φ => ⟨Φ.val.val,Φ.val.property.1,Φ.val.property.2,Φ.property⟩
      left_inv := fun Φ => by cases Φ; rfl
      right_inv := fun Φ => by cases Φ; rfl }
  rw [Nat.card_congr e]
  exact a3_regular_complete_fan_count

#print axioms cut_isTriangulation_iff
#print axioms fan_isRegular_iff_choices
#print axioms regularFanChoicesEquiv
#print axioms a3_regular_complete_fan_count
#print axioms a3_regular_complete_fan_count_explicit

end Unimodular.A3RegularFanCount
end

end Enumeration_A3RegularFanCount

#print axioms Unimodular.A3FanChoices.a3_complete_fan_count
#print axioms Unimodular.A3RegularFanCount.a3_regular_complete_fan_count_explicit
#check "UNIMODULAR_A3_ENUMERATION_EOF_V4"
