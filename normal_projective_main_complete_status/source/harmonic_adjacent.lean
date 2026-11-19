module

public import face_separation
public import exterior_path
public import walk_cycle

/-!
# The adjacent-face step in the positive-weight embedding theorem

This is the geometric heart of Floater's proof, specialized to the triangular
boundary needed by convex caps. Harmonicity, geometric simplex intersections,
and Jordan separation imply opposite signs at the third vertices of adjacent
faces. Neither local injectivity nor an embedding of the harmonic drawing is
assumed.
-/

@[expose] public section

noncomputable section

namespace NormalProjective.Planar

open Set Finset

theorem boundary_height_coordinate (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ σ : ℝ, σ ≠ 0 ∧ ∀ z : ℂ,
      edgeHeight (basePoint i) (basePoint j) z = σ * triangleCoordinate k z := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  · refine ⟨1,by norm_num,?_⟩
    intro z
    simp [edgeHeight,edgeNormalize,basePoint,triangleCoordinate]
  · refine ⟨-1,by norm_num,?_⟩
    intro z
    simp [edgeHeight,edgeNormalize,basePoint,triangleCoordinate]
  · refine ⟨-1,by norm_num,?_⟩
    intro z
    simp [edgeHeight,edgeNormalize,basePoint,triangleCoordinate]
  · refine ⟨1/2,by norm_num,?_⟩
    intro z
    norm_num [edgeHeight,edgeNormalize,basePoint,triangleCoordinate,
      Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    ring
  · refine ⟨1,by norm_num,?_⟩
    intro z
    simp [edgeHeight,edgeNormalize,basePoint,triangleCoordinate]
  · refine ⟨-(1/2),by norm_num,?_⟩
    intro z
    norm_num [edgeHeight,edgeNormalize,basePoint,triangleCoordinate,
      Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    ring

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TriangularDisk

variable (D : TriangularDisk V)

theorem coordinate_pos_of_ne_other_corners (i j k : Fin 3)
    (hcover : ∀ l : Fin 3, l = i ∨ l = j ∨ l = k)
    (v : V) (hvi : v ≠ D.corner i) (hvj : v ≠ D.corner j) :
    0 < triangleCoordinate k (D.point v) := by
  apply lt_of_le_of_ne (D.source_coordinates_nonnegative v k)
  intro hzero
  obtain ⟨l,hl,hvl⟩ := (D.coordinate_zero_iff k v).mp hzero.symm
  rcases hcover l with rfl | rfl | rfl
  · exact hvi hvl
  · exact hvj hvl
  · exact hl rfl

/-- A shared edge of two distinct genuine faces cannot join two of the three
boundary corners: all other source vertices are on the same strict side of
that boundary side. -/
theorem interior_endpoint_of_two_faces {a b x y : V}
    (hs : ({a,b,x} : Finset V) ∈ D.faces)
    (ht : ({a,b,y} : Finset V) ∈ D.faces)
    (hab : a ≠ b) (hxy : x ≠ y)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) :
    a ∉ D.boundary ∨ b ∉ D.boundary := by
  by_contra! h
  obtain ⟨i,rfl⟩ := h.1
  obtain ⟨j,rfl⟩ := h.2
  have hij : i ≠ j := fun h => hab (congrArg D.corner h)
  have hex : ∃ k : Fin 3, i ≠ k ∧ j ≠ k ∧
      ∀ l : Fin 3, l = i ∨ l = j ∨ l = k := by
    fin_cases i <;> fin_cases j <;> simp_all
    all_goals decide
  obtain ⟨k,hik,hjk,hcover⟩ := hex
  obtain ⟨σ,hσ,hheight⟩ := boundary_height_coordinate i j k hij hik hjk
  have hxk := D.coordinate_pos_of_ne_other_corners i j k hcover x hxa hxb
  have hyk := D.coordinate_pos_of_ne_other_corners i j k hcover y hya hyb
  have hxheight : edgeHeight (D.point (D.corner i)) (D.point (D.corner j)) (D.point x) =
      σ * triangleCoordinate k (D.point x) := by rw [D.corner_point,D.corner_point]; exact hheight _
  have hyheight : edgeHeight (D.point (D.corner i)) (D.point (D.corner j)) (D.point y) =
      σ * triangleCoordinate k (D.point y) := by rw [D.corner_point,D.corner_point]; exact hheight _
  rcases lt_or_gt_of_ne hσ with hσn | hσp
  · have hs' : ({D.corner j,D.corner i,x} : Finset V) ∈ D.faces := by
      simpa only [Finset.insert_comm] using hs
    have ht' : ({D.corner j,D.corner i,y} : Finset V) ∈ D.faces := by
      simpa only [Finset.insert_comm] using ht
    have hxpos : 0 < edgeHeight (D.point (D.corner j)) (D.point (D.corner i)) (D.point x) := by
      rw [edgeHeight_swap (D.point_injective.ne hab),hxheight]
      exact neg_pos.mpr (mul_neg_of_neg_of_pos hσn hxk)
    have hyneg := D.toTriangulation.adjacent_third_height_neg hs' ht' hab.symm hxy
      hxb hxa hyb hya hxpos
    rw [edgeHeight_swap (D.point_injective.ne hab),hyheight] at hyneg
    exact (neg_pos.mpr (mul_neg_of_neg_of_pos hσn hyk)).not_ge hyneg.le
  · have hxpos : 0 < edgeHeight (D.point (D.corner i)) (D.point (D.corner j)) (D.point x) := by
      rw [hxheight]
      exact mul_pos hσp hxk
    have hyneg := D.toTriangulation.adjacent_third_height_neg hs ht hab hxy hxa hxb hya hyb hxpos
    rw [hyheight] at hyneg
    exact (mul_pos hσp hyk).not_ge hyneg.le

/-- Opposite signs for every actual harmonic height. This statement is the
adjacent-face step itself, with all cycle construction and separation premises
discharged from the original geometric triangulation. -/
theorem harmonic_height_negative_at_adjacent_face
    (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (he : ∀ i j, D.toTriangulation.graph.Adj i j → 0 < w i j)
    (hoff : ∀ i j, ¬ D.toTriangulation.graph.Adj i j → w i j = 0)
    (h : V → ℝ) (hh : ∀ i, i ∉ D.boundary → Dirichlet.Harmonic w h i)
    {a b x y : V}
    (hs : ({a,b,x} : Finset V) ∈ D.faces)
    (ht : ({a,b,y} : Finset V) ∈ D.faces)
    (hab : a ≠ b) (hxy : x ≠ y)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (ha : h a = 0) (hb : h b = 0) (hx : 0 < h x) : h y < 0 := by
  by_contra hnot
  have hy : 0 ≤ h y := le_of_not_gt hnot
  have habG : D.toTriangulation.graph.Adj a b := ⟨hab,_,hs,by simp,by simp⟩
  have haxG : D.toTriangulation.graph.Adj a x := ⟨hxa.symm,_,hs,by simp,by simp⟩
  have hbxG : D.toTriangulation.graph.Adj b x := ⟨hxb.symm,_,hs,by simp,by simp⟩
  have hinterior := D.interior_endpoint_of_two_faces hs ht hab hxy hxa hxb hya hyb
  obtain ⟨C,i,hia,hib,hvertices⟩ := D.exists_negative_cycle w hw he hoff h hh
    habG haxG hbxG ha hb hx hinterior
  have hC : ∀ v ∈ C.vertices, h v ≤ 0 := by
    intro v hv
    rcases hvertices v hv with rfl | rfl | hv
    · exact ha.le
    · exact hb.le
    · exact hv.le
  have hxC : x ∉ C.vertices := fun hxc => hx.not_ge (hC x hxc)
  have hyC : y ∉ C.vertices := by
    intro hyc
    rcases hvertices y hyc with hya' | hyb' | hyn
    · exact hya hya'
    · exact hyb hyb'
    · exact hyn.not_ge hy
  have hxout := D.positive_vertex_outside_cycle C w hw he hoff h hh hC
    haxG.symm (by linarith) hx
  have hyinside := C.encloses_second_third_vertex hs ht hab hxy hxa hxb hya hyb
    i hia hib hxC hyC hxout
  have hyheight := D.toTriangulation.face_third_height_ne_zero ht (by simp) (by simp)
    (by simp) hab hya hyb
  let L := edgeHeightLinear (D.point a) (D.point b)
  let c := L (D.point a)
  have hbline : L (D.point b) = c := by
    have hz := edgeHeight_zero_on_segment (right_mem_segment ℝ (D.point a) (D.point b))
    rw [edgeHeight_eq_linear] at hz
    exact sub_eq_zero.mp hz
  have hex : ∃ (l : ℂ →L[ℝ] ℝ) (d : ℝ), l (D.point a) = d ∧
      l (D.point b) = d ∧ d < l (D.point y) := by
    rcases lt_or_gt_of_ne hyheight with hyn | hyp
    · refine ⟨-L,-c,rfl,by simpa using congrArg Neg.neg hbline,?_⟩
      have h := hyn
      rw [edgeHeight_eq_linear] at h
      change -c < -(L (D.point y))
      dsimp [c,L] at *
      linarith
    · refine ⟨L,c,rfl,hbline,?_⟩
      rw [edgeHeight_eq_linear] at hyp
      exact sub_pos.mp hyp
  obtain ⟨l,d,hla,hlb,hly⟩ := hex
  have hstrict : ∀ v ∈ C.vertices, d < l (D.point v) → h v < 0 := by
    intro v hv hvl
    rcases hvertices v hv with rfl | rfl | hv
    · exact False.elim (by simpa [hla] using hvl)
    · exact False.elim (by simpa [hlb] using hvl)
    · exact hv
  exact (D.strict_cycle_barrier C w hw he hoff h hh hC l d hstrict y hyinside hly).not_ge hy

end TriangularDisk

end NormalProjective.Planar
