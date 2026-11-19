module

public import polygon_local

/-!
# Complementary components on the two sides of a triangulation edge

The hypotheses are actual face incidences and the actual cycle. Paths from a
third vertex to points near the shared edge are geometric line segments in
that face. Exact simplicial intersections ensure that they avoid the cycle.
-/

@[expose] public section

noncomputable section

namespace NormalProjective.Planar

open Set Finset Metric
open scoped Topology

theorem edgeHeight_affine (a b m v : ℂ) (t : ℝ) :
    edgeHeight a b (m+t • (v-m)) =
      edgeHeight a b m+t*(edgeHeight a b v-edgeHeight a b m) := by
  simp only [edgeHeight_eq_linear,map_add,map_smul,map_sub,smul_eq_mul]
  ring

theorem edgeHeight_shift (a b m z : ℂ) :
    (((b-a)⁻¹*(z-m))).im = edgeHeight a b z-edgeHeight a b m := by
  simp [edgeHeight,edgeNormalize,mul_sub]

theorem convex_edgeHeight_pos (a b : ℂ) : Convex ℝ {z | 0 < edgeHeight a b z} := by
  have heq : {z | 0 < edgeHeight a b z} =
      {z | edgeHeightLinear a b a < edgeHeightLinear a b z} := by
    ext z
    simp [edgeHeight_eq_linear,sub_pos]
  rw [heq]
  exact convex_halfSpace_gt (edgeHeightLinear a b).toLinearMap.isLinear _

theorem convex_edgeHeight_neg (a b : ℂ) : Convex ℝ {z | edgeHeight a b z < 0} := by
  have heq : {z | edgeHeight a b z < 0} =
      {z | edgeHeightLinear a b z < edgeHeightLinear a b a} := by
    ext z
    simp [edgeHeight_eq_linear,sub_neg]
  rw [heq]
  exact convex_halfSpace_lt (edgeHeightLinear a b).toLinearMap.isLinear _

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Triangulation

variable (T : Triangulation V)

theorem triangle_intersection_base {a b x y : V}
    (hs : ({a,b,x} : Finset V) ∈ T.faces)
    (ht : ({a,b,y} : Finset V) ∈ T.faces) (hxy : x ≠ y)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) :
    convexHull ℝ ({T.point a,T.point b,T.point x} : Set ℂ) ∩
      convexHull ℝ ({T.point a,T.point b,T.point y} : Set ℂ) =
        segment ℝ (T.point a) (T.point b) := by
  have hint : ({a,b,x} ∩ {a,b,y} : Finset V) = {a,b} := by
    ext v
    simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
    aesop
  have hh := T.intersection _ hs _ ht
  rw [hint,T.simplex_pair] at hh
  simpa [simplex] using hh

theorem adjacent_third_height_neg {a b x y : V}
    (hs : ({a,b,x} : Finset V) ∈ T.faces)
    (ht : ({a,b,y} : Finset V) ∈ T.faces)
    (hab : a ≠ b) (hxy : x ≠ y)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (hx : 0 < edgeHeight (T.point a) (T.point b) (T.point x)) :
    edgeHeight (T.point a) (T.point b) (T.point y) < 0 := by
  apply third_vertex_negative_of_triangle_intersection (T.point_injective.ne hab) hx
  · exact T.face_third_height_ne_zero ht (by simp) (by simp) (by simp) hab hya hyb
  · rw [T.triangle_intersection_base hs ht hxy hxa hxb hya hyb]

end Triangulation

namespace GraphCycle

variable {T : Triangulation V} (C : GraphCycle T.graph)

theorem curve_inter_face_subset_base {a b v : V}
    (hs : ({a,b,v} : Finset V) ∈ T.faces) (hv : v ∉ C.vertices) :
    C.curve ∩ simplex T.point {a,b,v} ⊆ segment ℝ (T.point a) (T.point b) := by
  intro z hz
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz.1
  rw [C.edgeSet_eq,← T.simplex_pair] at hi
  obtain ⟨_,s,hs',hc,hd⟩ := C.edge i
  have he : ({C.vertex i,C.vertex (finRotate C.length i)} : Finset V) ⊆ s := by
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hc hd
  have hint : z ∈ simplex T.point
      ({a,b,v} ∩ {C.vertex i,C.vertex (finRotate C.length i)}) := by
    rw [← T.subface_intersection hs hs' (Finset.Subset.refl _) he]
    exact ⟨hz.2,hi⟩
  have hsub : ({a,b,v} ∩ {C.vertex i,C.vertex (finRotate C.length i)} : Finset V) ⊆ {a,b} := by
    intro u hu
    obtain ⟨hu,hui⟩ := Finset.mem_inter.mp hu
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu hui ⊢
    rcases hu with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rcases hui with h | h
      · exact False.elim (hv ⟨i,h.symm⟩)
      · exact False.elim (hv ⟨finRotate C.length i,h.symm⟩)
  rw [← T.simplex_pair]
  exact convexHull_mono (Set.image_mono hsub) hint

theorem same_component_on_face_side {a b v : V} {z : ℂ}
    (hs : ({a,b,v} : Finset V) ∈ T.faces) (hv : v ∉ C.vertices)
    (hz : z ∈ simplex T.point {a,b,v})
    (hside : (0 < edgeHeight (T.point a) (T.point b) (T.point v) ∧
        0 < edgeHeight (T.point a) (T.point b) z) ∨
      (edgeHeight (T.point a) (T.point b) (T.point v) < 0 ∧
        edgeHeight (T.point a) (T.point b) z < 0)) :
    z ∈ connectedComponentIn C.curveᶜ (T.point v) := by
  have hvface : T.point v ∈ simplex T.point {a,b,v} := point_mem_simplex _ _ (by simp)
  have hsegface := (convex_convexHull ℝ _).segment_subset hvface hz
  have hseg : segment ℝ (T.point v) z ⊆ C.curveᶜ := by
    intro u hu huC
    have hu0 := edgeHeight_zero_on_segment
      (C.curve_inter_face_subset_base hs hv ⟨huC,hsegface hu⟩)
    rcases hside with hside | hside
    · have hp := (convex_edgeHeight_pos (T.point a) (T.point b)).segment_subset hside.1 hside.2 hu
      exact hp.ne' hu0
    · have hn := (convex_edgeHeight_neg (T.point a) (T.point b)).segment_subset hside.1 hside.2 hu
      exact hn.ne hu0
  exact (convex_segment (𝕜 := ℝ) _ _).isPreconnected.subset_connectedComponentIn
    (left_mem_segment ℝ _ _) hseg (right_mem_segment ℝ _ _)

theorem exists_near_edge_same_component {a b v : V} {m : ℂ}
    (hs : ({a,b,v} : Finset V) ∈ T.faces) (hv : v ∉ C.vertices)
    (hm : m ∈ openSegment ℝ (T.point a) (T.point b))
    (hheight : edgeHeight (T.point a) (T.point b) (T.point v) ≠ 0)
    (r : ℝ) (hr : 0 < r) :
    ∃ z ∈ ball m r, z ∈ connectedComponentIn C.curveᶜ (T.point v) ∧
      ∃ t : ℝ, 0 < t ∧ edgeHeight (T.point a) (T.point b) z =
        t * edgeHeight (T.point a) (T.point b) (T.point v) := by
  let f : ℝ → ℂ := fun t => m+t • (T.point v-m)
  have hf : Continuous f := by fun_prop
  have hball : ∀ᶠ t : ℝ in 𝓝 0, f t ∈ ball m r :=
    (isOpen_ball.preimage hf).mem_nhds (by simpa [f] using (mem_ball_self (x := m) hr))
  have hlt : ∀ᶠ t : ℝ in 𝓝 0, t < 1 := isOpen_Iio.mem_nhds (by norm_num)
  obtain ⟨t,ht,hballt,ht1⟩ := (hball.and hlt).exists_gt
  have hm0 : edgeHeight (T.point a) (T.point b) m = 0 :=
    edgeHeight_zero_on_segment (openSegment_subset_segment ℝ _ _ hm)
  have heq : edgeHeight (T.point a) (T.point b) (f t) =
      t * edgeHeight (T.point a) (T.point b) (T.point v) := by
    change edgeHeight (T.point a) (T.point b) (m+t • (T.point v-m)) = _
    rw [edgeHeight_affine,hm0]
    ring
  have hmface : m ∈ simplex T.point {a,b,v} := by
    have hseg : m ∈ simplex T.point {a,b} := by
      rw [T.simplex_pair]
      exact openSegment_subset_segment ℝ _ _ hm
    exact convexHull_mono (Set.image_mono (by
      intro u hu
      simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hu ⊢
      aesop)) hseg
  have hfseg : f t ∈ segment ℝ m (T.point v) := by
    refine ⟨1-t,t,by linarith,ht.le,by ring,?_⟩
    dsimp [f]
    push_cast
    ring
  have hfface : f t ∈ simplex T.point {a,b,v} :=
    (convex_convexHull ℝ _).segment_subset hmface (point_mem_simplex _ _ (by simp)) hfseg
  refine ⟨f t,hballt,C.same_component_on_face_side hs hv hfface ?_,t,ht,heq⟩
  rcases lt_or_gt_of_ne hheight with hn | hp
  · exact Or.inr ⟨hn,by rw [heq]; exact mul_neg_of_pos_of_neg ht hn⟩
  · exact Or.inl ⟨hp,by rw [heq]; exact mul_pos ht hp⟩

theorem filledHull_iff_of_same_component {x y : ℂ}
    (hxy : y ∈ connectedComponentIn C.curveᶜ x) :
    x ∈ TauCeti.filledHull C.curve ↔ y ∈ TauCeti.filledHull C.curve := by
  simp only [TauCeti.mem_filledHull_iff]
  rw [connectedComponentIn_eq hxy]

/-- If the cycle contains the common edge of two actual adjacent faces, and
one third vertex lies outside its filled hull, then the other is enclosed.
Both third vertices are required to be off the cycle; in the harmonic
application this follows from their nonnegative heights and the cycle's strict
negativity at every vertex except the endpoints of the common edge. -/
theorem encloses_second_third_vertex {a b x y : V}
    (hs : ({a,b,x} : Finset V) ∈ T.faces)
    (ht : ({a,b,y} : Finset V) ∈ T.faces)
    (hab : a ≠ b) (hxy : x ≠ y)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (i : Fin C.length) (hia : C.vertex i = a)
    (hib : C.vertex (finRotate C.length i) = b)
    (hxC : x ∉ C.vertices) (hyC : y ∉ C.vertices)
    (hxout : T.point x ∉ TauCeti.filledHull C.curve) :
    T.point y ∈ TauCeti.filledHull C.curve \ C.curve := by
  let a₀ := T.point a
  let b₀ := T.point b
  let m := midpoint ℝ a₀ b₀
  have hm : m ∈ openSegment ℝ a₀ b₀ := midpoint_mem_openSegment _ _
  have hm0 : edgeHeight a₀ b₀ m = 0 :=
    edgeHeight_zero_on_segment (openSegment_subset_segment ℝ _ _ hm)
  have hw : m ∈ openSegment ℝ (T.point (C.vertex i))
      (T.point (C.vertex (finRotate C.length i))) := by
    rw [hia,hib]
    exact hm
  obtain ⟨r,hr,hline⟩ := C.locally_eq_line_of_openEdge i hw
  rw [hia,hib] at hline
  have hx0 := T.face_third_height_ne_zero hs (by simp) (by simp) (by simp) hab hxa hxb
  have hy0 := T.face_third_height_ne_zero ht (by simp) (by simp) (by simp) hab hya hyb
  obtain ⟨zx,hzxb,hzxc,t,htp,hzt⟩ := C.exists_near_edge_same_component hs hxC hm hx0 r hr
  obtain ⟨zy,hzyb,hzyc,s,hsp,hzs⟩ := C.exists_near_edge_same_component ht hyC hm hy0 r hr
  have hxzn : zx ∉ TauCeti.filledHull C.curve := fun h =>
    hxout ((C.filledHull_iff_of_same_component hzxc).mpr h)
  have hzyfilled : zy ∈ TauCeti.filledHull C.curve := by
    rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
    · have hswapS : ({b,a,x} : Finset V) ∈ T.faces := by
        simpa only [Finset.insert_comm] using hs
      have hswapT : ({b,a,y} : Finset V) ∈ T.faces := by
        simpa only [Finset.insert_comm] using ht
      have hswapx : 0 < edgeHeight (T.point b) (T.point a) (T.point x) := by
        rw [edgeHeight_swap (T.point_injective.ne hab)]
        linarith
      have hswapy := T.adjacent_third_height_neg hswapS hswapT hab.symm hxy
        hxb hxa hyb hya hswapx
      have hypos : 0 < edgeHeight a₀ b₀ (T.point y) := by
        rw [edgeHeight_swap (T.point_injective.ne hab)] at hswapy
        linarith
      have hline' : ∀ z ∈ ball m r,
          z ∈ C.curve ↔ (-((b₀-a₀)⁻¹)*(z-m)).im = 0 := by
        intro z hz
        simpa only [neg_mul,Complex.neg_im,neg_eq_zero] using hline z hz
      have hpos : 0 < (-((b₀-a₀)⁻¹)*(zx-m)).im := by
        rw [neg_mul,Complex.neg_im,edgeHeight_shift,hm0,sub_zero,hzt]
        exact neg_pos.mpr (mul_neg_of_pos_of_neg htp hxneg)
      have hneg : (-((b₀-a₀)⁻¹)*(zy-m)).im < 0 := by
        rw [neg_mul,Complex.neg_im,edgeHeight_shift,hm0,sub_zero,hzs]
        exact neg_neg_of_pos (mul_pos hsp hypos)
      have hequiv := C.isJordanCurve.mem_filledHull_iff_notMem_filledHull_of_locally_eq_line
        hline' hzxb hzyb hpos hneg
      by_contra hzyn
      exact hxzn (hequiv.mpr hzyn)
    · have hyneg := T.adjacent_third_height_neg hs ht hab hxy hxa hxb hya hyb hxpos
      have hpos : (((b₀-a₀)⁻¹)*(zx-m)).im > 0 := by
        rw [edgeHeight_shift,hm0,sub_zero,hzt]
        exact mul_pos htp hxpos
      have hneg : (((b₀-a₀)⁻¹)*(zy-m)).im < 0 := by
        rw [edgeHeight_shift,hm0,sub_zero,hzs]
        exact mul_neg_of_pos_of_neg hsp hyneg
      have hequiv := C.isJordanCurve.mem_filledHull_iff_notMem_filledHull_of_locally_eq_line
        hline hzxb hzyb hpos hneg
      by_contra hzyn
      exact hxzn (hequiv.mpr hzyn)
  exact ⟨(C.filledHull_iff_of_same_component hzyc).mpr hzyfilled,
    fun h => hyC ((C.point_mem_curve_iff y).mp h)⟩

end GraphCycle

end NormalProjective.Planar
