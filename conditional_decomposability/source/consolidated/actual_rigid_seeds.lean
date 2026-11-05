module
public import consolidated.rigid_tail_sets
public import consolidated_dev.actual_geometry
public import Mathlib.Combinatorics.SimpleGraph.Finite

set_option Elab.async false

section BundlePart0
/- Source: Papers/ActualTailGraph.lean -/




@[expose] public section
noncomputable section
namespace Papers.PolytopeFourRegularTail
open Set Module Papers.Polytopes
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {n : ℕ}
def smallTailGraph (P : ConvexPolytope n) (T : Finset (E n))
    (hTV : T ⊆ P.vertices) : SimpleGraph T where
  Adj x y := GeneralVertexStep P x.val y.val
  symm := ⟨by intro x y h; exact actualStep_symm (hTV x.property) h⟩
  loopless := ⟨by intro x h; exact h.2.1 rfl⟩
theorem smallTailGraph_degree_eq
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T ⊆ P.vertices) (v : T) :
    (smallTailGraph P T hTV).degree v =
      (T.filter (fun w => GeneralVertexStep P v.val w)).card := by
  let e : (smallTailGraph P T hTV).neighborSet v ≃
      (T.filter (fun w => GeneralVertexStep P v.val w)) := {
    toFun x := ⟨x.val.val,Finset.mem_filter.mpr ⟨x.val.property,x.property⟩⟩
    invFun x := ⟨⟨x.val,(Finset.mem_filter.mp x.property).1⟩,
      (Finset.mem_filter.mp x.property).2⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }
  simpa only [SimpleGraph.card_neighborSet_eq_degree,Fintype.card_coe] using
    Fintype.card_congr e
end Papers.PolytopeFourRegularTail


end
end
end BundlePart0

section BundlePart1
/- Source: Papers/PlanarEdgeStar.lean -/




@[expose] public section

/-! Three distinct actual edge rays at a vertex cannot lie in one plane. -/

noncomputable section
namespace Papers.Polytopes
open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem edges_distinct_at_vertex (P : ConvexPolytope d) {u v w : E d}
    (hu : u ∈ P.vertices) (hv : v ∈ P.vertices) (hw : w ∈ P.vertices)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    {F G : Set (E d)} (hF : P.IsFace F) (hG : P.IsFace G)
    (hdF : faceDim F = 1) (hdG : faceDim G = 1)
    (huF : u ∈ F) (hvF : v ∈ F) (huG : u ∈ G) (hwG : w ∈ G) : F ≠ G := by
  intro heq
  have hvG : v ∈ G := heq ▸ hvF
  rw [edge_eq_segment P hG hdG hu hw huG hwG huw] at hvG
  rcases (vertex_mem_segment_iff P hu hw hv).mp hvG with h | h
  · exact huv h.symm
  · exact hvw h

/-- This excludes the planar alternative in the K₂,₃ rigidity argument. -/
theorem no_three_edges_in_plane (P : ConvexPolytope d) {u v w z : E d}
    (hu : u ∈ P.vertices) (hv : v ∈ P.vertices)
    (hw : w ∈ P.vertices) (hz : z ∈ P.vertices)
    (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (huv : GeneralVertexStep P u v) (huw : GeneralVertexStep P u w)
    (huz : GeneralVertexStep P u z)
    (hplane : finrank ℝ (vectorSpan ℝ ({u, v, w, z} : Set (E d))) ≤ 2) : False := by
  let S : Finset (E d) := {u, v, w, z}
  have hS : S.Nonempty := ⟨u, by simp [S]⟩
  have hsub : S ⊆ P.vertices := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  let Q := vertexSubsetPolytope P S hS hsub
  have huQ : u ∈ Q.vertices := by change u ∈ S; simp [S]
  have hvQ : v ∈ Q.vertices := by change v ∈ S; simp [S]
  have hwQ : w ∈ Q.vertices := by change w ∈ S; simp [S]
  have hzQ : z ∈ Q.vertices := by change z ∈ S; simp [S]
  have hQvertices : (Q.vertices : Set (E d)) = {u, v, w, z} := by
    ext x
    simp [Q, vertexSubsetPolytope, S]
  have hdim : finrank ℝ (vectorSpan ℝ Q.toSet) = 2 := by
    rw [vectorSpan_polytope_vertices Q, hQvertices]
    have hnon := vertices_not_collinear P hu hv hw huv.2.1 huw.2.1 hvw
    have hlow : 2 ≤ finrank ℝ (vectorSpan ℝ ({u, v, w} : Set (E d))) := by
      have hn : ¬finrank ℝ (vectorSpan ℝ ({u, v, w} : Set (E d))) ≤ 1 := by
        intro h
        exact hnon (collinear_iff_finrank_le_one.mpr h)
      omega
    have hmono : finrank ℝ (vectorSpan ℝ ({u, v, w} : Set (E d))) ≤
        finrank ℝ (vectorSpan ℝ ({u, v, w, z} : Set (E d))) := by
      apply Submodule.finrank_mono
      apply vectorSpan_mono ℝ
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with h | h | h <;> tauto
    omega
  obtain ⟨_, huv', F, hF, hdF, huF, hvF⟩ := step_in_vertexSubset P S hS hsub huQ hvQ huv
  obtain ⟨_, huw', G, hG, hdG, huG, hwG⟩ := step_in_vertexSubset P S hS hsub huQ hwQ huw
  obtain ⟨_, huz', H, hH, hdH, huH, hzH⟩ := step_in_vertexSubset P S hS hsub huQ hzQ huz
  exact diamante_poligono Q hdim hF hdF hG hdG hH hdH
    (edges_distinct_at_vertex Q huQ hvQ hwQ huv' huw' hvw hF hG hdF hdG huF hvF huG hwG)
    (edges_distinct_at_vertex Q huQ hvQ hzQ huv' huz' hvz hF hH hdF hdH huF hvF huH hzH)
    (edges_distinct_at_vertex Q huQ hwQ hzQ huw' huz' hwz hG hH hdG hdH huG hwG huH hzH)
    huF huG huH

end Papers.Polytopes

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/ParallelFourCycle.lean -/



@[expose] public section

/-! A nonplanar four-cycle is parallel rigid. -/

noncomputable section
namespace Papers.Polytopes
open Set
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem homothety_along_parallel_edge (f : E d → E d) {u v : E d}
    {a : ℝ} {b : E d} (hu : f u = a • u + b)
    (hstep : f v - f u = a • (v - u)) : f v = a • v + b := by
  calc
    f v = (f v - f u) + f u := by abel
    _ = a • (v - u) + (a • u + b) := by rw [hstep, hu]
    _ = _ := by module

theorem homothetic_of_affine_cycle4 (p : Fin 4 → E d)
    (hp : AffineIndependent ℝ p) (f : E d → E d)
    (h01 : ∃ a : ℝ, f (p 1) - f (p 0) = a • (p 1 - p 0))
    (h12 : ∃ a : ℝ, f (p 2) - f (p 1) = a • (p 2 - p 1))
    (h23 : ∃ a : ℝ, f (p 3) - f (p 2) = a • (p 3 - p 2))
    (h30 : ∃ a : ℝ, f (p 0) - f (p 3) = a • (p 0 - p 3)) :
    HomotheticOn f (Set.range p) := by
  obtain ⟨a, ha⟩ := h01
  obtain ⟨b, hb⟩ := h12
  obtain ⟨c, hc⟩ := h23
  obtain ⟨e, he⟩ := h30
  have hlin : (e - a) • p 0 + (a - b) • p 1 + (b - c) • p 2 + (c - e) • p 3 = 0 := by
    calc
      _ = a • (p 1 - p 0) + b • (p 2 - p 1) + c • (p 3 - p 2) + e • (p 0 - p 3) := by module
      _ = (f (p 1) - f (p 0)) + (f (p 2) - f (p 1)) +
          (f (p 3) - f (p 2)) + (f (p 0) - f (p 3)) := by rw [ha, hb, hc, he]
      _ = 0 := by abel
  have hz := hp.eq_zero_of_sum_eq_zero (s := Finset.univ) (w := ![e - a, a - b, b - c, c - e])
    (by simp [Fin.sum_univ_succ])
    (by simpa [Fin.sum_univ_succ, add_assoc] using hlin)
  have hab : a = b := sub_eq_zero.mp (by simpa using hz 1 (Finset.mem_univ _))
  have hbc : b = c := sub_eq_zero.mp (by simpa using hz 2 (Finset.mem_univ _))
  subst b
  subst c
  let t : E d := f (p 0) - a • p 0
  have h0 : f (p 0) = a • p 0 + t := by dsimp [t]; abel
  have h1 := homothety_along_parallel_edge f h0 ha
  have h2 := homothety_along_parallel_edge f h1 hb
  have h3 := homothety_along_parallel_edge f h2 hc
  refine ⟨a, t, ?_⟩
  rintro v ⟨i, rfl⟩
  fin_cases i <;> assumption

theorem parallelRigid_affine_cycle4 (P : ConvexPolytope d) (p : Fin 4 → E d)
    (hp : AffineIndependent ℝ p)
    (h01 : GeneralVertexStep P (p 0) (p 1))
    (h12 : GeneralVertexStep P (p 1) (p 2))
    (h23 : GeneralVertexStep P (p 2) (p 3))
    (h30 : GeneralVertexStep P (p 3) (p 0)) : ParallelRigid P (Set.range p) := by
  intro f hf
  exact homothetic_of_affine_cycle4 p hp f
    (hf (p 0) (Set.mem_range_self 0) (p 1) (Set.mem_range_self 1) h01)
    (hf (p 1) (Set.mem_range_self 1) (p 2) (Set.mem_range_self 2) h12)
    (hf (p 2) (Set.mem_range_self 2) (p 3) (Set.mem_range_self 3) h23)
    (hf (p 3) (Set.mem_range_self 3) (p 0) (Set.mem_range_self 0) h30)

end Papers.Polytopes

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/ParallelK23.lean -/




@[expose] public section

/-!
# Rigidity of an actual K₂,₃

Two independent four-cycles are tested. If both were planar, the common
noncollinear triple would force all five vertices into one plane, contradicting
the three actual edges at one of the two degree-three vertices.
-/

noncomputable section
namespace Papers.Polytopes
open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem generalVertexStep_symm {P : ConvexPolytope d} {x y : E d}
    (hx : x ∈ P.vertices) (hxy : GeneralVertexStep P x y) : GeneralVertexStep P y x := by
  obtain ⟨_, hne, F, hF, hdF, hxF, hyF⟩ := hxy
  exact ⟨hx, hne.symm, F, hF, hdF, hyF, hxF⟩

theorem range_three (a b c : E d) : Set.range ![a, b, c] = ({a, b, c} : Set (E d)) := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

theorem range_four (a b c e : E d) : Set.range ![a, b, c, e] = ({a, b, c, e} : Set (E d)) := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩

theorem range_five (p : Fin 5 → E d) : Set.range p = ({p 0, p 1, p 2, p 3, p 4} : Set (E d)) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact Set.mem_range_self 0
    · exact Set.mem_range_self 1
    · exact Set.mem_range_self 2
    · exact Set.mem_range_self 3
    · exact Set.mem_range_self 4

/-- Planarity of a fourth point is membership in the plane spanned by any
noncollinear first three points; no projective general-position assumption is used. -/
theorem fourth_mem_plane {a b c x : E d}
    (hbase : AffineIndependent ℝ ![a, b, c])
    (hfour : ¬AffineIndependent ℝ ![a, b, c, x]) :
    x ∈ affineSpan ℝ ({a, b, c} : Set (E d)) := by
  have hd3 : finrank ℝ (vectorSpan ℝ ({a, b, c} : Set (E d))) = 2 := by
    have h := hbase.finrank_vectorSpan (n := 2) (Fintype.card_fin 3)
    rw [range_three a b c] at h
    exact h
  have hd4 : finrank ℝ (vectorSpan ℝ ({a, b, c, x} : Set (E d))) ≤ 2 := by
    have h := (finrank_vectorSpan_le_iff_not_affineIndependent ℝ ![a, b, c, x]
      (n := 2) (Fintype.card_fin 4)).mpr hfour
    rw [range_four a b c x] at h
    exact h
  have hsets : ({a, b, c} : Set (E d)) ⊆ {a, b, c, x} := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    tauto
  have hmono := Submodule.finrank_mono (vectorSpan_mono ℝ hsets)
  have hdim : finrank ℝ (affineSpan ℝ ({a, b, c, x} : Set (E d))).direction = 2 := by
    rw [direction_affineSpan]
    omega
  have hle : affineSpan ℝ (Set.range ![a, b, c]) ≤ affineSpan ℝ ({a, b, c, x} : Set (E d)) := by
    rw [range_three]
    exact affineSpan_mono ℝ hsets
  have heq := hbase.affineSpan_eq_of_le_of_card_eq_finrank_add_one hle (by rw [hdim]; rfl)
  rw [range_three] at heq
  rw [heq]
  exact subset_affineSpan ℝ _ (by simp)

theorem k23_has_nonplanar_cycle (P : ConvexPolytope d) (p : Fin 5 → E d)
    (hp : Function.Injective p) (hvertices : ∀ i, p i ∈ P.vertices)
    (h02 : GeneralVertexStep P (p 0) (p 2))
    (h03 : GeneralVertexStep P (p 0) (p 3))
    (h04 : GeneralVertexStep P (p 0) (p 4)) :
    AffineIndependent ℝ ![p 0, p 2, p 1, p 3] ∨
      AffineIndependent ℝ ![p 0, p 2, p 1, p 4] := by
  by_contra h
  push_neg at h
  have hbase : AffineIndependent ℝ ![p 0, p 2, p 1] :=
    affineIndependent_iff_not_collinear_set.mpr
      (vertices_not_collinear P (hvertices 0) (hvertices 2) (hvertices 1)
        (hp.ne (by decide)) (hp.ne (by decide)) (hp.ne (by decide)))
  let H := affineSpan ℝ ({p 0, p 2, p 1} : Set (E d))
  have h3 : p 3 ∈ H := fourth_mem_plane hbase h.1
  have h4 : p 4 ∈ H := fourth_mem_plane hbase h.2
  have hsub : ({p 0, p 2, p 3, p 4} : Set (E d)) ⊆ (H : Set (E d)) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact subset_affineSpan ℝ _ (by simp)
    · exact subset_affineSpan ℝ _ (by simp)
    · exact h3
    · exact h4
  have hspan : vectorSpan ℝ ({p 0, p 2, p 3, p 4} : Set (E d)) ≤ H.direction := by
    rw [AffineSubspace.direction_eq_vectorSpan]
    exact vectorSpan_mono ℝ hsub
  have hplane : finrank ℝ (vectorSpan ℝ ({p 0, p 2, p 3, p 4} : Set (E d))) ≤ 2 := by
    have hm := Submodule.finrank_mono hspan
    have hd3 := hbase.finrank_vectorSpan (n := 2) (Fintype.card_fin 3)
    rw [range_three] at hd3
    change finrank ℝ (vectorSpan ℝ ({p 0, p 2, p 3, p 4} : Set (E d))) ≤
      finrank ℝ (affineSpan ℝ ({p 0, p 2, p 1} : Set (E d))).direction at hm
    rw [direction_affineSpan,hd3] at hm
    exact hm
  exact no_three_edges_in_plane P (hvertices 0) (hvertices 2) (hvertices 3) (hvertices 4)
    (hp.ne (by decide)) (hp.ne (by decide)) (hp.ne (by decide)) h02 h03 h04 hplane

/-- All six edges are actual polytope edges. The conclusion is local
rigidity for every parallel map of the five-vertex induced geometric graph. -/
theorem parallelRigid_K23 (P : ConvexPolytope d) (p : Fin 5 → E d)
    (hp : Function.Injective p) (hvertices : ∀ i, p i ∈ P.vertices)
    (h02 : GeneralVertexStep P (p 0) (p 2))
    (h03 : GeneralVertexStep P (p 0) (p 3))
    (h04 : GeneralVertexStep P (p 0) (p 4))
    (h12 : GeneralVertexStep P (p 1) (p 2))
    (h13 : GeneralVertexStep P (p 1) (p 3))
    (h14 : GeneralVertexStep P (p 1) (p 4)) : ParallelRigid P (Set.range p) := by
  rcases k23_has_nonplanar_cycle P p hp hvertices h02 h03 h04 with h3 | h4
  · have hcycle := parallelRigid_affine_cycle4 P ![p 0, p 2, p 1, p 3] h3 h02
      (generalVertexStep_symm (hvertices 1) h12) h13
      (generalVertexStep_symm (hvertices 0) h03)
    have hsub : Set.range ![p 0, p 2, p 1, p 3] ⊆ (P.vertices : Set (E d)) := by
      rintro x ⟨i, rfl⟩
      fin_cases i <;> exact hvertices _
    have hrigid := hcycle.insert_two_neighbors hsub (hvertices 4)
      (Set.mem_range_self (f := ![p 0, p 2, p 1, p 3]) 0)
      (Set.mem_range_self (f := ![p 0, p 2, p 1, p 3]) 2)
      (hp.ne (by decide : (0 : Fin 5) ≠ 1)) h04 h14
    have hset : insert (p 4) (Set.range ![p 0, p 2, p 1, p 3]) = Set.range p := by
      rw [range_four, range_five]
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    exact hset ▸ hrigid
  · have hcycle := parallelRigid_affine_cycle4 P ![p 0, p 2, p 1, p 4] h4 h02
      (generalVertexStep_symm (hvertices 1) h12) h14
      (generalVertexStep_symm (hvertices 0) h04)
    have hsub : Set.range ![p 0, p 2, p 1, p 4] ⊆ (P.vertices : Set (E d)) := by
      rintro x ⟨i, rfl⟩
      fin_cases i <;> exact hvertices _
    have hrigid := hcycle.insert_two_neighbors hsub (hvertices 3)
      (Set.mem_range_self (f := ![p 0, p 2, p 1, p 4]) 0)
      (Set.mem_range_self (f := ![p 0, p 2, p 1, p 4]) 2)
      (hp.ne (by decide : (0 : Fin 5) ≠ 1)) h03 h13
    have hset : insert (p 3) (Set.range ![p 0, p 2, p 1, p 4]) = Set.range p := by
      rw [range_four, range_five]
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    exact hset ▸ hrigid

end Papers.Polytopes

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/ActualRigidity.lean -/




@[expose] public section
noncomputable section
namespace Papers.ActualRigidity
open Set Module Papers.Polytopes
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {n : ℕ}

def EdgeParallel (f : E n → E n) (x y : E n) : Prop :=
  ∃ μ : ℝ, f y-f x=μ•(y-x)

theorem EdgeParallel.symm {f : E n → E n} {x y : E n}
    (h : EdgeParallel f x y) : EdgeParallel f y x := by
  obtain ⟨μ,hμ⟩ := h
  refine ⟨μ,?_⟩
  calc
    f x-f y= -(f y-f x) := by abel
    _=μ•(x-y) := by rw [hμ]; module

theorem absorb_actual_two_neighbors
    (P : ConvexPolytope n) (x u v : P.vertices) (huv : u≠v)
    (hxu : GeneralVertexStep P x.val u.val)
    (hxv : GeneralVertexStep P x.val v.val)
    (f : E n → E n) (α : ℝ) (b : E n)
    (hu : f u.val=α•u.val+b) (hv : f v.val=α•v.val+b)
    (hpu : EdgeParallel f x.val u.val) (hpv : EdgeParallel f x.val v.val) :
    f x.val=α•x.val+b :=
  homothety_at_two_neighbors P f u.property x.property v.property
    (fun h => huv (Subtype.ext h)) hxu.2.1 hxv.2.1 hu hv hpu.symm hpv.symm

theorem pair_homothety
    (P : ConvexPolytope n) (x y : P.vertices)
    (hxy : GeneralVertexStep P x.val y.val) (f : E n → E n)
    (hp : EdgeParallel f x.val y.val) :
    ∃α:ℝ,∃b:E n,∀z∈({x.val,y.val}:Set (E n)),f z=α•z+b := by
  obtain ⟨α,hα⟩ := hp
  refine ⟨α,f x.val-α•x.val,?_⟩
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · module
  · have hz' := Set.mem_singleton_iff.mp hz
    subst z
    calc
      f y.val=(f y.val-f x.val)+f x.val := by abel
      _=α•y.val+(f x.val-α•x.val) := by rw [hα]; module

theorem triangle_homothety
    (P : ConvexPolytope n) (x y z : P.vertices)
    (hxy : GeneralVertexStep P x.val y.val)
    (hxz : GeneralVertexStep P x.val z.val)
    (hyz : GeneralVertexStep P y.val z.val)
    (f : E n → E n)
    (hp : EdgeParallel f x.val y.val)
    (hq : EdgeParallel f x.val z.val)
    (hr : EdgeParallel f y.val z.val) :
    ∃α:ℝ,∃b:E n,∀w∈({x.val,y.val,z.val}:Set (E n)),f w=α•w+b := by
  obtain ⟨α,b,hh⟩ := pair_homothety P x y hxy f hp
  have hz := absorb_actual_two_neighbors P z x y
    (fun h => hxy.2.1 (congrArg Subtype.val h))
    (actualStep_symm x.property hxz) (actualStep_symm y.property hyz)
    f α b (hh x.val (by simp)) (hh y.val (by simp)) hq.symm hr.symm
  refine ⟨α,b,?_⟩
  intro w hw
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl
  · exact hh x.val (by simp)
  · exact hh y.val (by simp)
  · exact hz

theorem k23_homothety
    (P : ConvexPolytope n) (u v : P.vertices) (p : Fin 3 → P.vertices)
    (huv : u≠v) (hp : Function.Injective p)
    (hu : ∀i,GeneralVertexStep P u.val (p i).val)
    (hv : ∀i,GeneralVertexStep P v.val (p i).val)
    (f : E n → E n)
    (hfu : ∀i,EdgeParallel f u.val (p i).val)
    (hfv : ∀i,EdgeParallel f v.val (p i).val) :
    ∃α:ℝ,∃b:E n,∀z∈insert u.val (insert v.val (Set.range (fun i => (p i).val))),
      f z=α•z+b := by
  let pts : Fin 5 → E n := ![u.val,v.val,(p 0).val,(p 1).val,(p 2).val]
  have huv' : u.val≠v.val := fun h => huv (Subtype.ext h)
  have h01 : (p 0).val≠(p 1).val := fun h => Fin.zero_ne_one (hp (Subtype.ext h))
  have h02 : (p 0).val≠(p 2).val := fun h => (by decide : (0:Fin 3)≠2) (hp (Subtype.ext h))
  have h12 : (p 1).val≠(p 2).val := fun h => (by decide : (1:Fin 3)≠2) (hp (Subtype.ext h))
  have hu0 := (hu 0).2.1
  have hu1 := (hu 1).2.1
  have hu2 := (hu 2).2.1
  have hv0 := (hv 0).2.1
  have hv1 := (hv 1).2.1
  have hv2 := (hv 2).2.1
  have hinj : Function.Injective pts := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [pts,Ne.symm]
  have hvertices : ∀i,pts i∈P.vertices := by
    intro i
    fin_cases i
    · exact u.property
    · exact v.property
    · exact (p 0).property
    · exact (p 1).property
    · exact (p 2).property
  have hnonplanar := k23_has_nonplanar_cycle P pts hinj hvertices (hu 0) (hu 1) (hu 2)
  have hex : ∃i:Fin 3,AffineIndependent ℝ ![u.val,(p 0).val,v.val,(p i).val] := by
    rcases hnonplanar with h | h
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
  obtain ⟨i,hi⟩ := hex
  obtain ⟨α,b,hh⟩ := homothetic_of_affine_cycle4
    ![u.val,(p 0).val,v.val,(p i).val] hi f
    (hfu 0) (hfv 0).symm (hfv i) (hfu i).symm
  have huH : f u.val=α•u.val+b := hh u.val ⟨0,rfl⟩
  have hvH : f v.val=α•v.val+b := hh v.val ⟨2,rfl⟩
  have hpH (j:Fin 3) : f (p j).val=α•(p j).val+b :=
    absorb_actual_two_neighbors P (p j) u v huv
      (actualStep_symm u.property (hu j)) (actualStep_symm v.property (hv j))
      f α b huH hvH (hfu j).symm (hfv j).symm
  refine ⟨α,b,?_⟩
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · exact huH
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · exact hvH
  obtain ⟨j,rfl⟩ := hz
  exact hpH j
end Papers.ActualRigidity


end
end
end BundlePart4

section BundlePart5
/- Source: Papers/ActualRigidSeedLimits.lean -/






@[expose] public section

noncomputable section
namespace Papers.ActualRigidSeedLimits
open Set Module Finset Papers.Polytopes
open Papers.PolytopeFourRegularTail Papers.NeighborhoodCounts Papers.ActualRigidity
open Papers.SmallNeighborComponents
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical BigOperators
variable {n : ℕ}

def vertexOfTail (P : ConvexPolytope n) (T : Finset (E n))
    (hTV : T ⊆ P.vertices) (v : T) : P.vertices :=
  ⟨v.val,hTV v.property⟩

theorem neighbor_matchings_of_no_rigid_four
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T ⊆ P.vertices)
    (hno : ∀ A : Finset (E n), A ⊆ T → A.card = 4 → ¬ RigidInTail P T A) :
    ∀ v a : T, a ∈ (smallTailGraph P T hTV).neighborFinset v →
      localDegree (smallTailGraph P T hTV)
        ((smallTailGraph P T hTV).neighborFinset v) a ≤ 1 := by
  intro v a ha
  let G := smallTailGraph P T hTV
  have hva : G.Adj v a := (G.mem_neighborFinset _ _).mp ha
  apply Finset.card_le_one.mpr
  intro b hb c hc
  obtain ⟨hbN,hab⟩ := Finset.mem_filter.mp hb
  obtain ⟨hcN,hac⟩ := Finset.mem_filter.mp hc
  have hvb : G.Adj v b := (G.mem_neighborFinset _ _).mp hbN
  have hvc : G.Adj v c := (G.mem_neighborFinset _ _).mp hcN
  by_contra hbc
  let A : Finset (E n) := {v.val,a.val,b.val,c.val}
  have hbcval : b.val ≠ c.val := fun h => hbc (Subtype.ext h)
  have hAT : A ⊆ T := by
    intro z hz
    simp only [A,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact v.property
    · exact a.property
    · exact b.property
    · exact c.property
  have hAc : A.card = 4 := by
    have hva' := hva.2.1
    have hvb' := hvb.2.1
    have hvc' := hvc.2.1
    have hab' := hab.2.1
    have hac' := hac.2.1
    simp [A,hva',hvb',hvc',hab',hac',hbcval,
      Ne.symm hva',Ne.symm hvb',Ne.symm hvc',
      Ne.symm hab',Ne.symm hac',Ne.symm hbcval]
  apply hno A hAT hAc
  intro f hf
  obtain ⟨α,q,htriangle⟩ := triangle_homothety P
    (vertexOfTail P T hTV v) (vertexOfTail P T hTV a)
    (vertexOfTail P T hTV b) hva hvb hab f
    (hf v.val v.property a.val a.property hva)
    (hf v.val v.property b.val b.property hvb)
    (hf a.val a.property b.val b.property hab)
  simp only [vertexOfTail] at htriangle
  have hcv : GeneralVertexStep P c.val v.val := actualStep_symm (hTV v.property) hvc
  have hca : GeneralVertexStep P c.val a.val := actualStep_symm (hTV a.property) hac
  have hvc_ne : vertexOfTail P T hTV v ≠ vertexOfTail P T hTV a := by
    intro h
    apply hva.2.1
    change (vertexOfTail P T hTV v).val = (vertexOfTail P T hTV a).val
    exact congrArg Subtype.val h
  have hcvalue := absorb_actual_two_neighbors P
    (vertexOfTail P T hTV c) (vertexOfTail P T hTV v)
    (vertexOfTail P T hTV a) hvc_ne hcv hca f α q
    (htriangle v.val (by simp)) (htriangle a.val (by simp))
    (hf c.val c.property v.val v.property hcv)
    (hf c.val c.property a.val a.property hca)
  refine ⟨α,q,?_⟩
  intro z hz
  simp only [A,Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact htriangle v.val (by simp)
  · exact htriangle a.val (by simp)
  · exact htriangle b.val (by simp)
  · exact hcvalue

theorem common_neighbors_le_two_of_no_rigid_four
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T ⊆ P.vertices)
    (hno : ∀ A : Finset (E n), A ⊆ T → A.card = 4 → ¬ RigidInTail P T A) :
    ∀ v w : T, w ∈ outsideStar (smallTailGraph P T hTV) v →
      localDegree (smallTailGraph P T hTV)
        ((smallTailGraph P T hTV).neighborFinset v) w ≤ 2 := by
  intro v w hw
  let G := smallTailGraph P T hTV
  have hwv : w ≠ v := by
    have h := (Finset.mem_sdiff.mp hw).2
    intro heq
    exact h (Finset.mem_insert.mpr (Or.inl heq))
  by_contra hlarge
  have hthree : 3 ≤ ((G.neighborFinset v).filter (G.Adj w)).card := by
    change ¬ ((G.neighborFinset v).filter (G.Adj w)).card ≤ 2 at hlarge
    omega
  obtain ⟨S,hS,hSc⟩ := Finset.exists_subset_card_eq hthree
  let e : Fin 3 ≃ S := (Fintype.equivFinOfCardEq (by simpa using hSc)).symm
  let a : Fin 3 → T := fun i => (e i).val
  let points : Fin 3 → P.vertices := fun i => vertexOfTail P T hTV (a i)
  have ha : ∀ i, a i ∈ (G.neighborFinset v).filter (G.Adj w) :=
    fun i => hS (e i).property
  have hvEdges : ∀ i, GeneralVertexStep P v.val (points i).val :=
    fun i => (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp (ha i)).1
  have hwEdges : ∀ i, GeneralVertexStep P w.val (points i).val :=
    fun i => (Finset.mem_filter.mp (ha i)).2
  have hinj : Function.Injective points := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    apply Subtype.ext
    change (points i).val = (points j).val
    exact congrArg Subtype.val hij
  have hvw : vertexOfTail P T hTV v ≠ vertexOfTail P T hTV w := by
    intro h
    exact hwv (Subtype.ext (congrArg Subtype.val h).symm)
  let A : Finset (E n) := {v.val,w.val,(points 0).val,(points 1).val}
  have hp01 : (points 0).val ≠ (points 1).val := by
    intro h
    have hi : (0 : Fin 3) = 1 := hinj (Subtype.ext h)
    exact (by decide : (0 : Fin 3) ≠ 1) hi
  have hAT : A ⊆ T := by
    intro z hz
    simp only [A,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact v.property
    · exact w.property
    · exact (a 0).property
    · exact (a 1).property
  have hvwval : v.val ≠ w.val := fun h => hwv (Subtype.ext h.symm)
  have hAc : A.card = 4 := by
    have hv0 := (hvEdges 0).2.1
    have hv1 := (hvEdges 1).2.1
    have hw0 := (hwEdges 0).2.1
    have hw1 := (hwEdges 1).2.1
    simp [A,hvwval,hv0,hv1,hw0,hw1,hp01,
      Ne.symm hvwval,Ne.symm hv0,Ne.symm hv1,Ne.symm hw0,Ne.symm hw1,Ne.symm hp01]
  apply hno A hAT hAc
  intro f hf
  obtain ⟨α,q,hhom⟩ := k23_homothety P
    (vertexOfTail P T hTV v) (vertexOfTail P T hTV w)
    points hvw hinj hvEdges hwEdges f
    (fun i => hf v.val v.property (points i).val (a i).property (hvEdges i))
    (fun i => hf w.val w.property (points i).val (a i).property (hwEdges i))
  refine ⟨α,q,?_⟩
  intro z hz
  apply hhom z
  simp only [A,Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨0,rfl⟩)
  · exact Or.inr (Or.inr ⟨1,rfl⟩)


end Papers.ActualRigidSeedLimits

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/SmallGraphRigidSeed.lean -/



@[expose] public section

noncomputable section
namespace Papers.PolytopeFourRegularTail
open Set Finset Papers.Polytopes Papers.ActualRigidSeedLimits Papers.NeighborhoodCounts
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical BigOperators
variable {n : ℕ}

theorem exists_rigid_three_of_min_three
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T ⊆ P.vertices)
    (hne : T.Nonempty) (hcard : T.card ≤ 7)
    (hmin : ∀ x ∈ T, 3 ≤ (T.filter (fun y => GeneralVertexStep P x y)).card) :
    ∃ A ⊆ T, 3 ≤ A.card ∧ RigidInTail P T A := by
  by_contra! hno
  let G := smallTailGraph P T hTV
  letI : Nonempty T := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  have hGmin (v : T) : 3 ≤ G.degree v := by
    rw [smallTailGraph_degree_eq]
    exact hmin v.val v.property
  have hno4 (A : Finset (E n)) (hAT : A ⊆ T) (hc : A.card=4) :
      ¬ RigidInTail P T A := hno A hAT (by omega)
  have hcap := common_neighbors_le_two_of_no_rigid_four P T hTV hno4
  have hzero (v w : T) (hw : w ∈ G.neighborFinset v) :
      localDegree G (G.neighborFinset v) w = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨huN,hwu⟩ := Finset.mem_filter.mp hu
    have hvw : GeneralVertexStep P v.val w.val := (G.mem_neighborFinset _ _).mp hw
    have hvu : GeneralVertexStep P v.val u.val := (G.mem_neighborFinset _ _).mp huN
    have hwu' : GeneralVertexStep P w.val u.val := hwu
    let A : Finset (E n) := {v.val,w.val,u.val}
    have hAT : A ⊆ T := by
      intro x hx
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact v.property
      · exact w.property
      · exact u.property
    have hAc : A.card=3 := by
      simp [A,hvw.2.1,hvu.2.1,hwu'.2.1,
        Ne.symm hvw.2.1,Ne.symm hvu.2.1,Ne.symm hwu'.2.1]
    exact hno A hAT (by omega)
      (rigid_triangle hTV v.property w.property u.property hvw hvu hwu')
  have hreg (v : T) : G.degree v=3 := by
    have hb := neighborhood_cut_bound G v 3 2 hGmin (hcap v)
    rw [outsideStar_card] at hb
    have hs : (∑ w ∈ G.neighborFinset v, localDegree G (G.neighborFinset v) w)=0 :=
      Finset.sum_eq_zero (hzero v)
    rw [hs] at hb
    have hc : Fintype.card T ≤ 7 := by simpa only [Fintype.card_coe] using hcard
    have hd := hGmin v
    have hlt := G.degree_lt_card_verts v
    omega
  have hseven : Fintype.card T=7 := by
    let v : T := Classical.choice inferInstance
    have hb := neighborhood_cut_bound G v 3 2 hGmin (hcap v)
    rw [outsideStar_card,hreg] at hb
    have hs : (∑ w ∈ G.neighborFinset v, localDegree G (G.neighborFinset v) w)=0 :=
      Finset.sum_eq_zero (hzero v)
    rw [hs] at hb
    have hc : Fintype.card T ≤ 7 := by simpa only [Fintype.card_coe] using hcard
    omega
  have hparity := G.sum_degrees_eq_twice_card_edges
  simp only [hreg, Finset.sum_const, Finset.card_univ, hseven, smul_eq_mul] at hparity
  omega

theorem exists_rigid_four_of_min_large
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T ⊆ P.vertices)
    (hne : T.Nonempty) (k : ℕ) (hk : 5 ≤ k) (hcard : T.card ≤ 4*k-6)
    (hmin : ∀ x ∈ T, k ≤ (T.filter (fun y => GeneralVertexStep P x y)).card) :
    ∃ A ⊆ T, 4 ≤ A.card ∧ RigidInTail P T A := by
  by_contra! hno
  let G := smallTailGraph P T hTV
  letI : Nonempty T := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  have hGmin (v : T) : k ≤ G.degree v := by
    rw [smallTailGraph_degree_eq]
    exact hmin v.val v.property
  have hno4 (A : Finset (E n)) (hAT : A ⊆ T) (hc : A.card=4) :
      ¬ RigidInTail P T A := hno A hAT (by omega)
  have hcap := common_neighbors_le_two_of_no_rigid_four P T hTV hno4
  have hmatch := neighbor_matchings_of_no_rigid_four P T hTV hno4
  by_cases hk5 : k=5
  · subst k
    exact Papers.NeighborhoodParity.impossible_min_five_order_at_most_fourteen G
      (by simpa only [Fintype.card_coe] using hcard) hGmin hcap hmatch
  · let v : T := Classical.choice inferInstance
    have hb := neighborhood_cut_bound G v k 2 hGmin (hcap v)
    rw [outsideStar_card] at hb
    have hs : (∑ w ∈ G.neighborFinset v,
        localDegree G (G.neighborFinset v) w) ≤ G.degree v := by
      calc
        _ ≤ ∑ w ∈ G.neighborFinset v, (1:ℕ) := Finset.sum_le_sum (hmatch v)
        _ = _ := by simp
    have hc : Fintype.card T ≤ 4*k-6 := by simpa only [Fintype.card_coe] using hcard
    have hd := hGmin v
    have hlt := G.degree_lt_card_verts v
    have hk6 : 6 ≤ k := by omega
    have hbound : G.degree v*k ≤ 8*k-14 := by omega
    have hsquare : k*k ≤ 8*k-14 := (Nat.mul_le_mul_right k hd).trans hbound
    have hnonneg : 0 ≤ (k-6)*(k-2) := Nat.zero_le _
    have h2 : 2 ≤ k := by omega
    have h6 : k-6+6=k := Nat.sub_add_cancel hk6
    have htwo : k-2+2=k := Nat.sub_add_cancel h2
    have h14 : 14 ≤ 8*k := by omega
    have hsub : 8*k-14+14=8*k := Nat.sub_add_cancel h14
    nlinarith

end Papers.PolytopeFourRegularTail

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/RigidTailCovers.lean -/



@[expose] public section

noncomputable section
namespace Papers.PolytopeFourRegularTail
open Set Finset
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical
variable {n : ℕ}

def HasRigidCover (P : ConvexPolytope n) (T : Finset (E n)) (m : ℕ) : Prop :=
  ∃ C : Finset (Finset (E n)), C.card ≤ m ∧
    (∀ A ∈ C, A ⊆ T ∧ RigidInTail P T A) ∧
    ∀ x ∈ T, ∃ A ∈ C, x ∈ A

theorem rigidCover_empty (P : ConvexPolytope n) (m : ℕ) :
    HasRigidCover P ∅ m := by
  refine ⟨∅, by simp, ?_, ?_⟩ <;> simp

theorem HasRigidCover.mono {P : ConvexPolytope n} {T : Finset (E n)} {k m : ℕ}
    (h : HasRigidCover P T k) (hkm : k ≤ m) : HasRigidCover P T m := by
  obtain ⟨C,hC,hR,hcover⟩ := h
  exact ⟨C,hC.trans hkm,hR,hcover⟩

theorem rigidCover_single {P : ConvexPolytope n} {T : Finset (E n)}
    (h : RigidInTail P T T) : HasRigidCover P T 1 := by
  refine ⟨{T}, by simp, ?_, ?_⟩
  · intro A hA
    have he := Finset.mem_singleton.mp hA
    subst A
    exact ⟨Finset.Subset.refl _,h⟩
  · intro x hx
    exact ⟨T,Finset.mem_singleton_self _,hx⟩

theorem rigidCover_pair {P : ConvexPolytope n} {T A B : Finset (E n)}
    (hAT : A ⊆ T) (hBT : B ⊆ T) (hAB : A ∪ B = T)
    (hA : RigidInTail P T A) (hB : RigidInTail P T B) : HasRigidCover P T 2 := by
  refine ⟨{A,B}, Finset.card_le_two, ?_, ?_⟩
  · intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · exact ⟨hAT,hA⟩
    · exact ⟨hBT,hB⟩
  · intro x hx
    rw [← hAB] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact ⟨A,by simp,hx⟩
    · exact ⟨B,by simp,hx⟩

theorem HasRigidCover.adjoin {P : ConvexPolytope n} {T A : Finset (E n)} {m : ℕ}
    (h : HasRigidCover P (T \ A) m) (hAT : A ⊆ T) (hA : RigidInTail P T A) :
    HasRigidCover P T (m+1) := by
  obtain ⟨C,hC,hR,hcover⟩ := h
  refine ⟨insert A C, (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hC 1), ?_, ?_⟩
  · intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact ⟨hAT,hA⟩
    · exact ⟨(hR B hB).1.trans Finset.sdiff_subset,
        (hR B hB).2.mono_tail Finset.sdiff_subset⟩
  · intro x hx
    by_cases hxA : x ∈ A
    · exact ⟨A,Finset.mem_insert_self _ _,hxA⟩
    · obtain ⟨B,hB,hxB⟩ := hcover x (Finset.mem_sdiff.mpr ⟨hx,hxA⟩)
      exact ⟨B,Finset.mem_insert_of_mem hB,hxB⟩

/-- A cover is supplied to the homothety-parameter argument with its
actual finite index type and its original vertex membership. -/
theorem HasRigidCover.indexed {P : ConvexPolytope n} {T : Finset (E n)} {m : ℕ}
    (h : HasRigidCover P T m) :
    ∃ (I : Type) (_ : Fintype I), ∃ A : I → Finset (E n),
      Fintype.card I ≤ m ∧ (∀ i, A i ⊆ T) ∧
      (∀ i, RigidInTail P T (A i)) ∧ ∀ x ∈ T, ∃ i, x ∈ A i := by
  obtain ⟨C,hC,hR,hcover⟩ := h
  refine ⟨C,inferInstance,Subtype.val,?_,?_,?_,?_⟩
  · simpa only [Fintype.card_coe] using hC
  · exact fun i => (hR i.val i.property).1
  · exact fun i => (hR i.val i.property).2
  · intro x hx
    obtain ⟨A,hA,hxA⟩ := hcover x hx
    exact ⟨⟨A,hA⟩,hxA⟩

end Papers.PolytopeFourRegularTail

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/SmallTailRigidCover.lean -/





@[expose] public section

noncomputable section
namespace Papers.PolytopeFourRegularTail
open Set Finset Papers.Polytopes Papers.FiniteMatchingCovers
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical
variable {n : ℕ}

def ambientActualGraph (P : ConvexPolytope n) : SimpleGraph (E n) where
  Adj x y := x ∈ P.vertices ∧ GeneralVertexStep P x y
  symm := ⟨by
    intro x y h
    exact ⟨h.2.1, actualStep_symm h.1 h.2⟩⟩
  loopless := ⟨by intro x h; exact h.2.2.1 rfl⟩

theorem rigid_of_min_two_card_le_three
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T ⊆ P.vertices)
    (hcard : T.card ≤ 3)
    (hmin : ∀ x ∈ T, 2 ≤ (T.filter (fun y => GeneralVertexStep P x y)).card) :
    RigidInTail P T T := by
  by_cases hne : T.Nonempty
  · have hcomplete {x y : E n} (hx : x∈T) (hy : y∈T) (hxy : x≠y) :
        GeneralVertexStep P x y := by
      have hsub : T.filter (fun z => GeneralVertexStep P x z) ⊆ T.erase x := by
        intro z hz
        obtain ⟨hzT,hxz⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_erase.mpr ⟨hxz.2.1.symm,hzT⟩
      have he : T.filter (fun z => GeneralVertexStep P x z) = T.erase x := by
        apply Finset.eq_of_subset_of_card_le hsub
        rw [Finset.card_erase_of_mem hx]
        have hm := hmin x hx
        omega
      have hyf : y ∈ T.filter (fun z => GeneralVertexStep P x z) := by
        rw [he]
        exact Finset.mem_erase.mpr ⟨hxy.symm,hy⟩
      exact (Finset.mem_filter.mp hyf).2
    obtain ⟨x,hx⟩ := hne
    have hm := hmin x hx
    obtain ⟨y,hy⟩ := Finset.card_pos.mp (by omega :
      0 < (T.filter (fun z => GeneralVertexStep P x z)).card)
    obtain ⟨hyT,hxy⟩ := Finset.mem_filter.mp hy
    intro f hf
    obtain ⟨a,b,hab⟩ := (rigid_pair hx hyT hxy) f hf
    refine ⟨a,b,?_⟩
    intro z hz
    by_cases hzx : z=x
    · subst z; exact hab x (by simp)
    by_cases hzy : z=y
    · subst z; exact hab y (by simp)
    exact homothety_at_two_neighbors P f (hTV hx) (hTV hz) (hTV hyT)
      hxy.2.1 hzx hzy (hab x (by simp)) (hab y (by simp))
      (hf x hx z hz (hcomplete hx hz (Ne.symm hzx)))
      (hf y hyT z hz (hcomplete hyT hz (Ne.symm hzy)))
  · have he : T=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst T
    exact rigid_empty P ∅

theorem rigidCover_two_of_min_two_card_le_four
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T ⊆ P.vertices)
    (hcard : T.card ≤ 4)
    (hmin : ∀ x ∈ T, 2 ≤ (T.filter (fun y => GeneralVertexStep P x y)).card) :
    HasRigidCover P T 2 := by
  by_cases hc3 : T.card≤3
  · exact (rigidCover_single (rigid_of_min_two_card_le_three P T hTV hc3 hmin)).mono (by omega)
  have hc4 : T.card=4 := by omega
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,hT⟩ := Finset.card_eq_four.mp hc4
  let G := ambientActualGraph P
  have hdeg : ∀ x∈({a,b,c,d}:Finset (E n)),
      2≤(({a,b,c,d}:Finset (E n)).filter (G.Adj x)).card := by
    intro x hx
    have hxT : x∈T := hT.symm ▸ hx
    have he : ({a,b,c,d}:Finset (E n)).filter (G.Adj x) =
        T.filter (fun y => GeneralVertexStep P x y) := by
      ext y
      simp only [Finset.mem_filter, ambientActualGraph, G]
      rw [hT]
      tauto
    rw [he]
    exact hmin x hxT
  have hmatch := matching_cover_of_four_min_degree_two G a b c d
    hab hac had hbc hbd hcd hdeg
  have haT : a∈T := by simp [hT]
  have hbT : b∈T := by simp [hT]
  have hcT : c∈T := by simp [hT]
  have hdT : d∈T := by simp [hT]
  have cover (u v w z : E n) (hu : u∈T) (hv : v∈T) (hw : w∈T) (hz : z∈T)
      (he : ({u,v}:Finset (E n)) ∪ {w,z}=T)
      (huv : G.Adj u v) (hwz : G.Adj w z) : HasRigidCover P T 2 := by
    apply rigidCover_pair (A := {u,v}) (B := {w,z})
    · intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · exact he
    · exact rigid_pair hu hv huv.2
    · exact rigid_pair hw hz hwz.2
  rcases hmatch with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩
  · apply cover a b c d haT hbT hcT hdT _ h1 h2
    ext x
    simp only [hT,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  · apply cover a c b d haT hcT hbT hdT _ h1 h2
    ext x
    simp only [hT,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  · apply cover a d b c haT hdT hbT hcT _ h1 h2
    ext x
    simp only [hT,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto

/-- Lemma 14, with the complete seven-vertex range. -/
theorem rigidCover_three_of_min_three_card_le_seven
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T ⊆ P.vertices)
    (hcard : T.card ≤ 7)
    (hmin : ∀ x ∈ T, 3 ≤ (T.filter (fun y => GeneralVertexStep P x y)).card) :
    HasRigidCover P T 3 := by
  by_cases hne : T.Nonempty
  · obtain ⟨B,hBT,hBc,hBR⟩ := exists_rigid_three_of_min_three P T hTV hne hcard hmin
    obtain ⟨A,hA⟩ := exists_largest_rigid P T
    have hAc : 3≤A.card := hBc.trans (hA.largest B hBT hBR)
    have hrem := Finset.card_sdiff_add_card_eq_card hA.subset
    have htail : (T \ A).card≤4 := by omega
    have hdegree := hA.residual_min_degree hTV 2 hmin
    exact (rigidCover_two_of_min_two_card_le_four P (T \ A)
      (Finset.sdiff_subset.trans hTV) htail hdegree).adjoin hA.subset hA.rigid
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    exact rigidCover_empty P 3

/-- The six-vertex conclusion of Lemma 14. -/
theorem rigidCover_two_of_min_three_card_le_six
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T ⊆ P.vertices)
    (hcard : T.card ≤ 6)
    (hmin : ∀ x ∈ T, 3 ≤ (T.filter (fun y => GeneralVertexStep P x y)).card) :
    HasRigidCover P T 2 := by
  by_cases hne : T.Nonempty
  · obtain ⟨B,hBT,hBc,hBR⟩ := exists_rigid_three_of_min_three P T hTV hne (by omega) hmin
    obtain ⟨A,hA⟩ := exists_largest_rigid P T
    have hAc : 3≤A.card := hBc.trans (hA.largest B hBT hBR)
    have hrem := Finset.card_sdiff_add_card_eq_card hA.subset
    have htail : (T \ A).card≤3 := by omega
    have hdegree := hA.residual_min_degree hTV 2 hmin
    exact (rigidCover_single (rigid_of_min_two_card_le_three P (T \ A)
      (Finset.sdiff_subset.trans hTV) htail hdegree)).adjoin hA.subset hA.rigid
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    exact rigidCover_empty P 2

end Papers.PolytopeFourRegularTail

end
end
end BundlePart8

