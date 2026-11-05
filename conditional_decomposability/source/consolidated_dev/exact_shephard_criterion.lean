module
public import consolidated_dev.minkowski_map_core
public import consolidated.actual_facet_hitting
public import Mathlib.Analysis.Convex.Segment

set_option Elab.async false

section BundlePart0
/- Source: Papers/ExactShephardFacet.lean -/





@[expose] public section

/-! A Shephard facet stated entirely using actual faces and actual edges. -/
noncomputable section
namespace Papers.ActualPaperCoverReduction

open Set
open Papers.PolytopeVertexCone Papers.ActualFaceOrder Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n m : ℕ}

def ExactShephardFacet (P : ConvexPolytope n) : Prop :=
  ∃ F : Set (E n),P.IsFace F ∧ faceDim F+1=n ∧
    2≤(P.vertices.filter (fun x => x∉F)).card ∧
    ∀ v∈P.vertices,v∈F →
      ((actualNeighbors P v).filter (fun y => y∉F)).card=1

theorem unique_exit_of_card_one
    (P : ConvexPolytope n) {F : Set (E n)} {v : E n}
    (h : ((actualNeighbors P v).filter (fun y => y∉F)).card=1) :
    ∃! y : E n,GeneralVertexStep P v y ∧ y∉F := by
  simpa only [Finset.mem_filter,mem_actualNeighbors_iff] using
    Finset.card_eq_one_iff_existsUnique.mp h

theorem card_one_of_unique_exit
    (P : ConvexPolytope n) {F : Set (E n)} {v : E n}
    (h : ∃! y : E n,GeneralVertexStep P v y ∧ y∉F) :
    ((actualNeighbors P v).filter (fun y => y∉F)).card=1 := by
  apply Finset.card_eq_one_iff_existsUnique.mpr
  simpa only [Finset.mem_filter,mem_actualNeighbors_iff] using h

theorem filter_vertex_card_transport
    {P : ConvexPolytope n} {Q : ConvexPolytope m}
    (e : FaceObject P ≃o FaceObject Q)
    (a : E n → Prop) (b : E m → Prop)
    (h : ∀ v : P.vertices,b (vertexEquiv e v).val ↔ a v.val) :
    (P.vertices.filter a).card=(Q.vertices.filter b).card := by
  classical
  refine Finset.card_bij
    (fun x hx => (vertexEquiv e ⟨x,(Finset.mem_filter.mp hx).1⟩).val) ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_filter.mpr ⟨(vertexEquiv e _).property,
      (h _).mpr (Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy heq
    exact congrArg Subtype.val ((vertexEquiv e).injective (Subtype.ext heq))
  · intro y hy
    let x := (vertexEquiv e).symm ⟨y,(Finset.mem_filter.mp hy).1⟩
    have hax : a x.val := (h x).mp (by
      simpa only [x,Equiv.apply_symm_apply] using (Finset.mem_filter.mp hy).2)
    refine ⟨x.val,Finset.mem_filter.mpr ⟨x.property,hax⟩,?_⟩
    exact congrArg Subtype.val ((vertexEquiv e).apply_symm_apply _)

theorem exactShephardFacet_transport
    {P : ConvexPolytope n} {Q : ConvexPolytope n}
    (e : FaceObject P ≃o FaceObject Q)
    (h : ExactShephardFacet P) : ExactShephardFacet Q := by
  obtain ⟨F,hF,hdim,hout,hexit⟩ := h
  let FF : FaceObject P := ⟨F,hF⟩
  let G := (e FF).val
  refine ⟨G,(e FF).property,?_,?_,?_⟩
  · rw [show faceDim G=faceDim F from faceDim_image e FF]
    exact hdim
  · obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hout
    let xx : P.vertices := ⟨x,(Finset.mem_filter.mp hx).1⟩
    let yy : P.vertices := ⟨y,(Finset.mem_filter.mp hy).1⟩
    apply Finset.one_lt_card.mpr
    refine ⟨(vertexEquiv e xx).val,?_,(vertexEquiv e yy).val,?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨(vertexEquiv e xx).property,
        fun h => (Finset.mem_filter.mp hx).2 ((vertex_mem_face_iff e xx FF).mp h)⟩
    · exact Finset.mem_filter.mpr ⟨(vertexEquiv e yy).property,
        fun h => (Finset.mem_filter.mp hy).2 ((vertex_mem_face_iff e yy FF).mp h)⟩
    · intro he
      exact hxy (congrArg Subtype.val ((vertexEquiv e).injective (Subtype.ext he)))
  · intro y hy hyG
    let x := (vertexEquiv e).symm ⟨y,hy⟩
    have hxeq : (vertexEquiv e x).val=y := by
      exact congrArg Subtype.val ((vertexEquiv e).apply_symm_apply _)
    have hxF : x.val∈F := (vertex_mem_face_iff e x FF).mp (by simpa only [hxeq] using hyG)
    obtain ⟨z,hz,hunique⟩ := unique_exit_of_card_one P (hexit x.val x.property hxF)
    let zz : P.vertices := ⟨z,hz.1.1⟩
    apply card_one_of_unique_exit Q
    refine ⟨(vertexEquiv e zz).val,?_,?_⟩
    · refine ⟨?_,?_⟩
      · simpa only [hxeq] using (edge_iff e x zz).mpr hz.1
      · exact fun hh => hz.2 ((vertex_mem_face_iff e zz FF).mp hh)
    · intro w hw
      let ww := (vertexEquiv e).symm ⟨w,hw.1.1⟩
      have hweq : (vertexEquiv e ww).val=w :=
        congrArg Subtype.val ((vertexEquiv e).apply_symm_apply _)
      have hxw : GeneralVertexStep P x.val ww.val := (edge_iff e x ww).mp
        (by simpa only [hxeq,hweq] using hw.1)
      have hwF : ww.val∉F := fun hh => hw.2 (by
        have him := (vertex_mem_face_iff e ww FF).mpr hh
        simpa only [hweq] using him)
      have hwz : ww=zz := Subtype.ext (hunique ww.val ⟨hxw,hwF⟩)
      calc
        w = (vertexEquiv e ww).val := hweq.symm
        _ = (vertexEquiv e zz).val := by rw [hwz]

end Papers.ActualPaperCoverReduction


end
end
end BundlePart0

section BundlePart1
/- Source: Papers/ShephardActiveFacets.lean -/




@[expose] public section

/-!
# Active facet normals and the Shephard construction

A facet distinct from F and incident to a vertex of F contains that
vertex's unique exterior neighbour.  Also, annihilating the common
active halfspace normals of an actual edge forces a vector to be
parallel to that edge.  Both statements concern genuine polytope
faces and edges; no face-incidence certificate is an input.
-/

noncomputable section
namespace Papers.ShephardActiveFacets

open Set Module
open Papers.FiniteGraphOptimization Papers.FiniteHalfspaceVertexSeparation
open Papers.PolytopeVertexCone Papers.PolytopeSimpleTailFace Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n : ℕ}

theorem other_facet_contains_unique_exit
    (P : ConvexPolytope n) {F G : Set (E n)}
    (hF : P.IsFace F) (hG : P.IsFace G)
    (hFG : faceDim F=faceDim G) (hne : G≠F)
    {v z : E n} (hv : v∈P.vertices) (hvF : v∈F) (hvG : v∈G)
    (hz : GeneralVertexStep P v z) (hzF : z∉F)
    (hunique : ∀ y,GeneralVertexStep P v y → y∉F → y=z) :
    z∈G := by
  by_contra hzG
  let Q := facePolytope P hG
  have hvQ : v∈Q.vertices :=
    (facePolytope_vertex_iff P hG v).mpr ⟨hv,hvG⟩
  obtain ⟨g,hgpos,hgF⟩ := exists_nonnegative_affine_face_form P F hF
  have hgv : g v=0 := (hgF v (vertex_mem_body_of_mem_vertices P hv)).mpr hvF
  have hneighbors : ∀ y,GeneralVertexStep Q v y → y∈F := by
    intro y hy
    by_contra hyF
    have hyz := hunique y (facePolytope_step P hG hy) hyF
    have hyG := ((facePolytope_vertex_iff P hG y).mp hy.1).2
    exact hzG (hyz ▸ hyG)
  have hspan : neighborSpan Q v≤g.linear.ker := by
    apply Submodule.span_le.mpr
    rintro t ⟨y,hy,rfl⟩
    have hyP := ((facePolytope_vertex_iff P hG y).mp hy.1).1
    have hgy : g y=0 :=
      (hgF y (vertex_mem_body_of_mem_vertices P hyP)).mpr (hneighbors y hy)
    change g.linear (y-v)=0
    have hh := g.linear_apply_vsub y v
    simpa only [vsub_eq_sub,hgy,hgv,sub_self] using hh
  have hdirQ : vectorSpan ℝ Q.toSet≤g.linear.ker := by
    rw [← neighborSpan_eq_vectorSpan Q hvQ]
    exact hspan
  have hdir : vectorSpan ℝ G≤g.linear.ker := by
    simpa only [Q,facePolytope_toSet] using hdirQ
  have hsub : G⊆F := by
    intro w hw
    have hh := hdir (vsub_mem_vectorSpan ℝ hw hvG)
    change g.linear (w-v)=0 at hh
    have hvsub := g.linear_apply_vsub w v
    have hgw : g w=0 := by
      simpa only [vsub_eq_sub,hh,hgv,sub_zero] using hvsub.symm
    exact (hgF w (face_subset_toSet P hG hw)).mp hgw
  have hproper : G⊂F := lt_of_le_of_ne hsub hne
  have hlt := faceDim_lt_of_ssubset P hG hF hproper
  omega

theorem exists_symmetric_feasible_perturbation
    (P : ConvexPolytope n) {I : Type*} [Fintype I]
    (g : I → E n →ᵃ[ℝ] ℝ)
    (hrep : ∀ x,x∈P.toSet ↔ ∀ i,0≤g i x)
    {v : E n} (hv : v∈P.toSet)
    (z : E n) (hz : ∀ i,g i v=0 → (g i).linear z=0) :
    ∃ ε : ℝ,0<ε ∧ v+ε•z∈P.toSet ∧ v-ε•z∈P.toSet := by
  have hnonneg := (hrep v).mp hv
  let S := Finset.univ.filter (fun i : I => 0<g i v)
  obtain ⟨ε,hε,hbound⟩ := exists_small_positive_perturbation S
    (fun i => g i v) (fun i => -|(g i).linear z|)
    (fun i hi => (Finset.mem_filter.mp hi).2)
  have hpm (t : ℝ) (ht : t=ε ∨ t= -ε) : v+t•z∈P.toSet := by
    apply (hrep _).mpr
    intro i
    rw [affine_add_smul]
    by_cases hi : g i v=0
    · rw [hi,hz i hi,mul_zero,add_zero]
    · have hipos : 0<g i v := lt_of_le_of_ne (hnonneg i) (Ne.symm hi)
      have hsmall := hbound ε hε le_rfl i
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hipos⟩)
      have ha := neg_abs_le ((g i).linear z)
      have hb := le_abs_self ((g i).linear z)
      have hmulA := mul_le_mul_of_nonneg_left ha hε.le
      have hmulB := mul_le_mul_of_nonneg_left hb hε.le
      rcases ht with rfl | rfl <;> nlinarith
  refine ⟨ε,hε,hpm ε (Or.inl rfl),?_⟩
  simpa only [neg_smul,sub_eq_add_neg] using hpm (-ε) (Or.inr rfl)

theorem parallel_of_active_edge_normals
    (P : ConvexPolytope n) {I : Type*} [Fintype I]
    (g : I → E n →ᵃ[ℝ] ℝ)
    (hrep : ∀ x,x∈P.toSet ↔ ∀ i,0≤g i x)
    {x y : E n} (hx : x∈P.vertices) (hxy : GeneralVertexStep P x y)
    (z : E n)
    (hz : ∀ i,g i x=0 → g i y=0 → (g i).linear z=0) :
    ∃ μ : ℝ,z=μ•(y-x) := by
  let v := midpoint ℝ x y
  have hxP := vertex_mem_body_of_mem_vertices P hx
  have hyP := vertex_mem_body_of_mem_vertices P hxy.1
  have hvP : v∈P.toSet := (convex_convexHull ℝ _).midpoint_mem hxP hyP
  have hvE : v∈segment ℝ x y := midpoint_mem_segment (𝕜 := ℝ) x y
  have hactive : ∀ i,g i v=0 → (g i).linear z=0 := by
    intro i hi
    have hxnonneg := (hrep x).mp hxP i
    have hynonneg := (hrep y).mp hyP i
    have hsum : g i v+g i v=g i x+g i y := by
      change g i (midpoint ℝ x y)+g i (midpoint ℝ x y)=_
      rw [AffineMap.map_midpoint]
      exact midpoint_add_self ℝ (g i x) (g i y)
    exact hz i (by linarith) (by linarith)
  obtain ⟨ε,hε,hplus,hminus⟩ :=
    exists_symmetric_feasible_perturbation P g hrep hvP z hactive
  have hE := segment_isFace_of_generalVertexStep P hx hxy
  obtain ⟨u,hu⟩ := hE.1 hE.2
  have hvmax := hvE
  rw [hu] at hvmax
  have hupper := hvmax.2 (v+ε•z) hplus
  have hlower := hvmax.2 (v-ε•z) hminus
  simp only [map_add,map_sub,map_smul,smul_eq_mul] at hupper hlower
  have huz : u z=0 := by nlinarith
  have hplusE : v+ε•z∈segment ℝ x y := by
    rw [hu]
    refine ⟨hplus,?_⟩
    intro w hw
    simpa only [map_add,map_smul,huz,smul_zero,add_zero] using hvmax.2 w hw
  obtain ⟨lam,μ,hlampos,hμpos,hunit,hcomb⟩ := hplusE
  have hlam : lam=1-μ := by linarith
  have hvform : v=(1/2:ℝ)•x+(1/2:ℝ)•y := by
    have hmid : v+v=x+y := midpoint_add_self ℝ x y
    calc
      v = (1/2:ℝ)•(v+v) := by module
      _ = (1/2:ℝ)•(x+y) := by rw [hmid]
      _ = (1/2:ℝ)•x+(1/2:ℝ)•y := by module
  have hvec : ε•z=(μ-1/2)•(y-x) := by
    calc
      ε•z = (v+ε•z)-v := by abel
      _ = (lam•x+μ•y)-v := by rw [hcomb]
      _ = (μ-1/2)•(y-x) := by rw [hlam,hvform]; module
  refine ⟨ε⁻¹*(μ-1/2),?_⟩
  calc
    z = ε⁻¹•(ε•z) := by rw [smul_smul,inv_mul_cancel₀ hε.ne',one_smul]
    _ = ε⁻¹•((μ-1/2)•(y-x)) := by rw [hvec]
    _ = (ε⁻¹*(μ-1/2))•(y-x) := by rw [smul_smul]

end Papers.ShephardActiveFacets

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/ExactShephardCriterion.lean -/







@[expose] public section

/-!
# Shephard's criterion from the actual facet normals

The normalized exterior-edge map has normal value one on the chosen
facet, and normal value zero on every other active facet. Its edge
differences annihilate the common active normals, hence are parallel
to actual edges. Two exterior vertices rule out a global homothety.
-/

noncomputable section
namespace Papers.ExactShephardCriterion

open Set
open Papers.ActualPaperCoverReduction Papers.ActualFaceOrder
open Papers.ShephardActiveFacets Papers.Polytopes
open Papers.PolytopeSimpleTailFace
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n : ℕ}

theorem decomposable_of_exact_shephard_facet
    (P : ConvexPolytope n) (hP : P.IsFullDim)
    (h : ExactShephardFacet P) : MinkowskiDecomposable P := by
  obtain ⟨F,hF,hdim,houtside,hone⟩ := h
  have hfacet : IsFacet P F := ⟨hF,hdim.trans hP.symm⟩
  let FF : FacetType P := ⟨⟨F,hF⟩,hfacet⟩
  let g := chosenFacetForm P
  let s := g FF
  have hs : SupportsFace P F s := chosenFacetForm_supports P FF
  have hexit : ∀ v∈P.vertices,v∈F →
      ∃! z : E n,GeneralVertexStep P v z ∧ z∉F :=
    fun v hv hvF => unique_exit_of_card_one P (hone v hv hvF)
  let z : E n → E n := fun v =>
    if hv : v∈P.vertices ∧ v∈F then (hexit v hv.1 hv.2).choose else 0
  have hz (v : E n) (hv : v∈P.vertices) (hvF : v∈F) :
      GeneralVertexStep P v (z v) ∧ z v∉F ∧
        ∀ y,GeneralVertexStep P v y → y∉F → y=z v := by
    have he := (hexit v hv hvF).choose_spec
    dsimp only [z]
    rw [dif_pos ⟨hv,hvF⟩]
    exact ⟨he.1.1,he.1.2,fun y hy hyF => he.2 y ⟨hy,hyF⟩⟩
  have hsz (v : E n) (hv : v∈P.vertices) (hvF : v∈F) : 0<s (z v) := by
    have hzz := hz v hv hvF
    have hbody := vertex_mem_body_of_mem_vertices P hzz.1.1
    apply lt_of_le_of_ne (hs.1 (z v) hbody)
    exact fun heq => hzz.2.1 ((hs.mem_iff _).mpr ⟨hbody,heq.symm⟩)
  let f : E n → E n := fun v => if v∈F then (s (z v))⁻¹ • (z v-v) else 0
  have hfoutside (v : E n) (hv : v∉F) : f v=0 := by simp only [f,if_neg hv]
  have hfchosen (v : E n) (hv : v∈P.vertices) (hvF : v∈F) :
      s.linear (f v)=1 := by
    have hlin : s.linear (z v-v)=s (z v)-s v := by
      simpa only [vsub_eq_sub] using s.linear_apply_vsub (z v) v
    simp only [f,if_pos hvF,map_smul,hlin,hs.eq_zero hvF,sub_zero,
      smul_eq_mul,inv_mul_cancel₀ (hsz v hv hvF).ne']
  have hfother (i : FacetType P) (hi : i≠FF)
      (v : E n) (hv : v∈P.vertices) (hvi : v∈i.val.val) :
      (g i).linear (f v)=0 := by
    by_cases hvF : v∈F
    · have hzi := hz v hv hvF
      have hine : i.val.val≠F := by
        intro heq
        exact hi (Subtype.ext (Subtype.ext heq))
      have hdim' : faceDim F=faceDim i.val.val := by
        have hiDim := i.property.2
        have hFDim := hfacet.2
        omega
      have hzI : z v∈i.val.val := other_facet_contains_unique_exit P
        hF i.val.property hdim' hine hv hvF hvi hzi.1 hzi.2.1 hzi.2.2
      have hgi := chosenFacetForm_supports P i
      have hlin : (g i).linear (z v-v)=g i (z v)-g i v := by
        simpa only [vsub_eq_sub] using (g i).linear_apply_vsub (z v) v
      have hgz : g i (z v)=0 := hgi.eq_zero hzI
      have hgv : g i v=0 := hgi.eq_zero hvi
      simp only [f,if_pos hvF,map_smul,hlin,hgz,hgv,sub_self,smul_zero]
    · rw [hfoutside v hvF,map_zero]
  have hfparallel : IsParallelMap P f := by
    intro x hx y hy hxy
    apply parallel_of_active_edge_normals P g
      (mem_body_iff_chosenFacetForms_nonneg P hP) hx hxy (f y-f x)
    intro i hix hiy
    have hxI : x∈i.val.val := ((chosenFacetForm_supports P i).mem_iff x).mpr
      ⟨vertex_mem_body_of_mem_vertices P hx,hix⟩
    have hyI : y∈i.val.val := ((chosenFacetForm_supports P i).mem_iff y).mpr
      ⟨vertex_mem_body_of_mem_vertices P hy,hiy⟩
    rw [map_sub]
    by_cases hi : i=FF
    · subst i
      rw [hfchosen y hy hyI,hfchosen x hx hxI,sub_self]
    · rw [hfother i hi y hy hyI,hfother i hi x hx hxI,sub_self]
  apply (minkowski_decomposable_iff_parallel_map P).mpr
  refine ⟨f,hfparallel,?_⟩
  rintro ⟨α,b,hhom⟩
  obtain ⟨x,hx,y,hy,hxy⟩ :=
    Finset.one_lt_card.mp (show 1<(P.vertices.filter (fun x => x∉F)).card by omega)
  have hxP := (Finset.mem_filter.mp hx).1
  have hxF := (Finset.mem_filter.mp hx).2
  have hyP := (Finset.mem_filter.mp hy).1
  have hyF := (Finset.mem_filter.mp hy).2
  have hparams : α=0 ∧ b=0 := homothety_parameters_unique hxy
    (by simpa only [hfoutside x hxF,zero_smul,zero_add] using (hhom x hxP).symm)
    (by simpa only [hfoutside y hyF,zero_smul,zero_add] using (hhom y hyP).symm)
  obtain ⟨v,hv⟩ := (facePolytope P hF).vertices_nonempty
  have hv' := (facePolytope_vertex_iff P hF v).mp hv
  have hvzero : f v=0 := by
    simpa only [hparams.1,hparams.2,zero_smul,zero_add] using hhom v hv'.1
  have hval := hfchosen v hv'.1 hv'.2
  rw [hvzero,map_zero] at hval
  exact zero_ne_one hval

theorem decomposable_after_iso_of_exact_shephard_facet
    (P : ConvexPolytope n) (h : ExactShephardFacet P)
    (Q : ConvexPolytope n) (hQ : Q.IsFullDim)
    (e : FaceObject P ≃o FaceObject Q) : MinkowskiDecomposable Q :=
  decomposable_of_exact_shephard_facet Q hQ (exactShephardFacet_transport e h)

end Papers.ExactShephardCriterion


end
end
end BundlePart2

section BundlePart3
/- Source: Papers/FaceWithOneExit.lean -/





@[expose] public section

/-! A proper face with at most one outside neighbor at each vertex is a facet. -/
noncomputable section
namespace Papers.Polytopes

open Set Module
open Papers.PolytopeVertexCone Papers.PolytopeBalinski
open Papers.ActualPaperCoverReduction
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n : ℕ}

theorem exists_neighbor_outside_face
    (P : ConvexPolytope n) (F : Set (E n)) (hF : P.IsFace F)
    {x w : E n} (hx : x∈P.vertices) (hxF : x∈F)
    (hw : w∈P.vertices) (hwF : w∉F) :
    ∃y,GeneralVertexStep P x y ∧ y∉F := by
  obtain ⟨g,hgpos,hgzero⟩ := exists_nonnegative_affine_face_form P F hF
  have hxT : x∈P.toSet := subset_convexHull ℝ _ hx
  have hwT : w∈P.toSet := subset_convexHull ℝ _ hw
  have hgx : g x=0 := (hgzero x hxT).mpr hxF
  have hgw : 0<g w := lt_of_le_of_ne (hgpos w hwT)
    (by intro h; exact hwF ((hgzero w hwT).mp h.symm))
  have hlt : g.linear.toContinuousLinearMap x < g.linear.toContinuousLinearMap w := by
    change g.linear x<g.linear w
    rw [affine_form_apply g x] at hgx
    rw [affine_form_apply g w] at hgw
    linarith
  obtain ⟨y,hxy,hheight⟩ := exists_improving_neighbor P g.linear.toContinuousLinearMap hx hw hlt
  refine ⟨y,hxy,?_⟩
  intro hyF
  have hgy := (hgzero y (subset_convexHull ℝ _ hxy.1)).mpr hyF
  change g.linear x<g.linear y at hheight
  rw [affine_form_apply g x] at hgx
  rw [affine_form_apply g y] at hgy
  linarith

theorem face_is_facet_of_one_exit
    (P : ConvexPolytope n) (hP : P.IsFullDim)
    (F : Set (E n)) (hF : P.IsFace F)
    (hw : ∃w∈P.vertices,w∉F)
    (hexit : ∀x∈P.vertices,x∈F →
      ((actualNeighbors P x).filter fun y => y∉F).card≤1) :
    faceDim F+1=n := by
  obtain ⟨w,hw,hwF⟩ := hw
  obtain ⟨x,hx⟩ := (facePolytope P hF).vertices_nonempty
  have hxV : x∈P.vertices := (Finset.mem_filter.mp hx).1
  have hxF : x∈F := (Finset.mem_filter.mp hx).2
  obtain ⟨z,hxz,hzF⟩ := exists_neighbor_outside_face P F hF hxV hxF hw hwF
  have hzN : z∈(actualNeighbors P x).filter fun y => y∉F :=
    Finset.mem_filter.mpr ⟨(mem_actualNeighbors_iff P x z).mpr hxz,hzF⟩
  let L := vectorSpan ℝ F
  let Z := Submodule.span ℝ ({z-x} : Set (E n))
  have hle : neighborSpan P x≤L⊔Z := by
    apply Submodule.span_le.mpr
    rintro u ⟨y,hxy,rfl⟩
    by_cases hyF : y∈F
    · exact (show L≤L⊔Z from le_sup_left) (vsub_mem_vectorSpan ℝ hyF hxF)
    · have hyN : y∈(actualNeighbors P x).filter fun y => y∉F :=
        Finset.mem_filter.mpr ⟨(mem_actualNeighbors_iff P x y).mpr hxy,hyF⟩
      have hyz := Finset.card_le_one.mp (hexit x hxV hxF) y hyN z hzN
      subst y
      exact (show Z≤L⊔Z from le_sup_right) (Submodule.mem_span_singleton_self _)
  have hrank := Submodule.finrank_mono hle
  rw [neighborSpan_eq_top P hP hxV] at hrank
  have hsup := Submodule.finrank_add_le_finrank_add_finrank L Z
  have hZ : finrank ℝ Z=1 :=
    finrank_span_singleton (sub_ne_zero.mpr hxz.2.1.symm)
  have hE : finrank ℝ (⊤ : Submodule ℝ (E n))=n := by simp [E]
  rw [hE] at hrank
  have hproper : F⊂P.toSet := (face_subset_toSet P hF).ssubset_of_ne (by
    intro heq
    apply hwF
    rw [heq]
    exact subset_convexHull ℝ _ hw)
  have hdimlt := faceDim_lt_of_ssubset P hF (toSet_isFace P) hproper
  change faceDim F<P.dim at hdimlt
  have hL : finrank ℝ L=faceDim F := rfl
  change P.dim=n at hP
  omega

theorem exactShephardFacet_of_face_with_one_exit
    (P : ConvexPolytope n) (hP : P.IsFullDim)
    (F : Set (E n)) (hF : P.IsFace F)
    (houtside : 2≤(P.vertices.filter fun x => x∉F).card)
    (hexit : ∀x∈P.vertices,x∈F →
      ((actualNeighbors P x).filter fun y => y∉F).card≤1) :
    ExactShephardFacet P := by
  obtain ⟨w,hw⟩ := Finset.card_pos.mp (show 0<(P.vertices.filter fun x => x∉F).card by omega)
  have hwV := (Finset.mem_filter.mp hw).1
  have hwF := (Finset.mem_filter.mp hw).2
  refine ⟨F,hF,face_is_facet_of_one_exit P hP F hF ⟨w,hwV,hwF⟩ hexit,houtside,?_⟩
  intro x hx hxF
  obtain ⟨y,hxy,hyF⟩ := exists_neighbor_outside_face P F hF hx hxF hwV hwF
  have hpos : 0<((actualNeighbors P x).filter fun y => y∉F).card :=
    Finset.card_pos.mpr ⟨y,Finset.mem_filter.mpr
      ⟨(mem_actualNeighbors_iff P x y).mpr hxy,hyF⟩⟩
  have hle := hexit x hx hxF
  omega

end Papers.Polytopes

end
end
end BundlePart3
