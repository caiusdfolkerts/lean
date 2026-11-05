module
public import consolidated.four_tail_rigid_cover
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.LinearCombination

set_option Elab.async false

section BundlePart0
/- Source: Papers/FacetHittingRigidity.lean -/







@[expose] public section

/-!
# A rigid set meeting every facet forces global homothety

This linear-algebra lemma is the form used with actual facet normals.
The geometric adapter supplies constancy of normal components along a
face and the fact that incident facet normals jointly separate vectors
at a vertex.  Consequently, if every nonsimple vertex belongs to a rigid
set in a decomposable polytope, some all-simple facet avoids that set.
-/

namespace Papers.FacetHitting

variable {V I E : Type*} [AddCommGroup E] [Module ℝ E]

theorem homothety_of_meets_every_facet
    (point value : V → E) (incident : I → V → Prop)
    (normal : I → E →ₗ[ℝ] ℝ) (R : Set V)
    (hposition : ∀ i v w, incident i v → incident i w →
      normal i (point v - point w) = 0)
    (hparallel : ∀ i v w, incident i v → incident i w →
      normal i (value v - value w) = 0)
    (hseparate : ∀ v z, (∀ i, incident i v → normal i z = 0) → z = 0)
    (alpha : ℝ) (b : E)
    (hR : ∀ v ∈ R, value v = alpha • point v + b)
    (hmeets : ∀ i, ∃ v ∈ R, incident i v) :
    ∀ v, value v = alpha • point v + b := by
  intro v
  apply sub_eq_zero.mp
  apply hseparate v
  intro i hiv
  obtain ⟨w, hwR, hiw⟩ := hmeets i
  have hp := hparallel i v w hiv hiw
  have hx := hposition i v w hiv hiw
  rw [hR w hwR] at hp
  simp only [map_sub, map_add, map_smul, smul_eq_mul] at hp hx ⊢
  linear_combination hp - alpha * hx

theorem exists_facet_avoiding_homothetic_set
    (point value : V → E) (incident : I → V → Prop)
    (normal : I → E →ₗ[ℝ] ℝ) (R : Set V)
    (hposition : ∀ i v w, incident i v → incident i w →
      normal i (point v - point w) = 0)
    (hparallel : ∀ i v w, incident i v → incident i w →
      normal i (value v - value w) = 0)
    (hseparate : ∀ v z, (∀ i, incident i v → normal i z = 0) → z = 0)
    (hR : ∃ alpha : ℝ, ∃ b : E, ∀ v ∈ R, value v = alpha • point v + b)
    (hnontrivial : ¬ ∃ alpha : ℝ, ∃ b : E,
      ∀ v, value v = alpha • point v + b) :
    ∃ i, ∀ v, incident i v → v ∉ R := by
  classical
  by_contra! h
  have hmeet : ∀ i, ∃ v ∈ R, incident i v := by
    intro i
    obtain ⟨v, hiv, hvR⟩ := h i
    exact ⟨v, hvR, hiv⟩
  obtain ⟨alpha, b, hab⟩ := hR
  exact hnontrivial ⟨alpha, b,
    homothety_of_meets_every_facet point value incident normal R
      hposition hparallel hseparate alpha b hab hmeet⟩

end Papers.FacetHitting

end
end BundlePart0

section BundlePart1
/- Source: Papers/FiniteHalfspaceVertexSeparation.lean -/








@[expose] public section

/-!
# Incident halfspace normals separate at an actual vertex

A finite halfspace description gives the separation property used in
the facet-hitting argument.  The proof constructs both small signed
perturbations inside the polytope and uses actual vertex extremality.
The halfspace description is a supporting lemma input, not an axiom;
the actual facet presentation is constructed separately.
-/

noncomputable section
namespace Papers.FiniteHalfspaceVertexSeparation

open Set Module
open Papers.FiniteGraphOptimization Papers.FacetHitting
open Papers.PolytopeFourRegularTail Papers.PolytopeBalinski
open Papers.PolytopeSimpleTailFace Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n : ℕ} {I : Type*} [Fintype I]

theorem parallel_value_difference_mem_face_direction
    (P : ConvexPolytope n) (f : E n → E n)
    (hf : ParallelOnTail P P.vertices f)
    {F : Set (E n)} (hF : P.IsFace F)
    {x y : E n} (hx : x ∈ (facePolytope P hF).vertices)
    (hy : y ∈ (facePolytope P hF).vertices) :
    f y - f x ∈ vectorSpan ℝ F := by
  let R := facePolytope P hF
  let xx : R.vertices := ⟨x,hx⟩
  let yy : R.vertices := ⟨y,hy⟩
  have hedge {a b : R.vertices} (hab : (vertexGraph R).Adj a b) :
      f b.val - f a.val ∈ vectorSpan ℝ F := by
    have ha := (facePolytope_vertex_iff P hF a.val).mp a.property
    have hb := (facePolytope_vertex_iff P hF b.val).mp b.property
    obtain ⟨μ,hμ⟩ := hf a.val ha.1 b.val hb.1 (facePolytope_step P hF hab)
    rw [hμ]
    exact (vectorSpan ℝ F).smul_mem μ (vsub_mem_vectorSpan ℝ hb.2 ha.2)
  have hwalk {a b : R.vertices} (p : (vertexGraph R).Walk a b) :
      f b.val - f a.val ∈ vectorSpan ℝ F := by
    induction p with
    | nil => simpa only [sub_self] using (vectorSpan ℝ F).zero_mem
    | cons hab p ih =>
        have h := (vectorSpan ℝ F).add_mem ih (hedge hab)
        simpa only [sub_add_sub_cancel] using h
  obtain ⟨p⟩ := (vertexGraph_connected R).preconnected xx yy
  exact hwalk p


theorem affine_add_smul (g : E n →ᵃ[ℝ] ℝ) (v z : E n) (t : ℝ) :
    g (v+t•z) = g v+t*g.linear z := by
  have h := g.map_vadd v (t•z)
  simpa only [vadd_eq_add,map_smul,smul_eq_mul,add_comm] using h

theorem incident_normals_separate
    (P : ConvexPolytope n)
    (g : I → E n →ᵃ[ℝ] ℝ)
    (hrep : ∀ x, x∈P.toSet ↔ ∀ i, 0≤g i x)
    {v : E n} (hv : v∈P.vertices)
    (z : E n) (hz : ∀ i, g i v=0 → (g i).linear z=0) : z=0 := by
  have hvP := vertex_mem_body_of_mem_vertices P hv
  have hnonneg := (hrep v).mp hvP
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
  have hminus : v-ε•z∈P.toSet := by
    simpa only [neg_smul,sub_eq_add_neg] using hpm (-ε) (Or.inr rfl)
  have hplus : v+ε•z∈P.toSet := hpm ε (Or.inl rfl)
  have hseg : v∈segment ℝ (v-ε•z) (v+ε•z) := mem_segment_sub_add (𝕜 := ℝ) v (ε•z)
  have hend := ExposedEdgeCenters.extreme_point_on_segment P.toSet
    (vertex_mem_body_extremePoints P hv) hminus hplus hseg
  have hscale : ε•z=0 := by
    rcases hend with hm | hp
    · have hh : v-(v-ε•z)=0 := sub_eq_zero.mpr hm
      simpa only [sub_sub_cancel] using hh
    · have hh := congrArg (fun x : E n => x-v) hp
      simpa only [sub_self,add_sub_cancel_left] using hh.symm
  exact (smul_eq_zero.mp hscale).resolve_left hε.ne'

theorem affine_zero_direction
    (g : E n →ᵃ[ℝ] ℝ) {F : Set (E n)}
    (hzero : ∀ x∈F,g x=0) :
    vectorSpan ℝ F ≤ g.linear.ker := by
  by_cases hne : F.Nonempty
  · obtain ⟨x,hx⟩ := hne
    rw [vectorSpan_eq_span_vsub_set_right ℝ hx]
    apply Submodule.span_le.mpr
    rintro z ⟨y,hy,rfl⟩
    change g.linear (y-x)=0
    have h := g.linear_apply_vsub y x
    simpa only [vsub_eq_sub,hzero y hy,hzero x hx,sub_self] using h
  · have hF : F=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [hF,vectorSpan_empty,bot_le]

theorem parallel_normal_constant_on_zero_face
    (P : ConvexPolytope n) (f : E n → E n)
    (hf : ParallelOnTail P P.vertices f)
    (g : E n →ᵃ[ℝ] ℝ)
    (hface : P.IsFace {x∈P.toSet | g x=0})
    {x y : E n} (hx : x∈P.vertices) (hy : y∈P.vertices)
    (hgx : g x=0) (hgy : g y=0) :
    g.linear (f y-f x)=0 := by
  have hxF : x∈(facePolytope P hface).vertices :=
    (facePolytope_vertex_iff P hface x).mpr
      ⟨hx,vertex_mem_body_of_mem_vertices P hx,hgx⟩
  have hyF : y∈(facePolytope P hface).vertices :=
    (facePolytope_vertex_iff P hface y).mpr
      ⟨hy,vertex_mem_body_of_mem_vertices P hy,hgy⟩
  exact (affine_zero_direction g (fun _ h => h.2))
    (parallel_value_difference_mem_face_direction P f hf hface hxF hyF)

/-- Every nonhomothetic parallel map that is homothetic on R has a
facet avoiding R, once the finite actual facet presentation is supplied. -/
theorem exists_zero_face_avoiding_homothetic_vertices
    (P : ConvexPolytope n) (f : E n → E n)
    (hf : ParallelOnTail P P.vertices f)
    (g : I → E n →ᵃ[ℝ] ℝ)
    (hrep : ∀ x, x∈P.toSet ↔ ∀ i,0≤g i x)
    (hface : ∀ i,P.IsFace {x∈P.toSet | g i x=0})
    (R : Finset (E n)) (hRsub : R⊆P.vertices)
    (hR : ∃ α : ℝ,∃ b : E n,∀ x∈R,f x=α•x+b)
    (hnontrivial : ¬ ∃ α : ℝ,∃ b : E n,∀ x∈P.vertices,f x=α•x+b) :
    ∃ i,∀ x∈R,g i x≠0 := by
  let point : P.vertices → E n := fun x => x.val
  let value : P.vertices → E n := fun x => f x.val
  let incident : I → P.vertices → Prop := fun i x => g i x.val=0
  let normal : I → E n →ₗ[ℝ] ℝ := fun i => (g i).linear
  let R' : Set P.vertices := {x | x.val∈R}
  have hposition : ∀ i v w,incident i v → incident i w →
      normal i (point v-point w)=0 := by
    intro i v w hv hw
    change g i v.val=0 at hv
    change g i w.val=0 at hw
    change (g i).linear (v.val-w.val)=0
    have h := (g i).linear_apply_vsub v.val w.val
    simpa only [vsub_eq_sub,hv,hw,sub_self] using h
  have hparallel : ∀ i v w,incident i v → incident i w →
      normal i (value v-value w)=0 := by
    intro i v w hv hw
    exact parallel_normal_constant_on_zero_face P f hf (g i) (hface i)
      w.property v.property hw hv
  have hseparate : ∀ v z,(∀ i,incident i v → normal i z=0) → z=0 :=
    fun v z hz => incident_normals_separate P g hrep v.property z hz
  have hR' : ∃ α : ℝ,∃ b : E n,∀ v∈R',value v=α•point v+b := by
    obtain ⟨α,b,h⟩ := hR
    exact ⟨α,b,fun v hv => h v.val hv⟩
  have hn' : ¬ ∃ α : ℝ,∃ b : E n,∀ v,value v=α•point v+b := by
    rintro ⟨α,b,h⟩
    exact hnontrivial ⟨α,b,fun x hx => h ⟨x,hx⟩⟩
  obtain ⟨i,hi⟩ := exists_facet_avoiding_homothetic_set point value incident normal R'
    hposition hparallel hseparate hR' hn'
  refine ⟨i,?_⟩
  intro x hx hgx
  exact hi ⟨x,hRsub hx⟩ hgx hx

end Papers.FiniteHalfspaceVertexSeparation

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/ActualPolytopeCoordinates.lean -/



@[expose] public section
noncomputable section
namespace Papers.ActualPolytopeCoordinates
open Set Module Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical
variable {n : ℕ}

theorem exists_actual_facet_halfspaces (P : ConvexPolytope n) (hP : P.IsFullDim) :
    ∃ (I : Type) (_ : Fintype I) (g : I→E n→ᵃ[ℝ]ℝ),
      (∀x,x∈P.toSet ↔ ∀i,0≤g i x) ∧
      ∀i,P.IsFace {x∈P.toSet | g i x=0} ∧
        faceDim {x∈P.toSet | g i x=0}+1=n := by
  refine ⟨FacetType P,inferInstance,chosenFacetForm P,
    mem_body_iff_chosenFacetForms_nonneg P hP,?_⟩
  intro F
  have he := (chosenFacetForm_supports P F).2
  rw [←he]
  exact ⟨F.val.property,F.property.2.trans hP⟩

end Papers.ActualPolytopeCoordinates

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/ActualFacetHitting.lean -/




@[expose] public section

/-!
# The actual facet-hitting reduction

A nonhomothetic parallel map that is homothetic on a vertex set R
misses R on some genuine facet.  If R contains every nonsimple vertex,
that facet has exactly one outside neighbour at each vertex.  Two
vertices of R ensure that the outside of the facet is nontrivial.
The finite halfspace presentation is constructed from the actual
polytope and is not a hypothesis of the endpoint.
-/

noncomputable section
namespace Papers.ActualFacetHitting

open Set Module
open Papers.FiniteHalfspaceVertexSeparation Papers.ActualPolytopeCoordinates
open Papers.PolytopeFourRegularTail Papers.PolytopeSimpleTailFace
open Papers.PolytopeVertexCone Papers.PolytopeBalinski Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n : ℕ}

theorem exists_facet_avoiding_homothetic_vertices
    (P : ConvexPolytope n) (hP : P.IsFullDim)
    (f : E n → E n) (hf : ParallelOnTail P P.vertices f)
    (R : Finset (E n)) (hRsub : R⊆P.vertices)
    (hR : ∃ α : ℝ,∃ b : E n,∀ x∈R,f x=α•x+b)
    (hnontrivial : ¬ ∃ α : ℝ,∃ b : E n,∀ x∈P.vertices,f x=α•x+b) :
    ∃ F : Set (E n), P.IsFace F ∧ faceDim F+1=n ∧ ∀ x∈R,x∉F := by
  obtain ⟨I,hI,g,hrep,hfacets⟩ := exists_actual_facet_halfspaces P hP
  letI : Fintype I := hI
  obtain ⟨i,hi⟩ := exists_zero_face_avoiding_homothetic_vertices P f hf g hrep
    (fun i => (hfacets i).1) R hRsub hR hnontrivial
  exact ⟨{x∈P.toSet | g i x=0},(hfacets i).1,(hfacets i).2,
    fun x hx hxF => hi x hx hxF.2⟩

theorem exists_outside_neighbor_of_proper_face
    (P : ConvexPolytope n) {F : Set (E n)} (hF : P.IsFace F)
    (hproper : F≠P.toSet)
    {v : E n} (hv : v∈P.vertices) (hvF : v∈F) :
    ∃ y,GeneralVertexStep P v y ∧ y∉F := by
  have hex : ∃ w∈P.vertices,w∉F := by
    by_contra h
    push_neg at h
    apply hproper
    apply le_antisymm (face_subset_toSet P hF)
    exact convexHull_min h (hF.1.convex (convex_convexHull ℝ _))
  obtain ⟨w,hw,hwF⟩ := hex
  obtain ⟨u,hu⟩ := hF.1 hF.2
  have hvmax := hvF
  rw [hu] at hvmax
  have huv : u w<u v := by
    have hle := hvmax.2 w (vertex_mem_body_of_mem_vertices P hw)
    apply lt_of_le_of_ne hle
    intro heq
    apply hwF
    rw [hu]
    refine ⟨vertex_mem_body_of_mem_vertices P hw,?_⟩
    intro z hz
    rw [heq]
    exact hvmax.2 z hz
  obtain ⟨y,hvy,hval⟩ :=
    exists_improving_neighbor P (-u) hv hw (neg_lt_neg huv)
  refine ⟨y,hvy,?_⟩
  intro hyF
  rw [hu] at hyF
  have hymax := hyF.2 v hvmax.1
  change -u v < -u y at hval
  linarith

theorem simple_vertex_of_facet_has_one_outside_neighbor
    (P : ConvexPolytope n) (hP : P.IsFullDim)
    {F : Set (E n)} (hF : P.IsFace F) (hdim : faceDim F+1=n)
    {v : E n} (hv : v∈P.vertices) (hvF : v∈F)
    (hsimple : (actualNeighbors P v).card=n) :
    ((actualNeighbors P v).filter (fun y => y∉F)).card=1 := by
  let Q := facePolytope P hF
  let A := actualNeighbors Q v
  let B := (actualNeighbors P v).filter (fun y => y∉F)
  have hvQ : v∈Q.vertices := (facePolytope_vertex_iff P hF v).mpr ⟨hv,hvF⟩
  have hA : Q.dim≤A.card := intrinsic_dim_le_neighbor_card Q hvQ
  have hQdim : Q.dim+1=n := by
    change finrank ℝ (vectorSpan ℝ Q.toSet)+1=n
    rw [facePolytope_toSet P hF]
    exact hdim
  have hproper : F≠P.toSet := by
    intro heq
    have hh : faceDim F=P.dim := by rw [heq]; rfl
    rw [hh,hP] at hdim
    omega
  obtain ⟨y,hvy,hyF⟩ := exists_outside_neighbor_of_proper_face P hF hproper hv hvF
  have hBn : B.Nonempty := ⟨y,Finset.mem_filter.mpr
    ⟨(mem_actualNeighbors_iff P v y).mpr hvy,hyF⟩⟩
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    have hxQ := ((mem_actualNeighbors_iff Q v x).mp hxA).1
    exact (Finset.mem_filter.mp hxB).2
      ((facePolytope_vertex_iff P hF x).mp hxQ).2
  have hsub : A∪B⊆actualNeighbors P v := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (mem_actualNeighbors_iff P v x).mpr
        (facePolytope_step P hF ((mem_actualNeighbors_iff Q v x).mp hx))
    · exact (Finset.mem_filter.mp hx).1
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,hsimple] at hcount
  have hBpos := Finset.card_pos.mpr hBn
  change B.card=1
  omega

theorem actual_shephard_facet_of_homothetic_set_containing_nonsimple
    (P : ConvexPolytope n) (hP : P.IsFullDim)
    (f : E n → E n) (hf : ParallelOnTail P P.vertices f)
    (R : Finset (E n)) (hRsub : R⊆P.vertices) (hRcard : 2≤R.card)
    (hR : ∃ α : ℝ,∃ b : E n,∀ x∈R,f x=α•x+b)
    (hsimple : ∀ x∈P.vertices,x∉R → (actualNeighbors P x).card=n)
    (hnontrivial : ¬ ∃ α : ℝ,∃ b : E n,∀ x∈P.vertices,f x=α•x+b) :
    ∃ F : Set (E n), P.IsFace F ∧ faceDim F+1=n ∧
      2≤(P.vertices.filter (fun x => x∉F)).card ∧
      ∀ v∈P.vertices,v∈F →
        ((actualNeighbors P v).filter (fun y => y∉F)).card=1 := by
  obtain ⟨F,hF,hdim,havoid⟩ :=
    exists_facet_avoiding_homothetic_vertices P hP f hf R hRsub hR hnontrivial
  have hsub : R⊆P.vertices.filter (fun x => x∉F) :=
    fun x hx => Finset.mem_filter.mpr ⟨hRsub hx,havoid x hx⟩
  refine ⟨F,hF,hdim,hRcard.trans (Finset.card_le_card hsub),?_⟩
  intro v hv hvF
  apply simple_vertex_of_facet_has_one_outside_neighbor P hP hF hdim hv hvF
  apply hsimple v hv
  exact fun hvR => havoid v hvR hvF

end Papers.ActualFacetHitting

end
end
end BundlePart3

