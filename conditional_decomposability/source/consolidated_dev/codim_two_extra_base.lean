module
public import consolidated_dev.minkowski_homothetic_core
public import consolidated_dev.projective_crossing_geometry
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option Elab.async false

section BundlePart0
/- Source: Papers/MinkowskiExtraFace.lean -/





@[expose] public section

/-! A point outside an actual homothetic fiber core exposes an actual
face outside that core containing a translate of a summand facet. -/
noncomputable section
namespace Papers.MinkowskiExtraFace

open Set Module
open Papers.Polytopes Papers.MinkowskiFaces Papers.MinkowskiVertexMap
open Papers.MinkowskiHomotheticCore Papers.AmbientHomotheticCore
open Papers.MinkowskiQuotientCounting Papers.MinkowskiSummandFibers
open Papers.MinkowskiCodimensionTwoCounts Papers.LinearImageFibers
open Papers.FiniteExposedFaces Papers.ProperMinkowskiMap
open Papers.ParallelSupportEvaluation
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {n : ℕ}

theorem extra_face_contains_translated_summand_facet
    (P A B : ConvexPolytope n) (hsum : P.toSet=A.toSet+B.toSet)
    (hApos : 0<A.dim)
    (hAI : AffineIndependent ℝ (fun q : (quotientPolytope P A).vertices => q.val))
    (hhom : ∀q:(quotientPolytope P A).vertices,SummandHomotheticFiber P A B hsum q)
    {x:E n} (hx:x∈extraVertices P A) :
    ∃F:FacetType A,∃w:E n →L[ℝ] ℝ,∃b:E n,
      maxFace A.toSet w.toLinearMap=F.val.val ∧
      (homothetyMap 1 b) '' F.val.val⊆maxFace P.toSet w.toLinearMap ∧
      Disjoint (maxFace P.toSet w.toLinearMap) (vertexCore P A) := by
  let π := summandProjection A
  let Q := quotientPolytope P A
  obtain ⟨a0,ha0V⟩ := A.vertices_nonempty
  have ha0 : a0∈A.toSet := subset_convexHull ℝ _ ha0V
  obtain ⟨scale,shift,hs,hbody,hproj⟩ :=
    exists_actual_core_parameters P A B hsum hApos hAI hhom a0 ha0
  have hcore := vertexCore_eq_ambientFibres P A scale shift hs hbody
  have hxP : x∈P.toSet := subset_convexHull ℝ _ (Finset.mem_filter.mp hx).1
  have hxQ : π x∈Q.toSet := by
    rw [linear_imagePolytope_toSet]
    exact ⟨x,hxP,rfl⟩
  have hxout := extra_vertex_not_in_core P A
    (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  have hxout' : x∉convexHull ℝ
      (ambientFibres A.toSet (Q.vertices : Set (E n)) scale shift) := by
    rw [convexHull_ambientFibres A.toSet _ (convex_convexHull ℝ _) scale shift hs]
    exact fun h => hxout (hcore.symm ▸ h)
  obtain ⟨F,hviolate⟩ := violated_facet_side A π (summandProjection_kernel A) a0 ha0
    (Q.vertices : Set (E n)) scale shift hs x hxQ (hproj _ hxQ) hxout'
  let g := chosenFacetForm A F
  let s := sideForm π scale shift g
  let w : E n →L[ℝ] ℝ := (-s.linear).toContinuousLinearMap
  have hw (z:E n) : w z=s 0-s z := by
    change -s.linear z=s 0-s z
    rw [affine_form_apply s z]
    ring
  have hnonnegative : ∀z∈vertexCore P A,0≤s z := by
    intro z hz
    rw [hcore] at hz
    obtain ⟨q,hq,a,ha,hz⟩ := (mem_ambientFibres _ _ _ _ _).mp hz
    have haπ : π a=π a0 := by
      have hk : a-a0∈π.ker := by
        rw [summandProjection_kernel]
        exact vsub_mem_vectorSpan ℝ ha ha0
      change π (a-a0)=0 at hk
      rw [map_sub] at hk
      exact sub_eq_zero.mp hk
    have hπz : π z=q := by
      rw [hz,map_add,map_smul,haπ,add_comm]
      exact hproj q hq
    have hscale := Papers.HomotheticFiberCore.positive_on_convexHull scale hs q hq
    have hsz : s z=scale q*g a := by
      rw [sideForm_apply,hπz,hz,map_add,map_smul,smul_eq_mul,
        affine_form_apply g a]
      ring
    rw [hsz]
    exact mul_nonneg hscale.le ((chosenFacetForm_supports A F).1 a ha)
  have hdis : Disjoint (maxFace P.toSet w.toLinearMap) (vertexCore P A) := by
    apply Set.disjoint_left.mpr
    intro z hz hzcore
    have hmax := hz.2 x hxP
    change w x≤w z at hmax
    rw [hw x,hw z] at hmax
    have hnonneg := hnonnegative z hzcore
    change s x<0 at hviolate
    linarith
  obtain ⟨aF,haF⟩ := F.val.property.2
  have haFA := face_subset_toSet A F.val.property haF
  have hvalue (a:E n) (ha:a∈A.toSet) : w a-w aF= -g a := by
    have hk : π (a-aF)=0 := by
      change a-aF∈π.ker
      rw [summandProjection_kernel]
      exact vsub_mem_vectorSpan ℝ ha haFA
    have hgd : g.linear (a-aF)=g a-g aF := by
      simpa only [vsub_eq_sub] using g.linear_apply_vsub a aF
    calc
      w a-w aF = -s.linear (a-aF) := by
        change -s.linear a- -s.linear aF= -s.linear (a-aF)
        rw [map_sub]
        ring
      _ = -g.linear (a-aF) := by rw [sideForm_linear_on_kernel π scale shift g hk]
      _ = -g a := by rw [hgd,(chosenFacetForm_supports A F).eq_zero haF,sub_zero]
  have hface : maxFace A.toSet w.toLinearMap=F.val.val := by
    ext a
    constructor
    · intro ha
      have hm := ha.2 aF haFA
      change w aF≤w a at hm
      have hv := hvalue a ha.1
      have hnn := (chosenFacetForm_supports A F).1 a ha.1
      exact ((chosenFacetForm_supports A F).mem_iff a).mpr ⟨ha.1,by linarith⟩
    · intro ha
      refine ⟨face_subset_toSet A F.val.property ha,?_⟩
      intro z hz
      have hva := hvalue a (face_subset_toSet A F.val.property ha)
      have hvz := hvalue z hz
      rw [(chosenFacetForm_supports A F).eq_zero ha] at hva
      have hnn := (chosenFacetForm_supports A F).1 z hz
      change w z≤w a
      linarith
  have hne := (maxFace_isFace P w).2
  rw [hsum,maxFace_add,hface] at hne
  obtain ⟨z,a,ha,b,hb,hz⟩ := hne
  refine ⟨F,w,b,hface,?_,hdis⟩
  rintro z ⟨a,ha,rfl⟩
  rw [hsum,maxFace_add,hface]
  exact Set.mem_add.mpr ⟨a,ha,b,hb,by change a+b=(1:ℝ)•a+b; rw [one_smul]⟩

theorem extra_card_ge_summand_dimension
    (P A B : ConvexPolytope n) (hsum : P.toSet=A.toSet+B.toSet)
    (hApos : 0<A.dim)
    (hAI : AffineIndependent ℝ (fun q : (quotientPolytope P A).vertices => q.val))
    (hhom : ∀q:(quotientPolytope P A).vertices,SummandHomotheticFiber P A B hsum q)
    (hextra:(extraVertices P A).Nonempty) : A.dim≤(extraVertices P A).card := by
  obtain ⟨x,hx⟩ := hextra
  obtain ⟨F,w,b,hface,himage,hdis⟩ :=
    extra_face_contains_translated_summand_facet P A B hsum hApos hAI hhom hx
  have hinj : Function.Injective (homothetyMap (1:ℝ) b).linear := by
    intro x y h
    change (1:ℝ)•x=(1:ℝ)•y at h
    simpa only [one_smul] using h
  have hc := outside_card_of_exposed_affineImage P.vertices w.toLinearMap
    (vertexCore P A) F.val.property.2 (homothetyMap 1 b) hinj himage hdis
  have hsub : (P.vertices.filter fun x => x∉vertexCore P A)⊆extraVertices P A := by
    intro y hy
    obtain ⟨hy,hout⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_filter.mpr ⟨hy,?_⟩
    intro hq
    exact hout (subset_convexHull ℝ _ (Finset.mem_filter.mpr ⟨hy,hq⟩))
  have hcard := Finset.card_le_card hsub
  have hd := F.property.2
  change faceDim F.val.val+1≤_ at hc
  omega

end Papers.MinkowskiExtraFace

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/MinkowskiCrossingCenters.lean -/




@[expose] public section

/-!
# The actual parallel centers of Minkowski label families

The label of a vertex of P=A+B is its uniquely determined A-component.
For two different labels, every crossing edge has the same point at infinity.
The construction proves both the projective incidence and the matching and
no-three-in-a-two-face properties used by the later combinatorial argument.
-/

noncomputable section
namespace Papers.MinkowskiCrossingCenters

open Set Module
open Papers.Coordinates Papers.Polytopes Papers.MinkowskiVertexMap
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {n : ℕ}

def summandLabel (P A B : ConvexPolytope n)
    (hP : P.toSet = A.toSet + B.toSet) (x : P.vertices) : A.vertices :=
  ⟨leftVertexMap P A B hP x.val, (leftVertexMap_spec P A B hP x.property).1⟩

def parallelCenter (a b : E n) : Submodule ℝ (E n × ℝ) :=
  Submodule.span ℝ ({(b-a,0)} : Set (E n × ℝ))

theorem parallelCenter_rank_one {a b : E n} (hab : a ≠ b) :
    finrank ℝ (parallelCenter a b) = 1 := by
  apply finrank_span_singleton
  intro h
  have hfirst : b-a = 0 := congrArg Prod.fst h
  exact hab (sub_eq_zero.mp hfirst).symm

theorem homogenize_not_mem_parallelCenter (a b x : E n) :
    homogenize x ∉ parallelCenter a b := by
  intro h
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp h
  have hlast := congrArg Prod.snd hc
  norm_num [homogenize] at hlast

theorem crossing_center_incidence
    (P A B : ConvexPolytope n) (hP : P.toSet = A.toSet + B.toSet)
    (a b : A.vertices) (e : CrossingFamily P (summandLabel P A B hP) a b) :
    parallelCenter a.val b.val ≤ e.line := by
  apply Submodule.span_le.mpr
  intro z hz
  have hz' : z = (b.val-a.val,0) := Set.mem_singleton_iff.mp hz
  subst z
  have ha : leftVertexMap P A B hP e.left.val = a.val :=
    congrArg Subtype.val e.property.2.1
  have hb : leftVertexMap P A B hP e.right.val = b.val :=
    congrArg Subtype.val e.property.2.2
  obtain ⟨μ,hμ⟩ := leftVertexMap_parallel P A B hP
    e.left.val e.left.property e.right.val e.right.property e.isEdge
  rw [ha,hb] at hμ
  have hdiff : homogenize e.right.val - homogenize e.left.val ∈ e.line := by
    apply e.line.sub_mem
    · exact homogenize_mem_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · exact homogenize_mem_span (Set.mem_insert _ _)
  have h := e.line.smul_mem μ hdiff
  have heq : (b.val-a.val,(0:ℝ))=μ•(homogenize e.right.val-homogenize e.left.val) := by
    apply Prod.ext
    · exact hμ
    · simp only [Prod.smul_snd,Prod.snd_sub,homogenize,sub_self,smul_zero]
  rw [heq]
  exact h

theorem crossing_endpoint_injective
    (P A B : ConvexPolytope n) (hP : P.toSet = A.toSet + B.toSet)
    (a b : A.vertices) (hab : a ≠ b) :
    Function.Injective (fun e : CrossingFamily P (summandLabel P A B hP) a b => e.left.val) ∧
    Function.Injective (fun e : CrossingFamily P (summandLabel P A B hP) a b => e.right.val) := by
  exact CrossingFamily.endpoint_injections_of_nonvertex_center
    (parallelCenter a.val b.val)
    (parallelCenter_rank_one (fun h => hab (Subtype.ext h)))
    (crossing_center_incidence P A B hP a b)
    (fun x _ => homogenize_not_mem_parallelCenter a.val b.val x)

theorem crossing_no_three
    (P A B : ConvexPolytope n) (hP : P.toSet = A.toSet + B.toSet)
    (a b : A.vertices) (hab : a ≠ b)
    (F : Set (E n)) (hF : P.IsFace F) (hdim : faceDim F = 2)
    (e : Fin 3 → CrossingFamily P (summandLabel P A B hP) a b)
    (hinj : Function.Injective e) (hlies : ∀ i, CrossingFamily.liesIn F (e i)) : False := by
  exact CrossingFamily.no_three_in_actual_twoFace hab (parallelCenter a.val b.val)
    (parallelCenter_rank_one (fun h => hab (Subtype.ext h)))
    (crossing_center_incidence P A B hP a b)
    (fun x _ => homogenize_not_mem_parallelCenter a.val b.val x)
    F hF hdim e hinj hlies

end Papers.MinkowskiCrossingCenters

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/ActualHomothetyClasses.lean -/






@[expose] public section

/-!
# The essential homothety class bound for actual polytopes

A private vertex and the actual edge-star spanning theorem force every
homogeneous polytope point into the parameter-direction span plus the
span of the noncentral vertices in its homothety class.  The resulting
cardinality estimate uses the intrinsic dimension of the polytope.
-/

noncomputable section
namespace Papers.ActualHomothetyClasses

open Set Module
open Papers.Polytopes
open Papers.HomogeneousSpanDimension Papers.FaceVertexCardinality
open Papers.PolytopeVertexCone
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n : ℕ} {I : Type*}

def evaluate (p : ℝ × E n) (x : E n) : E n := p.1 • x + p.2

def directionSpan (p : I → ℝ × E n) : Submodule ℝ (E n × ℝ) :=
  Submodule.span ℝ (Set.range fun ij : I × I =>
    differenceCenterVector (p ij.1) (p ij.2))

theorem difference_mem (p : I → ℝ × E n) (i j : I) :
    differenceCenterVector (p i) (p j) ∈ directionSpan p :=
  Submodule.subset_span ⟨(i,j),rfl⟩

def noncentralClass (P : ConvexPolytope n) (f : E n → E n)
    (p : I → ℝ × E n) (i : I) : Finset (E n) :=
  P.vertices.filter fun x => f x = evaluate (p i) x ∧ liftPoint x ∉ directionSpan p

theorem edge_identity
    (f : E n → E n) (p q : ℝ × E n) (x y : E n) (μ : ℝ)
    (hx : f x = evaluate p x) (hy : f y = evaluate q y)
    (hparallel : f y - f x = μ • (y - x)) :
    differenceCenterVector p q =
      (q.1 - μ) • liftPoint y - (p.1 - μ) • liftPoint x := by
  apply Prod.ext
  · change -(q.2 - p.2) = (q.1 - μ) • y - (p.1 - μ) • x
    calc
      -(q.2 - p.2) = (q.1 • y - p.1 • x) - (f y - f x) := by
        rw [hy,hx]
        unfold evaluate
        module
      _ = (q.1 - μ) • y - (p.1 - μ) • x := by
        rw [hparallel]
        module
  · change q.1 - p.1 = (q.1 - μ) * 1 - (p.1 - μ) * 1
    ring

theorem coefficient_ne_zero_at_private_vertex
    (f : E n → E n) (p q : ℝ × E n) (x y : E n) (μ : ℝ)
    (hy : f y = evaluate q y)
    (hparallel : f y - f x = μ • (y - x))
    (hprivate : f x ≠ evaluate q x) :
    q.1 - μ ≠ 0 := by
  intro hz
  have hqμ : q.1 = μ := sub_eq_zero.mp hz
  apply hprivate
  calc
    f x = f y - μ • (y - x) := by rw [← hparallel]; abel
    _ = evaluate q x := by rw [hy]; unfold evaluate; rw [hqμ]; module

theorem lift_class_mem
    (P : ConvexPolytope n) (f : E n → E n) (p : I → ℝ × E n) (i : I)
    {x : E n} (hx : x ∈ P.vertices) (hclass : f x = evaluate (p i) x) :
    liftPoint x ∈ directionSpan p ⊔
      liftSpan ((noncentralClass P f p i : Finset (E n)) : Set (E n)) := by
  by_cases hc : liftPoint x ∈ directionSpan p
  · exact Submodule.mem_sup_left hc
  · exact Submodule.mem_sup_right (liftPoint_mem
      (Finset.mem_filter.mpr ⟨hx,hclass,hc⟩))

theorem lift_neighbors_mem
    (P : ConvexPolytope n) (f : E n → E n) (p : I → ℝ × E n)
    (hparallel : IsParallelMap P f)
    (hcover : ∀ y ∈ P.vertices, ∃ j : I, f y = evaluate (p j) y)
    (i : I) {x : E n} (hxV : x ∈ P.vertices)
    (hxi : f x = evaluate (p i) x)
    (hprivate : ∀ j : I, j ≠ i → f x ≠ evaluate (p j) x)
    {y : E n} (hxy : GeneralVertexStep P x y) :
    liftPoint y ∈ directionSpan p ⊔
      liftSpan ((noncentralClass P f p i : Finset (E n)) : Set (E n)) := by
  let W := directionSpan p ⊔
    liftSpan ((noncentralClass P f p i : Finset (E n)) : Set (E n))
  have hxW : liftPoint x ∈ W := lift_class_mem P f p i hxV hxi
  by_cases hyi : f y = evaluate (p i) y
  · exact lift_class_mem P f p i hxy.1 hyi
  obtain ⟨j,hyj⟩ := hcover y hxy.1
  have hji : j ≠ i := by rintro rfl; exact hyi hyj
  obtain ⟨μ,hμ⟩ := hparallel x hxV y hxy.1 hxy
  have hcoeff := coefficient_ne_zero_at_private_vertex f (p i) (p j) x y μ
    hyj hμ (hprivate j hji)
  have heq := edge_identity f (p i) (p j) x y μ hxi hyj hμ
  have hsmul : ((p j).1 - μ) • liftPoint y ∈ W := by
    have hrew : ((p j).1 - μ) • liftPoint y =
        differenceCenterVector (p i) (p j) + ((p i).1 - μ) • liftPoint x := by
      rw [heq]
      module
    rw [hrew]
    exact W.add_mem (Submodule.mem_sup_left (difference_mem p i j)) (W.smul_mem _ hxW)
  have h := W.smul_mem (((p j).1 - μ)⁻¹) hsmul
  simpa only [smul_smul,inv_mul_cancel₀ hcoeff,one_smul] using h

theorem liftSpan_le_class_sup
    (P : ConvexPolytope n) (f : E n → E n) (p : I → ℝ × E n)
    (hparallel : IsParallelMap P f)
    (hcover : ∀ y ∈ P.vertices, ∃ j : I, f y = evaluate (p j) y)
    (i : I) {x : E n} (hxV : x ∈ P.vertices)
    (hxi : f x = evaluate (p i) x)
    (hprivate : ∀ j : I, j ≠ i → f x ≠ evaluate (p j) x) :
    liftSpan P.toSet ≤ directionSpan p ⊔
      liftSpan ((noncentralClass P f p i : Finset (E n)) : Set (E n)) := by
  let W := directionSpan p ⊔
    liftSpan ((noncentralClass P f p i : Finset (E n)) : Set (E n))
  have hxW : liftPoint x ∈ W := lift_class_mem P f p i hxV hxi
  have hneighbor : neighborSpan P x ≤ W.comap (LinearMap.inl ℝ (E n) ℝ) := by
    apply Submodule.span_le.mpr
    rintro u ⟨y,hxy,rfl⟩
    change (LinearMap.inl ℝ (E n) ℝ) (y - x) ∈ W
    have hyW := lift_neighbors_mem P f p hparallel hcover i hxV hxi hprivate hxy
    have hd := W.sub_mem hyW hxW
    simpa only [liftPoint,Prod.mk_sub_mk,sub_self,LinearMap.inl_apply] using hd
  apply Submodule.span_le.mpr
  rintro u ⟨y,hy,rfl⟩
  have hd : (LinearMap.inl ℝ (E n) ℝ) (y - x) ∈ W :=
    hneighbor (sub_mem_neighborSpan P hxV hy)
  have h := W.add_mem hd hxW
  change liftPoint y∈W
  change (y - x + x, (0 : ℝ) + 1) ∈ W at h
  simpa only [LinearMap.inl_apply,liftPoint,Prod.mk_add_mk,sub_add_cancel,zero_add] using h

theorem dimension_le_class_card_add_parameter_dimension
    (P : ConvexPolytope n) (f : E n → E n) (p : I → ℝ × E n)
    (hparallel : IsParallelMap P f)
    (hcover : ∀ y ∈ P.vertices, ∃ j : I, f y = evaluate (p j) y)
    (i : I) {x : E n} (hxV : x ∈ P.vertices)
    (hxi : f x = evaluate (p i) x)
    (hprivate : ∀ j : I, j ≠ i → f x ≠ evaluate (p j) x) :
    P.dim + 1 ≤ (noncentralClass P f p i).card + finrank ℝ (directionSpan p) := by
  let A := liftSpan ((noncentralClass P f p i : Finset (E n)) : Set (E n))
  have hle := Submodule.finrank_mono
    (liftSpan_le_class_sup P f p hparallel hcover i hxV hxi hprivate)
  have hdim : finrank ℝ (liftSpan P.toSet) = P.dim + 1 :=
    finrank_liftSpan ⟨x,subset_convexHull ℝ _ hxV⟩
  have hcard : finrank ℝ A ≤ (noncentralClass P f p i).card :=
    finrank_liftSpan_finset_le_card (noncentralClass P f p i)
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (directionSpan p) A
  rw [hdim] at hle
  change P.dim + 1 ≤ finrank ℝ (directionSpan p ⊔ A : Submodule ℝ (E n × ℝ)) at hle
  omega

theorem essential_class_bound
    (P : ConvexPolytope n) (f : E n → E n) (p : I → ℝ × E n)
    (hparallel : IsParallelMap P f)
    (hcover : ∀ y ∈ P.vertices, ∃ j : I, f y = evaluate (p j) y)
    (i : I) {x : E n} (hxV : x ∈ P.vertices)
    (hxi : f x = evaluate (p i) x)
    (hprivate : ∀ j : I, j ≠ i → f x ≠ evaluate (p j) x) :
    P.dim + 1 - finrank ℝ (directionSpan p) ≤ (noncentralClass P f p i).card := by
  have h := dimension_le_class_card_add_parameter_dimension
    P f p hparallel hcover i hxV hxi hprivate
  omega

theorem equal_evaluation_central
    (p : I → ℝ × E n) (i j : I) (x : E n)
    (hneq : p i ≠ p j) (heval : evaluate (p i) x = evaluate (p j) x) :
    liftPoint x ∈ directionSpan p := by
  have hcoeff : (p j).1 - (p i).1 ≠ 0 := by
    intro hz
    have hα : (p j).1 = (p i).1 := sub_eq_zero.mp hz
    have hb : (p i).2 = (p j).2 := by
      apply add_left_cancel (a := (p i).1 • x)
      simpa only [evaluate,hα] using heval
    exact hneq (Prod.ext hα.symm hb)
  have heq : differenceCenterVector (p i) (p j) =
      ((p j).1 - (p i).1) • liftPoint x := by
    apply Prod.ext
    · change -((p j).2 - (p i).2) = ((p j).1 - (p i).1) • x
      calc
        -((p j).2 - (p i).2) =
            ((p j).1 • x - (p i).1 • x) +
              (evaluate (p i) x - evaluate (p j) x) := by
          unfold evaluate
          module
        _ = ((p j).1 - (p i).1) • x := by rw [heval]; module
    · change (p j).1 - (p i).1 = ((p j).1 - (p i).1) * 1
      rw [mul_one]
  have hm : ((p j).1 - (p i).1) • liftPoint x ∈ directionSpan p := by
    rw [← heq]
    exact difference_mem p i j
  have h := (directionSpan p).smul_mem (((p j).1 - (p i).1)⁻¹) hm
  simpa only [smul_smul,inv_mul_cancel₀ hcoeff,one_smul] using h

def coloredNoncentral (P : ConvexPolytope n) (color : P.vertices → I)
    (p : I → ℝ × E n) (i : I) : Finset P.vertices :=
  Finset.univ.filter fun v => color v = i ∧ liftPoint v.val ∉ directionSpan p

theorem class_color_unique_at_private_vertex
    (P : ConvexPolytope n) (f : E n → E n) (p : I → ℝ × E n)
    (color : P.vertices → I)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (i : I) {x : E n}
    (hxi : f x = evaluate (p i) x)
    (hprivate : ∀ j : I, j ≠ i → f x ≠ evaluate (p j) x)
    (v : P.vertices) (hvi : f v.val = evaluate (p i) v.val)
    (hnc : liftPoint v.val ∉ directionSpan p) :
    color v = i := by
  by_contra hci
  have hpneq : p i ≠ p (color v) := by
    intro hp
    apply hprivate (color v) hci
    rw [← hp]
    exact hxi
  exact hnc (equal_evaluation_central p i (color v) v.val hpneq
    (hvi.symm.trans (hcover v)))

theorem noncentralClass_card_le_coloredNoncentral
    (P : ConvexPolytope n) (f : E n → E n) (p : I → ℝ × E n)
    (color : P.vertices → I)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (i : I) {x : E n}
    (hxi : f x = evaluate (p i) x)
    (hprivate : ∀ j : I, j ≠ i → f x ≠ evaluate (p j) x) :
    (noncentralClass P f p i).card ≤ (coloredNoncentral P color p i).card := by
  let g : (noncentralClass P f p i) → (coloredNoncentral P color p i) :=
    fun v =>
      let hv := Finset.mem_filter.mp v.property
      ⟨⟨v.val,hv.1⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
        exact ⟨class_color_unique_at_private_vertex P f p color hcover i hxi
          hprivate ⟨v.val,hv.1⟩ hv.2.1 hv.2.2,hv.2.2⟩⟩⟩
  have hg : Function.Injective g := by
    intro v w h
    apply Subtype.ext
    exact congrArg (fun u : coloredNoncentral P color p i => u.val.val) h
  simpa using Fintype.card_le_of_injective g hg

theorem colored_essential_class_bound
    (P : ConvexPolytope n) (f : E n → E n) (p : I → ℝ × E n)
    (hparallel : IsParallelMap P f)
    (color : P.vertices → I)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (i : I) {x : E n} (hxV : x ∈ P.vertices)
    (hxi : f x = evaluate (p i) x)
    (hprivate : ∀ j : I, j ≠ i → f x ≠ evaluate (p j) x) :
    P.dim + 1 - finrank ℝ (directionSpan p) ≤
      (coloredNoncentral P color p i).card := by
  have hfull : ∀ y ∈ P.vertices, ∃ j : I, f y = evaluate (p j) y := by
    intro y hy
    exact ⟨color ⟨y,hy⟩,hcover ⟨y,hy⟩⟩
  exact (essential_class_bound P f p hparallel hfull i hxV hxi hprivate).trans
    (noncentralClass_card_le_coloredNoncentral P f p color hcover i hxi hprivate)

theorem three_color_class_bound
    (P : ConvexPolytope n) (f : E n → E n) (p : Fin 3 → ℝ × E n)
    (hparallel : IsParallelMap P f)
    (color : P.vertices → Fin 3)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (hrank : finrank ℝ (directionSpan p) = 2)
    (i : Fin 3) {x : E n} (hxV : x ∈ P.vertices)
    (hxi : f x = evaluate (p i) x)
    (hprivate : ∀ j : Fin 3, j ≠ i → f x ≠ evaluate (p j) x) :
    P.dim - 1 ≤ (coloredNoncentral P color p i).card := by
  have h := colored_essential_class_bound P f p hparallel color hcover i hxV hxi hprivate
  rw [hrank] at h
  omega

end Papers.ActualHomothetyClasses

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/MinkowskiLabelCounting.lean -/






@[expose] public section

/-!
# Actual summand-label class sizes

Constant homotheties at the genuine summand vertices form an essential
cover: surjectivity of the vertex component map supplies each private
vertex. Their parameter directions lie in the summand direction space.
The intrinsic class estimate therefore gives at least q+1 vertices of
each label. Matching endpoint injections then give the strict family
size bound used by projective concurrence when q is at least three.
-/

noncomputable section
namespace Papers.MinkowskiLabelCounting

open Set Module
open Papers.Polytopes Papers.MinkowskiVertexMap Papers.MinkowskiCrossingCenters
open Papers.ActualHomothetyClasses Papers.HomogeneousSpanDimension
open Papers.MinkowskiQuotientCounting Papers.ProperMinkowskiMap
open Papers.ProperSummandCounting
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise BigOperators

variable {n : ℕ}

def labelVertices (P A B : ConvexPolytope n)
    (hSum : P.toSet=A.toSet+B.toSet) (a : E n) : Finset (E n) :=
  P.vertices.filter fun x => leftVertexMap P A B hSum x=a

theorem constant_parameter_rank_le (A : ConvexPolytope n) :
    finrank ℝ (directionSpan (fun a : A.vertices => ((0:ℝ),a.val))) ≤ A.dim := by
  let L := vectorSpan ℝ A.toSet
  let inl := LinearMap.inl ℝ (E n) ℝ
  have hle : directionSpan (fun a : A.vertices => ((0:ℝ),a.val)) ≤ L.map inl := by
    apply Submodule.span_le.mpr
    rintro z ⟨⟨a,b⟩,rfl⟩
    refine Submodule.mem_map.mpr ⟨a.val-b.val,?_,?_⟩
    · exact vsub_mem_vectorSpan ℝ (subset_convexHull ℝ _ a.property)
        (subset_convexHull ℝ _ b.property)
    · change (a.val-b.val,0)=(-(b.val-a.val),(0:ℝ)-0)
      apply Prod.ext
      · abel
      · simp
  have h := Submodule.finrank_mono hle
  rw [finrank_map_inl] at h
  exact h

theorem label_card_add_summand_dim
    (P A B : ConvexPolytope n) (hSum : P.toSet=A.toSet+B.toSet)
    (a : A.vertices) :
    P.dim+1 ≤ (labelVertices P A B hSum a.val).card+A.dim := by
  let f := leftVertexMap P A B hSum
  let p : A.vertices → ℝ × E n := fun a => (0,a.val)
  obtain ⟨x,hx,hfx⟩ := leftVertexMap_surjective P A B hSum a.property
  have hcover : ∀y∈P.vertices,∃b : A.vertices,f y=evaluate (p b) y := by
    intro y hy
    exact ⟨⟨f y,(leftVertexMap_spec P A B hSum hy).1⟩,by simp [evaluate,p]⟩
  have hprivate : ∀b : A.vertices,b≠a → f x≠evaluate (p b) x := by
    intro b hba heq
    apply hba
    apply Subtype.ext
    have hfx' : f x=a.val := hfx
    simpa only [evaluate,p,zero_smul,zero_add,hfx'] using heq.symm
  have h := dimension_le_class_card_add_parameter_dimension P f p
    (leftVertexMap_parallel P A B hSum) hcover a hx
    (by simpa [evaluate,p] using hfx) hprivate
  have hsub : noncentralClass P f p a ⊆ labelVertices P A B hSum a.val := by
    intro y hy
    obtain ⟨hy,hclass,hnc⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hy,by simpa only [evaluate,p,zero_smul,zero_add] using hclass⟩
  have hc := Finset.card_le_card hsub
  have hrank := constant_parameter_rank_le A
  change finrank ℝ (directionSpan p) ≤ A.dim at hrank
  omega

theorem quotient_dim_add_one_le_label_card
    (P A B : ConvexPolytope n) (hP : P.IsFullDim)
    (hSum : P.toSet=A.toSet+B.toSet) (a : A.vertices) :
    (quotientPolytope P A).dim+1 ≤ (labelVertices P A B hSum a.val).card := by
  have h := label_card_add_summand_dim P A B hSum a
  have hd := quotient_dimension_add_summand_dimension P A hP
  change P.dim=n at hP
  omega

theorem sum_label_card (P A B : ConvexPolytope n)
    (hSum : P.toSet=A.toSet+B.toSet) :
    ∑a∈A.vertices,(labelVertices P A B hSum a).card=P.vertices.card := by
  have h := Finset.sum_card_fiberwise_eq_card_filter P.vertices A.vertices
    (leftVertexMap P A B hSum)
  have hfilter : P.vertices.filter (fun x => leftVertexMap P A B hSum x∈A.vertices)=P.vertices := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    exact (leftVertexMap_spec P A B hSum hx).1
  simpa only [labelVertices,hfilter] using h

theorem family_card_le_each_label
    (P A B : ConvexPolytope n) (hSum : P.toSet=A.toSet+B.toSet)
    (a b : A.vertices) (hab : a≠b) :
    Fintype.card (CrossingFamily P (summandLabel P A B hSum) a b) ≤
        (labelVertices P A B hSum a.val).card ∧
    Fintype.card (CrossingFamily P (summandLabel P A B hSum) a b) ≤
        (labelVertices P A B hSum b.val).card := by
  obtain ⟨hl,hr⟩ := crossing_endpoint_injective P A B hSum a b hab
  let l : CrossingFamily P (summandLabel P A B hSum) a b → labelVertices P A B hSum a.val :=
    fun e => ⟨e.left.val,Finset.mem_filter.mpr
      ⟨e.left.property,congrArg Subtype.val e.property.2.1⟩⟩
  let r : CrossingFamily P (summandLabel P A B hSum) a b → labelVertices P A B hSum b.val :=
    fun e => ⟨e.right.val,Finset.mem_filter.mpr
      ⟨e.right.property,congrArg Subtype.val e.property.2.2⟩⟩
  constructor
  · simpa only [Fintype.card_coe] using Fintype.card_le_of_injective l
      (fun e f h => hl (show e.left.val=f.left.val from congrArg (fun z:labelVertices P A B hSum a.val => z.val) h))
  · simpa only [Fintype.card_coe] using Fintype.card_le_of_injective r
      (fun e f h => hr (show e.right.val=f.right.val from congrArg (fun z:labelVertices P A B hSum b.val => z.val) h))

theorem matching_class_count
    (P A B : ConvexPolytope n) (hP : P.IsFullDim)
    (hSum : P.toSet=A.toSet+B.toSet) (a b : A.vertices) (hab : a≠b) :
    2*Fintype.card (CrossingFamily P (summandLabel P A B hSum) a b) +
      (A.vertices.card-2)*((quotientPolytope P A).dim+1) ≤ P.vertices.card := by
  let s := (A.vertices.erase a.val).erase b.val
  let c := fun x => (labelVertices P A B hSum x).card
  have habval : a.val≠b.val := fun h => hab (Subtype.ext h)
  have hb : b.val∈A.vertices.erase a.val := Finset.mem_erase.mpr ⟨habval.symm,b.property⟩
  have hs : s.card=A.vertices.card-2 := by
    simp only [s,Finset.card_erase_of_mem hb,Finset.card_erase_of_mem a.property]
    omega
  have hsum : (∑x∈s,c x)+c b.val+c a.val=P.vertices.card := by
    rw [Finset.sum_erase_add _ _ hb,Finset.sum_erase_add _ _ a.property]
    exact sum_label_card P A B hSum
  have hmin : s.card*((quotientPolytope P A).dim+1) ≤ ∑x∈s,c x := by
    calc
      _ = ∑_x∈s,((quotientPolytope P A).dim+1) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun x hx => quotient_dim_add_one_le_label_card P A B hP hSum
        ⟨x,Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)⟩)
  obtain ⟨ha,hb⟩ := family_card_le_each_label P A B hSum a b hab
  rw [hs] at hmin
  change _≤c a.val at ha
  change _≤c b.val at hb
  omega

theorem family_card_lt_twice_codimension
    (P A B : ConvexPolytope n) (hP : P.IsFullDim)
    (hSum : P.toSet=A.toSet+B.toSet)
    (hr : 2≤A.dim) (hq : 3≤(quotientPolytope P A).dim)
    (hN : P.vertices.card≤4*n-5) (a b : A.vertices) (hab : a≠b) :
    Fintype.card (CrossingFamily P (summandLabel P A B hSum) a b) <
      2*(quotientPolytope P A).dim := by
  have hs := summand_minimal_vertices_of_codimension_at_least_three P A B hP hSum hr hq hN
  have hcount := matching_class_count P A B hP hSum a b hab
  have hdim := quotient_dimension_add_summand_dimension P A hP
  rw [hs] at hcount
  have hsub : A.dim+1-2=A.dim-1 := by omega
  rw [hsub] at hcount
  have hcountz : 2*(Fintype.card (CrossingFamily P (summandLabel P A B hSum) a b) : ℤ) +
      ((A.dim : ℤ)-1)*((quotientPolytope P A).dim+1) ≤ P.vertices.card := by
    have ht : ((A.dim-1 : ℕ) : ℤ)=(A.dim : ℤ)-1 := by omega
    have hh : 2*(Fintype.card (CrossingFamily P (summandLabel P A B hSum) a b):ℤ)+
        ((A.dim-1:ℕ):ℤ)*((quotientPolytope P A).dim+1)≤P.vertices.card := by
      exact_mod_cast hcount
    rwa [ht] at hh
  have h := crossing_family_small (r := (A.dim : ℤ))
    (q := ((quotientPolytope P A).dim : ℤ)) (by exact_mod_cast hr) (by exact_mod_cast hq)
    hcountz (by omega)
  omega

end Papers.MinkowskiLabelCounting

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/MinkowskiCofacialGeometry.lean -/






@[expose] public section

/-!
# Counting the two-faces in a summand-label family

For a fixed crossing edge, an incident two-face that carries a third label
is determined by that label. The two independent differences of the three
actual summand vertices span its direction plane. All remaining two-faces
contain another crossing edge of the same family, by polygon parity.
-/

noncomputable section
namespace Papers.MinkowskiCofacialGeometry

open Set Module
open Papers.Polytopes Papers.Coordinates
open Papers.MinkowskiVertexMap Papers.MinkowskiCrossingCenters
open Papers.PolytopeFourRegularTail Papers.PolytopeSimpleTailFace
open Papers.ParallelFaceDirections
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {n : ℕ}

theorem three_vertex_differences_independent (A : ConvexPolytope n)
    (a b c : A.vertices) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LinearIndependent ℝ ![b.val-a.val,c.val-a.val] := by
  apply Fintype.linearIndependent_iff.mpr
  intro w hw i
  have hnot := vertices_not_collinear A a.property b.property c.property
    (fun h => hab (Subtype.ext h)) (fun h => hac (Subtype.ext h))
    (fun h => hbc (Subtype.ext h))
  have hsum : w 0 • (b.val-a.val) + w 1 • (c.val-a.val) = 0 := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using hw
  have hrel : (-w 0-w 1) • a.val + w 0 • b.val + w 1 • c.val = 0 := by
    calc
      _ = w 0 • (b.val-a.val) + w 1 • (c.val-a.val) := by module
      _ = 0 := hsum
  have hc0 := affine_triple_coefficients hnot
    (show (-w 0-w 1)+w 0+w 1=0 by ring) hrel
  fin_cases i
  · exact hc0.2.1
  · exact hc0.2.2

theorem twoFaces_eq_of_three_parallel_values
    (P A : ConvexPolytope n) (f : E n → E n)
    (hf : ParallelOnTail P P.vertices f)
    (a b c : A.vertices) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (F G : Set (E n)) (hF : P.IsFace F) (hG : P.IsFace G)
    (hdF : faceDim F=2) (hdG : faceDim G=2)
    (x y : P.vertices) (hxF : x.val∈F) (hyF : y.val∈F)
    (hxG : x.val∈G) (hyG : y.val∈G)
    (hfx : f x.val=a.val) (hfy : f y.val=b.val)
    (hcF : ∃z∈(facePolytope P hF).vertices,f z=c.val)
    (hcG : ∃z∈(facePolytope P hG).vertices,f z=c.val) : F=G := by
  let U := Submodule.span ℝ (Set.range ![b.val-a.val,c.val-a.val])
  have hU : finrank ℝ U=2 := by
    simpa only [U,Fintype.card_fin] using
      finrank_span_eq_card (three_vertex_differences_independent A a b c hab hac hbc)
  have hspan (H : Set (E n)) (hH : P.IsFace H) (hdH : faceDim H=2)
      (hxH : x.val∈H) (hyH : y.val∈H)
      (hcH : ∃z∈(facePolytope P hH).vertices,f z=c.val) :
      U=vectorSpan ℝ H := by
    have hxR := (facePolytope_vertex_iff P hH x.val).mpr ⟨x.property,hxH⟩
    have hyR := (facePolytope_vertex_iff P hH y.val).mpr ⟨y.property,hyH⟩
    obtain ⟨z,hz,hfz⟩ := hcH
    have hba := parallel_value_difference_mem_face_direction P f hf hH hxR hyR
    have hca := parallel_value_difference_mem_face_direction P f hf hH hxR hz
    rw [hfx,hfy] at hba
    rw [hfx,hfz] at hca
    apply Submodule.eq_of_le_of_finrank_le
    · apply Submodule.span_le.mpr
      rintro v ⟨i,rfl⟩
      fin_cases i
      · exact hba
      · exact hca
    · change faceDim H≤finrank ℝ U
      rw [hdH,hU]
  have heqdir := (hspan F hF hdF hxF hyF hcF).symm.trans
    (hspan G hG hdG hxG hyG hcG)
  have hspanFG : affineSpan ℝ F=affineSpan ℝ G := by
    apply (AffineSubspace.eq_iff_direction_eq_of_mem
      (mem_affineSpan ℝ hxF) (mem_affineSpan ℝ hxG)).mpr
    simpa only [direction_affineSpan] using heqdir
  rw [← body_inter_affineSpan_face P hF, ← body_inter_affineSpan_face P hG, hspanFG]

set_option maxHeartbeats 1600000 in
theorem summand_family_cofacial_degree
    (P A B : ConvexPolytope n) (hP : P.IsFullDim)
    (hSum : P.toSet=A.toSet+B.toSet)
    (a b : A.vertices) (hab : a ≠ b)
    (e : CrossingFamily P (summandLabel P A B hSum) a b) :
    n+1 ≤ (CrossingFamily.cofacialGraph (P := P)
      (color := summandLabel P A B hSum) (a := a) (b := b)).degree e + A.vertices.card := by
  let color := summandLabel P A B hSum
  let G := CrossingFamily.cofacialGraph (P := P) (color := color) (a := a) (b := b)
  let faces := incidentTwoFaces P e.left.val e.right.val
  let bad (F : ActualFaceType P) :=
    ∃z : P.vertices,z.val∈F.val ∧ color z≠a ∧ color z≠b
  let partner (F : ActualFaceType P) (f : CrossingFamily P color a b) :=
    e≠f ∧ CrossingFamily.liesIn F.val f
  have hmem (F : ActualFaceType P) (hF : F∈faces) :
      faceDim F.val=2 ∧ CrossingFamily.liesIn F.val e :=
    (Finset.mem_filter.mp hF).2
  have hbad : (faces.filter bad).card ≤ A.vertices.card-2 := by
    let others : Finset A.vertices := Finset.univ.erase a |>.erase b
    have hchoose (F : faces.filter bad) :
        ∃c : A.vertices,c∈others ∧ ∃z∈(facePolytope P F.val.property).vertices,
          leftVertexMap P A B hSum z=c.val := by
      obtain ⟨z,hz,hza,hzb⟩ := (Finset.mem_filter.mp F.property).2
      refine ⟨color z,?_,z.val,?_,rfl⟩
      · simp [others,hza,hzb]
      · exact (facePolytope_vertex_iff P F.val.property z.val).mpr ⟨z.property,hz⟩
    let pick : (faces.filter bad) → others :=
      fun F => ⟨(hchoose F).choose,(hchoose F).choose_spec.1⟩
    have hinj : Function.Injective pick := by
      intro F H heq
      apply Subtype.ext
      apply Subtype.ext
      have hFc := (hchoose F).choose_spec.2
      have hHc := (hchoose H).choose_spec.2
      have hc : (hchoose F).choose=(hchoose H).choose := congrArg Subtype.val heq
      rw [← hc] at hHc
      have hother : (hchoose F).choose≠a ∧ (hchoose F).choose≠b := by
        have hh := (hchoose F).choose_spec.1
        exact ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hh).2).1,
          (Finset.mem_erase.mp hh).1⟩
      exact twoFaces_eq_of_three_parallel_values P A (leftVertexMap P A B hSum)
        (leftVertexMap_parallel P A B hSum) a b (hchoose F).choose hab
        hother.1.symm hother.2.symm F.val.val H.val.val F.val.property H.val.property
        (hmem _ (Finset.mem_filter.mp F.property).1).1
        (hmem _ (Finset.mem_filter.mp H.property).1).1 e.left e.right
        (hmem _ (Finset.mem_filter.mp F.property).1).2.1
        (hmem _ (Finset.mem_filter.mp F.property).1).2.2
        (hmem _ (Finset.mem_filter.mp H.property).1).2.1
        (hmem _ (Finset.mem_filter.mp H.property).1).2.2
        (congrArg Subtype.val e.property.2.1) (congrArg Subtype.val e.property.2.2) hFc hHc
    have hc := Fintype.card_le_of_injective pick hinj
    have hc' : (faces.filter bad).card≤others.card := by
      simpa only [Fintype.card_coe] using hc
    have ho : others.card=A.vertices.card-2 := by
      simp [others,hab,Ne.symm hab]
      omega
    rwa [ho] at hc'
  have hfaces := incidentTwoFaces_card_actual P e.left.property e.isEdge
  have hcount := CofacialCounting.incident_count_le_degree_add_bad G e faces bad partner
    (A.vertices.card-2) hbad ?_ ?_
  · have hAcard : 2≤A.vertices.card := by
      have hc := Finset.card_le_card (Finset.subset_univ ({a,b} : Finset A.vertices))
      simpa [hab] using hc
    change P.dim=n at hP
    change P.dim≤faces.card+1 at hfaces
    change n+1≤G.degree e+A.vertices.card
    omega
  · intro F hF hgood
    obtain ⟨f,hef,hfF⟩ := CrossingFamily.second_edge_in_twoFace hab e F.val F.property
      (hmem F hF).1 (hmem F hF).2 (by
        intro x y hxF hyF hxy hxa hya
        by_contra hyb
        exact hgood ⟨y,hyF,hya,hyb⟩)
    exact ⟨f,⟨hef,F.val,F.property,(hmem F hF).1,(hmem F hF).2,hfF⟩,hef,hfF⟩
  · intro F hF H hH f hfF hfH
    apply Subtype.ext
    exact actual_twoFaces_eq_of_two_lines P F.val H.val F.property H.property
      F.property.2 H.property.2 (hmem F hF).1 (hmem H hH).1 e.line f.line
      (CrossingFamily.pair_line_rank_ge_three hab e f hfF.1)
      (Papers.Polytopes.ExposedProjectiveBridge.line_le_span (hmem F hF).2.1 (hmem F hF).2.2)
      (Papers.Polytopes.ExposedProjectiveBridge.line_le_span (hmem H hH).2.1 (hmem H hH).2.2)
      (Papers.Polytopes.ExposedProjectiveBridge.line_le_span hfF.2.1 hfF.2.2)
      (Papers.Polytopes.ExposedProjectiveBridge.line_le_span hfH.2.1 hfH.2.2)

end Papers.MinkowskiCofacialGeometry

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/MinkowskiForcedCenters.lean -/






@[expose] public section

/-! Projective centers forced in every realization by the actual summand data. -/
noncomputable section
namespace Papers.MinkowskiForcedCenters

open Set Module
open Papers.Polytopes Papers.ActualFaceOrder
open Papers.MinkowskiVertexMap Papers.MinkowskiCrossingCenters
open Papers.MinkowskiCofacialGeometry Papers.MinkowskiLabelCounting
open Papers.MinkowskiQuotientCounting
open Papers.Polytopes.CrossingFamilyTransport
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {n m : ℕ}

theorem family_degree_ge_codimension
    (P A B : ConvexPolytope n) (hP : P.IsFullDim)
    (hSum : P.toSet=A.toSet+B.toSet)
    (hr : 2≤A.dim) (hq : 3≤(quotientPolytope P A).dim)
    (hN : P.vertices.card≤4*n-5) (a b : A.vertices) (hab : a≠b)
    (e : CrossingFamily P (summandLabel P A B hSum) a b) :
    (quotientPolytope P A).dim ≤
      (CrossingFamily.cofacialGraph (P := P)
        (color := summandLabel P A B hSum) (a := a) (b := b)).degree e := by
  have h := summand_family_cofacial_degree P A B hP hSum a b hab e
  have ha := summand_minimal_vertices_of_codimension_at_least_three P A B hP hSum hr hq hN
  have hd := quotient_dimension_add_summand_dimension P A hP
  omega

theorem family_center_in_every_realization
    (P A B : ConvexPolytope n) (hP : P.IsFullDim)
    (hSum : P.toSet=A.toSet+B.toSet)
    (hr : 2≤A.dim) (hq : 3≤(quotientPolytope P A).dim)
    (hN : P.vertices.card≤4*n-5)
    (Q : ConvexPolytope m) (φ : FaceObject P ≃o FaceObject Q)
    (a b : A.vertices) (hab : a≠b)
    (e : CrossingFamily Q (colorAlong φ (summandLabel P A B hSum)) a b) :
    ∃J : Submodule ℝ (E m × ℝ),finrank ℝ J=1 ∧
      ∀f : CrossingFamily Q (colorAlong φ (summandLabel P A B hSum)) a b,J≤f.line := by
  let color := summandLabel P A B hSum
  have hd := minimum_degree_transport φ color a b (quotientPolytope P A).dim
    (family_degree_ge_codimension P A B hP hSum hr hq hN a b hab)
  have hc := family_card_lt_twice_codimension P A B hP hSum hr hq hN a b hab
  rw [family_card_eq φ color a b] at hc
  have hn := no_three_transport φ color a b (crossing_no_three P A B hSum a b hab)
  exact CrossingFamily.concurrent_of_dense_actual_cofacial_graph hab
    (quotientPolytope P A).dim (by omega) hd hc hn e

end Papers.MinkowskiForcedCenters

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/MinkowskiSmallFibers.lean -/






@[expose] public section

/-!
# Reconstruction from two actual small quotient fibers

The vertices of each homothetic fiber are labelled bijectively by the
actual summand vertices. When the summand has the minimum vertex number,
the fiber is a genuine simplex, hence every pair of its labelled vertices
is an edge. A support of the first fiber is strictly positive at the
second fiber after any face-order isomorphism. The normalized support
construction therefore supplies a nonhomothetic parallel map in the new
realization.
-/

noncomputable section
namespace Papers.MinkowskiSmallFibers

open Set Module
open Papers.Polytopes Papers.ActualFaceOrder
open Papers.MinkowskiVertexMap Papers.MinkowskiSummandFibers
open Papers.MinkowskiQuotientCounting Papers.MinkowskiCrossingCenters
open Papers.MinkowskiForcedCenters Papers.LinearImageFibers
open Papers.ParallelSupportEvaluation Papers.PolytopeSimpleTailFace
open Papers.Polytopes.CrossingFamilyTransport
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {n m : ℕ}

theorem fiberRepresentative_exists
    (P A B : ConvexPolytope n) (hSum : P.toSet=A.toSet+B.toSet)
    (q : (quotientPolytope P A).vertices) (a : A.vertices) :
    ∃x∈(vertexFiber P (summandProjection A) q).vertices,
      leftVertexMap P A B hSum x=a.val := by
  have h := a.property
  change a.val∈(A.vertices : Set (E n)) at h
  rw [← summand_vertexFiber_image P A B hSum q] at h
  exact h

def fiberRepresentative
    (P A B : ConvexPolytope n) (hSum : P.toSet=A.toSet+B.toSet)
    (q : (quotientPolytope P A).vertices) (a : A.vertices) : P.vertices :=
  let h := fiberRepresentative_exists P A B hSum q a
  ⟨h.choose,by
    exact ((facePolytope_vertex_iff P
      (maxFace_isFace P (fiberFunctional P (summandProjection A) q)) h.choose).mp
      h.choose_spec.1).1⟩

theorem fiberRepresentative_mem
    (P A B : ConvexPolytope n) (hSum : P.toSet=A.toSet+B.toSet)
    (q : (quotientPolytope P A).vertices) (a : A.vertices) :
    (fiberRepresentative P A B hSum q a).val∈
      (vertexFiber P (summandProjection A) q).vertices :=
  (fiberRepresentative_exists P A B hSum q a).choose_spec.1

theorem fiberRepresentative_label
    (P A B : ConvexPolytope n) (hSum : P.toSet=A.toSet+B.toSet)
    (q : (quotientPolytope P A).vertices) (a : A.vertices) :
    summandLabel P A B hSum (fiberRepresentative P A B hSum q a)=a := by
  apply Subtype.ext
  exact (fiberRepresentative_exists P A B hSum q a).choose_spec.2

theorem fiberRepresentative_project
    (P A B : ConvexPolytope n) (hSum : P.toSet=A.toSet+B.toSet)
    (q : (quotientPolytope P A).vertices) (a : A.vertices) :
    summandProjection A (fiberRepresentative P A B hSum q a).val=q.val := by
  have h := fiberRepresentative_mem P A B hSum q a
  rw [vertexFiber_vertices] at h
  exact (Finset.mem_filter.mp h).2

theorem fiberRepresentative_injective
    (P A B : ConvexPolytope n) (hSum : P.toSet=A.toSet+B.toSet)
    (q : (quotientPolytope P A).vertices) :
    Function.Injective (fiberRepresentative P A B hSum q) := by
  intro a b h
  have hh := congrArg (summandLabel P A B hSum) h
  simpa only [fiberRepresentative_label] using hh

theorem fiberRepresentative_edge
    (P A B : ConvexPolytope n) (hSum : P.toSet=A.toSet+B.toSet)
    (hAcard : A.vertices.card=A.dim+1)
    (q : (quotientPolytope P A).vertices)
    (hq : SummandHomotheticFiber P A B hSum q)
    (a b : A.vertices) (hab : a≠b) :
    GeneralVertexStep P (fiberRepresentative P A B hSum q a).val
      (fiberRepresentative P A B hSum q b).val := by
  let R := vertexFiber P (summandProjection A) q
  have hcard : R.vertices.card=R.dim+1 := by
    rw [homothetic_summand_fiber_card P A B hSum q hq,
      summand_vertexFiber_dim P A B hSum q,hAcard]
  have hAI := (vertices_affineIndependent_iff R).mpr hcard
  let x : VertexType R := ⟨(fiberRepresentative P A B hSum q a).val,
    fiberRepresentative_mem P A B hSum q a⟩
  let y : VertexType R := ⟨(fiberRepresentative P A B hSum q b).val,
    fiberRepresentative_mem P A B hSum q b⟩
  have hxy : x≠y := by
    intro h
    apply hab
    apply fiberRepresentative_injective P A B hSum q
    exact Subtype.ext (congrArg (fun t : VertexType R => t.val) h)
  have hedge := simplex_graph_adj R hAI x y hxy
  have hstep : GeneralVertexStep R x.val y.val :=
    ⟨y.property,fun h => hxy (Subtype.ext h),hedge.2⟩
  exact facePolytope_step P
    (maxFace_isFace P (fiberFunctional P (summandProjection A) q)) hstep

theorem decomposable_after_iso_of_two_simplex_fibers_and_centers
    (P A B : ConvexPolytope n) (hSum : P.toSet=A.toSet+B.toSet)
    (hApos : 0<A.dim) (hAcard : A.vertices.card=A.dim+1)
    (q0 q1 : (quotientPolytope P A).vertices) (hne : q0≠q1)
    (h0 : SummandHomotheticFiber P A B hSum q0)
    (h1 : SummandHomotheticFiber P A B hSum q1)
    (Q : ConvexPolytope m) (φ : FaceObject P ≃o FaceObject Q)
    (hcenters : ∀a b:A.vertices,a≠b→
      CrossingFamily Q (colorAlong φ (summandLabel P A B hSum)) a b→
      ∃J:Submodule ℝ (E m×ℝ),finrank ℝ J=1 ∧
        ∀e:CrossingFamily Q (colorAlong φ (summandLabel P A B hSum)) a b,J≤e.line) :
    MinkowskiDecomposable Q := by
  let color := summandLabel P A B hSum
  let colorQ := colorAlong φ color
  let x0 := fiberRepresentative P A B hSum q0
  let x1 := fiberRepresentative P A B hSum q1
  let y0 : A.vertices → Q.vertices := fun a => vertexEquiv φ (x0 a)
  let y1 : A.vertices → Q.vertices := fun a => vertexEquiv φ (x1 a)
  obtain ⟨a0,ha0⟩ := A.vertices_nonempty
  let label : E m → A.vertices := fun x => if h : x∈Q.vertices then colorQ ⟨x,h⟩ else ⟨a0,ha0⟩
  have label_vertex (x : Q.vertices) : label x.val=colorQ x := by
    simp only [label,dif_pos x.property]
  have label_y0 (a : A.vertices) : label (y0 a).val=a := by
    rw [label_vertex]
    change color ((vertexEquiv φ).symm (vertexEquiv φ (x0 a)))=a
    rw [Equiv.symm_apply_apply]
    exact fiberRepresentative_label P A B hSum q0 a
  have label_y1 (a : A.vertices) : label (y1 a).val=a := by
    rw [label_vertex]
    change color ((vertexEquiv φ).symm (vertexEquiv φ (x1 a)))=a
    rw [Equiv.symm_apply_apply]
    exact fiberRepresentative_label P A B hSum q1 a
  have hy01 (a : A.vertices) : (y0 a).val≠(y1 a).val := by
    intro h
    have hx := (vertexEquiv φ).injective (Subtype.ext h)
    have hp := congrArg (fun x : P.vertices => summandProjection A x.val) hx
    rw [fiberRepresentative_project,fiberRepresentative_project] at hp
    exact hne (Subtype.ext hp)
  have edge0 (a b : A.vertices) (hab : a≠b) : GeneralVertexStep Q (y0 a).val (y0 b).val :=
    edge_forward φ (x0 a) (x0 b) (fiberRepresentative_edge P A B hSum hAcard q0 h0 a b hab)
  have edge1 (a b : A.vertices) (hab : a≠b) : GeneralVertexStep Q (y1 a).val (y1 b).val :=
    edge_forward φ (x1 a) (x1 b) (fiberRepresentative_edge P A B hSum hAcard q1 h1 a b hab)
  let family0 (a b : A.vertices) (hab : a≠b) : CrossingFamily Q colorQ a b :=
    ⟨(y0 a,y0 b),edge0 a b hab,
      (label_vertex (y0 a)).symm.trans (label_y0 a),
      (label_vertex (y0 b)).symm.trans (label_y0 b)⟩
  have centers (a b : A.vertices) (hab : a≠b) :
      ∃J : Submodule ℝ (E m × ℝ),finrank ℝ J=1 ∧
        ∀e : CrossingFamily Q colorQ a b,J≤e.line :=
    hcenters a b hab (family0 a b hab)
  let J : A.vertices → A.vertices → Submodule ℝ (E m × ℝ) :=
    fun a b => if h : a≠b then (centers a b h).choose else ⊥
  have hJ (a b : A.vertices) (hab : a≠b) :
      finrank ℝ (J a b)=1 ∧ ∀e : CrossingFamily Q colorQ a b,J a b≤e.line := by
    have hJeq : J a b=(centers a b hab).choose := dif_pos hab
    rw [hJeq]
    exact (centers a b hab).choose_spec
  let F0 := Papers.MinkowskiFaces.maxFace P.toSet (fiberFunctional P (summandProjection A) q0).toLinearMap
  have hF0 : P.IsFace F0 := maxFace_isFace P (fiberFunctional P (summandProjection A) q0)
  let G0 := φ ⟨F0,hF0⟩
  obtain ⟨g,hg⟩ := exists_supportsFace Q G0.property
  have hy0G (a : A.vertices) : (y0 a).val∈G0.val := by
    apply (vertex_mem_face_iff φ (x0 a) ⟨F0,hF0⟩).mpr
    exact (facePolytope_vertex_iff P hF0 (x0 a).val).mp
      (fiberRepresentative_mem P A B hSum q0 a) |>.2
  have hy1notG (a : A.vertices) : (y1 a).val∉G0.val := by
    intro hy
    have hxF := (vertex_mem_face_iff φ (x1 a) ⟨F0,hF0⟩).mp hy
    have hxR := (facePolytope_vertex_iff P hF0 (x1 a).val).mpr ⟨(x1 a).property,hxF⟩
    change (x1 a).val∈(vertexFiber P (summandProjection A) q0).vertices at hxR
    rw [vertexFiber_vertices] at hxR
    have hp := (Finset.mem_filter.mp hxR).2
    rw [fiberRepresentative_project] at hp
    exact hne (Subtype.ext hp.symm)
  apply decomposable_of_supporting_center_data Q label g
    (fun a => (y0 a).val) (fun a => (y1 a).val) J
  · intro a
    exact hg.eq_zero (hy0G a)
  · intro a
    have hnonneg := hg.1 (y1 a).val (subset_convexHull ℝ _ (y1 a).property)
    have hneq : g (y1 a).val≠0 := by
      intro hz
      exact hy1notG a ((hg.mem_iff _).mpr ⟨subset_convexHull ℝ _ (y1 a).property,hz⟩)
    exact lt_of_le_of_ne hnonneg hneq.symm
  · exact label_y1
  · intro a
    exact ⟨(y0 a).val,(y0 a).property,(y1 a).val,(y1 a).property,
      hy01 a,label_y0 a,label_y1 a⟩
  · have hcard : 2≤Fintype.card A.vertices := by simpa only [Fintype.card_coe] using
        (show 2≤A.vertices.card by omega)
    exact Fintype.one_lt_card_iff.mp (by omega)
  · intro a b hab
    exact (hJ a b hab).1
  · intro a b hab
    exact (hJ a b hab).2 (family0 a b hab)
  · intro a b hab
    exact (hJ a b hab).2 ⟨(y1 a,y1 b),edge1 a b hab,
      (label_vertex (y1 a)).symm.trans (label_y1 a),
      (label_vertex (y1 b)).symm.trans (label_y1 b)⟩
  · intro x hx y hxy hlabel
    have hcx : colorQ ⟨x,hx⟩=label x := (label_vertex ⟨x,hx⟩).symm
    have hcy : colorQ ⟨y,hxy.1⟩=label y := (label_vertex ⟨y,hxy.1⟩).symm
    exact (hJ (label x) (label y) hlabel).2 ⟨(⟨x,hx⟩,⟨y,hxy.1⟩),hxy,hcx,hcy⟩

theorem decomposable_after_iso_of_two_homothetic_fibers
    (P A B : ConvexPolytope n) (hP : P.IsFullDim)
    (hSum : P.toSet=A.toSet+B.toSet)
    (hr : 2≤A.dim) (hq : 3≤(quotientPolytope P A).dim)
    (hN : P.vertices.card≤4*n-5)
    (q0 q1 : (quotientPolytope P A).vertices) (hne : q0≠q1)
    (h0 : SummandHomotheticFiber P A B hSum q0)
    (h1 : SummandHomotheticFiber P A B hSum q1)
    (Q : ConvexPolytope m) (φ : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  apply decomposable_after_iso_of_two_simplex_fibers_and_centers P A B hSum (by omega)
    (summand_minimal_vertices_of_codimension_at_least_three P A B hP hSum hr hq hN)
    q0 q1 hne h0 h1 Q φ
  intro a b hab e
  exact family_center_in_every_realization P A B hP hSum hr hq hN Q φ a b hab e

theorem proper_summand_dim_and_codim_at_least_three_universal
    (P A B : ConvexPolytope n) (hP : P.IsFullDim)
    (hSum : P.toSet=A.toSet+B.toSet)
    (hr : 3≤A.dim) (hq : 3≤(quotientPolytope P A).dim)
    (hN : P.vertices.card≤4*n-5)
    (Q : ConvexPolytope m) (φ : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  obtain ⟨q0,q1,hne,h0,h1⟩ := exists_two_homothetic_summand_fibers P A B hP hSum hr hq hN
  exact decomposable_after_iso_of_two_homothetic_fibers P A B hP hSum
    (by omega) hq hN q0 q1 hne h0 h1 Q φ

end Papers.MinkowskiSmallFibers

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/FourLineConcurrence.lean -/



@[expose] public section
noncomputable section
namespace Papers.FourLineConcurrence
open Set Module
open scoped Classical

variable {I : Type*} [Fintype I]

theorem closed_set_eq_univ_of_four
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (hcard : Fintype.card I≤4) (hdegree : ∀i,2≤G.degree i)
    (e:I) (hedeg:3≤G.degree e) (S:Set I) (he:e∈S) (hS:2≤Nat.card S)
    (hunique : ∀v∉S,∀x∈S,∀y∈S,G.Adj v x→G.Adj v y→x=y) : S=Set.univ := by
  classical
  have huniv : G.IsUniversal e := (G.degree_eq_card_sub_one e).mp
    (by have hh := G.degree_lt_card_verts e; omega)
  let T := S.toFinset
  have heT : e∈T := by simpa only [T,Set.mem_toFinset] using he
  have hTcard : 2≤T.card := by simpa only [T,Set.toFinset_card,Nat.card_eq_fintype_card] using hS
  obtain ⟨f,hfT,hfe⟩ := Finset.exists_mem_ne hTcard e
  have hfS : f∈S := by simpa only [T,Set.mem_toFinset] using hfT
  have hfN : G.neighborFinset f⊆T.erase f := by
    intro v hv
    have hfv := (G.mem_neighborFinset f v).mp hv
    refine Finset.mem_erase.mpr ⟨Ne.symm hfv.ne,?_⟩
    by_contra hn
    have hvS : v∉S := by simpa only [T,Set.mem_toFinset] using hn
    have hve : v≠e := fun h => hvS (h.symm ▸ he)
    have hveAdj := G.adj_symm (huniv (Ne.symm hve))
    have heq := hunique v hvS e he f hfS hveAdj (G.adj_symm hfv)
    exact hfe heq.symm
  have hlarge : 3≤T.card := by
    have hc := Finset.card_le_card hfN
    rw [SimpleGraph.card_neighborFinset_eq_degree,Finset.card_erase_of_mem hfT] at hc
    have hd := hdegree f
    omega
  apply Set.eq_univ_of_forall
  intro u
  by_contra hu
  have huT : u∉T := by simpa only [T,Set.mem_toFinset] using hu
  have huC : u∈(Finset.univ\T) := by simp [huT]
  have hNu : G.neighborFinset u⊆((Finset.univ\T).erase u)∪{e} := by
    intro v hv
    have huv := (G.mem_neighborFinset u v).mp hv
    by_cases hvS : v∈S
    · have hue : u≠e := fun h => hu (h.symm ▸ he)
      have hev := hunique u hu e he v hvS (G.adj_symm (huniv (Ne.symm hue))) huv
      exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hev.symm)
    · apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      refine ⟨Ne.symm huv.ne,?_⟩
      simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and,T,Set.mem_toFinset] using hvS
  have hc := (Finset.card_le_card hNu).trans (Finset.card_union_le _ _)
  rw [SimpleGraph.card_neighborFinset_eq_degree,Finset.card_erase_of_mem huC,
    Finset.card_singleton,Finset.card_sdiff_of_subset (Finset.subset_univ T),Finset.card_univ] at hc
  have hd := hdegree u
  omega

end Papers.FourLineConcurrence

namespace Papers.Polytopes.CrossingFamily
open Set Module Papers.Coordinates
open ExposedProjectiveBridge HomogeneousFaceSpans CrossingLineGeometry
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d:ℕ} {C:Type*} {P:ConvexPolytope d} {color:P.vertices→C} {a b:C}

theorem concurrent_of_four_with_high_degree
    (hab:a≠b)
    (hdegree:∀e:CrossingFamily P color a b,2≤(cofacialGraph (P:=P) (color:=color) (a:=a) (b:=b)).degree e)
    (hcard:Fintype.card (CrossingFamily P color a b)≤4)
    (hno3:∀F:Set (E d),P.IsFace F→faceDim F=2→
      ∀t:Fin 3→CrossingFamily P color a b,Function.Injective t→(∀i,liesIn F (t i))→False)
    (e:CrossingFamily P color a b)
    (hedeg:3≤(cofacialGraph (P:=P) (color:=color) (a:=a) (b:=b)).degree e) :
    ∃J:Submodule ℝ (E d×ℝ),finrank ℝ J=1∧∀f:CrossingFamily P color a b,J≤f.line := by
  let I := CrossingFamily P color a b
  let G := cofacialGraph (P:=P) (color:=color) (a:=a) (b:=b)
  have hn : (G.neighborFinset e).Nonempty := by
    apply Finset.card_pos.mp
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact lt_of_lt_of_le (by norm_num) hedeg
  obtain ⟨f,hf⟩ := hn
  have hef : G.Adj e f := (G.mem_neighborFinset e f).mp hf
  have hspan : finrank ℝ ↥(e.line⊔f.line)=3 :=
    le_antisymm (cofacial_pair_span_le_three e f hef) (pair_line_rank_ge_three hab e f hef.1)
  obtain ⟨J,hJ,hJe,hJf⟩ := common_point_of_coplanar_distinct_lines
    e.line f.line e.line_finrank_eq_two f.line_finrank_eq_two hspan
  let S : Set (CrossingFamily P color a b) :=
    {i | J≤CrossingFamily.line i}
  have hS : 2≤Nat.card S := by
    let se:S := ⟨e,hJe⟩
    let sf:S := ⟨f,hJf⟩
    have hne:se≠sf := fun h => hef.1 (congrArg Subtype.val h)
    have hc := Finset.card_mono (Finset.subset_univ ({se,sf}:Finset S))
    have hc2:({se,sf}:Finset S).card=2 := by simp [hne]
    rw [hc2,Finset.card_univ] at hc
    simpa only [Nat.card_eq_fintype_card] using hc
  have hclosed : ∀ v ∉ S, ∀ x ∈ S, ∀ y ∈ S,
      G.Adj v x → G.Adj v y → x = y := by
    intro v hv x hx y hy hvx hvy
    by_contra hxy
    obtain ⟨hvxne,F,hF,hFdim,hvF,hxF⟩ := hvx
    obtain ⟨hvyne,H,hH,hHdim,hvH,hyH⟩ := hvy
    have hlow : 3 ≤ finrank ℝ ↥(v.line ⊔ J) := by
      by_contra h
      have heq : v.line = v.line ⊔ J :=
        Submodule.eq_of_le_of_finrank_le le_sup_left
          (by have hd := v.line_finrank_eq_two; omega)
      apply hv
      change J ≤ v.line
      rw [heq]
      exact le_sup_right
    have hJF : J ≤ homogeneousSpan F :=
      hx.trans (line_le_span hxF.1 hxF.2)
    have hJH : J ≤ homogeneousSpan H :=
      hy.trans (line_le_span hyH.1 hyH.2)
    have hFH : F = H :=
      actual_twoFaces_eq_of_two_lines P F H hF hH hF.2 hH.2 hFdim hHdim
        v.line J hlow (line_le_span hvF.1 hvF.2) (line_le_span hvH.1 hvH.2) hJF hJH
    have hyF : liesIn F y := by rw [hFH]; exact hyH
    let t : Fin 3 → I := ![v,x,y]
    have hinj : Function.Injective t := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [t]
    apply hno3 F hF hFdim t hinj
    intro i
    fin_cases i
    · exact hvF
    · exact hxF
    · exact hyF
  have heqS : S=Set.univ := Papers.FourLineConcurrence.closed_set_eq_univ_of_four
    G hcard hdegree e hedeg S hJe hS hclosed
  refine ⟨J,hJ,?_⟩
  intro i
  have hi:i∈S := by rw [heqS]; trivial
  exact hi
end Papers.Polytopes.CrossingFamily

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/MinkowskiLargeCodimension.lean -/






@[expose] public section

/-! Persistence of every genuine summand of dimension and codimension at least two,
with quotient dimension at least three. -/
noncomputable section
namespace Papers.MinkowskiLargeCodimension

open Set Module
open Papers.Polytopes Papers.ActualFaceOrder
open Papers.MinkowskiQuotientCounting Papers.MinkowskiSummandFibers
open Papers.MinkowskiSmallFibers Papers.MinkowskiFiberPartition
open Papers.MinkowskiShephardNoExtras Papers.ExactShephardCriterion
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {n : ℕ}

theorem proper_summand_codimension_at_least_three_persists
    (P A B : ConvexPolytope n) (hfull : P.IsFullDim)
    (hsum : P.toSet=A.toSet+B.toSet)
    (hr : 2≤A.dim) (hq : 3≤(quotientPolytope P A).dim)
    (hN : P.vertices.card≤4*n-5)
    (Q : ConvexPolytope n) (hQ : Q.IsFullDim)
    (φ : FaceObject P ≃o FaceObject Q) : MinkowskiDecomposable Q := by
  have hdim := quotient_dimension_add_summand_dimension P A hfull
  obtain ⟨q0,hh0⟩ := exists_homothetic_summand_fiber P A B hfull hsum
    (by omega) (by omega) hN
  by_cases htwo : ∃q1:(quotientPolytope P A).vertices,
      q0≠q1 ∧ SummandHomotheticFiber P A B hsum q1
  · obtain ⟨q1,hne,hh1⟩ := htwo
    exact decomposable_after_iso_of_two_homothetic_fibers P A B hfull hsum hr hq hN
      q0 q1 hne hh0 hh1 Q φ
  · have hother : ∀q,q≠q0→¬SummandHomotheticFiber P A B hsum q := by
      intro q hne hh
      exact htwo ⟨q,hne.symm,hh⟩
    have hr2 : A.dim=2 := by
      by_contra hne
      obtain ⟨a,b,hab,ha,hb⟩ := exists_two_homothetic_summand_fibers P A B hfull hsum
        (by omega) hq hN
      by_cases heq : a=q0
      · exact hother b (by aesop) hb
      · exact hother a heq ha
    obtain ⟨hQcard,hcover⟩ := planar_unique_homothetic_fiber_saturation P A B
      hfull hsum hr2 hq hN q0 hother
    have hShephard := shephardFacet_of_simplex_quotient_no_extras P A B hfull hsum
      (by omega) hQcard (by omega) hcover q0 hh0
    exact decomposable_after_iso_of_exact_shephard_facet P hShephard Q hQ φ

end Papers.MinkowskiLargeCodimension

end
end
end BundlePart8

section BundlePart9
/- Source: Papers/ThreeDimensionalProperSummand.lean -/





@[expose] public section
noncomputable section
namespace Papers.ThreeDimensionalProperSummand

open Set Module
open Papers.Polytopes Papers.MinkowskiSummandFibers
open Papers.MinkowskiQuotientCounting Papers.MinkowskiCodimensionTwoCounts
open Papers.LinearImageFibers Papers.MinkowskiExtraFace
open Papers.SimplexQuotientOppositeFace Papers.MinkowskiShephardNoExtras
open Papers.ActualPaperCoverReduction Papers.ExactShephardCriterion Papers.ActualFaceOrder
open scoped Classical Pointwise BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

theorem shephard_of_two_dimensional_summand_with_at_most_seven_vertices
    (P A B : ConvexPolytope 3) (hP:P.IsFullDim)
    (hsum:P.toSet=A.toSet+B.toSet) (hr:A.dim=2) (hN:P.vertices.card≤7) :
    ExactShephardFacet P := by
  let Q := quotientPolytope P A
  let π := summandProjection A
  have hdim := quotient_dimension_add_summand_dimension P A hP
  have hqdim : Q.dim=1 := by change Q.dim+A.dim=3 at hdim; omega
  have ha := dimension_add_one_le_vertices A
  have hq := dimension_add_one_le_vertices Q
  have hp := actual_vertex_product_bound P A B hsum
  change A.vertices.card*Q.vertices.card≤P.vertices.card at hp
  have hacard : A.vertices.card=3 := by nlinarith
  have hqcard : Q.vertices.card=2 := by nlinarith
  have hminimal : Q.vertices.card=Q.dim+1 := by omega
  obtain ⟨q0,h0⟩ := exists_homothetic_summand_fiber P A B hP hsum (by omega)
    (by omega) (by simpa using hN)
  let sizes : Q.vertices→ℕ := fun q => (vertexFiber P π q).vertices.card
  have hpartition : (∑q:Q.vertices,sizes q)+(extraVertices P A).card=P.vertices.card :=
    fiber_extra_partition P A
  have hzero : sizes q0=3 := by
    change (vertexFiber P (summandProjection A) q0).vertices.card=3
    rw [homothetic_summand_fiber_card P A B hsum q0 h0,hacard]
  have hezero : (extraVertices P A).card=0 := by
    by_cases hall : ∀q:Q.vertices,SummandHomotheticFiber P A B hsum q
    · have hsumsize : (∑q:Q.vertices,sizes q)=6 := by
        have heach (q:Q.vertices):sizes q=3 := by
          change (vertexFiber P (summandProjection A) q).vertices.card=3
          rw [homothetic_summand_fiber_card P A B hsum q (hall q),hacard]
        simp only [heach,Finset.sum_const,Finset.card_univ,Fintype.card_coe,smul_eq_mul]
        rw [hqcard]
      by_contra he
      have hne : (extraVertices P A).Nonempty := Finset.card_pos.mp (by omega)
      have hlarge := extra_card_ge_summand_dimension P A B hsum (by omega)
        (actual_vertices_affineIndependent_of_minimal_card Q hminimal) hall hne
      omega
    · push_neg at hall
      obtain ⟨q,hbad⟩ := hall
      have hne : q0≠q := by intro h; subst q; exact hbad h0
      have hlarge := (summand_fiber_homothetic_or_large P A B hsum (by omega)
        (by change A.dim<P.dim; change P.dim=3 at hP; omega) q).resolve_left hbad
      change 2*A.dim≤sizes q at hlarge
      have hpair : sizes q0+sizes q≤∑q:Q.vertices,sizes q := by
        calc
          sizes q0+sizes q = ∑t∈({q0,q}:Finset Q.vertices),sizes t := by rw [Finset.sum_pair hne]
          _ ≤ ∑t:Q.vertices,sizes t := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
      omega
  have hcover : ∀x∈P.vertices,π x∈Q.vertices := by
    intro x hx
    by_contra hn
    have hm : x∈extraVertices P A := Finset.mem_filter.mpr ⟨hx,hn⟩
    rw [Finset.card_eq_zero.mp hezero] at hm
    exact Finset.notMem_empty _ hm
  exact shephardFacet_of_simplex_quotient_no_extras P A B hP hsum (by omega)
    hminimal (by omega) hcover q0 h0

theorem decomposable_after_iso_of_planar_summand_seven
    (P A B : ConvexPolytope 3) (hP:P.IsFullDim)
    (hsum:P.toSet=A.toSet+B.toSet) (hr:A.dim=2) (hN:P.vertices.card≤7)
    (Q:ConvexPolytope 3) (hQ:Q.IsFullDim) (φ:FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q :=
  decomposable_after_iso_of_exact_shephard_facet P
    (shephard_of_two_dimensional_summand_with_at_most_seven_vertices P A B hP hsum hr hN)
    Q hQ φ

end Papers.ThreeDimensionalProperSummand

end
end
end BundlePart9

section BundlePart10
/- Source: Papers/MinkowskiExtraVertexCount.lean -/




@[expose] public section

/-!
# Extra vertices outside a core of homothetic fibres

A violated side of the homothetic core exposes a face of the actual
Minkowski sum containing a translate of the corresponding summand face.
All vertices of this exposed face are outside the core.  Its dimension
therefore supplies the lower bound on the number of extra vertices.
-/

noncomputable section
namespace Papers.MinkowskiExtraVertexCount

open Set Module
open scoped Classical Pointwise
open Papers.MinkowskiFaces Papers.HomotheticFiberCore Papers.HomotheticFiberSide
open Papers.FiniteExposedFaces

variable {E F I : Type*}
  [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]

def translatedInl (b : E × F) : E →ᵃ[ℝ] (E × F) where
  toFun a := (LinearMap.inl ℝ E F) a + b
  linear := LinearMap.inl ℝ E F
  map_vadd' a v := by simp only [vadd_eq_add, map_add, add_assoc]

theorem extra_card_of_violated_side
    (X : Finset (E × F)) (hX : X.Nonempty)
    (A : Set E) (B : Set (E × F)) (Q : Set F)
    (hP : convexHull ℝ (X : Set (E × F)) =
      ((LinearMap.inl ℝ E F) '' A) + B)
    (hA : Convex ℝ A) (scale : F →ᵃ[ℝ] ℝ) (shift : F →ᵃ[ℝ] E)
    (hscale : ∀ q ∈ Q, 0 < scale q)
    (u : E →ₗ[ℝ] ℝ) (c : ℝ) (hu : ∀ a ∈ A, u a ≤ c)
    (hface : (maxFace A u).Nonempty)
    (hw : ∃ w ∈ convexHull ℝ (X : Set (E × F)),
      sideConstant scale shift u c < sideNormal scale shift u c w) :
    finrank ℝ (vectorSpan ℝ (maxFace A u)) + 1 ≤
      (X.filter fun x => x ∉ convexHull ℝ (fibres A Q scale shift)).card := by
  let U := sideNormal scale shift u c
  let C := convexHull ℝ (fibres A Q scale shift)
  have hne : (maxFace (((LinearMap.inl ℝ E F) '' A) + B) U).Nonempty := by
    rw [← hP]
    exact maxFace_convexHull_nonempty X hX U
  obtain ⟨b,hb,himage⟩ :=
    contains_translated_summand_face A B scale shift u c hne
  have himage' : (translatedInl b) '' maxFace A u ⊆
      maxFace (convexHull ℝ (X : Set (E × F))) U := by
    rw [hP]
    exact himage
  have hdis : Disjoint (maxFace (convexHull ℝ (X : Set (E × F))) U) C :=
    maxFace_disjoint_of_strict_witness U (sideConstant scale shift u c)
      (side_inequality_on_core hA scale shift hscale u c hu) hw
  exact outside_card_of_exposed_affineImage X U C hface (translatedInl b)
    (LinearMap.inl_injective (R := ℝ) (M := E) (M₂ := F)) himage' hdis

/-- A facet presentation of the summand turns any point outside the
homothetic core, but over its quotient, into a lower bound on extras. -/
theorem extra_card_of_point_outside_core
    (X : Finset (E × F)) (hX : X.Nonempty)
    (A : Set E) (B : Set (E × F)) (Q : Set F)
    (hP : convexHull ℝ (X : Set (E × F)) =
      ((LinearMap.inl ℝ E F) '' A) + B)
    (hA : Convex ℝ A) (scale : F →ᵃ[ℝ] ℝ) (shift : F →ᵃ[ℝ] E)
    (hscale : ∀ q ∈ Q, 0 < scale q)
    (normal : I → E →ₗ[ℝ] ℝ) (bound : I → ℝ)
    (hdescr : ∀ a, a ∈ A ↔ ∀ i, normal i a ≤ bound i)
    (hfaces : ∀ i, (maxFace A (normal i)).Nonempty)
    (r : ℕ)
    (hdim : ∀ i, r ≤ finrank ℝ (vectorSpan ℝ (maxFace A (normal i))) + 1)
    {z : E × F} (hz : z ∈ convexHull ℝ (X : Set (E × F)))
    (hq : z.2 ∈ convexHull ℝ Q)
    (hout : z ∉ convexHull ℝ (fibres A Q scale shift)) :
    r ≤ (X.filter fun x => x ∉ convexHull ℝ (fibres A Q scale shift)).card := by
  obtain ⟨i,hviolate⟩ :=
    exists_violated_side hA scale shift hscale normal bound hdescr hq hout
  have hw : sideConstant scale shift (normal i) (bound i) <
      sideNormal scale shift (normal i) (bound i) z := by
    apply lt_of_not_ge
    intro h
    have hle := (sideNormal_le_iff scale shift (normal i) (bound i) z).mp h
    exact (not_lt_of_ge hle) hviolate
  exact (hdim i).trans
    (extra_card_of_violated_side X hX A B Q hP hA scale shift hscale
      (normal i) (bound i) (fun a ha => (hdescr a).mp ha i)
      (hfaces i) ⟨z,hz,hw⟩)

end Papers.MinkowskiExtraVertexCount

end
end
end BundlePart10

section BundlePart11
/- Source: Papers/ExposedFaceCountEquality.lean -/




@[expose] public section

/-!
# Equality in the exposed-face count

If the total number of points outside a core is no greater than the
minimum required by a translated summand face, every outside point lies
on the same exposed face.  Those points are affinely independent, and
their direction space is exactly that of the contained summand face.
For an inl-translate this also forces a single quotient position.
-/

noncomputable section
namespace Papers.ExposedFaceCountEquality

open Set Module AffineSubspace
open Papers.MinkowskiFaces Papers.FiniteExposedFaces
open Papers.FaceVertexCardinality Papers.MinkowskiExtraVertexCount
open scoped Classical

variable {E F : Type*}
  [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]

theorem equality_case
    (X : Finset F) (u : F →ₗ[ℝ] ℝ) (C : Set F)
    {S : Set E} (hS : S.Nonempty)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f.linear)
    (himage : f '' S ⊆ maxFace (convexHull ℝ (X : Set F)) u)
    (hdis : Disjoint (maxFace (convexHull ℝ (X : Set F)) u) C)
    (hcard : (X.filter fun x => x ∉ C).card ≤ finrank ℝ (vectorSpan ℝ S) + 1) :
    (X.filter fun x => x ∈ maxFace (convexHull ℝ (X : Set F)) u) =
        (X.filter fun x => x ∉ C) ∧
    maxFace (convexHull ℝ (X : Set F)) u =
        convexHull ℝ (↑(X.filter fun x => x ∉ C) : Set F) ∧
    (X.filter fun x => x ∉ C).card = finrank ℝ (vectorSpan ℝ S) + 1 ∧
    vectorSpan ℝ (maxFace (convexHull ℝ (X : Set F)) u) =
        (vectorSpan ℝ S).map f.linear ∧
    AffineIndependent ℝ (fun v : (X.filter fun x => x ∉ C) => (v : F)) := by
  let A := maxFace (convexHull ℝ (X : Set F)) u
  let M := X.filter fun x => x ∈ A
  let Y := X.filter fun x => x ∉ C
  have hM : A = convexHull ℝ (M : Set F) := maxFace_convexHull X u
  have hMY : M ⊆ Y := by
    intro x hx
    obtain ⟨hxX,hxA⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr
      ⟨hxX,fun hxC => Set.disjoint_left.mp hdis hxA hxC⟩
  have himageM : f '' S ⊆ convexHull ℝ (M : Set F) := by
    rw [← hM]
    exact himage
  have hMlow := dimension_add_one_le_card_of_affineImage_subset_hull hS f hf M himageM
  have hMYcard := Finset.card_le_card hMY
  change Y.card≤finrank ℝ (vectorSpan ℝ S)+1 at hcard
  have hYcard : Y.card = finrank ℝ (vectorSpan ℝ S) + 1 := by omega
  have hMeq : M = Y :=
    Finset.eq_of_subset_of_card_le hMY (by omega)
  have hA : A = convexHull ℝ (Y : Set F) := hM.trans (by rw [hMeq])
  have hAn : A.Nonempty := (hS.image f).mono himage
  have hAlow := Submodule.finrank_mono (vectorSpan_mono ℝ himage)
  rw [finrank_vectorSpan_affineImage f hf S] at hAlow
  change finrank ℝ (vectorSpan ℝ S)≤finrank ℝ (vectorSpan ℝ A) at hAlow
  have hAhigh : finrank ℝ (vectorSpan ℝ A) + 1 ≤ Y.card :=
    dimension_add_one_le_card_of_subset_hull hAn Y hA.subset
  have hAdim : finrank ℝ (vectorSpan ℝ A) = finrank ℝ (vectorSpan ℝ S) := by
    omega
  have hsub : (vectorSpan ℝ S).map f.linear ≤ vectorSpan ℝ A := by
    rw [AffineMap.map_vectorSpan f]
    exact vectorSpan_mono ℝ himage
  have hdir : vectorSpan ℝ A = (vectorSpan ℝ S).map f.linear := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq hsub
    rw [AffineMap.map_vectorSpan f,finrank_vectorSpan_affineImage f hf S]
    exact hAdim.symm
  have hYdim : finrank ℝ (vectorSpan ℝ (Y : Set F)) =
      finrank ℝ (vectorSpan ℝ S) := by
    rw [hA] at hAdim
    have hspan : vectorSpan ℝ (convexHull ℝ (Y : Set F)) =
        vectorSpan ℝ (Y : Set F) := by
      rw [← direction_affineSpan,affineSpan_convexHull,direction_affineSpan]
    rwa [hspan] at hAdim
  have hrange : Set.range (fun v : Y => (v : F)) = (Y : Set F) := by
    ext x
    constructor
    · rintro ⟨v,rfl⟩
      exact v.property
    · intro hx
      exact ⟨⟨x,hx⟩,rfl⟩
  have hYi : AffineIndependent ℝ (fun v : Y => (v : F)) := by
    apply (affineIndependent_iff_finrank_vectorSpan_eq ℝ
      (fun v : Y => (v : F)) (by simpa using hYcard)).mpr
    exact (congrArg (fun T:Set F => finrank ℝ (vectorSpan ℝ T)) hrange).trans hYdim
  exact ⟨hMeq,hA,hYcard,hdir,hYi⟩

variable {G : Type*} [AddCommGroup G] [Module ℝ G] [FiniteDimensional ℝ G]

theorem quotient_constant_of_equality
    (X : Finset (E × G)) (u : (E × G) →ₗ[ℝ] ℝ) (C : Set (E × G))
    {S : Set E} (hS : S.Nonempty) (b : E × G)
    (himage : (translatedInl b) '' S ⊆ maxFace (convexHull ℝ (X : Set (E × G))) u)
    (hdis : Disjoint (maxFace (convexHull ℝ (X : Set (E × G))) u) C)
    (hcard : (X.filter fun x => x ∉ C).card ≤ finrank ℝ (vectorSpan ℝ S) + 1) :
    ∀ x ∈ X, x ∉ C → x.2 = b.2 := by
  obtain ⟨hM,hA,hYcard,hdir,hind⟩ :=
    equality_case X u C hS (translatedInl b)
      (LinearMap.inl_injective (R := ℝ) (M := E) (M₂ := G)) himage hdis hcard
  obtain ⟨a,ha⟩ := hS
  have hbase : translatedInl b a ∈
      maxFace (convexHull ℝ (X : Set (E × G))) u :=
    himage ⟨a,ha,rfl⟩
  intro x hxX hxC
  have hxM : x ∈ X.filter
      (fun y => y ∈ maxFace (convexHull ℝ (X : Set (E × G))) u) := by
    rw [hM]
    exact Finset.mem_filter.mpr ⟨hxX,hxC⟩
  have hxF := (Finset.mem_filter.mp hxM).2
  have hd := vsub_mem_vectorSpan ℝ hxF hbase
  rw [hdir] at hd
  obtain ⟨v,hv,hveq⟩ := Submodule.mem_map.mp hd
  have hzero : x.2 - b.2 = 0 := by
    have h := congrArg Prod.snd hveq
    simpa [translatedInl,vsub_eq_sub] using h.symm
  exact sub_eq_zero.mp hzero

end Papers.ExposedFaceCountEquality

end
end
end BundlePart11

