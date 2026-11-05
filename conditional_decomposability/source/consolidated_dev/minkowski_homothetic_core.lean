module
public import consolidated_dev.minkowski_fiber_geometry
public import consolidated_dev.affine_interpolation

set_option Elab.async false

section BundlePart0
/- Source: Papers/AmbientHomotheticCore.lean -/






@[expose] public section

/-! Positive homothetic fiber cores in the original ambient space.

The summand may have any intrinsic dimension.  Its facet inequalities
are used only on its affine span, so no full-dimensional presentation
is silently imposed on a proper summand.
-/
noncomputable section
namespace Papers.AmbientHomotheticCore

open Set Module
open Papers.HomotheticFiberCore Papers.Polytopes Papers.ProperMinkowskiMap
open Papers.RelativeFacetHalfspaces
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n : ℕ}

def ambientFibres (A Q : Set (E n)) (scale : E n →ᵃ[ℝ] ℝ)
    (shift : E n →ᵃ[ℝ] E n) : Set (E n) :=
  (LinearMap.fst ℝ (E n) (E n)) '' fibres A Q scale shift

theorem mem_ambientFibres (A Q : Set (E n)) (scale : E n →ᵃ[ℝ] ℝ)
    (shift : E n →ᵃ[ℝ] E n) (x : E n) :
    x∈ambientFibres A Q scale shift ↔
      ∃q∈Q,∃a∈A,x=scale q•a+shift q := by
  constructor
  · rintro ⟨z,⟨hz,a,ha,he⟩,rfl⟩
    exact ⟨z.2,hz,a,ha,he⟩
  · rintro ⟨q,hq,a,ha,he⟩
    exact ⟨(x,q),⟨hq,a,ha,he⟩,rfl⟩

theorem convexHull_ambientFibres (A Q : Set (E n)) (hA : Convex ℝ A)
    (scale : E n →ᵃ[ℝ] ℝ) (shift : E n →ᵃ[ℝ] E n)
    (hs : ∀q∈Q,0<scale q) :
    convexHull ℝ (ambientFibres A Q scale shift)=
      ambientFibres A (convexHull ℝ Q) scale shift := by
  rw [ambientFibres,← LinearMap.image_convexHull,convexHull_fibres hA scale shift hs]
  rfl

def sideForm (π : E n →L[ℝ] E n) (scale : E n →ᵃ[ℝ] ℝ)
    (shift : E n →ᵃ[ℝ] E n) (g : E n →ᵃ[ℝ] ℝ) : E n →ᵃ[ℝ] ℝ :=
  g.linear.toAffineMap - g.linear.toAffineMap.comp (shift.comp π.toLinearMap.toAffineMap) +
    (g 0) • (scale.comp π.toLinearMap.toAffineMap)

theorem sideForm_apply (π : E n →L[ℝ] E n) (scale : E n →ᵃ[ℝ] ℝ)
    (shift : E n →ᵃ[ℝ] E n) (g : E n →ᵃ[ℝ] ℝ) (x : E n) :
    sideForm π scale shift g x=g.linear x-g.linear (shift (π x))+(g 0)*scale (π x) := by
  rfl

theorem sideForm_normalized (π : E n →L[ℝ] E n) (scale : E n →ᵃ[ℝ] ℝ)
    (shift : E n →ᵃ[ℝ] E n) (g : E n →ᵃ[ℝ] ℝ) (x : E n)
    (hs : scale (π x)≠0) :
    sideForm π scale shift g x=
      scale (π x)*g ((scale (π x))⁻¹•(x-shift (π x))) := by
  rw [sideForm_apply,affine_form_apply g ((scale (π x))⁻¹•(x-shift (π x)))]
  simp only [map_smul,map_sub,smul_eq_mul]
  field_simp

theorem sideForm_linear_on_kernel
    (π : E n →L[ℝ] E n) (scale : E n →ᵃ[ℝ] ℝ)
    (shift : E n →ᵃ[ℝ] E n) (g : E n →ᵃ[ℝ] ℝ)
    {z : E n} (hz : π z=0) :
    (sideForm π scale shift g).linear z=g.linear z := by
  change g.linear z-g.linear (shift.linear (π z))+(g 0)•scale.linear (π z)=g.linear z
  simp only [hz,map_zero,smul_zero,sub_zero,add_zero]

theorem normalized_point_in_affineSpan
    (A : ConvexPolytope n) (π : E n →L[ℝ] E n)
    (hker : π.ker=vectorSpan ℝ A.toSet) (a0 : E n) (ha0 : a0∈A.toSet)
    (scale : E n →ᵃ[ℝ] ℝ) (shift : E n →ᵃ[ℝ] E n)
    (x : E n) (hs : scale (π x)≠0)
    (hproj : π (shift (π x))+scale (π x)•π a0=π x) :
    (scale (π x))⁻¹•(x-shift (π x))∈affineSpan ℝ A.toSet := by
  let a := (scale (π x))⁻¹•(x-shift (π x))
  have hk : a-a0∈π.ker := by
    change π (a-a0)=0
    have heq : π x-π (shift (π x))=scale (π x)•π a0 := by
      calc
        π x-π (shift (π x)) =
            (π (shift (π x))+scale (π x)•π a0)-π (shift (π x)) :=
          congrArg (fun z => z-π (shift (π x))) hproj.symm
        _ = scale (π x)•π a0 := by abel
    simp only [a,map_sub,map_smul,heq,smul_smul,inv_mul_cancel₀ hs,one_smul,sub_self]
  rw [hker] at hk
  have hm := vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan
    (mem_affineSpan ℝ ha0) hk
  simpa only [vadd_eq_add,sub_add_cancel] using hm

theorem violated_facet_side
    (A : ConvexPolytope n) (π : E n →L[ℝ] E n)
    (hker : π.ker=vectorSpan ℝ A.toSet) (a0 : E n) (ha0 : a0∈A.toSet)
    (Q : Set (E n)) (scale : E n →ᵃ[ℝ] ℝ) (shift : E n →ᵃ[ℝ] E n)
    (hs : ∀q∈Q,0<scale q) (x : E n) (hxq : π x∈convexHull ℝ Q)
    (hproj : π (shift (π x))+scale (π x)•π a0=π x)
    (hout : x∉convexHull ℝ (ambientFibres A.toSet Q scale shift)) :
    ∃F:FacetType A,sideForm π scale shift (chosenFacetForm A F) x<0 := by
  have hpos := positive_on_convexHull scale hs (π x) hxq
  let a := (scale (π x))⁻¹•(x-shift (π x))
  have haSpan : a∈affineSpan ℝ A.toSet :=
    normalized_point_in_affineSpan A π hker a0 ha0 scale shift x hpos.ne' hproj
  have haout : a∉A.toSet := by
    intro ha
    apply hout
    rw [convexHull_ambientFibres A.toSet Q (convex_convexHull ℝ (A.vertices : Set (E n))) scale shift hs,
      mem_ambientFibres]
    refine ⟨π x,hxq,a,ha,?_⟩
    simp only [a,smul_smul,mul_inv_cancel₀ hpos.ne',one_smul,sub_add_cancel]
  have hbad : ¬∀F:FacetType A,0≤chosenFacetForm A F a := by
    intro h
    exact haout ((mem_body_iff_span_and_chosenFacetForms A a).mpr ⟨haSpan,h⟩)
  push_neg at hbad
  obtain ⟨F,hF⟩ := hbad
  refine ⟨F,?_⟩
  rw [sideForm_normalized π scale shift _ x hpos.ne']
  exact mul_neg_of_pos_of_neg hpos hF

end Papers.AmbientHomotheticCore

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/MinkowskiHomotheticCore.lean -/




@[expose] public section

/-! Affine scale and translation functions are derived from actual
homothetic quotient fibers.  No interpolation data are assumed. -/
noncomputable section
namespace Papers.MinkowskiHomotheticCore

open Set Module
open Papers.Polytopes Papers.ProperMinkowskiMap Papers.AffineInterpolation
open Papers.MinkowskiPositiveFibers Papers.MinkowskiSummandFibers
open Papers.MinkowskiQuotientCounting Papers.LinearImageFibers
open Papers.AmbientHomotheticCore Papers.PolytopeSimpleTailFace
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {n : ℕ}

theorem vertexFiber_toSet (P : ConvexPolytope n) (π : E n →L[ℝ] E n)
    (q : (Papers.FiniteHullPolytope.imagePolytope P π).vertices) :
    (vertexFiber P π q).toSet={x∈P.toSet | π x=q.val} := by
  rw [vertexFiber,facePolytope_toSet,fiberFunctional_face]

theorem exists_actual_core_parameters
    (P A B : ConvexPolytope n) (hsum : P.toSet=A.toSet+B.toSet)
    (hApos : 0<A.dim)
    (hAI : AffineIndependent ℝ (fun q : (quotientPolytope P A).vertices => q.val))
    (hhom : ∀q:(quotientPolytope P A).vertices,SummandHomotheticFiber P A B hsum q)
    (a0 : E n) (ha0 : a0∈A.toSet) :
    ∃scale:E n →ᵃ[ℝ] ℝ,∃shift:E n →ᵃ[ℝ] E n,
      (∀q∈(quotientPolytope P A).vertices,0<scale q) ∧
      (∀q:(quotientPolytope P A).vertices,
        (vertexFiber P (summandProjection A) q).toSet=
          homothetyMap (scale q.val) (shift q.val) '' A.toSet) ∧
      ∀q∈(quotientPolytope P A).toSet,
        summandProjection A (shift q)+scale q•summandProjection A a0=q := by
  let Q := quotientPolytope P A
  let π := summandProjection A
  have hcopies (q:Q.vertices) :=
    summand_fiber_is_positive_homothetic_copy P A B hsum hApos q (hhom q)
  choose lam t hlam hbody using hcopies
  obtain ⟨scale,hscale⟩ := exists_affine_interpolant
    (fun q:Q.vertices => q.val) hAI lam
  obtain ⟨shift,hshift⟩ := exists_affine_interpolant
    (fun q:Q.vertices => q.val) hAI t
  have hscalePos : ∀q∈Q.vertices,0<scale q := by
    intro q hq
    rw [hscale ⟨q,hq⟩]
    exact hlam ⟨q,hq⟩
  have hbody' (q:Q.vertices) : (vertexFiber P π q).toSet=
      homothetyMap (scale q.val) (shift q.val) '' A.toSet := by
    rw [hscale q,hshift q]
    exact hbody q
  refine ⟨scale,shift,hscalePos,hbody',?_⟩
  let K : E n →ᵃ[ℝ] E n :=
    π.toLinearMap.toAffineMap.comp shift +
      ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (π a0)).toAffineMap.comp scale
  have hK : Set.EqOn K (AffineMap.id ℝ (E n)) (Q.vertices : Set (E n)) := by
    intro q hq
    have hm : homothetyMap (scale q) (shift q) a0∈(vertexFiber P π ⟨q,hq⟩).toSet := by
      rw [hbody']
      exact ⟨a0,ha0,rfl⟩
    rw [vertexFiber_toSet] at hm
    have heq := hm.2
    change π (scale q•a0+shift q)=q at heq
    rw [map_add,map_smul] at heq
    change π (shift q)+scale q•π a0=q
    simpa only [add_comm] using heq
  intro q hq
  exact AffineMap.eqOn_affineSpan hK
    (convexHull_subset_affineSpan (Q.vertices : Set (E n)) hq)

def vertexCore (P A : ConvexPolytope n) : Set (E n) :=
  convexHull ℝ ((P.vertices.filter fun x =>
    summandProjection A x∈(quotientPolytope P A).vertices) : Set (E n))

theorem vertexCore_eq_ambientFibres
    (P A : ConvexPolytope n) (scale : E n →ᵃ[ℝ] ℝ)
    (shift : E n →ᵃ[ℝ] E n)
    (hs : ∀q∈(quotientPolytope P A).vertices,0<scale q)
    (hbody : ∀q:(quotientPolytope P A).vertices,
      (vertexFiber P (summandProjection A) q).toSet=
        homothetyMap (scale q.val) (shift q.val) '' A.toSet) :
    vertexCore P A=
      ambientFibres A.toSet (quotientPolytope P A).toSet scale shift := by
  let Q := quotientPolytope P A
  let π := summandProjection A
  let T := P.vertices.filter fun x => π x∈Q.vertices
  have hC : convexHull ℝ (T : Set (E n))=
      convexHull ℝ (ambientFibres A.toSet (Q.vertices : Set (E n)) scale shift) := by
    apply Set.Subset.antisymm
    · apply convexHull_mono
      intro x hx
      obtain ⟨hx,hπx⟩ := Finset.mem_filter.mp hx
      have hxR : x∈(vertexFiber P π ⟨π x,hπx⟩).toSet := by
        rw [vertexFiber_toSet]
        exact ⟨subset_convexHull ℝ _ hx,rfl⟩
      rw [hbody] at hxR
      obtain ⟨a,ha,hax⟩ := hxR
      exact (mem_ambientFibres _ _ _ _ _).mpr ⟨π x,hπx,a,ha,hax.symm⟩
    · apply convexHull_min _ (convex_convexHull ℝ _)
      intro x hx
      obtain ⟨q,hq,a,ha,hx⟩ := (mem_ambientFibres _ _ _ _ _).mp hx
      have hxR : x∈(vertexFiber P π ⟨q,hq⟩).toSet := by
        rw [hbody]
        exact ⟨a,ha,hx.symm⟩
      apply convexHull_mono (s := ((vertexFiber P π ⟨q,hq⟩).vertices : Set (E n))) _ hxR
      intro y hy
      rw [vertexFiber_vertices] at hy
      obtain ⟨hy,hπy⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hy,hπy.symm ▸ hq⟩
  change convexHull ℝ (T : Set (E n))=ambientFibres A.toSet Q.toSet scale shift
  rw [hC,convexHull_ambientFibres A.toSet _ (convex_convexHull ℝ _) scale shift hs]
  rfl

theorem extra_vertex_not_in_core (P A : ConvexPolytope n)
    {x:E n} (hx:x∈P.vertices)
    (hout:summandProjection A x∉(quotientPolytope P A).vertices) :
    x∉vertexCore P A := by
  intro hc
  let T := P.vertices.filter fun x => summandProjection A x∈(quotientPolytope P A).vertices
  have hsub : convexHull ℝ (T : Set (E n))⊆P.toSet :=
    convexHull_mono (Finset.filter_subset _ _)
  have hext : x∈Set.extremePoints ℝ (convexHull ℝ (T : Set (E n))) := by
    apply mem_extremePoints_iff_forall_segment.mpr
    refine ⟨hc,?_⟩
    intro y hy z hz hseg
    exact (mem_extremePoints_iff_forall_segment.mp (vertex_mem_body_extremePoints P hx)).2
      y (hsub hy) z (hsub hz) hseg
  have hT := extremePoints_convexHull_subset hext
  exact hout (Finset.mem_filter.mp hT).2

end Papers.MinkowskiHomotheticCore

end
end
end BundlePart1
