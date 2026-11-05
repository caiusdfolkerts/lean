module

public import Ellipsoid.CoefficientProperness
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Ring.Units

@[expose] public section

/-!
# The coefficient transform as an actual manifold-with-corners embedding

The source is Mathlib's `EuclideanQuadrant m`, with its standard quadrant
model. The map is the literal coefficient transform, transported only by the
continuous linear equivalence between Euclidean coordinates and a finite
function space. The complement in the immersion charts is the zero space.

For each boundary point, an ambient inverse-function chart is restricted to
an open set on which the derivative remains invertible. Its inverse is smooth
on that whole chart, not merely smooth to each finite order at the centre.
This supplies the actual `Manifold.IsSmoothEmbedding ... ∞` predicate.
Properness and the closed-image assertion are transported by the explicit
homeomorphism with the already checked closed coefficient orthant.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold Matrix

namespace EllipsoidVerification

/-- The standard coordinate identification, with no change of the entries. -/
def coefficientEuclideanCoordinates (m : ℕ) :
    EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)

@[simp] theorem coefficientEuclideanCoordinates_apply (m : ℕ)
    (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    coefficientEuclideanCoordinates m x i = x i := rfl

/-- The two literal closed-orthant representations are homeomorphic. -/
def quadrantCoefficientOrthantHomeomorph (m : ℕ) :
    EuclideanQuadrant m ≃ₜ closedCoefficientOrthant m where
  toFun x := ⟨coefficientEuclideanCoordinates m x.val, x.property⟩
  invFun x := ⟨(coefficientEuclideanCoordinates m).symm x.val, x.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (coefficientEuclideanCoordinates m).symm_apply_apply x.val
  right_inv x := by
    apply Subtype.ext
    exact (coefficientEuclideanCoordinates m).apply_symm_apply x.val
  continuous_toFun :=
    ((coefficientEuclideanCoordinates m).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((coefficientEuclideanCoordinates m).symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- The actual coefficient map on the standard quadrant manifold. -/
def quadrantCoefficientMap (m : ℕ) (e0 en : ℝ) :
    EuclideanQuadrant m → (Fin m → ℝ) :=
  restrictedCoefficientMap m e0 en ∘ quadrantCoefficientOrthantHomeomorph m

@[simp] theorem quadrantCoefficientMap_apply (m : ℕ) (e0 en : ℝ)
    (x : EuclideanQuadrant m) :
    quadrantCoefficientMap m e0 en x =
      coefficientMap m e0 en (fun i => x.val i) := rfl

theorem quadrantCoefficientMap_isProperMap {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) :
    IsProperMap (quadrantCoefficientMap m e0 en) :=
  (restrictedCoefficientMap_isProperMap h0 hn).comp
    (quadrantCoefficientOrthantHomeomorph m).isProperMap

theorem quadrantCoefficientMap_isClosedEmbedding {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) :
    Topology.IsClosedEmbedding (quadrantCoefficientMap m e0 en) :=
  (restrictedCoefficientMap_isClosedEmbedding h0 hn).comp
    (quadrantCoefficientOrthantHomeomorph m).isClosedEmbedding

theorem range_quadrantCoefficientMap (m : ℕ) (e0 en : ℝ) :
    Set.range (quadrantCoefficientMap m e0 en) =
      coefficientMap m e0 en '' closedCoefficientOrthant m := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(quadrantCoefficientOrthantHomeomorph m).symm ⟨x, hx⟩, ?_⟩
    change restrictedCoefficientMap m e0 en
      (quadrantCoefficientOrthantHomeomorph m
        ((quadrantCoefficientOrthantHomeomorph m).symm ⟨x, hx⟩)) = _
    rw [Homeomorph.apply_symm_apply]
    rfl

section AmbientChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A smooth ambient map with an invertible derivative has one chart whose
forward and inverse maps are smooth on their entire open domains. -/
theorem exists_smooth_ambient_inverse_chart
    {f : E → E} {U : Set E} {x : E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hx : x ∈ U)
    (A : E ≃L[ℝ] E) (hA : HasFDerivAt f (A : E →L[ℝ] E) x) :
    ∃ e : OpenPartialHomeomorph E E,
      x ∈ e.source ∧ (e : E → E) = f ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hU.mem_nhds hx)
  have hunit : IsUnit (fderiv ℝ f x) := by
    rw [hA.fderiv]
    exact (ContinuousLinearEquiv.toUnit A).isUnit
  have hnear : ∀ᶠ z in 𝓝 x, IsUnit (fderiv ℝ f z) :=
    (hfx.continuousAt_fderiv (by simp)).eventually (Units.isOpen.mem_nhds hunit)
  obtain ⟨V, hVunit, hVopen, hxV⟩ := mem_nhds_iff.mp hnear
  let e₀ := hfx.toOpenPartialHomeomorph f hA (by simp)
  let e := e₀.restrOpen (U ∩ V) (hU.inter hVopen)
  have hecoe : (e : E → E) = f := rfl
  have heU (z : E) (hz : z ∈ e.source) : z ∈ U := hz.2.1
  have heunit (z : E) (hz : z ∈ e.source) : IsUnit (fderiv ℝ f z) :=
    hVunit hz.2.2
  have heF : ContDiffOn ℝ ∞ e e.source := by
    intro z hz
    rw [hecoe]
    exact (hf.contDiffAt (hU.mem_nhds (heU z hz))).contDiffWithinAt
  refine ⟨e, ?_, hecoe, heF, ?_⟩
  · exact ⟨hfx.mem_toOpenPartialHomeomorph_source hA (by simp), hx, hxV⟩
  · intro y hy
    have hz := e.symm.map_source hy
    have hfu : ContDiffAt ℝ ∞ f (e.symm y) :=
      hf.contDiffAt (hU.mem_nhds (heU _ hz))
    let B := ContinuousLinearEquiv.ofUnit (heunit _ hz).unit
    have hB : (B : E →L[ℝ] E) = fderiv ℝ f (e.symm y) :=
      (heunit _ hz).unit_spec
    have hderiv : HasFDerivAt e (B : E →L[ℝ] E) (e.symm y) := by
      rw [hecoe, hB]
      exact (hfu.differentiableAt (by simp)).hasFDerivAt
    have hse : ContDiffAt ℝ ∞ e (e.symm y) := by
      simpa only [hecoe] using hfu
    exact (e.contDiffAt_symm hy hderiv hse).contDiffWithinAt

end AmbientChart

/-- The actual coefficient Jacobian is a linear isomorphism at every point
of the closed orthant, including every boundary face and dimension zero. -/
theorem coefficientMap_has_deriv_equiv {m : ℕ} {e0 en : ℝ} {x : Fin m → ℝ}
    (h0 : 0 < e0) (hn : 0 < en) (hx : 0 ≤ x) :
    ∃ A : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ),
      HasFDerivAt (coefficientMap m e0 en) (A : _ →L[ℝ] _) x := by
  let J := fixedCoefficientJacobian m e0 en x
  have hJ := fixedCoefficientJacobian_diagonallyStable h0 hn hx
  have hinj : Function.Injective (matrixDerivative J) := by
    apply (injective_iff_map_eq_zero (matrixDerivative J)).mpr
    intro v hv
    by_contra hne
    obtain ⟨i, hi⟩ := hJ.exists_positive_coordinate hne
    have hvi := congrFun hv i
    change (J *ᵥ v) i = 0 at hvi
    rw [hvi, mul_zero] at hi
    exact (lt_irrefl 0) hi
  let A := (LinearEquiv.ofInjectiveEndo
    (matrixDerivative J).toLinearMap hinj).toContinuousLinearEquiv
  exact ⟨A, hasFDerivAt_coefficientMap h0 hn hx⟩

set_option backward.isDefEq.respectTransparency false in
/-- Actual smooth immersion charts: the source chart is a relative open
quadrant neighbourhood and the target chart is the smooth ambient inverse. -/
theorem quadrantCoefficientMap_isImmersion {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) :
    Manifold.IsImmersion (𝓡c m) 𝓘(ℝ, Fin m → ℝ) ∞
      (quadrantCoefficientMap m e0 en) := by
  apply Manifold.IsImmersionOfComplement.isImmersion (F := PUnit.{1})
  intro x
  let C := coefficientEuclideanCoordinates m
  obtain ⟨U, hU, hOU, hF⟩ := coefficientMap_smooth_neighborhood (m := m) h0 hn
  obtain ⟨A, hA⟩ := coefficientMap_has_deriv_equiv h0 hn x.property
  obtain ⟨e, hxe, heF, hesmooth, heinverse⟩ :=
    exists_smooth_ambient_inverse_chart hU hF (hOU x.property) A hA
  let V : Set (EuclideanQuadrant m) := {y | C y.val ∈ e.source}
  have hV : IsOpen V :=
    e.open_source.preimage (C.continuous.comp continuous_subtype_val)
  let D := OpenPartialHomeomorph.ofSet V hV
  let L : (EuclideanSpace ℝ (Fin m) × PUnit.{1}) ≃L[ℝ] (Fin m → ℝ) :=
    (ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin m)) PUnit.{1}).trans C
  have hxD : x ∈ D.source := hxe
  have hxe' : quadrantCoefficientMap m e0 en x ∈ e.symm.source := by
    change coefficientMap m e0 en (C x.val) ∈ e.target
    rw [← heF]
    exact e.map_source hxe
  have hD : D ∈ IsManifold.maximalAtlas (𝓡c m) ∞ (EuclideanQuadrant m) := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact contMDiffOn_id
    · exact contMDiffOn_id
  have he : e.symm ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin m → ℝ) ∞ (Fin m → ℝ) := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact heinverse.contMDiffOn
    · simpa only [OpenPartialHomeomorph.symm_symm,
        OpenPartialHomeomorph.symm_target] using hesmooth.contMDiffOn
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts L D e.symm
    hxD hxe' hD he ?_ ?_
  · intro y hy
    change coefficientMap m e0 en (C y.val) ∈ e.target
    rw [← heF]
    exact e.map_source hy
  · intro z hz
    rw [D.extend_target'] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hy' : C y.val ∈ e.source := hy
    have hleft : e.symm (coefficientMap m e0 en (C y.val)) = C y.val := by
      rw [← heF]
      exact e.left_inv hy'
    have hcoords : (fun i : Fin m => y.val i) = C y.val := by
      funext i
      exact (coefficientEuclideanCoordinates_apply m y.val i).symm
    simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      Function.comp_apply, D, OpenPartialHomeomorph.ofSet_apply,
      OpenPartialHomeomorph.ofSet_symm, ModelWithCorners.left_inv,
      modelWithCornersSelf_coe, id_eq, L, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.prodUnique_apply]
    change e.symm (coefficientMap m e0 en (fun i => y.val i)) = C y.val
    exact (congrArg (fun v => e.symm (coefficientMap m e0 en v)) hcoords).trans hleft

/-- The genuine Mathlib smooth-embedding conclusion for the standard
manifold with corners, in arbitrary natural dimension. -/
theorem quadrantCoefficientMap_isSmoothEmbedding {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) :
    Manifold.IsSmoothEmbedding (𝓡c m) 𝓘(ℝ, Fin m → ℝ) ∞
      (quadrantCoefficientMap m e0 en) :=
  ⟨quadrantCoefficientMap_isImmersion h0 hn,
    (quadrantCoefficientMap_isClosedEmbedding h0 hn).isEmbedding⟩

/-- Smoothness, properness and closed image all concern the same literal
map and the standard quadrant structure. -/
theorem coefficient_transform_manifold_with_corners {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) :
    Manifold.IsSmoothEmbedding (𝓡c m) 𝓘(ℝ, Fin m → ℝ) ∞
      (quadrantCoefficientMap m e0 en) ∧
    IsProperMap (quadrantCoefficientMap m e0 en) ∧
    IsClosed (Set.range (quadrantCoefficientMap m e0 en)) :=
  ⟨quadrantCoefficientMap_isSmoothEmbedding h0 hn,
    quadrantCoefficientMap_isProperMap h0 hn,
    (quadrantCoefficientMap_isProperMap h0 hn).isClosed_range⟩

end EllipsoidVerification
