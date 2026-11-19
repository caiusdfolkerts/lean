module
public import Papers.ActualProjectionReconstruction
public import Papers.FiniteProjectionData

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: Papers/FiniteProjectionBoundary.lean -/




@[expose] public section

/-!
# Finite labelled boundary interface for projection certificates

The finite data contain facet and two-face vertex masks. `RealizesBoundary`
requires equality with the actual geometric face families in both
directions. It is supplied by the actual boundary encoding, not by a
standalone combinatorial incidence assumption.

The apex has label zero; the other labels are successors. Plane nodes are
defined canonically from these complete masks. Extra triangles are included
and can be removed first by the three-point polygon rule.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeIncidenceConfiguration

def faceLabels {n : ℕ} (P : ConvexPolytope 4) (lab : Fin (n + 1) ≃ VertexType P)
    (F : FaceType P) : Finset (Fin (n + 1)) :=
  actualFaceLabels P lab ⟨F.val, F.property⟩

@[simp] theorem mem_faceLabels {n : ℕ} (P : ConvexPolytope 4)
    (lab : Fin (n + 1) ≃ VertexType P) (F : FaceType P) (i : Fin (n + 1)) :
    i ∈ faceLabels P lab F ↔ (lab i).val ∈ F.val :=
  mem_actualFaceLabels P lab _ i

theorem faceLabels_injective {n : ℕ} (P : ConvexPolytope 4)
    (lab : Fin (n + 1) ≃ VertexType P) : Function.Injective (faceLabels P lab) := by
  intro F G h
  apply Subtype.ext
  exact congrArg PolytopeFace.carrier (actualFaceLabels_injective P lab h)

theorem faceLabels_subset_iff {n : ℕ} (P : ConvexPolytope 4)
    (lab : Fin (n + 1) ≃ VertexType P) (F G : FaceType P) :
    faceLabels P lab F ⊆ faceLabels P lab G ↔ F.val ⊆ G.val :=
  actualFaceLabels_subset_iff P lab ⟨F.val, F.property⟩ ⟨G.val, G.property⟩

theorem actualFaceLabels_relabel {n : ℕ} (P : ConvexPolytope 4)
    (lab : Fin (n + 1) ≃ VertexType P) (σ : Fin (n + 1) ≃ Fin (n + 1))
    (F : PolytopeFace P) :
    actualFaceLabels P (σ.symm.trans lab) F = (actualFaceLabels P lab F).image σ := by
  ext i
  rw [mem_actualFaceLabels]
  change (lab (σ.symm i)).val ∈ F.carrier ↔ _
  constructor
  · intro hi
    exact Finset.mem_image.mpr ⟨σ.symm i, (mem_actualFaceLabels P lab F _).mpr hi,
      σ.apply_symm_apply i⟩
  · intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    have heq : j = σ.symm i := (Equiv.eq_symm_apply σ).mpr hji
    simpa only [heq] using (mem_actualFaceLabels P lab F j).mp hj

theorem faceLabels_relabel {n : ℕ} (P : ConvexPolytope 4)
    (lab : Fin (n + 1) ≃ VertexType P) (σ : Fin (n + 1) ≃ Fin (n + 1))
    (F : FaceType P) :
    faceLabels P (σ.symm.trans lab) F = (faceLabels P lab F).image σ :=
  actualFaceLabels_relabel P lab σ ⟨F.val, F.property⟩

structure RealizesBoundary {n : ℕ} (P : ConvexPolytope 4)
    (lab : Fin (n + 1) ≃ VertexType P) (B : Boundary n) : Prop where
  facet : ∀ S, S ∈ B.facets ↔ ∃ F : FacetType P, faceLabels P lab F.val = S
  polygon : ∀ S, S ∈ B.polygons ↔
    ∃ R : Face P 2, actualFaceLabels P lab R.val = S

namespace RealizesBoundary

variable {n : ℕ} {P : ConvexPolytope 4} {lab : Fin (n + 1) ≃ VertexType P}
    {B : Boundary n}

def facetFor (h : RealizesBoundary P lab B) (S : B.facets) : FacetType P :=
  ((h.facet S.val).mp S.property).choose

theorem facetFor_labels (h : RealizesBoundary P lab B) (S : B.facets) :
    faceLabels P lab (h.facetFor S).val = S.val :=
  ((h.facet S.val).mp S.property).choose_spec

theorem facetFor_mem (h : RealizesBoundary P lab B) (S : B.facets) (i : Fin (n + 1)) :
    (lab i).val ∈ (h.facetFor S).val.val ↔ i ∈ S.val := by
  rw [← mem_faceLabels, h.facetFor_labels]

def polygonFor (h : RealizesBoundary P lab B) (S : B.polygons) : Face P 2 :=
  ((h.polygon S.val).mp S.property).choose

theorem polygonFor_labels (h : RealizesBoundary P lab B) (S : B.polygons) :
    actualFaceLabels P lab (h.polygonFor S).val = S.val :=
  ((h.polygon S.val).mp S.property).choose_spec

theorem polygonFor_mem (h : RealizesBoundary P lab B) (S : B.polygons) (i : Fin (n + 1)) :
    (lab i).val ∈ (h.polygonFor S).val.carrier ↔ i ∈ S.val := by
  rw [← mem_actualFaceLabels, h.polygonFor_labels]

theorem facet_labels_mem (h : RealizesBoundary P lab B) (F : FacetType P) :
    faceLabels P lab F.val ∈ B.facets := (h.facet _).mpr ⟨F, rfl⟩

theorem polygon_labels_mem (h : RealizesBoundary P lab B) (R : Face P 2) :
    actualFaceLabels P lab R.val ∈ B.polygons := (h.polygon _).mpr ⟨R, rfl⟩

theorem facetFor_actual (h : RealizesBoundary P lab B) (F : FacetType P) :
    h.facetFor ⟨faceLabels P lab F.val, h.facet_labels_mem F⟩ = F := by
  apply Subtype.ext
  exact faceLabels_injective P lab (h.facetFor_labels _)

theorem polygonFor_actual (h : RealizesBoundary P lab B) (R : Face P 2) :
    h.polygonFor ⟨actualFaceLabels P lab R.val, h.polygon_labels_mem R⟩ = R := by
  apply Subtype.ext
  exact actualFaceLabels_injective P lab (h.polygonFor_labels _)

def facetEquiv (h : RealizesBoundary P lab B) : B.facets ≃ FacetType P where
  toFun := h.facetFor
  invFun F := ⟨faceLabels P lab F.val, h.facet_labels_mem F⟩
  left_inv S := Subtype.ext (h.facetFor_labels S)
  right_inv F := h.facetFor_actual F

def polygonEquiv (h : RealizesBoundary P lab B) : B.polygons ≃ Face P 2 where
  toFun := h.polygonFor
  invFun R := ⟨actualFaceLabels P lab R.val, h.polygon_labels_mem R⟩
  left_inv S := Subtype.ext (h.polygonFor_labels S)
  right_inv R := h.polygonFor_actual R

end RealizesBoundary

/-- A checked finite relabelling changes only the vertex names. Both
directions of the actual facet and polygon correspondence are retained. -/
theorem RealizesBoundary.relabel {n : ℕ} {P : ConvexPolytope 4}
    {lab : Fin (n + 1) ≃ VertexType P} {B : Boundary n}
    (h : RealizesBoundary P lab B) (σ : Fin (n + 1) ≃ Fin (n + 1)) :
    RealizesBoundary P (σ.symm.trans lab) (B.relabel σ) := by
  constructor
  · intro S
    constructor
    · intro hS
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
      obtain ⟨F, hF⟩ := (h.facet T).mp hT
      exact ⟨F, (faceLabels_relabel P lab σ F.val).trans
        (congrArg (fun U : Finset (Fin (n + 1)) => U.image σ) hF)⟩
    · rintro ⟨F, hF⟩
      exact Finset.mem_image.mpr ⟨faceLabels P lab F.val,
        (h.facet _).mpr ⟨F, rfl⟩, (faceLabels_relabel P lab σ F.val).symm.trans hF⟩
  · intro S
    constructor
    · intro hS
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
      obtain ⟨R, hR⟩ := (h.polygon T).mp hT
      exact ⟨R, (actualFaceLabels_relabel P lab σ R.val).trans
        (congrArg (fun U : Finset (Fin (n + 1)) => U.image σ) hR)⟩
    · rintro ⟨R, hR⟩
      exact Finset.mem_image.mpr ⟨actualFaceLabels P lab R.val,
        (h.polygon _).mpr ⟨R, rfl⟩, (actualFaceLabels_relabel P lab σ R.val).symm.trans hR⟩

namespace RealizesBoundary

variable {n : ℕ} {P : ConvexPolytope 4} {a : VertexType P}
    {e : Fin n ≃ ProjectionPoint P a} {B : Boundary n}

def ordinaryActual (h : RealizesBoundary P (projectionVertexLabels e) B)
    (F : Finset (Fin (n + 1))) (hF : F ∈ B.facets) (hzero : 0 ∈ F) :
    OrdinaryProjectionPlane P a :=
  ⟨h.facetFor ⟨F, hF⟩, by
    simpa only [projectionVertexLabels_zero] using (h.facetFor_mem ⟨F, hF⟩ 0).mpr hzero⟩

def extraActual (h : RealizesBoundary P (projectionVertexLabels e) B)
    (R : Finset (Fin (n + 1))) (hR : IsExtraMask B R) : ExtraProjectionPlane P a := by
  let S := h.polygonFor ⟨R, hR.1⟩
  have ha : a.val ∉ S.val.carrier := by
    intro ha
    apply hR.2.1
    exact (h.polygonFor_mem ⟨R, hR.1⟩ 0).mp (by simpa only [projectionVertexLabels_zero] using ha)
  refine ⟨S, ha, ?_⟩
  intro F hSF
  let T := faceLabels P (projectionVertexLabels e) F.val.val
  have hT : T ∈ B.facets := h.facet_labels_mem F.val
  have hz : 0 ∈ T := by
    simpa only [T, mem_faceLabels, projectionVertexLabels_zero] using F.property
  apply hR.2.2 T hT hz
  have hh := actualFaceLabels_mono P (projectionVertexLabels e)
    (F := S.val) (G := ⟨F.val.val.val, F.val.property.1⟩) hSF
  simpa only [S, h.polygonFor_labels, T, faceLabels] using hh

def planeActual (h : RealizesBoundary P (projectionVertexLabels e) B) :
    PlaneNode B → ActualProjectionPlane P a
  | ⟨(false, F), hF⟩ =>
      Sum.inl (h.ordinaryActual F ((ordinary_mem_planes B F).mp hF).1
        ((ordinary_mem_planes B F).mp hF).2)
  | ⟨(true, R), hR⟩ => Sum.inr (h.extraActual R ((extra_mem_planes B R).mp hR))

def actualPlaneCode (h : RealizesBoundary P (projectionVertexLabels e) B) :
    ActualProjectionPlane P a → PlaneNode B
  | Sum.inl F => ⟨(false, faceLabels P (projectionVertexLabels e) F.val.val), by
      apply (ordinary_mem_planes B _).mpr
      exact ⟨h.facet_labels_mem F.val, by
        simpa only [mem_faceLabels, projectionVertexLabels_zero] using F.property⟩⟩
  | Sum.inr R => ⟨(true, actualFaceLabels P (projectionVertexLabels e) R.val.val), by
      apply (extra_mem_planes B _).mpr
      refine ⟨h.polygon_labels_mem R.val, ?_, ?_⟩
      · simpa only [mem_actualFaceLabels, projectionVertexLabels_zero] using R.property.1
      · intro F hF hzero hRF
        let G := h.ordinaryActual F hF hzero
        apply R.property.2 G
        apply (actualFaceLabels_subset_iff P (projectionVertexLabels e)
          R.val.val ⟨G.val.val.val, G.val.property.1⟩).mp
        change actualFaceLabels P (projectionVertexLabels e) R.val.val ⊆
          faceLabels P (projectionVertexLabels e) G.val.val
        rw [show faceLabels P (projectionVertexLabels e) G.val.val = F from h.facetFor_labels _]
        exact hRF⟩

theorem planeActual_carrier_labels (h : RealizesBoundary P (projectionVertexLabels e) B)
    (p : PlaneNode B) :
    faceLabels P (projectionVertexLabels e)
      ⟨projectionPlaneCarrier (h.planeActual p), projectionPlaneCarrier_isFace _⟩ = carrier p := by
  rcases p with ⟨⟨b, S⟩, hp⟩
  cases b
  · exact h.facetFor_labels _
  · exact h.polygonFor_labels _

theorem planeActual_code (h : RealizesBoundary P (projectionVertexLabels e) B)
    (p : PlaneNode B) : h.actualPlaneCode (h.planeActual p) = p := by
  apply Subtype.ext
  rcases p with ⟨⟨b, S⟩, hp⟩
  cases b
  · apply Prod.ext
    · rfl
    · exact h.facetFor_labels _
  · apply Prod.ext
    · rfl
    · exact h.polygonFor_labels _

theorem code_planeActual (h : RealizesBoundary P (projectionVertexLabels e) B)
    (p : ActualProjectionPlane P a) : h.planeActual (h.actualPlaneCode p) = p := by
  cases p with
  | inl F =>
    apply congrArg Sum.inl
    apply Subtype.ext
    exact h.facetFor_actual F.val
  | inr R =>
    apply congrArg Sum.inr
    apply Subtype.ext
    exact h.polygonFor_actual R.val

def planeEquiv (h : RealizesBoundary P (projectionVertexLabels e) B) :
    PlaneNode B ≃ ActualProjectionPlane P a where
  toFun := h.planeActual
  invFun := h.actualPlaneCode
  left_inv := h.planeActual_code
  right_inv := h.code_planeActual

theorem planeEquiv_ordinary (h : RealizesBoundary P (projectionVertexLabels e) B)
    (p : PlaneNode B) (hp : p.val.1 = false) :
    ∃ F : OrdinaryProjectionPlane P a, h.planeEquiv p = Sum.inl F := by
  rcases p with ⟨⟨b, S⟩, hS⟩
  cases b
  · exact ⟨_, rfl⟩
  · cases hp

theorem planeEquiv_extra (h : RealizesBoundary P (projectionVertexLabels e) B)
    (p : PlaneNode B) (hp : p.val.1 = true) :
    ∃ R : ExtraProjectionPlane P a, h.planeEquiv p = Sum.inr R := by
  rcases p with ⟨⟨b, S⟩, hS⟩
  cases b
  · cases hp
  · exact ⟨_, rfl⟩

theorem plane_incidence_iff (h : RealizesBoundary P (projectionVertexLabels e) B)
    (i : Fin n) (p : PlaneNode B) :
    actualProjectionIncidence (e i) (h.planeEquiv p) ↔ incidence i p := by
  have hm := mem_faceLabels P (projectionVertexLabels e)
    ⟨projectionPlaneCarrier (h.planeActual p), projectionPlaneCarrier_isFace _⟩ i.succ
  rw [h.planeActual_carrier_labels] at hm
  change ((e i).val.val ∈ projectionPlaneCarrier (h.planeActual p)) ↔ incidence i p
  simpa only [projectionVertexLabels_succ, incidence] using hm.symm

theorem actual_trace_of_mask_intersection
    (h : RealizesBoundary P (projectionVertexLabels e) B)
    (p : PlaneNode B) (F : B.facets) (R : B.polygons)
    (hR : R.val = F.val ∩ carrier p) :
    ProjectedFacetTrace (h.planeEquiv p) (h.facetFor F) (h.polygonFor R) := by
  let FF := (h.facetFor F).val
  let RR : FaceType P := ⟨(h.polygonFor R).val.carrier, (h.polygonFor R).val.isFace⟩
  let BB : FaceType P := ⟨projectionPlaneCarrier (h.planeEquiv p),
    projectionPlaneCarrier_isFace _⟩
  have hlabels : faceLabels P (projectionVertexLabels e) RR =
      faceLabels P (projectionVertexLabels e) FF ∩ faceLabels P (projectionVertexLabels e) BB := by
    rw [show faceLabels P (projectionVertexLabels e) RR = R.val from h.polygonFor_labels _,
      show faceLabels P (projectionVertexLabels e) FF = F.val from h.facetFor_labels _,
      show faceLabels P (projectionVertexLabels e) BB = carrier p from h.planeActual_carrier_labels _]
    exact hR
  have hRF : RR.val ⊆ FF.val := (faceLabels_subset_iff P _ RR FF).mp (by
    rw [hlabels]
    exact Finset.inter_subset_left)
  have hRB : RR.val ⊆ BB.val := (faceLabels_subset_iff P _ RR BB).mp (by
    rw [hlabels]
    exact Finset.inter_subset_right)
  have hI : P.IsFace (FF.val ∩ BB.val) := by
    obtain ⟨x, hx⟩ := RR.property.2
    exact ⟨FF.property.1.inter BB.property.1, x, hRF hx, hRB hx⟩
  let II : FaceType P := ⟨FF.val ∩ BB.val, hI⟩
  have hIlabels : faceLabels P (projectionVertexLabels e) II =
      faceLabels P (projectionVertexLabels e) FF ∩ faceLabels P (projectionVertexLabels e) BB := by
    ext i
    simp only [mem_faceLabels, Finset.mem_inter, II, Set.mem_inter_iff]
  have heq : RR = II := faceLabels_injective P _ (hlabels.trans hIlabels.symm)
  exact congrArg Subtype.val heq

end RealizesBoundary
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/FiniteProjectionIncidenceCertificate.lean -/



@[expose] public section

/-!
# Soundness of finite projection-incidence certificates

Every premise in the finite constructors is a decidable statement about
vertex masks. These statements can be discharged by kernel evaluation of
literal data. The soundness proof turns each witness into the corresponding
actual geometric witness, using the complete boundary correspondence.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting

variable {n : ℕ}

namespace RealizesBoundary

variable {P : ConvexPolytope 4} {a : VertexType P}
    {e : Fin n ≃ ProjectionPoint P a} {B : Boundary n}

theorem polygon_apex_not_mem (h : RealizesBoundary P (projectionVertexLabels e) B)
    (R : B.polygons) (ha : 0 ∉ R.val) : a.val ∉ (h.polygonFor R).val.carrier := by
  simpa only [projectionVertexLabels_zero] using
    (not_congr (h.polygonFor_mem R 0)).mpr ha

theorem facet_apex_not_mem (h : RealizesBoundary P (projectionVertexLabels e) B)
    (F : B.facets) (ha : 0 ∉ F.val) : a.val ∉ (h.facetFor F).val.val := by
  simpa only [projectionVertexLabels_zero] using
    (not_congr (h.facetFor_mem F 0)).mpr ha

theorem pointRule_sound (h : RealizesBoundary P (projectionVertexLabels e) B)
    (S : Finset (Fin n)) (hS : PointRule B S) :
    ProjectionPointRule (S.map e.toEmbedding) := by
  cases hS with
  | atMostTwo hc => exact .atMostTwo (by simpa using hc)
  | avoidingPolygon hc R ha hmem =>
    apply ProjectionPointRule.avoidingPolygon (by simpa using hc) (h.polygonFor R)
      (h.polygon_apex_not_mem R ha)
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
    simpa only [projectionVertexLabels_succ, Equiv.toEmbedding_apply] using (h.polygonFor_mem R i.succ).mpr (hmem i hi)
  | facialWitness hc R ha v hv hout hin =>
    apply ProjectionPointRule.facialWitness (by simpa using hc) (h.polygonFor R)
      (by simpa only [projectionVertexLabels_zero] using (h.polygonFor_mem R 0).mpr ha)
      (e v) (Finset.mem_map.mpr ⟨v, hv, rfl⟩)
      (by simpa only [projectionVertexLabels_succ, Equiv.toEmbedding_apply] using
        (not_congr (h.polygonFor_mem R v.succ)).mpr hout)
    intro w hw hwv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hw
    have hiv : i ≠ v := fun heq => hwv (congrArg e heq)
    simpa only [projectionVertexLabels_succ, Equiv.toEmbedding_apply] using
      (h.polygonFor_mem R i.succ).mpr (hin i hi hiv)

theorem planePairRule_sound (h : RealizesBoundary P (projectionVertexLabels e) B)
    (p q : PlaneNode B) (hpq : PlanePairRule p q) :
    ProjectionPlanePairRule (h.planeEquiv p) (h.planeEquiv q) := by
  cases hpq with
  | ordinary hp hq hne =>
    obtain ⟨F, hF⟩ := h.planeEquiv_ordinary p hp
    obtain ⟨G, hG⟩ := h.planeEquiv_ordinary q hq
    rw [hF, hG]
    exact .ordinary F G (fun hFG => hne (h.planeEquiv.injective (by rw [hF, hG, hFG])))
  | extraOrdinary hp hq =>
    obtain ⟨R, hR⟩ := h.planeEquiv_extra p hp
    obtain ⟨F, hF⟩ := h.planeEquiv_ordinary q hq
    rw [hR, hF]
    exact .extraOrdinary R F
  | ordinaryExtra hp hq =>
    obtain ⟨F, hF⟩ := h.planeEquiv_ordinary p hp
    obtain ⟨R, hR⟩ := h.planeEquiv_extra q hq
    rw [hF, hR]
    exact .ordinaryExtra F R
  | commonFacet F ha R S hR hS hne =>
    exact .commonFacet (h.facetFor F) (h.facet_apex_not_mem F ha)
      (h.planeEquiv p) (h.planeEquiv q) (h.polygonFor R) (h.polygonFor S)
      (h.actual_trace_of_mask_intersection p F R hR)
      (h.actual_trace_of_mask_intersection q F S hS)
      (fun heq => hne (h.polygonEquiv.injective heq))

theorem planeRule_sound (h : RealizesBoundary P (projectionVertexLabels e) B)
    (S : Finset (PlaneNode B)) (hS : PlaneRule B S) :
    ProjectionPlaneRule (S.map h.planeEquiv.toEmbedding) := by
  cases hS with
  | atMostOne hc => exact .atMostOne (by simpa using hc)
  | atMostTwo hc hpairs =>
    apply ProjectionPlaneRule.atMostTwo (by simpa using hc)
    intro A hA C hC hAC
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hA
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hC
    exact h.planePairRule_sound p q (hpairs p hp q hq (fun heq => hAC (congrArg h.planeEquiv heq)))
  | ordinary hc hord =>
    apply ProjectionPlaneRule.ordinary (by simpa using hc)
    intro A hA
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hA
    exact h.planeEquiv_ordinary p (hord p hp)
  | commonFacet hc F ha R hinj htrace =>
    let E := Finset.equivMap h.planeEquiv.toEmbedding S
    let r : S.map h.planeEquiv.toEmbedding → Face P 2 :=
      fun A => h.polygonFor (R (E.symm A))
    apply ProjectionPlaneRule.commonFacet (by simpa using hc) (h.facetFor F)
      (h.facet_apex_not_mem F ha) r
    · intro A C heq
      exact E.symm.injective (hinj (h.polygonEquiv.injective heq))
    · intro A
      have hA : h.planeEquiv (E.symm A).val = A.val :=
        congrArg Subtype.val (E.apply_symm_apply A)
      exact hA ▸ h.actual_trace_of_mask_intersection
        (E.symm A).val F (R (E.symm A)) (htrace (E.symm A))
  | commonPoint p q r hr w hpair hwp hwq hwr hsub =>
    obtain ⟨F, hF⟩ := h.planeEquiv_ordinary r hr
    apply ProjectionPlaneRule.commonPoint (h.planeEquiv p) (h.planeEquiv q) F (e w)
      (h.planePairRule_sound p q hpair) ((h.plane_incidence_iff w p).mpr hwp)
      ((h.plane_incidence_iff w q).mpr hwq)
      (by rw [← hF]; exact (not_congr (h.plane_incidence_iff w r)).mpr hwr)
    intro A hA
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hA
    have hs' : s = p ∨ s = q ∨ s = r := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hsub hs
    rcases hs' with rfl | rfl | rfl
    · simp
    · simp
    · simp [hF]

def nodeEquiv (h : RealizesBoundary P (projectionVertexLabels e) B) :
    Node B ≃ ProjectionNode P a := Equiv.sumCongr e h.planeEquiv

def actualPriority (h : RealizesBoundary P (projectionVertexLabels e) B)
    (C : IncidenceCertificate B) : ProjectionNode P a → ℕ :=
  fun j => C.priority (h.nodeEquiv.symm j)

@[simp] theorem actualPriority_point (h : RealizesBoundary P (projectionVertexLabels e) B)
    (C : IncidenceCertificate B) (i : Fin n) :
    h.actualPriority C (Sum.inl (e i)) = C.priority (Sum.inl i) := by
  simp [actualPriority, nodeEquiv]

@[simp] theorem actualPriority_plane (h : RealizesBoundary P (projectionVertexLabels e) B)
    (C : IncidenceCertificate B) (p : PlaneNode B) :
    h.actualPriority C (Sum.inr (h.planeEquiv p)) = C.priority (Sum.inr p) := by
  simp [actualPriority, nodeEquiv]

theorem retained_points_transport (h : RealizesBoundary P (projectionVertexLabels e) B)
    (C : IncidenceCertificate B) (p : PlaneNode B) :
    retainedProjectionPoints (h.actualPriority C) (h.planeEquiv p) =
      (retainedPoints C.priority p).map e.toEmbedding := by
  ext v
  obtain ⟨i, rfl⟩ := e.surjective v
  have hi : e i ∈ retainedProjectionPoints (h.actualPriority C) (h.planeEquiv p) ↔
      i ∈ retainedPoints C.priority p := by
    simp only [retainedProjectionPoints, retainedPoints, Finset.mem_filter,
      Finset.mem_univ, true_and, h.actualPriority_point, h.actualPriority_plane,
      h.plane_incidence_iff]
  rw [hi]
  constructor
  · intro hmem
    exact Finset.mem_map.mpr ⟨i, hmem, rfl⟩
  · intro hmem
    obtain ⟨j, hj, heq⟩ := Finset.mem_map.mp hmem
    exact e.injective heq ▸ hj

theorem retained_planes_transport (h : RealizesBoundary P (projectionVertexLabels e) B)
    (C : IncidenceCertificate B) (i : Fin n) :
    retainedProjectionPlanes (h.actualPriority C) (e i) =
      (retainedPlanes C.priority i).map h.planeEquiv.toEmbedding := by
  ext A
  obtain ⟨p, rfl⟩ := h.planeEquiv.surjective A
  have hp : h.planeEquiv p ∈ retainedProjectionPlanes (h.actualPriority C) (e i) ↔
      p ∈ retainedPlanes C.priority i := by
    simp only [retainedProjectionPlanes, retainedPlanes, Finset.mem_filter,
      Finset.mem_univ, true_and, h.actualPriority_point, h.actualPriority_plane,
      h.plane_incidence_iff]
  rw [hp]
  constructor
  · intro hmem
    exact Finset.mem_map.mpr ⟨p, hmem, rfl⟩
  · intro hmem
    obtain ⟨q, hq, heq⟩ := Finset.mem_map.mp hmem
    exact h.planeEquiv.injective heq ▸ hq

def incidenceCertificate (h : RealizesBoundary P (projectionVertexLabels e) B)
    (C : IncidenceCertificate B) : ActualProjectionDeletionCertificate P a where
  priority := h.actualPriority C
  injective := C.injective.comp h.nodeEquiv.symm.injective
  plane_rule A := by
    obtain ⟨p, rfl⟩ := h.planeEquiv.surjective A
    rw [h.retained_points_transport]
    exact h.pointRule_sound _ (C.plane_rule p)
  point_rule v := by
    obtain ⟨i, rfl⟩ := e.surjective v
    rw [h.retained_planes_transport]
    exact h.planeRule_sound _ (C.point_rule i)

end RealizesBoundary
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/FiniteProjectionHeightCertificate.lean -/



@[expose] public section

/-!
# Soundness of finite geometric height certificates

The finite templates contain only vertex labels, actual face masks,
facial frame witnesses, nonzero-pivot witnesses, and coverage of all
avoiding facets. Their soundness theorem produces the full geometric
projection reconstruction certificate, hence rational approximation of
the actual polytope realizing the supplied boundary masks.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting

variable {n c : ℕ}

namespace RealizesBoundary

variable {P : ConvexPolytope 4} {a : VertexType P}
    {e : Fin n ≃ ProjectionPoint P a} {B : Boundary n}

def faceActual (h : RealizesBoundary P (projectionVertexLabels e) B) :
    FaceReference B → FaceType P
  | Sum.inl F => (h.facetFor F).val
  | Sum.inr R => ⟨(h.polygonFor R).val.carrier, (h.polygonFor R).val.isFace⟩

theorem faceActual_labels (h : RealizesBoundary P (projectionVertexLabels e) B)
    (F : FaceReference B) :
    faceLabels P (projectionVertexLabels e) (h.faceActual F) = faceMask F := by
  cases F with
  | inl F => exact h.facetFor_labels F
  | inr R => exact h.polygonFor_labels R

theorem faceActual_mem (h : RealizesBoundary P (projectionVertexLabels e) B)
    (F : FaceReference B) (i : Fin (n + 1)) :
    (projectionVertexLabels e i).val ∈ (h.faceActual F).val ↔ i ∈ faceMask F := by
  rw [← mem_faceLabels, h.faceActual_labels]

theorem faceActual_projectedLabels (h : RealizesBoundary P (projectionVertexLabels e) B)
    (F : FaceReference B) :
    projectedFaceLabels e (h.faceActual F) = pointLabels (faceMask F) := by
  ext i
  rw [mem_projectedFaceLabels, mem_pointLabels]
  simpa only [projectionVertexLabels_succ] using h.faceActual_mem F i.succ

theorem facetFor_projectedLabels (h : RealizesBoundary P (projectionVertexLabels e) B)
    (F : B.facets) :
    projectedFaceLabels e (h.facetFor F).val = pointLabels F.val :=
  h.faceActual_projectedLabels (Sum.inl F)

theorem frameCertificate_sound (h : RealizesBoundary P (projectionVertexLabels e) B)
    {k : ℕ} (b : Fin k → Fin n) (hb : FrameCertificate B b) :
    ProjectedFrameCertificate e b := by
  cases hb with
  | polygon hk hinj R ha hmem =>
    apply ProjectedFrameCertificate.polygon hk hinj (h.polygonFor R)
      (h.polygon_apex_not_mem R ha)
    intro j
    simpa only [projectionVertexLabels_succ] using (h.polygonFor_mem R (b j).succ).mpr (hmem j)
  | facial hk hinj R F ha hmem t hout hin =>
    refine ProjectedFrameCertificate.facial hk hinj (h.polygonFor R) (h.facetFor F)
      (h.facet_apex_not_mem F ha) ?_ t ?_ ?_
    · intro j
      simpa only [projectionVertexLabels_succ] using (h.facetFor_mem F (b j).succ).mpr (hmem j)
    · simpa only [projectionVertexLabels_succ] using
        (not_congr (h.polygonFor_mem R (b t).succ)).mpr hout
    · intro j hj
      simpa only [projectionVertexLabels_succ] using
        (h.polygonFor_mem R (b j).succ).mpr (hin j hj)

def heightRow (h : RealizesBoundary P (projectionVertexLabels e) B) (R : HeightRow B) :
    CertifiedHeightRow e where
  toProjectedRelationTemplate := R.toProjectedRelationTemplate
  carrier := h.faceActual R.face
  avoids := by
    simpa only [projectionVertexLabels_zero] using
      (not_congr (h.faceActual_mem R.face 0)).mpr R.avoids
  frame_mem j := by
    simpa only [projectionVertexLabels_succ] using
      (h.faceActual_mem R.face (R.frame j).succ).mpr (R.frame_mem j)
  vertex_mem := by
    simpa only [projectionVertexLabels_succ] using
      (h.faceActual_mem R.face R.vertex.succ).mpr R.vertex_mem
  vertex_outside_frame := R.vertex_outside_frame
  frame_certificate := h.frameCertificate_sound R.frame R.frame_certificate
  spanning_certificate := by
    rcases R.spanning_certificate with hfour | ⟨hthree, p, hsub⟩
    · exact Or.inl hfour
    · refine Or.inr ⟨hthree, h.planeEquiv p, ?_⟩
      apply (faceLabels_subset_iff P (projectionVertexLabels e)
        (h.faceActual R.face) ⟨projectionPlaneCarrier (h.planeEquiv p),
          projectionPlaneCarrier_isFace _⟩).mp
      change faceLabels P (projectionVertexLabels e) (h.faceActual R.face) ⊆
        faceLabels P (projectionVertexLabels e) ⟨projectionPlaneCarrier (h.planeActual p),
          projectionPlaneCarrier_isFace _⟩
      rw [h.faceActual_labels, h.planeActual_carrier_labels]
      exact hsub

def heightCertificate (h : RealizesBoundary P (projectionVertexLabels e) B)
    (H : HeightCertificate B c) : ActualHeightRowCertificate e c where
  rows i := h.heightRow (H.rows i)
  pivot := H.pivot
  pivot_certificate i := by
    rcases H.pivot_certificate i with hi | ⟨j, hij, hj⟩
    · exact Or.inl hi
    · exact Or.inr ⟨j, hij, h.frameCertificate_sound _ hj⟩
  later_absent := H.later_absent

@[simp] theorem heightCertificate_templates (h : RealizesBoundary P (projectionVertexLabels e) B)
    (H : HeightCertificate B c) : (h.heightCertificate H).templates = H.templates := rfl

def facetCoverage (h : RealizesBoundary P (projectionVertexLabels e) B)
    (H : HeightCertificate B c) (F : B.facets) (K : FacetCoverage H F) :
    ProjectionFacetHeightCoverage e (h.heightCertificate H) (h.facetFor F) := by
  cases K with
  | fundamental b hframe hmem hcovered =>
    apply ProjectionFacetHeightCoverage.fundamental b (h.frameCertificate_sound b hframe)
    · intro j
      simpa only [projectionVertexLabels_succ] using (h.facetFor_mem F (b j).succ).mpr (hmem j)
    · intro v hv hvb
      rw [h.facetFor_projectedLabels] at hv
      exact hcovered v hv hvb
  | oneRow b hframe hmem hcard i hsupport =>
    refine ProjectionFacetHeightCoverage.oneRow b (h.frameCertificate_sound b hframe)
      ?_ ?_ i ?_
    · intro j
      simpa only [projectionVertexLabels_succ] using (h.facetFor_mem F (b j).succ).mpr (hmem j)
    · simpa only [h.facetFor_projectedLabels] using hcard
    · apply (faceLabels_subset_iff P (projectionVertexLabels e)
        (h.faceActual (H.rows i).face) (h.facetFor F).val).mp
      rw [h.faceActual_labels, h.facetFor_labels]
      exact hsupport
  | fromLargerFacet b hframe hmem hcard R haR hRcard hRF G g hgframe hgmem hRG hcovered =>
    refine ProjectionFacetHeightCoverage.fromLargerFacet b (h.frameCertificate_sound b hframe)
      ?_ ?_ (h.polygonFor R) (h.polygon_apex_not_mem R haR) ?_ ?_ (h.facetFor G) g
      (h.frameCertificate_sound g hgframe) ?_ ?_ ?_
    · intro j
      simpa only [projectionVertexLabels_succ] using (h.facetFor_mem F (b j).succ).mpr (hmem j)
    · simpa only [h.facetFor_projectedLabels] using hcard
    · simpa only [show projectedFaceLabels e
          (⟨(h.polygonFor R).val.carrier, (h.polygonFor R).val.isFace⟩ : FaceType P) =
            pointLabels R.val from h.faceActual_projectedLabels (Sum.inr R)] using hRcard
    · apply (faceLabels_subset_iff P (projectionVertexLabels e)
        (h.faceActual (Sum.inr R)) (h.facetFor F).val).mp
      rw [h.faceActual_labels, h.facetFor_labels]
      exact hRF
    · intro j
      simpa only [projectionVertexLabels_succ] using (h.facetFor_mem G (g j).succ).mpr (hgmem j)
    · apply (faceLabels_subset_iff P (projectionVertexLabels e)
        (h.faceActual (Sum.inr R)) (h.facetFor G).val).mp
      rw [h.faceActual_labels, h.facetFor_labels]
      exact hRG
    · intro v hv hvg
      rw [h.facetFor_projectedLabels] at hv
      exact hcovered v hv hvg

def reconstructionCertificate (h : RealizesBoundary P (projectionVertexLabels e) B)
    (K : ReconstructionCertificate B c) : ActualProjectionReconstructionCertificate e c where
  incidence := h.incidenceCertificate K.incidence
  heights := h.heightCertificate K.heights
  facet F := by
    let S : B.facets := ⟨faceLabels P (projectionVertexLabels e) F.val.val,
      h.facet_labels_mem F.val⟩
    have hzero : 0 ∉ S.val := by
      simpa only [S, mem_faceLabels, projectionVertexLabels_zero] using F.property
    have hc := h.facetCoverage K.heights S (K.facet ⟨S, hzero⟩)
    simpa only [S, h.facetFor_actual] using hc

end RealizesBoundary

theorem actual_polytope_rationallyApproximable_of_finite_projection_certificate
    {P : ConvexPolytope 4} {a : VertexType P}
    (hP : P.IsFullDim) (e : Fin n ≃ ProjectionPoint P a) (B : Boundary n)
    (hB : RealizesBoundary P (projectionVertexLabels e) B)
    (K : ReconstructionCertificate B c) : RationallyApproximable P := by
  obtain ⟨D⟩ := exists_vertexProjectionChart P hP a
  exact actual_projection_certificate_rationallyApproximable hP D e (hB.reconstructionCertificate K)

/-- Every complete vertex labelling has the required center/successor
form; the JSON reindexing therefore imposes no geometric restriction. -/
def nonapexLabels {P : ConvexPolytope 4} (lab : Fin (n + 1) ≃ VertexType P) :
    Fin n ≃ ProjectionPoint P (lab 0) where
  toFun i := ⟨lab i.succ, fun h => Fin.succ_ne_zero i (lab.injective h)⟩
  invFun v := (lab.symm v.val).pred (by
    intro h
    apply v.property
    have hh := congrArg lab h
    simpa only [Equiv.apply_symm_apply] using hh)
  left_inv i := by simp only [Equiv.symm_apply_apply, Fin.pred_succ]
  right_inv v := by
    apply Subtype.ext
    change lab ((lab.symm v.val).pred _).succ = v.val
    rw [Fin.succ_pred, Equiv.apply_symm_apply]

theorem projectionVertexLabels_nonapexLabels {P : ConvexPolytope 4}
    (lab : Fin (n + 1) ≃ VertexType P) : projectionVertexLabels (nonapexLabels lab) = lab := by
  apply Equiv.ext
  intro i
  cases i using Fin.cases
  · exact projectionVertexLabels_zero _
  · exact projectionVertexLabels_succ _ _

theorem actual_labelled_polytope_rationallyApproximable_of_finite_projection_certificate
    {P : ConvexPolytope 4} (hP : P.IsFullDim) (lab : Fin (n + 1) ≃ VertexType P)
    (B : Boundary n) (hB : RealizesBoundary P lab B) (K : ReconstructionCertificate B c) :
    RationallyApproximable P := by
  apply actual_polytope_rationallyApproximable_of_finite_projection_certificate
    hP (nonapexLabels lab) B _ K
  simpa only [projectionVertexLabels_nonapexLabels] using hB

theorem CertifiedRelabelling.rationallyApproximable {B : Boundary n}
    (C : CertifiedRelabelling B) {P : ConvexPolytope 4} (hP : P.IsFullDim)
    (lab : Fin (n + 1) ≃ VertexType P) (hB : RealizesBoundary P lab B) :
    RationallyApproximable P := by
  apply actual_labelled_polytope_rationallyApproximable_of_finite_projection_certificate
    hP (C.permutation.symm.trans lab) C.target _ C.certificate
  simpa only [C.boundary_eq] using hB.relabel C.permutation

/-- The boundary search may normalize a root facet and then apply a root
symmetry. Its explicit relabelling is undone before using the certificate. -/
theorem CertifiedRelabelling.rationallyApproximable_of_relabel {B : Boundary n}
    (C : CertifiedRelabelling B) (τ : Fin (n + 1) ≃ Fin (n + 1))
    {P : ConvexPolytope 4} (hP : P.IsFullDim)
    (lab : Fin (n + 1) ≃ VertexType P) (hB : RealizesBoundary P lab (B.relabel τ)) :
    RationallyApproximable P := by
  apply C.rationallyApproximable hP (τ.symm.symm.trans lab)
  simpa only [Boundary.relabel_symm] using hB.relabel τ.symm

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection

end
end
end BundlePart2
