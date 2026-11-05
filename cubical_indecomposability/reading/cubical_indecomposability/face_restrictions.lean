import cubical_indecomposability.deformation_dimension

/-!
# Restriction of deformation spaces to actual faces

The restriction map is defined on vertex assignments and then descends to
the quotient by translations. A face determines a polytope when this quotient
map is injective, exactly as in Section 2 of the paper. The final lemma turns
explicit difference-coordinate identities into an upper bound for the
dimension of a restriction image.
-/

set_option autoImplicit false

noncomputable section

namespace Papers.Polytopes

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} (P : ConvexPolytope d) {F : Set (E d)} (hF : P.IsFace F)

/-- A vertex of a face is an actual vertex of the original polytope. -/
def faceVertex (v : Vertex (facePolytope P hF)) : Vertex P :=
  ⟨v, (Finset.mem_filter.mp v.property).1⟩

theorem faceVertex_mem (v : Vertex (facePolytope P hF)) :
    (faceVertex P hF v : E d) ∈ F :=
  (Finset.mem_filter.mp v.property).2

/-- Restriction respects actual exposed edges, hence parallelism. -/
def redrawingRestriction :
    redrawingSpace P →ₗ[ℝ] redrawingSpace (facePolytope P hF) where
  toFun h := ⟨fun v => h (faceVertex P hF v), by
    intro u v huv
    obtain ⟨hv, hne, e, he, hde, hue, hve⟩ := huv
    exact h.property (faceVertex P hF u) (faceVertex P hF v)
      ⟨(Finset.mem_filter.mp hv).1, hne, e,
        isFace_of_facePolytope P hF he, hde, hue, hve⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem redrawingRestriction_apply (h : redrawingSpace P)
    (v : Vertex (facePolytope P hF)) :
    redrawingRestriction P hF h v = h (faceVertex P hF v) := rfl

@[simp] theorem redrawingRestriction_translation (b : E d) :
    redrawingRestriction P hF (translationMap P b) =
      translationMap (facePolytope P hF) b := rfl

/-- The linear restriction map on redrawings modulo translations. -/
def deformationRestriction :
    DeformationSpace P →ₗ[ℝ] DeformationSpace (facePolytope P hF) :=
  (translationSpace P).mapQ (translationSpace (facePolytope P hF))
    (redrawingRestriction P hF) (by
      rintro h ⟨b, rfl⟩
      exact ⟨b, rfl⟩)

@[simp] theorem deformationRestriction_mk (h : redrawingSpace P) :
    deformationRestriction P hF (Submodule.Quotient.mk h) =
      Submodule.Quotient.mk (redrawingRestriction P hF h) := rfl

/-- The precise quotient-space definition of a determining face. -/
def FaceDetermines : Prop := Function.Injective (deformationRestriction P hF)

/-- It suffices to recover a redrawing that vanishes identically on the face. -/
theorem determines_of_zero_restriction
    (hzero : ∀ h : redrawingSpace P, redrawingRestriction P hF h = 0 → h = 0) :
    FaceDetermines P hF := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro q hq
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective (translationSpace P) q
  change (Submodule.Quotient.mk (redrawingRestriction P hF h) :
    DeformationSpace (facePolytope P hF)) = 0 at hq
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero (translationSpace (facePolytope P hF))).mp hq
  have hz : redrawingRestriction P hF (h - translationMap P b) = 0 := by
    rw [map_sub, redrawingRestriction_translation, ← hb, sub_self]
  apply (Submodule.Quotient.mk_eq_zero (translationSpace P)).mpr
  exact ⟨b, (sub_eq_zero.mp (hzero _ hz)).symm⟩

/-- Pointwise form of the determining-face criterion. -/
theorem determines_of_vanishing
    (hzero : ∀ h : redrawingSpace P,
      (∀ u : Vertex (facePolytope P hF), h (faceVertex P hF u) = 0) →
      ∀ v : Vertex P, h v = 0) :
    FaceDetermines P hF := by
  apply determines_of_zero_restriction P hF
  intro h hr
  apply Subtype.ext
  funext v
  apply hzero h ?_ v
  intro u
  exact congrArg (fun k : redrawingSpace (facePolytope P hF) => k u) hr

variable {P hF}

/-- A coordinate difference is a linear functional on full redrawings. -/
def redrawingDifference (P : ConvexPolytope d) (u v : Vertex P) (i : Fin d) :
    redrawingSpace P →ₗ[ℝ] ℝ where
  toFun h := h v i - h u i
  map_add' h k := by
    change (h v + k v) i - (h u + k u) i = _
    simp only [PiLp.add_apply]
    ring
  map_smul' a h := by
    change (a • h v) i - (a • h u) i = _
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Coordinate differences are unchanged by translation, so they descend. -/
def deformationDifference (P : ConvexPolytope d) (u v : Vertex P) (i : Fin d) :
    DeformationSpace P →ₗ[ℝ] ℝ :=
  (translationSpace P).liftQ (redrawingDifference P u v i) (by
    rintro h ⟨b, rfl⟩
    change b i - b i = 0
    exact sub_self _)

@[simp] theorem deformationDifference_mk (P : ConvexPolytope d)
    (u v : Vertex P) (i : Fin d) (h : redrawingSpace P) :
    deformationDifference P u v i (Submodule.Quotient.mk h) = h v i - h u i := rfl

/-- `k` translation-invariant coordinates that determine every restricted
assignment give a genuine `k`-dimensional upper bound on the quotient image. -/
theorem restriction_rank_le_of_difference_determination
    (P : ConvexPolytope d) {F : Set (E d)} (hF : P.IsFace F) {k : ℕ}
    (anchor : Vertex (facePolytope P hF))
    (vertices : Fin k → Vertex (facePolytope P hF))
    (coordinates : Fin k → Fin d)
    (hdet : ∀ h : redrawingSpace P,
      (∀ j : Fin k,
        h (faceVertex P hF (vertices j)) (coordinates j) -
          h (faceVertex P hF anchor) (coordinates j) = 0) →
      ∀ v : Vertex (facePolytope P hF),
        h (faceVertex P hF v) = h (faceVertex P hF anchor)) :
    Module.finrank ℝ (deformationRestriction P hF).range ≤ k := by
  classical
  let Q := facePolytope P hF
  let coordinatesMap : DeformationSpace Q →ₗ[ℝ] (Fin k → ℝ) :=
    LinearMap.pi fun j => deformationDifference Q anchor (vertices j) (coordinates j)
  let imageCoordinates : (deformationRestriction P hF).range →ₗ[ℝ] (Fin k → ℝ) :=
    coordinatesMap.comp (deformationRestriction P hF).range.subtype
  have hinj : Function.Injective imageCoordinates := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    obtain ⟨q, hq⟩ := z.property
    obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective (translationSpace P) q
    have hz' : coordinatesMap
        (Submodule.Quotient.mk (redrawingRestriction P hF h)) = 0 := by
      change coordinatesMap z.val = 0 at hz
      rw [← hq] at hz
      exact hz
    have heval (j : Fin k) :
        h (faceVertex P hF (vertices j)) (coordinates j) -
          h (faceVertex P hF anchor) (coordinates j) = 0 := by
      exact congrArg (fun x : Fin k → ℝ => x j) hz'
    apply Subtype.ext
    rw [← hq]
    change (Submodule.Quotient.mk (redrawingRestriction P hF h) : DeformationSpace Q) = 0
    apply (Submodule.Quotient.mk_eq_zero (translationSpace Q)).mpr
    refine ⟨h (faceVertex P hF anchor), ?_⟩
    apply Subtype.ext
    funext v
    exact (hdet h heval v).symm
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

end Papers.Polytopes
