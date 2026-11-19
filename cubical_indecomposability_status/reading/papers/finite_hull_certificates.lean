module
public import cubical.polytope.faces
public import cubical.polytope.faccia_argmax

@[expose] public section

/-!
# Finite supporting-form certificates for actual convex polytopes

A certificate is used only to supply linear inequalities.  The conclusions
about extreme points and exposed faces are derived with Mathlib convexity.
-/

noncomputable section
open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

namespace Papers.Polytopes

variable {d n m : ℕ}

theorem linear_lower_bound_on_hull (s : Finset (E d))
    (l : E d →L[ℝ] ℝ) (c : ℝ) (h : ∀ v ∈ s, c ≤ l v) :
    ∀ x ∈ convexHull ℝ (s : Set (E d)), c ≤ l x := by
  exact convexHull_min h (convex_halfSpace_ge (LinearMap.isLinear l.toLinearMap) c)

/-- A strict linear minimum on the generators is an exposed point of their
ordinary convex hull. -/
theorem strict_minimum_is_exposed (s : Finset (E d)) {v : E d} (hv : v ∈ s)
    (l : E d →L[ℝ] ℝ) (hstrict : ∀ w ∈ s, w ≠ v → l v < l w) :
    IsExposed ℝ (convexHull ℝ (s : Set (E d))) {v} := by
  have hmin : ∀ w ∈ convexHull ℝ (s : Set (E d)), l v ≤ l w := by
    apply linear_lower_bound_on_hull s l (l v)
    intro w hw
    by_cases h : w = v
    · simp [h]
    · exact (hstrict w hw h).le
  intro _
  refine ⟨-l, ?_⟩
  ext x
  constructor
  · rintro rfl
    exact ⟨subset_convexHull ℝ _ hv, fun w hw => by
      simpa only [ContinuousLinearMap.neg_apply, neg_le_neg_iff] using hmin w hw⟩
  · rintro ⟨hx, hmax⟩
    have hxv : l x = l v := by
      have h := hmax v (subset_convexHull ℝ _ hv)
      simp only [ContinuousLinearMap.neg_apply, neg_le_neg_iff] at h
      exact le_antisymm h (hmin x hx)
    have hxHull := PlatoniciL3.faccia_argmax s (-l) hx hmax
    have hsub : {w ∈ (s : Set (E d)) | (-l) w = (-l) x} ⊆ {v} := by
      rintro w ⟨hw, heq⟩
      change w = v
      by_contra hne
      have hlt := hstrict w hw hne
      simp only [ContinuousLinearMap.neg_apply, neg_inj] at heq
      rw [heq, hxv] at hlt
      exact lt_irrefl _ hlt
    exact (convexHull_min hsub (convex_singleton v)) hxHull

def polytopeOfStrictMinima (s : Finset (E d)) (hne : s.Nonempty)
    (hmin : ∀ v ∈ s, ∃ l : E d →L[ℝ] ℝ, ∀ w ∈ s, w ≠ v → l v < l w) :
    ConvexPolytope d where
  vertices := s
  vertices_nonempty := hne
  vertices_eq_extremePoints := by
    apply Set.Subset.antisymm
    · intro v hv
      obtain ⟨l, hl⟩ := hmin v hv
      exact (strict_minimum_is_exposed s hv l hl).isExtreme.mem_extremePoints
    · exact extremePoints_convexHull_subset

/-- Nonnegative forms separating ordered pairs of labels imply that every
label represents an actual extreme vertex. -/
def polytopeOfSeparatingSupports (p : Fin n → E d) (hn : 0 < n)
    (l : Fin m → E d →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hl : ∀ f v, c f ≤ l f (p v))
    (hsep : ∀ v w, v ≠ w → ∃ f, l f (p v) = c f ∧ c f < l f (p w)) :
    ConvexPolytope d := by
  classical
  let s := Finset.univ.image p
  have hs : s.Nonempty := ⟨p ⟨0, hn⟩, Finset.mem_image.mpr
    ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩
  apply polytopeOfStrictMinima s hs
  intro x hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  let selected : Finset (Fin m) := Finset.univ.filter (fun f => l f (p v) = c f)
  refine ⟨∑ f ∈ selected, l f, ?_⟩
  intro y hy hyne
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hy
  have hvw : v ≠ w := by
    intro h
    subst w
    exact hyne rfl
  obtain ⟨f, hfv, hfw⟩ := hsep v w hvw
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_lt_sum
  · intro g hg
    rw [(Finset.mem_filter.mp hg).2]
    exact hl g w
  · exact ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfv⟩, by simpa [hfv] using hfw⟩

@[simp] theorem polytopeOfSeparatingSupports_vertices
    (p : Fin n → E d) (hn : 0 < n)
    (l : Fin m → E d →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hl : ∀ f v, c f ≤ l f (p v))
    (hsep : ∀ v w, v ≠ w → ∃ f, l f (p v) = c f ∧ c f < l f (p w)) :
    (polytopeOfSeparatingSupports p hn l c hl hsep).vertices = Finset.univ.image p := rfl

theorem separatingSupports_injective (p : Fin n → E d)
    (l : Fin m → E d →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hsep : ∀ v w, v ≠ w → ∃ f, l f (p v) = c f ∧ c f < l f (p w)) :
    Function.Injective p := by
  intro v w hvw
  by_contra hne
  obtain ⟨f, hfv, hfw⟩ := hsep v w hne
  rw [← hvw, hfv] at hfw
  exact lt_irrefl _ hfw

theorem polytopeOfSeparatingSupports_card
    (p : Fin n → E d) (hn : 0 < n)
    (l : Fin m → E d →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hl : ∀ f v, c f ≤ l f (p v))
    (hsep : ∀ v w, v ≠ w → ∃ f, l f (p v) = c f ∧ c f < l f (p w)) :
    (polytopeOfSeparatingSupports p hn l c hl hsep).vertices.card = n := by
  classical
  rw [polytopeOfSeparatingSupports_vertices,
    Finset.card_image_of_injective _ (separatingSupports_injective p l c hsep)]
  simp

def minimumFace (P : ConvexPolytope d) (l : E d →L[ℝ] ℝ) (c : ℝ) : Set (E d) :=
  {x ∈ P.toSet | l x = c}

theorem minimumFace_isFace (P : ConvexPolytope d) (l : E d →L[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ v ∈ P.vertices, c ≤ l v)
    (hattained : ∃ v ∈ P.vertices, l v = c) : P.IsFace (minimumFace P l c) := by
  obtain ⟨v, hv, hvc⟩ := hattained
  have hvbody : v ∈ P.toSet := subset_convexHull ℝ _ hv
  have hglobal := linear_lower_bound_on_hull P.vertices l c hbound
  refine ⟨?_, ⟨v, hvbody, hvc⟩⟩
  intro _
  refine ⟨-l, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hxc⟩
    refine ⟨hx, fun y hy => ?_⟩
    simp only [ContinuousLinearMap.neg_apply, neg_le_neg_iff]
    rw [hxc]
    exact hglobal y hy
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, le_antisymm ?_ (hglobal x hx)⟩
    have h := hmax v hvbody
    simp only [ContinuousLinearMap.neg_apply, neg_le_neg_iff] at h
    simpa [hvc] using h

end Papers.Polytopes
