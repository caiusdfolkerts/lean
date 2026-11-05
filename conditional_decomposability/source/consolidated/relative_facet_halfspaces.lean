module
public import consolidated.deletion_fields
public import Mathlib.LinearAlgebra.AffineSpace.Dimension
public import Mathlib.Tactic.Abel

set_option Elab.async false

section BundlePart0
/- Source: Papers/RelativeFacetHalfspaces.lean -/





@[expose] public section

/-! The facet halfspace representation inside the actual affine span.
No ambient full-dimensionality assumption is made. -/

noncomputable section
namespace Papers.RelativeFacetHalfspaces
open Set Module Papers.Polytopes Papers.Coordinates Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical
variable {d : ℕ}

theorem zero_on_affineSpan (S : Set (E d)) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ y ∈ S, f y = 0) {x : E d} (hx : x ∈ affineSpan ℝ S) : f x = 0 := by
  exact AffineMap.eqOn_affineSpan (f := f) (g := 0) (fun y hy => hf y hy) hx

theorem zeroFace_ne_body (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ)
    (x : E d) (hx : x ∈ affineSpan ℝ P.toSet) (hn : f x ≠ 0) :
    affineZeroFace P f ≠ P.toSet := by
  intro heq
  apply hn
  apply zero_on_affineSpan P.toSet f _ hx
  intro y hy
  have hz : y ∈ affineZeroFace P f := heq.symm ▸ hy
  exact hz.2

theorem positive_pivot_form (P : ConvexPolytope d)
    (F : Set (E d)) (x : E d) (hgap : faceDim F + 2 ≤ P.dim) :
    ∃ h : E d →ᵃ[ℝ] ℝ, h x = 0 ∧ (∀ y ∈ F, h y = 0) ∧
      ∃ v ∈ P.vertices, 0 < h v := by
  let U := vectorSpan ℝ (insert x F)
  obtain ⟨v, hv, hnv⟩ : ∃ v ∈ P.vertices, v - x ∉ U := by
    by_contra hn
    push_neg at hn
    have hle : vectorSpan ℝ (P.vertices : Set (E d)) ≤ U := by
      rw [vectorSpan_def]
      apply Submodule.span_le.mpr
      rintro z ⟨a, ha, b, hb, rfl⟩
      have hh := U.sub_mem (hn a ha) (hn b hb)
      change a - b ∈ U
      convert hh using 1 <;> abel
    have hdim : P.dim ≤ finrank ℝ U := by
      change finrank ℝ (vectorSpan ℝ (convexHull ℝ (P.vertices : Set (E d)))) ≤ _
      rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
      exact Submodule.finrank_mono hle
    have hu := finrank_vectorSpan_insert_le_set (k := ℝ) F x
    change finrank ℝ U ≤ faceDim F + 1 at hu
    omega
  obtain ⟨l, hln, hU⟩ := Submodule.exists_le_ker_of_notMem hnv
  let h : E d →ᵃ[ℝ] ℝ := l.toAffineMap - AffineMap.const ℝ (E d) (l x)
  have happly (y : E d) : h y = l (y - x) := by
    change l y - l x = l (y - x)
    rw [map_sub]
  have hx : h x = 0 := by rw [happly, sub_self, map_zero]
  have hF : ∀ y ∈ F, h y = 0 := by
    intro y hy
    rw [happly]
    exact hU (vsub_mem_vectorSpan ℝ (Set.mem_insert_of_mem x hy) (Set.mem_insert x F))
  have hn : h v ≠ 0 := by rw [happly]; exact hln
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · refine ⟨-h, ?_, ?_, v, hv, ?_⟩
    · change -h x = 0
      rw [hx, neg_zero]
    · intro y hy
      change -h y = 0
      rw [hF y hy, neg_zero]
    · exact neg_pos.mpr hneg
  · exact ⟨h, hx, hF, v, hv, hpos⟩

theorem enlarge_supported_face
    (P : ConvexPolytope d)
    (F : Set (E d)) (hF : P.IsFace F) (f : E d →ᵃ[ℝ] ℝ)
    (hf : SupportsFace P F f) (x : E d) (hx : f x ≠ 0)
    (hP : x ∈ affineSpan ℝ P.toSet) (hgap : faceDim F + 2 ≤ P.dim) :
    ∃ G : Set (E d), ∃ g : E d →ᵃ[ℝ] ℝ,
      P.IsFace G ∧ SupportsFace P G g ∧ F ⊂ G ∧ G ≠ P.toSet ∧ g x = f x := by
  classical
  obtain ⟨h, hx0, hF0, v, hv, hvpos⟩ := positive_pivot_form P F x hgap
  let S := P.vertices.filter (fun y => 0 < h y)
  have hS : S.Nonempty := ⟨v, Finset.mem_filter.mpr ⟨hv, hvpos⟩⟩
  let r : E d → ℝ := fun y => f y / h y
  have hr : ∀ y ∈ S, 0 < r y := by
    intro y hy
    obtain ⟨hyP, hyp⟩ := Finset.mem_filter.mp hy
    have hbody : y ∈ P.toSet := subset_convexHull ℝ _ hyP
    have hfy : 0 < f y := by
      rcases lt_or_eq_of_le (hf.1 y hbody) with ht | he
      · exact ht
      · have hyF := (hf.mem_iff y).mpr ⟨hbody, he.symm⟩
        rw [hF0 y hyF] at hyp
        exact False.elim ((lt_irrefl _) hyp)
    exact div_pos hfy hyp
  let R := S.image r
  have hR : R.Nonempty := hS.image r
  let τ := R.min' hR
  have hτmem : τ ∈ R := Finset.min'_mem R hR
  obtain ⟨w, hwS, hwτ⟩ := Finset.mem_image.mp hτmem
  have hτ : 0 < τ := hwτ ▸ hr w hwS
  let g : E d →ᵃ[ℝ] ℝ := f - τ • h
  have gapply (y : E d) : g y = f y - τ * h y := rfl
  have hgV : ∀ y ∈ P.vertices, 0 ≤ g y := by
    intro y hy
    have hfy := hf.1 y (subset_convexHull ℝ _ hy)
    rw [gapply]
    by_cases hhy : 0 < h y
    · have hyS : y ∈ S := Finset.mem_filter.mpr ⟨hy, hhy⟩
      have hle : τ ≤ r y := Finset.min'_le R (r y) (Finset.mem_image_of_mem r hyS)
      have hm : τ * h y ≤ f y := (le_div_iff₀ hhy).mp hle
      exact sub_nonneg.mpr hm
    · have hm : τ * h y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hτ.le (le_of_not_gt hhy)
      linarith
  have hgP : ∀ y ∈ P.toSet, 0 ≤ g y := affine_nonneg_on_hull P.vertices g hgV
  have hgF : ∀ y ∈ F, g y = 0 := by
    intro y hy
    rw [gapply, hf.eq_zero hy, hF0 y hy, mul_zero, sub_zero]
  have hgx : g x = f x := by rw [gapply, hx0, mul_zero, sub_zero]
  let G := affineZeroFace P g
  have hsub : F ⊆ G := fun y hy => ⟨face_subset_toSet P hF hy, hgF y hy⟩
  have hneG : G.Nonempty := hF.2.mono hsub
  have hG : P.IsFace G := affineZeroFace_isFace P g hgP hneG
  have hwP : w ∈ P.vertices := (Finset.mem_filter.mp hwS).1
  have hwp : 0 < h w := (Finset.mem_filter.mp hwS).2
  have hwg : g w = 0 := by
    rw [gapply, ← hwτ]
    dsimp only [r]
    rw [div_mul_cancel₀ _ (ne_of_gt hwp), sub_self]
  have hwF : w ∉ F := by
    intro hw
    rw [hF0 w hw] at hwp
    exact (lt_irrefl _) hwp
  refine ⟨G, g, hG, ⟨hgP, rfl⟩, ?_,
    zeroFace_ne_body P g x hP (hgx.trans_ne hx), hgx⟩
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro heq
  apply hwF
  rw [heq]
  exact ⟨subset_convexHull ℝ _ hwP, hwg⟩

theorem facet_containing_preserving_value
    (P : ConvexPolytope d)
    (F : Set (E d)) (hF : P.IsFace F) (f : E d →ᵃ[ℝ] ℝ)
    (hf : SupportsFace P F f) (x : E d) (hx : f x ≠ 0) (hP : x ∈ affineSpan ℝ P.toSet) :
    ∃ G : Set (E d), ∃ g : E d →ᵃ[ℝ] ℝ,
      IsFacet P G ∧ SupportsFace P G g ∧ F ⊆ G ∧ g x = f x := by
  suffices H : ∀ k : ℕ, ∀ (F : Set (E d)) (f : E d →ᵃ[ℝ] ℝ),
      P.IsFace F → SupportsFace P F f → f x ≠ 0 →
      P.dim - 1 - faceDim F ≤ k →
      ∃ G : Set (E d), ∃ g : E d →ᵃ[ℝ] ℝ,
        IsFacet P G ∧ SupportsFace P G g ∧ F ⊆ G ∧ g x = f x by
    exact H (P.dim - 1 - faceDim F) F f hF hf hx le_rfl
  intro k
  induction k with
  | zero =>
    intro F f hF hf hx hk
    have hproper : F ≠ P.toSet := by
      rw [hf.2]
      exact zeroFace_ne_body P f x hP hx
    have hlt := faceDim_lt_of_ssubset P hF (toSet_isFace P)
      (Set.ssubset_iff_subset_ne.mpr ⟨face_subset_toSet P hF, hproper⟩)
    change faceDim F < P.dim at hlt
    have hd : faceDim F + 1 = P.dim := by omega
    exact ⟨F, f, ⟨hF, hd⟩, hf, Set.Subset.rfl, rfl⟩
  | succ k ih =>
    intro F f hF hf hx hk
    by_cases heq : faceDim F + 1 = P.dim
    · exact ⟨F, f, ⟨hF, heq⟩, hf, Set.Subset.rfl, rfl⟩
    have hproper : F ≠ P.toSet := by
      rw [hf.2]
      exact zeroFace_ne_body P f x hP hx
    have hlt := faceDim_lt_of_ssubset P hF (toSet_isFace P)
      (Set.ssubset_iff_subset_ne.mpr ⟨face_subset_toSet P hF, hproper⟩)
    change faceDim F < P.dim at hlt
    have hgap : faceDim F + 2 ≤ P.dim := by omega
    obtain ⟨G, g, hG, hg, hFG, _, hgx⟩ := enlarge_supported_face P F hF f hf x hx hP hgap
    have hdim := faceDim_lt_of_ssubset P hF hG hFG
    obtain ⟨H, k, hH, hk, hGH, hkx⟩ := ih G g hG hg (hgx.trans_ne hx) (by omega)
    exact ⟨H, k, hH, hk, hFG.1.trans hGH, hkx.trans hgx⟩

theorem separating_facet_of_separating_face
    (P : ConvexPolytope d)
    (F : Set (E d)) (hF : P.IsFace F) (f : E d →ᵃ[ℝ] ℝ)
    (hf : SupportsFace P F f) (x : E d) (hx : f x < 0) (hP : x ∈ affineSpan ℝ P.toSet) :
    ∃ G : Set (E d), ∃ g : E d →ᵃ[ℝ] ℝ,
      IsFacet P G ∧ SupportsFace P G g ∧ g x < 0 := by
  obtain ⟨G, g, hG, hg, _, hval⟩ :=
    facet_containing_preserving_value P F hF f hf x (ne_of_lt hx) hP
  exact ⟨G, g, hG, hg, hval.trans_lt hx⟩

theorem exists_separating_facet (P : ConvexPolytope d)
    (x : E d) (hx : x ∉ P.toSet) (hP : x ∈ affineSpan ℝ P.toSet) :
    ∃ F : Set (E d), ∃ f : E d →ᵃ[ℝ] ℝ,
      IsFacet P F ∧ SupportsFace P F f ∧ f x < 0 := by
  obtain ⟨l, c, hbound, hcx⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (P.vertices : Set (E d)))
    (P.vertices.finite_toSet.isClosed_convexHull ℝ) hx
  obtain ⟨v, hv, hmax⟩ := P.vertices.exists_max_image l P.vertices_nonempty
  let f : E d →ᵃ[ℝ] ℝ := AffineMap.const ℝ (E d) (l v) - l.toLinearMap.toAffineMap
  have hf : ∀ y ∈ P.toSet, 0 ≤ f y := by
    intro y hy
    have hm := le_su_toSet P l hmax y hy
    change 0 ≤ l v - l y
    linarith
  have hne : (affineZeroFace P f).Nonempty := by
    refine ⟨v, subset_convexHull ℝ _ hv, ?_⟩
    change l v - l v = 0
    exact sub_self _
  have hfx : f x < 0 := by
    have hvlt := hbound v (subset_convexHull ℝ _ hv)
    change l v - l x < 0
    linarith
  exact separating_facet_of_separating_face P (affineZeroFace P f)
    (affineZeroFace_isFace P f hf hne) f ⟨hf, rfl⟩ x hfx hP


theorem supportsFacet_positive_proportional_on_span
    (P : ConvexPolytope d) (F : Set (E d)) (hF : IsFacet P F)
    (f g : E d →ᵃ[ℝ] ℝ) (hf : SupportsFace P F f) (hg : SupportsFace P F g) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ affineSpan ℝ P.toSet, f y = c * g y := by
  obtain ⟨x, hxP, hxF⟩ : ∃ x, x ∈ P.toSet ∧ x ∉ F := by
    by_contra h
    push_neg at h
    exact hF.ne_toSet (Set.Subset.antisymm (face_subset_toSet P hF.1) h)
  have hfx : 0 < f x := lt_of_le_of_ne (hf.1 x hxP)
    (fun hz => hxF ((hf.mem_iff x).mpr ⟨hxP, hz.symm⟩))
  have hgx : 0 < g x := lt_of_le_of_ne (hg.1 x hxP)
    (fun hz => hxF ((hg.mem_iff x).mpr ⟨hxP, hz.symm⟩))
  let U := homogeneousSpan (K := ℝ) F
  let W := homogeneousSpan (K := ℝ) P.toSet
  have hUker : U ≤ (affineLift g).ker := by
    apply Submodule.span_le.mpr
    rintro z ⟨y, hy, rfl⟩
    change homogeneousEvaluation (y, (1 : ℝ)) g = 0
    rw [homogeneousEvaluation_homogenize, hg.eq_zero hy]
  have hnot : homogenize (K := ℝ) x ∉ U := by
    intro hx
    have hz := hUker hx
    change homogeneousEvaluation (x, (1 : ℝ)) g = 0 at hz
    rw [homogeneousEvaluation_homogenize] at hz
    exact hgx.ne' hz
  have hUW : U ≤ W := by
    apply Submodule.span_mono
    exact Set.image_mono (face_subset_toSet P hF.1)
  have hxW : homogenize (K := ℝ) x ∈ W := homogenize_mem_span hxP
  have hspan : U ⊔ Submodule.span ℝ {homogenize (K := ℝ) x} = W := by
    apply Submodule.eq_of_le_of_finrank_eq
      (sup_le hUW (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxW)))
    rw [Submodule.finrank_sup_span_singleton hnot]
    change finrank ℝ (homogeneousSpan (K := ℝ) F) + 1 =
      finrank ℝ (homogeneousSpan (K := ℝ) P.toSet)
    rw [finrank_homogeneousSpan hF.1.2, finrank_homogeneousSpan ⟨x, hxP⟩]
    change faceDim F + 1 + 1 = P.dim + 1
    rw [hF.2]
  let c := f x / g x
  let L := affineLift f - c • affineLift g
  have hEval (y : E d) : L (homogenize (K := ℝ) y) = f y - c * g y := by
    simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, affineLift_apply,
      homogenize, homogeneousEvaluation_homogenize, smul_eq_mul]
  have hUL : U ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro z ⟨y, hy, rfl⟩
    change L (homogenize (K := ℝ) y) = 0
    rw [hEval, hf.eq_zero hy, hg.eq_zero hy, mul_zero, sub_self]
  have hxL : homogenize (K := ℝ) x ∈ L.ker := by
    change L (homogenize (K := ℝ) x) = 0
    rw [hEval]
    dsimp [c]
    rw [div_mul_cancel₀ _ hgx.ne', sub_self]
  have hWL : W ≤ L.ker := by
    rw [← hspan]
    exact sup_le hUL (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxL))
  refine ⟨c, div_pos hfx hgx, ?_⟩
  intro y hy
  have hz := hWL ((homogenize_mem_span_iff ⟨x, hxP⟩ y).mpr hy)
  change L (homogenize (K := ℝ) y) = 0 at hz
  rw [hEval] at hz
  exact sub_eq_zero.mp hz

/-- The complete finite facet description of any polytope, including
those embedded in a larger ambient vector space. -/
theorem mem_body_iff_span_and_chosenFacetForms
    (P : ConvexPolytope d) (x : E d) :
    x ∈ P.toSet ↔ x ∈ affineSpan ℝ P.toSet ∧
      ∀ F : FacetType P, 0 ≤ chosenFacetForm P F x := by
  constructor
  · intro hx
    exact ⟨subset_affineSpan ℝ P.toSet hx,
      fun F => (chosenFacetForm_supports P F).1 x hx⟩
  · rintro ⟨hxspan, hall⟩
    by_contra hx
    obtain ⟨F, f, hF, hf, hneg⟩ := exists_separating_facet P x hx hxspan
    let F' : FacetType P := ⟨⟨F, hF.1⟩, hF⟩
    obtain ⟨c, hc, heq⟩ := supportsFacet_positive_proportional_on_span P F hF f
      (chosenFacetForm P F') hf (chosenFacetForm_supports P F')
    have hn : 0 ≤ f x := by rw [heq x hxspan]; exact mul_nonneg hc.le (hall F')
    exact (not_lt_of_ge hn) hneg

theorem chosenFacetForm_positive_somewhere (P : ConvexPolytope d)
    (F : FacetType P) : ∃ x ∈ P.toSet, 0 < chosenFacetForm P F x := by
  obtain ⟨x, hxP, hxF⟩ : ∃ x, x ∈ P.toSet ∧ x ∉ F.val.val := by
    by_contra h
    push_neg at h
    exact F.property.ne_toSet
      (Set.Subset.antisymm (face_subset_toSet P F.val.property) h)
  have hf := chosenFacetForm_supports P F
  exact ⟨x, hxP, lt_of_le_of_ne (hf.1 x hxP)
    (fun hz => hxF ((hf.mem_iff x).mpr ⟨hxP, hz.symm⟩))⟩

end Papers.RelativeFacetHalfspaces

end
end
end BundlePart0

