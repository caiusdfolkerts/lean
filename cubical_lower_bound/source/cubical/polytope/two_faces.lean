import cubical.polytope.graph
import cubical.polytope.dim_stretta

/-! # Uniqueness of a two-face through two nonadjacent vertices -/

open Set

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

theorem face_eq_of_subset_of_dimension_eq (P : ConvexPolytope n)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (hFG : F ⊆ G) (hdim : faceDim F = faceDim G) : F = G := by
  by_contra hne
  have hlt := faceDim_lt_of_ssubset P hF hG (hFG.ssubset_of_ne hne)
  omega

/-- Two different two-faces cannot share two nonadjacent vertices. This is
the geometric fact ensuring that different link edges have distinct opposite
white vertices in Lemma 2. -/
theorem two_faces_eq_of_nonadjacent_vertices (P : ConvexPolytope n)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (hdF : faceDim F = 2) (hdG : faceDim G = 2)
    (u v : VertexType P) (huF : u.val ∈ F) (hvF : v.val ∈ F)
    (huG : u.val ∈ G) (hvG : v.val ∈ G)
    (hne : u ≠ v) (hnadj : ¬(polytopeGraph P).Adj u v) : F = G := by
  have hI : P.IsFace (F ∩ G) := isFace_inter P hF hG ⟨u.val, huF, huG⟩
  have hdim0 : faceDim (F ∩ G) ≠ 0 := by
    intro hdim
    obtain ⟨x, hx, _⟩ := punto_di_faccia0_e_vertice P hI hdim
    have hu : u.val = x := by simpa [hx] using (show u.val ∈ F ∩ G from ⟨huF, huG⟩)
    have hv : v.val = x := by simpa [hx] using (show v.val ∈ F ∩ G from ⟨hvF, hvG⟩)
    exact hne (Subtype.ext (hu.trans hv.symm))
  have hdim1 : faceDim (F ∩ G) ≠ 1 := by
    intro hdim
    exact hnadj ⟨hne, F ∩ G, hI, hdim, ⟨huF, huG⟩, ⟨hvF, hvG⟩⟩
  have hle : faceDim (F ∩ G) ≤ faceDim F :=
    Submodule.finrank_mono (vectorSpan_mono ℝ Set.inter_subset_left)
  have hdI : faceDim (F ∩ G) = 2 := by omega
  have hIF := face_eq_of_subset_of_dimension_eq P hI hF Set.inter_subset_left
    (hdI.trans hdF.symm)
  have hIG := face_eq_of_subset_of_dimension_eq P hI hG Set.inter_subset_right
    (hdI.trans hdG.symm)
  exact hIF.symm.trans hIG

end LeanEval.Geometry.PlatonicClassification
