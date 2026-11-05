import Schoenflies.FaceCyclesLand
import Schoenflies.Graph.K33Land

/-!
Actual plane-drawing obstructions used in the planar corollaries.

The auxiliary intersection theorem below uses the proved polygonal crosscut theorem,
not an assumed Euler identity or a definition of planarity by an edge inequality.
-/

open Set Schoenflies

namespace GraphicalZonotopes.PlanarGeometry

/-- Alternating simple arcs in the same complementary region of a polygonal
Jordan curve must intersect.  The second arc may be an arbitrary topological arc. -/
theorem alternating_arc_inter_nonempty
    {C A B P Q Ω : Set Plane} {p q u v : Plane}
    (hC : IsSeparating C) (hCpoly : IsPolygonal C)
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
    (hApoly : IsPolygonal A) (hBpoly : IsPolygonal B)
    (hAB : A ∪ B = C) (hAiB : A ∩ B = {p, q})
    (hP : IsArcBetween P p q) (hPpoly : IsPolygonal P)
    (hPC : P ∩ C = {p, q})
    (hΩ : IsRegionOf C Ω) (hPΩ : P \ {p, q} ⊆ Ω)
    (hQ : IsArcBetween Q u v) (hQΩ : Q \ {u, v} ⊆ Ω)
    (hu : u ∈ A \ {p, q}) (hv : v ∈ B \ {p, q}) :
    (Q ∩ P).Nonempty := by
  classical
  by_contra hempty
  have hdis : ∀ z ∈ Q, z ∉ P := by
    intro z hz hzp
    exact hempty ⟨z, hz, hzp⟩
  have hsub : Q \ {u, v} ⊆ Ω \ P := fun z hz =>
    ⟨hQΩ hz, hdis z hz.1⟩
  obtain ⟨z, hz⟩ : (Q \ {u, v}).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hlim := hQ.left_mem_closure_diff
    simpa [h] using hlim
  have hsubset := hQ.isPreconnected_diff.subset_connectedComponentIn hz hsub
  have hucl : u ∈ closure (connectedComponentIn (Ω \ P) z) :=
    closure_mono hsubset hQ.left_mem_closure_diff
  have hvcl : v ∈ closure (connectedComponentIn (Ω \ P) z) :=
    closure_mono hsubset hQ.right_mem_closure_diff
  have hAC : A ⊆ C := by rw [← hAB]; exact Set.subset_union_left
  have hBC : B ⊆ C := by rw [← hAB]; exact Set.subset_union_right
  have hsep : ∀ {D : Set Plane}, IsArcBetween D p q →
      IsPolygonal D → D ⊆ C → IsSeparating (D ∪ P) := by
    intro D hD hDp hDC
    apply Schoenflies.isSeparating_of_isJordanCurve
    · apply Schoenflies.isJordanCurve_union hD hP
      intro w hwD hwP
      have hw : w ∈ ({p, q} : Set Plane) := by
        rw [← hPC]
        exact ⟨hwP, hDC hwD⟩
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hw
    · exact hDp.union hPpoly ⟨p, hD.left_mem, hP.left_mem⟩
  have huB : u ∉ B := by
    intro huB
    exact hu.2 (hAiB ▸ (show u ∈ A ∩ B from ⟨hu.1, huB⟩))
  have hvA : v ∉ A := by
    intro hvA
    exact hv.2 (hAiB ▸ (show v ∈ A ∩ B from ⟨hvA, hv.1⟩))
  have hcompC : connectedComponentIn (Ω \ P) z ⊆ Cᶜ :=
    (connectedComponentIn_subset _ _).trans (Set.diff_subset.trans hΩ.subset_compl)
  rcases Schoenflies.crosscutSplitsRegion C A B P Ω p q hC hCpoly hPpoly
      hA hB hAB hAiB hP hPC hΩ hPΩ z (hsub hz) with hreg | hreg
  · rw [hreg.closure_eq (hsep hA hApoly hAC)] at hvcl
    rcases hvcl with hvcomp | hvA' | hvP
    · exact hcompC hvcomp (hBC hv.1)
    · exact hvA hvA'
    · exact hdis v hQ.right_mem hvP
  · rw [hreg.closure_eq (hsep hB hBpoly hBC)] at hucl
    rcases hucl with hucomp | huB' | huP
    · exact hcompC hucomp (hAC hu.1)
    · exact huB huB'
    · exact hdis u hQ.left_mem huP

end GraphicalZonotopes.PlanarGeometry
