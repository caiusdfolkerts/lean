module
public import PaperVerification.ToricFaceInheritance
public import PaperVerification.ToricChartSmoothness
public import PaperVerification.ToricIDP
@[expose] public section
/-!
# Smooth face inheritance and the unrestricted integer decomposition theorem

The face chart is constructed from actual primitive edge directions. Saturation
preserves all lattice points and exact edge lengths; changing the local chart at
each vertex proves global smoothness. This closes the dimension induction in
the integer decomposition property without an additional geometric hypothesis.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- Every geometric edge bound passes to a saturated coordinate polytope of
an actual face, with precisely the same bound. -/
theorem edgesAtLeast_face_chart {d bound : ℕ} (hP : P.EdgesAtLeast bound)
    (F : Set (Ambient n)) (hF : IsExtreme ℝ P.carrier F)
    (Q : LatticePolytope d) (e : IntegralAffineEmbedding d n)
    (heF : e.realMap '' Q.carrier = F) : Q.EdgesAtLeast bound := by
  apply (Q.edgesAtLeast_iff bound).mpr
  intro v w hvw
  have hedge : P.IsEdge (embed n (e.latticeMap v)) (embed n (e.latticeMap w)) := by
    rw [e.embed_latticeMap, e.embed_latticeMap]
    refine ⟨fun h => hvw.1 (e.realMap_injective h), ?_⟩
    have h := affine_isExtreme_image e.realMap e.realMap_injective hvw.2
    rw [heF, image_segment] at h
    exact hF.trans h
  have hlen := (P.edgesAtLeast_iff bound).mp hP (e.latticeMap v) (e.latticeMap w) hedge
  simpa only [e.latticeLength_latticeMap] using hlen

/-- Every nonempty actual convex face of a smooth lattice polytope is a
saturated integral affine image of a smooth full-dimensional lattice polytope.
All edge bounds are inherited, and every proper face has smaller dimension. -/
theorem smooth_face_chart {bound : ℕ} (hP : P.Smooth) (hlP : P.EdgesAtLeast bound)
    (F : Set (Ambient n)) (hFne : F.Nonempty) (hFconv : Convex ℝ F)
    (hF : IsExtreme ℝ P.carrier F) :
    ∃ (d : ℕ) (Q : LatticePolytope d) (e : IntegralAffineEmbedding d n),
      d ≤ n ∧ (F ≠ P.carrier → d < n) ∧ Q.Smooth ∧ Q.EdgesAtLeast bound ∧
        e.realMap '' Q.carrier = F := by
  obtain ⟨v, hv⟩ := P.face_vertices_nonempty F hFconv hF hFne
  obtain ⟨d, Q, e, lengths, hd, hdstrict, hezero, heF, hedges, hall⟩ :=
    P.exists_face_chart_at_vertex hP F hFconv hF v hv
  refine ⟨d, Q, e, hd, hdstrict, ?_, P.edgesAtLeast_face_chart hlP F hF Q e heF, heF⟩
  apply smooth_of_local_saturated_charts F Q e heF
  intro w hw
  obtain ⟨k, R, f, ls, hk, hkstrict, hfzero, hfF, haxis, hcomplete⟩ :=
    P.exists_face_chart_at_vertex hP F hFconv hF w hw
  exact ⟨k, R, f, ls, hfzero, hfF, haxis, hcomplete⟩

/-- The proper-face form needed in unrestricted dimension induction. -/
theorem proper_smooth_face_chart {bound : ℕ} (hP : P.Smooth)
    (hlP : P.EdgesAtLeast bound) (F : Set (Ambient n)) (hFne : F.Nonempty)
    (hFconv : Convex ℝ F) (hF : IsExtreme ℝ P.carrier F) (hproper : F ≠ P.carrier) :
    ∃ (d : ℕ) (Q : LatticePolytope d) (e : IntegralAffineEmbedding d n),
      d < n ∧ Q.Smooth ∧ Q.EdgesAtLeast bound ∧ e.realMap '' Q.carrier = F := by
  obtain ⟨d, Q, e, hd, hstrict, hQ, hlQ, heQ⟩ :=
    P.smooth_face_chart hP hlP F hFne hFconv hF
  exact ⟨d, Q, e, hstrict hproper, hQ, hlQ, heQ⟩

/-- Corollary 4.3: every smooth lattice polytope whose edges have length at
least its dimension has the full integer decomposition property in every degree.
This includes dimension zero and does not assume decomposition on its faces. -/
theorem integerDecomposition_of_smooth_long_edges (hP : P.Smooth)
    (hlP : P.EdgesAtLeast n) : P.HasIDP := by
  apply idp_of_smooth_face_charts ?_ n P hP hlP
  intro k R hR hlR F hFne hFconv hF hproper
  exact R.proper_smooth_face_chart hR hlR F hFne hFconv hF hproper

end LatticePolytope

end PaperVerification.ToricGeometry
