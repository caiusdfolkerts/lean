module

public import Unimodular.CycleTopology

@[expose] public section

open scoped Pointwise Topology BigOperators
open Filter Set

namespace Unimodular.CycleDegree.FullCones

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] (S : FullCones I V)

theorem face_isClosed {F : PointedCone ℝ V} (hF : S.IsFace F) : IsClosed (F : Set V) := by
  obtain ⟨i, hi⟩ := hF
  have he : (F : Set V) = (S.cone i : Set V) ∩ Submodule.span ℝ (F : Set V) := by
    exact congrArg (fun K : PointedCone ℝ V => (K : Set V))
      (QuotientFaces.inf_span_eq hi).symm
  rw [he]
  exact (ConeInterior.isClosed_of_fg (S.fg i)).inter
    (Submodule.closed_of_finiteDimensional _)

/-- Restrict a chain to the actual star of a face. -/
noncomputable def starCoeff (c : I → ℤ) (F : PointedCone ℝ V) (i : I) : ℤ :=
  if F.IsFaceOf (S.cone i) then c i else 0

theorem starCoeff_nonneg (c : I → ℤ) (hc : ∀ i, 0 ≤ c i) (F : PointedCone ℝ V) :
    ∀ i, 0 ≤ S.starCoeff c F i := by
  intro i
  dsimp [starCoeff]
  split_ifs
  · exact hc i
  · exact le_rfl

theorem starCoeff_pos_iff (c : I → ℤ) (F : PointedCone ℝ V) (i : I) :
    0 < S.starCoeff c F i ↔ F.IsFaceOf (S.cone i) ∧ 0 < c i := by
  by_cases hF : F.IsFaceOf (S.cone i) <;> simp [starCoeff, hF]

def BadFacet (F : PointedCone ℝ V) (G : S.Facet) : Prop :=
  ¬ F.IsFaceOf G.1 ∧ ∃ i, F.IsFaceOf (S.cone i) ∧ G.1.IsFaceOf (S.cone i)

/-- Remove only facets which can bound this star but do not contain its central face. -/
def StarRegion (F : PointedCone ℝ V) : Set V :=
  {x | ∀ G : S.Facet, S.BadFacet F G → x ∉ G.1}

theorem starRegion_isOpen (F : PointedCone ℝ V) : IsOpen (S.StarRegion F) := by
  have he : S.StarRegion F =
      (⋃ G : {G : S.Facet // S.BadFacet F G}, (G.1.1 : Set V))ᶜ := by
    ext x
    simp [StarRegion]
  rw [he]
  exact (isClosed_iUnion_of_finite (fun G => S.face_isClosed G.1.2.1)).isOpen_compl

theorem active_mem_starRegion {F : PointedCone ℝ V} {x : V} (hx : Active F x) :
    x ∈ S.StarRegion F := by
  rintro G ⟨hnot, i, hFi, hGi⟩ hxG
  have hm := ((S.active_iff hFi).1 hx).2
  have hle : F ≤ G.1 := by
    rw [← hm]
    exact MinimalFaces.dominatedCone_le hGi hxG
  exact hnot ((PointedCone.IsFaceOf.isFaceOf_iff_le hFi hGi).2 hle)

/-- All facet rows of the restricted chain cancel wherever the corresponding facet is
active in the star region. This is proved directly from the original rows. -/
theorem star_active_rows (c : I → ℤ) (hc : S.IsCycle c) (F : PointedCone ℝ V)
    {x : V} (hx : x ∈ S.StarRegion F) (G : S.Facet) (hGx : Active G.1 x) :
    ∑ i, S.starCoeff c F i * S.boundary G i = 0 := by
  by_cases hFG : F.IsFaceOf G.1
  · have he : ∀ i, S.starCoeff c F i * S.boundary G i = c i * S.boundary G i := by
      intro i
      by_cases hGi : G.1.IsFaceOf (S.cone i)
      · simp [starCoeff, hFG.trans hGi]
      · simp [boundary, hGi]
    simpa only [he] using hc G
  · apply Finset.sum_eq_zero
    intro i _
    by_cases hFi : F.IsFaceOf (S.cone i)
    · have hn : ¬ G.1.IsFaceOf (S.cone i) := by
        intro hGi
        exact hx G ⟨hFG, i, hFi, hGi⟩ hGx.1
      simp [boundary, hn]
    · simp [starCoeff, hFi]

/-- The full neighborhood conclusion of the star argument. It applies to every positive
integral cycle, without simpliciality, unimodularity, projectivity, or a supplied fan. -/
theorem star_selected_mem_nhds (c : I → ℤ) (hc0 : ∀ i, 0 ≤ c i) (hc : S.IsCycle c)
    {F : PointedCone ℝ V} {x : V} (hx : Active F x)
    {i : I} (hFi : F.IsFaceOf (S.cone i)) (hci : 0 < c i) :
    S.Selected (S.starCoeff c F) ∈ 𝓝 x := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    ((S.starRegion_isOpen F).mem_nhds (S.active_mem_starRegion hx))
  have hxCi : x ∈ S.cone i := hFi.le hx.1
  have hxcl := S.cone_subset_closure_interior i hxCi
  obtain ⟨z, hzball, hzint⟩ := (mem_closure_iff.1 hxcl)
    (Metric.ball x r) Metric.isOpen_ball (Metric.mem_ball_self hr)
  obtain ⟨y, hy, hygen⟩ := S.generic_dense.inter_open_nonempty
    (Metric.ball x r ∩ interior (S.cone i : Set V))
    (Metric.isOpen_ball.inter isOpen_interior) ⟨z, hzball, hzint⟩
  have hpos : 0 < S.weightedDegree (S.starCoeff c F) y := by
    have ht := S.term_le_weightedDegree (S.starCoeff c F) (S.starCoeff_nonneg c hc0 F) i y
    rw [FacetLine.weight_of_interior hy.2] at ht
    simp only [starCoeff, if_pos hFi] at ht
    omega
  have hcover : Metric.ball x r ⊆ S.Selected (S.starCoeff c F) :=
    S.open_subset_selected_of_local_cycle (S.starCoeff c F) (S.starCoeff_nonneg c hc0 F)
      Metric.isOpen_ball (convex_ball x r)
      (fun q hq G hG => S.star_active_rows c hc F (hball hq) G hG)
      hy.1 (S.generic_regular hygen) hpos
  exact Filter.mem_of_superset (Metric.ball_mem_nhds x hr) hcover

end Unimodular.CycleDegree.FullCones
