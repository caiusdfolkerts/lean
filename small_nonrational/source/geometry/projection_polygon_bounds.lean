module
public import ProjectionPolygonCondition
public import PaperPolygon.Checks
public import PaperPolygon.Explicit1982

@[expose] public section

namespace Nonrational.TerminalVerification
open Nonrational.TerminalData
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection

/-- Every target other than1982 has only triangles and quadrilaterals. -/
theorem target_all_polygons_small (j : Nat) (hj : j < targetCount) (hne : j ≠ 1982) :
    AllPolygonsSmall (decode (targets j)) :=
  allPolygonsSmall_of_raw_check (PaperPolygon.targets_checked j hj) hne

/-- The supplied reconstruction certificates satisfy the paper's explicit
polygon bound at their projection centre. The sole pentagonal target uses
its independently exposed, exact centre-zero certificate. -/
theorem paper_certifies_of_certifies (j : Nat) (hj : j < targetCount)
    (h : Certifies j) : PaperCertifies j := by
  by_cases heq : j = 1982
  · subst j
    exact paper_projection_1982
  · obtain ⟨C⟩ := h
    exact ⟨C.with_small_polygons (target_all_polygons_small j hj heq)⟩

#print axioms paper_projection_1982
#print axioms target_all_polygons_small
#print axioms paper_certifies_of_certifies

end Nonrational.TerminalVerification
