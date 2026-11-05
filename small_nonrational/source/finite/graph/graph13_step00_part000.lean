module
prelude
public import GraphCatalogueData
public import Graph13Frames
public import Graph13Level00
public import Graph13Level01
public import FastGraphCatalogueCheck

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step00.Part000
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
noncomputable def table : Table Nat :=
(.leaf 11374984405597749999641104061037363861296257700495360392991593594470748414456546338620412384697867636978813340904060037907468317477481394120200810172358879699036772873395304424330382159386280264609329299947315652421333177559617893454678066009416504982401062064244035411424512562419862761207473809166488386704058260315556979116140916729947516616286459562331239598173115311580593638807712170419978868121088330204285689935677610665050114)
noncomputable def lookup (i : Nat) : Nat := table.get i
noncomputable def test (i : Nat) : Bool := (List.finRange 45).all fun edge =>
  FastGraphCatalogueCheck.extensionCheck TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level00.entry (Fin.ofNat 1 i)) Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level01.entry edge
    (choiceAt (lookup i) edge)
theorem checked_0 : Interval test 0 1 :=
  interval_of_check test 0 1 (by decide +kernel)

theorem checked : Interval test 0 1 :=
  checked_0
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step00.Part000
