module
prelude
public import GraphCatalogueData
public import Graph13Frames
public import Graph13Level01
public import Graph13Level02
public import FastGraphCatalogueCheck

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step01.Part000
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
noncomputable def table : Table Nat :=
(.leaf 2648444947133064177540414457013306493159909714752721693887935303402904536534175084569494064829563855305058342215536679260511041164138852102717042562399613107089588731993766843990282204913664606017209185731110010870060599601384030712623845427719279458833761618180392641652461235261231671005666360233225312000955878627403785464527698893685148186444938840963885612651454451075318304837586533096412524933986427622888149868806146)
noncomputable def lookup (i : Nat) : Nat := table.get i
noncomputable def test (i : Nat) : Bool := (List.finRange 45).all fun edge =>
  FastGraphCatalogueCheck.extensionCheck TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level01.entry (Fin.ofNat 1 i)) Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level02.entry edge
    (choiceAt (lookup i) edge)
theorem checked_0 : Interval test 0 1 :=
  interval_of_check test 0 1 (by decide +kernel)

theorem checked : Interval test 0 1 :=
  checked_0
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step01.Part000
