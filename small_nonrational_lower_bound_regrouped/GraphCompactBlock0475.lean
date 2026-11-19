module
prelude
import GraphInputsRow29Part00041Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0475
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 7593905096960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record000_result⟩)
 (.leaf ⟨(29, 7597818183936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 7598065715456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 7598074103808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003_result⟩)
 (.leaf ⟨(29, 7598082360064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21055 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 21055 21060 :=
  block_of_table results 21055 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0475
