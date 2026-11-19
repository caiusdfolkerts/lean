module
prelude
import GraphInputsRow31Part00097Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0885
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 20965014700032), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00097.record000_result⟩)
 (.leaf ⟨(31, 21015950262272), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00097.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 21328807739456), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00097.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 21446017482752), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00097.record003_result⟩)
 (.leaf ⟨(31, 21513508520192), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00097.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26319 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 26319 26324 :=
  block_of_table results 26319 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0885
