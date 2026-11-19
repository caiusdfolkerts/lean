module
prelude
import GraphInputsRow29Part00130Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0564
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 21925829083136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record000_result⟩)
 (.leaf ⟨(29, 21926101647360), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 21926613614592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record002_result⟩)
 (.leaf ⟨(29, 21930121953280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22339 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 22339 22343 :=
  block_of_table results 22339 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0564
