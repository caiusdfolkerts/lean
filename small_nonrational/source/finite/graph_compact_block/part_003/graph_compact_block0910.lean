module
prelude
import GraphInputsRow31Part00122Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0910
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 27129299402752), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00122.record000_result⟩)
 (.leaf ⟨(31, 27132113715712), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00122.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 27226603528192), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00122.record002_result⟩)
 (.leaf ⟨(31, 27238717210752), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00122.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26498 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 26498 26502 :=
  block_of_table results 26498 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0910
