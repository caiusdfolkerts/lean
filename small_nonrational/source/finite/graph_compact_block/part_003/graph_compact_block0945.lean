module
prelude
import GraphInputsRow31Part00157Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0945
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 31068451774464), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00157.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 31074122998016), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00157.record001_result⟩)
 (.leaf ⟨(31, 31079525269632), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00157.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 31079860805632), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00157.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 31080565457024), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00157.record004_result⟩)
 (.leaf ⟨(31, 31080934023168), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00157.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26668 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 26668 26674 :=
  block_of_table results 26668 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0945
