module
prelude
import GraphInputsRow29Part00027Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0461
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 6711570137088), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027.record000_result⟩)
 (.leaf ⟨(29, 6720160038912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 6727198113792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027.record002_result⟩)
 (.leaf ⟨(29, 6727206436864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 6738963693600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027.record004_result⟩)
 (.leaf ⟨(29, 6752966836480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 6791622623232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027.record006_result⟩)
 (.leaf ⟨(29, 6791630946304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20913 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 20913 20921 :=
  block_of_table results 20913 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0461
