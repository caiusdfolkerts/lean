module
prelude
import GraphInputsRow31Part00081Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0869
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 16499150979328), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00081.record000_result⟩)
 (.leaf ⟨(31, 16499922702336), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00081.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 16531346456832), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00081.record002_result⟩)
 (.leaf ⟨(31, 16531601817856), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00081.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 16531614924800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00081.record004_result⟩)
 (.leaf ⟨(31, 16531623247872), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00081.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 16532134694912), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00081.record006_result⟩)
 (.leaf ⟨(31, 16532403028224), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00081.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26124 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 26124 26132 :=
  block_of_table results 26124 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0869
