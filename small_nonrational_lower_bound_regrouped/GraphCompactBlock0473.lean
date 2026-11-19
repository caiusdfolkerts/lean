module
prelude
import GraphInputsRow29Part00039Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0473
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 7562766320384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00039.record000_result⟩)
 (.leaf ⟨(29, 7563039014912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00039.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 7563047337984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00039.record002_result⟩)
 (.leaf ⟨(29, 7564846695168), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00039.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 7564855148544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00039.record004_result⟩)
 (.leaf ⟨(29, 7565119389696), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00039.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 7565127712768), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00039.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 7572607205376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00039.record007_result⟩)
 (.leaf ⟨(29, 7577465291008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00039.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21040 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 21040 21049 :=
  block_of_table results 21040 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0473
