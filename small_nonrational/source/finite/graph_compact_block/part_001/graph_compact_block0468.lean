module
prelude
import GraphInputsRow29Part00034Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0468
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 7186826854656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00034.record000_result⟩)
 (.leaf ⟨(29, 7186831016192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00034.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 7186831081472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00034.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 7187363594496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00034.record003_result⟩)
 (.leaf ⟨(29, 7187371917313), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00034.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 7187371982848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00034.record005_result⟩)
 (.leaf ⟨(29, 7190069460992), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00034.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 7190070956288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00034.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 7190333702144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00034.record008_result⟩)
 (.leaf ⟨(29, 7190335197440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00034.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20977 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 20977 20987 :=
  block_of_table results 20977 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0468
