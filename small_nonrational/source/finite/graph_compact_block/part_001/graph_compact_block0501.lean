module
prelude
import GraphInputsRow29Part00067Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0501
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 12135031668992), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record000_result⟩)
 (.leaf ⟨(29, 12135040057344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 12135163789568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record002_result⟩)
 (.leaf ⟨(29, 12139064524800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 12139324539136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record004_result⟩)
 (.leaf ⟨(29, 12139332927488), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 12142275789056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 12142544191744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_result⟩)
 (.leaf ⟨(29, 12142556221440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21432 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 21432 21441 :=
  block_of_table results 21432 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0501
