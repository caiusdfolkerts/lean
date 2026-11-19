module
prelude
import GraphInputsRow29Part00134Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0568
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 22875801125440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record000_result⟩)
 (.leaf ⟨(29, 22910160863776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 22997545058304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 23006130798592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record003_result⟩)
 (.leaf ⟨(29, 23006799724544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 23014724861952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 23108580810816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record006_result⟩)
 (.leaf ⟨(29, 23168799539456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 23177121038592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 23177389441280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record009_result⟩)
 (.leaf ⟨(29, 23177400950784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22420 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 22420 22431 :=
  block_of_table results 22420 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0568
