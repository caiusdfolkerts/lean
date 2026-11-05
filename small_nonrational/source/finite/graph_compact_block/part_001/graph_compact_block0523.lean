module
prelude
import GraphInputsRow29Part00089Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0523
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 15679382634624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00089.record000_result⟩)
 (.leaf ⟨(29, 15705760104704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00089.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 15706296975360), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00089.record002_result⟩)
 (.leaf ⟨(29, 15706429095936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00089.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 15712410140672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00089.record004_result⟩)
 (.leaf ⟨(29, 15712670220288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00089.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 15722939973632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00089.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 15723208376320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00089.record007_result⟩)
 (.leaf ⟨(29, 15809306984448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00089.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21764 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 21764 21773 :=
  block_of_table results 21764 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0523
