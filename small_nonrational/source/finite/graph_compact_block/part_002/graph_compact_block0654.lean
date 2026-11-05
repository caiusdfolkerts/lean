module
prelude
import GraphInputsRow29Part00220Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0654
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 29766674087936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00220.record000_result⟩)
 (.leaf ⟨(29, 29772914888832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00220.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 29773988364928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00220.record002_result⟩)
 (.leaf ⟨(29, 29831098597376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00220.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 29833985802496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00220.record004_result⟩)
 (.leaf ⟨(29, 29834120069120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00220.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 29835025989888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00220.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 29837172424960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00220.record007_result⟩)
 (.leaf ⟨(29, 29902705328128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00220.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23132 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 23132 23141 :=
  block_of_table results 23132 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0654
