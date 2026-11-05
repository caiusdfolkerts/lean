module
prelude
import GraphInputsRow29Part00100Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0534
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 17198533836800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00100.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 17198928101888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00100.record001_result⟩)
 (.leaf ⟨(29, 17201381834752), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00100.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 17202149851136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00100.record003_result⟩)
 (.leaf ⟨(29, 17205639123200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00100.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 17218800779264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00100.record005_result⟩)
 (.leaf ⟨(29, 17227659083776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00100.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21939 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 21939 21946 :=
  block_of_table results 21939 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0534
