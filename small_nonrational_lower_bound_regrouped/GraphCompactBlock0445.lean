module
prelude
import GraphInputsRow29Part00011Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0445
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 3208479047936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00011.record000_result⟩)
 (.leaf ⟨(29, 3208743224064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00011.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 3209015918592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00011.record002_result⟩)
 (.leaf ⟨(29, 3209024241664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00011.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 3217068949760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00011.record004_result⟩)
 (.leaf ⟨(29, 3217737940992), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00011.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 3225658916864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00011.record006_result⟩)
 (.leaf ⟨(29, 3225931481088), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00011.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20680 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 20680 20688 :=
  block_of_table results 20680 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0445
