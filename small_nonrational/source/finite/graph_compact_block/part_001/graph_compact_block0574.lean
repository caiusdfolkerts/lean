module
prelude
import GraphInputsRow29Part00140Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0574
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 24058838122496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00140.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 24070139740160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00140.record001_result⟩)
 (.leaf ⟨(29, 24070676545536), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00140.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 24086195536128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00140.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 24090496794624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00140.record004_result⟩)
 (.leaf ⟨(29, 24091033600000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00140.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22529 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 22529 22535 :=
  block_of_table results 22529 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0574
