module
prelude
import GraphInputsRow29Part00274Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0708
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 34095631974656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00274.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 34096269496320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00274.record001_result⟩)
 (.leaf ⟨(29, 34110664351808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00274.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 34123532501248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00274.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 34123800969216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00274.record004_result⟩)
 (.leaf ⟨(29, 34123809292288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00274.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23469 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 23469 23475 :=
  block_of_table results 23469 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0708
