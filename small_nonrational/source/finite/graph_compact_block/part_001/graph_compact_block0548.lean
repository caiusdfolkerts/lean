module
prelude
import GraphInputsRow29Part00114Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0548
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 19649752203264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00114.record000_result⟩)
 (.leaf ⟨(29, 19650280685568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00114.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 19701694464000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00114.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 19709743398912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00114.record003_result⟩)
 (.leaf ⟨(29, 19710412324864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00114.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22164 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 22164 22169 :=
  block_of_table results 22164 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0548
