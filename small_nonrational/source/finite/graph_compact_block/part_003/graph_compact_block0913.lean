module
prelude
import GraphInputsRow31Part00125Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0913
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 28662196895744), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00125.record000_result⟩)
 (.leaf ⟨(31, 28665754714368), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00125.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 28666089242624), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00125.record002_result⟩)
 (.leaf ⟨(31, 28666357645312), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00125.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26518 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 26518 26522 :=
  block_of_table results 26518 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0913
