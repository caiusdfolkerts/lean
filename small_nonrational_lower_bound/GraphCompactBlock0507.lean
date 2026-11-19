module
prelude
import GraphInputsRow29Part00073Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0507
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 12577966981120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00073.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 12577975304192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00073.record001_result⟩)
 (.leaf ⟨(29, 12578107424768), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00073.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21502 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 21502 21505 :=
  block_of_table results 21502 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0507
