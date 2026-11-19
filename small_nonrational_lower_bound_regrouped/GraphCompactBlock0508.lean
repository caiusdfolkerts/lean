module
prelude
import GraphInputsRow29Part00074Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0508
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 12578214707200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00074.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 12578367504384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00074.record001_result⟩)
 (.leaf ⟨(29, 12578371665920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00074.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21505 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 21505 21508 :=
  block_of_table results 21505 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0508
