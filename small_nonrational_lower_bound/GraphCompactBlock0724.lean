module
prelude
import GraphInputsRow29Part00290Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0724
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 34712479858688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00290.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 34712999624704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00290.record001_result⟩)
 (.leaf ⟨(29, 34729105690624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00290.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23537 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 23537 23540 :=
  block_of_table results 23537 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0724
