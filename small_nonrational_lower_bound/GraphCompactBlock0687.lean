module
prelude
import GraphInputsRow29Part00253Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0687
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 32488617410560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00253.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 32491465408512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00253.record001_result⟩)
 (.leaf ⟨(29, 32492233424896), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00253.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23385 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 23385 23388 :=
  block_of_table results 23385 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0687
