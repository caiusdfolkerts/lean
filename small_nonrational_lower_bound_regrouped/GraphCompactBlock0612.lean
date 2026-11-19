module
prelude
import GraphInputsRow29Part00178Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0612
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 25993159393536), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00178.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 25993696264192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00178.record001_result⟩)
 (.leaf ⟨(29, 25993813430272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00178.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22817 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 22817 22820 :=
  block_of_table results 22817 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0612
