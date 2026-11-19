module
prelude
import GraphInputsRow29Part00256Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0690
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 32523677663232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00256.record000_result⟩)
 (.leaf ⟨(29, 32524445679616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00256.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 32564442234880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00256.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 32642900754432), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00256.record003_result⟩)
 (.leaf ⟨(29, 32645517934592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00256.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23395 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 23395 23400 :=
  block_of_table results 23395 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0690
