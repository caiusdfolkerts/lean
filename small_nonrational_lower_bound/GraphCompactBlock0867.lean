module
prelude
import GraphInputsRow31Part00079Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0867
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 15540936507936), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00079.record000_result⟩)
 (.leaf ⟨(31, 15548924592384), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00079.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 15549259120640), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00079.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 15549527523328), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00079.record003_result⟩)
 (.leaf ⟨(31, 15584427311104), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00079.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26103 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 26103 26108 :=
  block_of_table results 26103 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0867
