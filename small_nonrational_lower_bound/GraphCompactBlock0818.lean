module
prelude
import GraphInputsRow31Part00030Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0818
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 7035962802176), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00030.record000_result⟩)
 (.leaf ⟨(31, 7186826723584), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00030.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 7187363594240), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00030.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 7187371917312), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00030.record003_result⟩)
 (.leaf ⟨(31, 7190987473152), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00030.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25748 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 25748 25753 :=
  block_of_table results 25748 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0818
