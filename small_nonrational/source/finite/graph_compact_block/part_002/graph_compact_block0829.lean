module
prelude
import GraphInputsRow31Part00041Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0829
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 8252511813632), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00041.record000_result⟩)
 (.leaf ⟨(31, 8259256254720), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00041.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 8264626503936), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00041.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 8264994062336), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00041.record003_result⟩)
 (.leaf ⟨(31, 8265167536128), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00041.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25815 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 25815 25820 :=
  block_of_table results 25815 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0829
