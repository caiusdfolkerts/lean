module
prelude
import GraphInputsRow29Part00287Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0721
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 34644850377216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00287.record000_result⟩)
 (.leaf ⟨(29, 34647535321088), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00287.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 34660386213904), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00287.record002_result⟩)
 (.leaf ⟨(29, 34670188232704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00287.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23528 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 23528 23532 :=
  block_of_table results 23528 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0721
