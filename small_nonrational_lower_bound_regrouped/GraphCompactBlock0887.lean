module
prelude
import GraphInputsRow31Part00099Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0887
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 21805549125632), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00099.record000_result⟩)
 (.leaf ⟨(31, 21857227046912), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00099.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 21878699720704), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00099.record002_result⟩)
 (.leaf ⟨(31, 21926084870144), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00099.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 21934934851584), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00099.record004_result⟩)
 (.leaf ⟨(31, 21947417100288), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00099.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 21993567043840), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00099.record006_result⟩)
 (.leaf ⟨(31, 21993765224704), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00099.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26331 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 26331 26339 :=
  block_of_table results 26331 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0887
