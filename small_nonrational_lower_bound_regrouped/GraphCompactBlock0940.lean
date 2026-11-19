module
prelude
import GraphInputsRow31Part00152Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0940
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 30864189169696), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00152.record000_result⟩)
 (.leaf ⟨(31, 30864239235104), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00152.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 30864776954112), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00152.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 30865312711200), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00152.record003_result⟩)
 (.leaf ⟨(31, 30865313824768), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00152.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26635 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 26635 26640 :=
  block_of_table results 26635 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0940
