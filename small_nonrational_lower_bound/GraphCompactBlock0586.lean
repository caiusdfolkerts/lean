module
prelude
import GraphInputsRow29Part00152Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0586
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 24681635643392), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00152.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 24740171907328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00152.record001_result⟩)
 (.leaf ⟨(29, 24740171972608), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00152.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 24741314891776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00152.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 24741322690576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00152.record004_result⟩)
 (.leaf ⟨(29, 24741339465744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00152.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22613 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 22613 22619 :=
  block_of_table results 22613 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0586
