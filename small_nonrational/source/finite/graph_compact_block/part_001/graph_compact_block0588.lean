module
prelude
import GraphInputsRow29Part00154Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0588
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 24779012768000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00154.record000_result⟩)
 (.leaf ⟨(29, 24779285495808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00154.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 24779549638656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00154.record002_result⟩)
 (.leaf ⟨(29, 24779557961728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00154.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 24783173517568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00154.record004_result⟩)
 (.leaf ⟨(29, 24783446147072), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00154.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 24783710388224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00154.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 24783718711296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00154.record007_result⟩)
 (.leaf ⟨(29, 24783842508800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00154.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22628 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 22628 22637 :=
  block_of_table results 22628 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0588
