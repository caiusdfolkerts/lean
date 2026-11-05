module
prelude
import GraphInputsRow29Part00109Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0543
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 18543793995776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00109.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 18544330801152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00109.record001_result⟩)
 (.leaf ⟨(29, 18545738023168), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00109.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 18548491550720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00109.record003_result⟩)
 (.leaf ⟨(29, 18593115046144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00109.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 18595736256512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00109.record005_result⟩)
 (.leaf ⟨(29, 18731637965056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00109.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(29, 18778875265280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00109.record007_result⟩)
 (.leaf ⟨(29, 18779352342656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00109.record008_result⟩))
 (.branch 10
 (.leaf ⟨(29, 18779488657472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00109.record009_result⟩)
 (.leaf ⟨(29, 18801894686976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00109.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(29, 18814785847296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00109.record011_result⟩)
 (.leaf ⟨(29, 18817531052032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00109.record012_result⟩))
 (.branch 14
 (.leaf ⟨(29, 18839414784256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00109.record013_result⟩)
 (.leaf ⟨(29, 18839414849536), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00109.record014_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22082 + i))) 0 15 :=
  interval_of_check _ 0 15 (by decide +kernel)

public theorem complete : Block 22082 22097 :=
  block_of_table results 22082 15 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0543
