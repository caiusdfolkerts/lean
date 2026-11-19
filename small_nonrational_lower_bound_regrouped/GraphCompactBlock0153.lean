module
prelude
import GraphInputsRow24Part00037Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0153
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 17198328381440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 17198336704512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record001_result⟩)
 (.leaf ⟨(24, 17198468825088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 17198525448960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record003_result⟩)
 (.leaf ⟨(24, 17199232221440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 17202149327376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record005_result⟩)
 (.leaf ⟨(24, 17215441142016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 17219874521088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 17220411326464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record008_result⟩)
 (.leaf ⟨(24, 17224572076032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 17227114021120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record010_result⟩)
 (.leaf ⟨(24, 17227155832832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 17228732825600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record012_result⟩)
 (.leaf ⟨(24, 17232621010944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9397 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 9397 9411 :=
  block_of_table results 9397 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0153
