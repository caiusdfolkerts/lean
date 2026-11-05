module
prelude
import GraphInputsRow26Part00027Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0343
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 17199232221440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 17202149327376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record001_result⟩)
 (.leaf ⟨(26, 17215441142016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 17219874521088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 17220411326464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record004_result⟩)
 (.leaf ⟨(26, 17224572076032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 17227155832832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 17228732825600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record007_result⟩)
 (.leaf ⟨(26, 17232621010944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(26, 17232893575168), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record009_result⟩)
 (.branch 11
 (.leaf ⟨(26, 17235741573120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record010_result⟩)
 (.leaf ⟨(26, 17236509589504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(26, 17237054324736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 17244335636480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record013_result⟩)
 (.leaf ⟨(26, 17292100370432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(26, 17300149305344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 17300933836800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record016_result⟩)
 (.leaf ⟨(26, 17317329307664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(26, 17328448798720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record018_result⟩)
 (.branch 20
 (.leaf ⟨(26, 17361742594048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record019_result⟩)
 (.leaf ⟨(26, 17429270888448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(26, 17455890071808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record021_result⟩)
 (.branch 23
 (.leaf ⟨(26, 17458106793984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record022_result⟩)
 (.leaf ⟨(26, 17458379358208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record023_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (15496 + i))) 0 24 :=
  interval_of_check _ 0 24 (by decide +kernel)

public theorem complete : Block 15496 15520 :=
  block_of_table results 15496 24 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0343
