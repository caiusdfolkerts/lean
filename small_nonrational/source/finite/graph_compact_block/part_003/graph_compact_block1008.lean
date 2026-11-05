module
prelude
import GraphInputsSix0Part00043Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1008
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(32, 17179894548496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record000_result⟩)
 (.leaf ⟨(32, 17180163051776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record001_result⟩))
 (.branch 3
 (.leaf ⟨(32, 17184449954048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record002_result⟩)
 (.leaf ⟨(32, 17184718356736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(32, 17184730386432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record004_result⟩)
 (.leaf ⟨(32, 17186349449472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record005_result⟩))
 (.branch 7
 (.leaf ⟨(32, 17187117531136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record006_result⟩)
 (.leaf ⟨(32, 17189004511248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(32, 17189021679617), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record008_result⟩)
 (.leaf ⟨(32, 17189023256576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record009_result⟩))
 (.branch 11
 (.leaf ⟨(32, 17189130473728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record010_result⟩)
 (.leaf ⟨(32, 17189742641152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(32, 17190078251009), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record012_result⟩)
 (.leaf ⟨(32, 17190147325952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record013_result⟩))
 (.branch 15
 (.leaf ⟨(32, 17190203949824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record014_result⟩)
 (.leaf ⟨(32, 17191278280704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(32, 17197326010384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record016_result⟩)
 (.leaf ⟨(32, 17197451972864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record017_result⟩))
 (.branch 19
 (.leaf ⟨(32, 17198192034048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record018_result⟩)
 (.leaf ⟨(32, 17198328381440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(32, 17198336704512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record020_result⟩)
 (.leaf ⟨(32, 17198468825088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record021_result⟩))
 (.branch 23
 (.leaf ⟨(32, 17198525448960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record022_result⟩)
 (.leaf ⟨(32, 17199232221440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(32, 17202149327376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record024_result⟩)
 (.leaf ⟨(32, 17215441142016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record025_result⟩))
 (.branch 27
 (.leaf ⟨(32, 17219874521088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record026_result⟩)
 (.leaf ⟨(32, 17220411326464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(32, 17224572076032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record028_result⟩)
 (.leaf ⟨(32, 17227114021120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record029_result⟩))
 (.branch 31
 (.leaf ⟨(32, 17227155832832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record030_result⟩)
 (.leaf ⟨(32, 17228732825600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record031_result⟩))))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf ⟨(32, 17232621010944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record032_result⟩)
 (.leaf ⟨(32, 17232893575168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record033_result⟩))
 (.branch 35
 (.leaf ⟨(32, 17235703922944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record034_result⟩)
 (.leaf ⟨(32, 17235741573120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record035_result⟩)))
 (.branch 38
 (.branch 37
 (.leaf ⟨(32, 17236509065728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record036_result⟩)
 (.leaf ⟨(32, 17236509589504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record037_result⟩))
 (.branch 39
 (.leaf ⟨(32, 17237054324736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record038_result⟩)
 (.leaf ⟨(32, 17237582807040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record039_result⟩))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf ⟨(32, 17244335636480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record040_result⟩)
 (.leaf ⟨(32, 17244864118784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record041_result⟩))
 (.branch 43
 (.leaf ⟨(32, 17282969436416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record042_result⟩)
 (.leaf ⟨(32, 17291563565056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record043_result⟩)))
 (.branch 46
 (.branch 45
 (.leaf ⟨(32, 17292100370432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record044_result⟩)
 (.leaf ⟨(32, 17300149305344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record045_result⟩))
 (.branch 47
 (.leaf ⟨(32, 17300933836800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record046_result⟩)
 (.leaf ⟨(32, 17308718399488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record047_result⟩)))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf ⟨(32, 17317325406224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record048_result⟩)
 (.leaf ⟨(32, 17317329307664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record049_result⟩))
 (.branch 51
 (.leaf ⟨(32, 17317597810944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record050_result⟩)
 (.leaf ⟨(32, 17326193774592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record051_result⟩)))
 (.branch 54
 (.branch 53
 (.leaf ⟨(32, 17328448798720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record052_result⟩)
 (.leaf ⟨(32, 17361742594048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record053_result⟩))
 (.branch 55
 (.leaf ⟨(32, 17429270888448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record054_result⟩)
 (.leaf ⟨(32, 17455890071808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record055_result⟩))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf ⟨(32, 17458106793984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record056_result⟩)
 (.leaf ⟨(32, 17458379358208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record057_result⟩))
 (.branch 59
 (.leaf ⟨(32, 17461227356160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record058_result⟩)
 (.leaf ⟨(32, 17461995372544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record059_result⟩)))
 (.branch 62
 (.branch 61
 (.leaf ⟨(32, 17464620482560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record060_result⟩)
 (.leaf ⟨(32, 17466156122112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record061_result⟩))
 (.branch 63
 (.leaf ⟨(32, 17469821419520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record062_result⟩)
 (.leaf ⟨(32, 17470349901824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00043.record063_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (31086 + i))) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

public theorem complete : Block 31086 31150 :=
  block_of_table results 31086 64 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1008
