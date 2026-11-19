module
prelude
import GraphInputsRow16Part00028Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0028
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 28
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 27206872990464), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 27208689319936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record001_result⟩)
 (.leaf ⟨(16, 27225031196928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(16, 27225099403264), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record003_result⟩)
 (.leaf ⟨(16, 27261573070848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record004_result⟩))
 (.branch 6
 (.leaf ⟨(16, 27291637784832), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record005_result⟩)
 (.leaf ⟨(16, 27296971948032), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(16, 27356062294272), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record007_result⟩)
 (.branch 9
 (.leaf ⟨(16, 27365491146752), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record008_result⟩)
 (.leaf ⟨(16, 27365557207040), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(16, 27365787312384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record010_result⟩)
 (.leaf ⟨(16, 27387267909888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record011_result⟩))
 (.branch 13
 (.leaf ⟨(16, 27389297959168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record012_result⟩)
 (.leaf ⟨(16, 27389348284672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(16, 27536949002496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record014_result⟩)
 (.branch 16
 (.leaf ⟨(16, 27536951148544), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record015_result⟩)
 (.leaf ⟨(16, 27536957390848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(16, 27569169645568), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record017_result⟩)
 (.leaf ⟨(16, 27601365123072), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record018_result⟩))
 (.branch 20
 (.leaf ⟨(16, 27605034139904), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record019_result⟩)
 (.leaf ⟨(16, 27605042528256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record020_result⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨(16, 27605500723456), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record021_result⟩)
 (.branch 23
 (.leaf ⟨(16, 27613760389120), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record022_result⟩)
 (.leaf ⟨(16, 27632852861184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record023_result⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨(16, 27645737779200), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record024_result⟩)
 (.leaf ⟨(16, 27645801693440), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record025_result⟩))
 (.branch 27
 (.leaf ⟨(16, 27645801758720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record026_result⟩)
 (.leaf ⟨(16, 27645808001024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record027_result⟩))))))
 (.branch 42
 (.branch 35
 (.branch 31
 (.branch 29
 (.leaf ⟨(16, 27646076403712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record028_result⟩)
 (.branch 30
 (.leaf ⟨(16, 27646571855872), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record029_result⟩)
 (.leaf ⟨(16, 27697382195456), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record030_result⟩)))
 (.branch 33
 (.branch 32
 (.leaf ⟨(16, 27699528630528), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record031_result⟩)
 (.leaf ⟨(16, 27712407240960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record032_result⟩))
 (.branch 34
 (.leaf ⟨(16, 27714100150272), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record033_result⟩)
 (.leaf ⟨(16, 27733160657152), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(16, 27774925422592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record035_result⟩)
 (.branch 37
 (.leaf ⟨(16, 27811058499584), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record036_result⟩)
 (.leaf ⟨(16, 28076495388928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record037_result⟩)))
 (.branch 40
 (.branch 39
 (.leaf ⟨(16, 28076759630080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record038_result⟩)
 (.leaf ⟨(16, 28077621084160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record039_result⟩))
 (.branch 41
 (.leaf ⟨(16, 28078763938048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record040_result⟩)
 (.leaf ⟨(16, 28081781768448), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record041_result⟩)))))
 (.branch 49
 (.branch 45
 (.branch 43
 (.leaf ⟨(16, 28110850957568), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record042_result⟩)
 (.branch 44
 (.leaf ⟨(16, 28116242145536), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record043_result⟩)
 (.leaf ⟨(16, 28116506386688), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(16, 28120527732992), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record045_result⟩)
 (.leaf ⟨(16, 28120796135680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record046_result⟩))
 (.branch 48
 (.leaf ⟨(16, 28120807645184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record047_result⟩)
 (.leaf ⟨(16, 28121064603648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record048_result⟩))))
 (.branch 53
 (.branch 51
 (.branch 50
 (.leaf ⟨(16, 28121072926720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record049_result⟩)
 (.leaf ⟨(16, 28144253862144), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record050_result⟩))
 (.branch 52
 (.leaf ⟨(16, 28144262250496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record051_result⟩)
 (.leaf ⟨(16, 28150895509760), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record052_result⟩)))
 (.branch 55
 (.branch 54
 (.leaf ⟨(16, 28152046817280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record053_result⟩)
 (.leaf ⟨(16, 28152575361280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record054_result⟩))
 (.branch 56
 (.leaf ⟨(16, 28152847990784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record055_result⟩)
 (.leaf ⟨(16, 28153112231936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record056_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1620 + i))) 0 57 :=
  interval_of_check _ 0 57 (by decide +kernel)

public theorem complete : Block 1620 1677 :=
  block_of_table results 1620 57 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0028
