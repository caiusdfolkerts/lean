module
prelude
import GraphInputsRow16Part00014Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0014
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 17154904953088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 17171296583936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record001_result⟩)
 (.leaf ⟨(16, 17171333840896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(16, 17171342163968), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record003_result⟩)
 (.leaf ⟨(16, 17171565051904), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record004_result⟩))
 (.branch 6
 (.leaf ⟨(16, 17171573374976), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record005_result⟩)
 (.leaf ⟨(16, 17172084822016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(16, 17172101857280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record007_result⟩)
 (.leaf ⟨(16, 17172621623296), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record008_result⟩))
 (.branch 10
 (.leaf ⟨(16, 17172629946368), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record009_result⟩)
 (.leaf ⟨(16, 17182180249856), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(16, 17183662964992), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record011_result⟩)
 (.leaf ⟨(16, 17183667191808), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record012_result⟩))
 (.branch 14
 (.leaf ⟨(16, 17187960061952), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record013_result⟩)
 (.leaf ⟨(16, 17187968385024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record014_result⟩)))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨(16, 17188232626176), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record015_result⟩)
 (.branch 17
 (.leaf ⟨(16, 17189021704192), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record016_result⟩)
 (.leaf ⟨(16, 17190106497024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record017_result⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨(16, 17192393375744), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018_result⟩)
 (.leaf ⟨(16, 17195472584704), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record019_result⟩))
 (.branch 21
 (.leaf ⟨(16, 17195480907776), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record020_result⟩)
 (.leaf ⟨(16, 17198324678912), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record021_result⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨(16, 17198336708608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record022_result⟩)
 (.leaf ⟨(16, 17198468829184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record023_result⟩))
 (.branch 25
 (.leaf ⟨(16, 17200305963264), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record024_result⟩)
 (.leaf ⟨(16, 17200442310656), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record025_result⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨(16, 17200450633728), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026_result⟩)
 (.leaf ⟨(16, 17200582754304), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record027_result⟩))
 (.branch 29
 (.leaf ⟨(16, 17200673521664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record028_result⟩)
 (.leaf ⟨(16, 17201210327040), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (950 + i))) 0 30 :=
  interval_of_check _ 0 30 (by decide +kernel)

public theorem complete : Block 950 980 :=
  block_of_table results 950 30 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0014
