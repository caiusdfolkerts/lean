module
prelude
import GraphInputsRow16Part00012Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0012
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 16688275783680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record000_result⟩)
 (.leaf ⟨(16, 16700067119104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 16700070174976), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record002_result⟩)
 (.leaf ⟨(16, 16700195012864), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(16, 16702660182272), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record004_result⟩)
 (.leaf ⟨(16, 16703421948160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record005_result⟩))
 (.branch 7
 (.leaf ⟨(16, 16703710824480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record006_result⟩)
 (.branch 8
 (.leaf ⟨(16, 16711769194752), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record007_result⟩)
 (.leaf ⟨(16, 16711777583104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(16, 16712280317952), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record009_result⟩)
 (.leaf ⟨(16, 16720359096576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record010_result⟩))
 (.branch 12
 (.leaf ⟨(16, 16720363323392), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record011_result⟩)
 (.branch 13
 (.leaf ⟨(16, 16720370606080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record012_result⟩)
 (.leaf ⟨(16, 16720601817088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(16, 16721452924928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record014_result⟩)
 (.leaf ⟨(16, 16721461117952), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record015_result⟩))
 (.branch 17
 (.leaf ⟨(16, 16721658388480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record016_result⟩)
 (.branch 18
 (.leaf ⟨(16, 16728939700224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record017_result⟩)
 (.leaf ⟨(16, 16735495323904), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record018_result⟩))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf ⟨(16, 16735503712256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record019_result⟩)
 (.leaf ⟨(16, 16735743049984), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record020_result⟩))
 (.branch 22
 (.leaf ⟨(16, 16735895847168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record021_result⟩)
 (.branch 23
 (.leaf ⟨(16, 16735900073984), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record022_result⟩)
 (.leaf ⟨(16, 16736011452672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record023_result⟩))))
 (.branch 26
 (.branch 25
 (.leaf ⟨(16, 16736023742464), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record024_result⟩)
 (.leaf ⟨(16, 16748225167616), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record025_result⟩))
 (.branch 27
 (.leaf ⟨(16, 16748762038272), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record026_result⟩)
 (.branch 28
 (.leaf ⟨(16, 16748770361344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record027_result⟩)
 (.leaf ⟨(16, 16750718486528), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record028_result⟩)))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf ⟨(16, 16751515435264), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record029_result⟩)
 (.leaf ⟨(16, 16757083537408), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record030_result⟩))
 (.branch 32
 (.leaf ⟨(16, 16757091860480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record031_result⟩)
 (.branch 33
 (.leaf ⟨(16, 16773229322496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record032_result⟩)
 (.leaf ⟨(16, 16781823451136), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033_result⟩))))
 (.branch 36
 (.branch 35
 (.leaf ⟨(16, 16781948289024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record034_result⟩)
 (.leaf ⟨(16, 16781956612096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record035_result⟩))
 (.branch 37
 (.leaf ⟨(16, 16805542297600), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record036_result⟩)
 (.branch 38
 (.leaf ⟨(16, 16807622672384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record037_result⟩)
 (.leaf ⟨(16, 16817347690496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record038_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (854 + i))) 0 39 :=
  interval_of_check _ 0 39 (by decide +kernel)

public theorem complete : Block 854 893 :=
  block_of_table results 854 39 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0012
