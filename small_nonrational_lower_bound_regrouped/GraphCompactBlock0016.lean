module
prelude
import GraphInputsRow16Part00016Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0016
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 17329563893760), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 17332643102720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record001_result⟩)
 (.leaf ⟨(16, 17353033187328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(16, 17356252839936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record003_result⟩)
 (.leaf ⟨(16, 17360545710080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record004_result⟩))
 (.branch 6
 (.leaf ⟨(16, 17364838580224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record005_result⟩)
 (.leaf ⟨(16, 17364846903296), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(16, 17455906849024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record007_result⟩)
 (.branch 9
 (.leaf ⟨(16, 17455911075840), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008_result⟩)
 (.leaf ⟨(16, 17456109256704), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(16, 17456166864896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record010_result⟩)
 (.leaf ⟨(16, 17457046126848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record011_result⟩))
 (.branch 13
 (.leaf ⟨(16, 17457050353664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record012_result⟩)
 (.leaf ⟨(16, 17457058156544), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(16, 17457182474240), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record014_result⟩)
 (.branch 16
 (.leaf ⟨(16, 17457190277120), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record015_result⟩)
 (.leaf ⟨(16, 17457207052288), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(16, 17457297494272), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record017_result⟩)
 (.leaf ⟨(16, 17461475344384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record018_result⟩))
 (.branch 20
 (.leaf ⟨(16, 17462012149760), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record019_result⟩)
 (.leaf ⟨(16, 17463448176640), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record020_result⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨(16, 17463538618624), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record021_result⟩)
 (.branch 23
 (.leaf ⟨(16, 17463893823488), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record022_result⟩)
 (.leaf ⟨(16, 17463910598656), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record023_result⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨(16, 17466172899328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record024_result⟩)
 (.leaf ⟨(16, 17469813227520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record025_result⟩))
 (.branch 27
 (.leaf ⟨(16, 17469821550592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record026_result⟩)
 (.leaf ⟨(16, 17470316482560), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record027_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1028 + i))) 0 28 :=
  interval_of_check _ 0 28 (by decide +kernel)

public theorem complete : Block 1028 1056 :=
  block_of_table results 1028 28 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0016
