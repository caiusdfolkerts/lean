module
prelude
import GraphInputsSix0Part00090Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1055
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 34712462690320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 34712479334928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record001_result⟩)
 (.leaf ⟨(32, 34737712824576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 34738790268928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 34739062833152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record004_result⟩)
 (.leaf ⟨(32, 34739574800384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 34746302791680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 34746839597056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record007_result⟩)
 (.leaf ⟨(32, 34746856112128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(32, 34747359363072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record009_result⟩)
 (.leaf ⟨(32, 34763465294340), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record010_result⟩))
 (.branch 12
 (.leaf ⟨(32, 34763465428992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record011_result⟩)
 (.leaf ⟨(32, 34763482595328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(32, 34763515625472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record013_result⟩)
 (.branch 15
 (.leaf ⟨(32, 34764539166720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record014_result⟩)
 (.leaf ⟨(32, 34772072403200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(32, 34875134576896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record016_result⟩)
 (.branch 18
 (.leaf ⟨(32, 34875151548416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record017_result⟩)
 (.leaf ⟨(32, 34875688353792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(32, 34892314445824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record019_result⟩)
 (.branch 21
 (.leaf ⟨(32, 34909494578192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record020_result⟩)
 (.leaf ⟨(32, 35115652745224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(32, 35115669522432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record022_result⟩)
 (.leaf ⟨(32, 35115669782528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record023_result⟩))
 (.branch 25
 (.leaf ⟨(32, 35150012483584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record024_result⟩)
 (.leaf ⟨(32, 35150029389824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090.record025_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (35093 + i))) 0 26 :=
  interval_of_check _ 0 26 (by decide +kernel)

public theorem complete : Block 35093 35119 :=
  block_of_table results 35093 26 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1055
