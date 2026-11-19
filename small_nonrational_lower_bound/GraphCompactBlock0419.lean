module
prelude
import GraphInputsRow27Part00016Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0419
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(27, 34675150029312), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record000_result⟩)
 (.branch 2
 (.leaf ⟨(27, 34675150553088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record001_result⟩)
 (.leaf ⟨(27, 34681861050624), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(27, 34681895059456), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record003_result⟩)
 (.leaf ⟨(27, 34682976600064), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record004_result⟩))
 (.branch 6
 (.leaf ⟨(27, 34699074863104), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record005_result⟩)
 (.leaf ⟨(27, 34703629619200), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(27, 34712462690320), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record007_result⟩)
 (.leaf ⟨(27, 34712479334928), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record008_result⟩))
 (.branch 10
 (.leaf ⟨(27, 34737712824576), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record009_result⟩)
 (.leaf ⟨(27, 34738790268928), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(27, 34739062833152), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record011_result⟩)
 (.leaf ⟨(27, 34739574800384), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record012_result⟩))
 (.branch 14
 (.leaf ⟨(27, 34746302791680), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record013_result⟩)
 (.leaf ⟨(27, 34746839597056), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record014_result⟩)))))
 (.branch 23
 (.branch 19
 (.branch 17
 (.branch 16
 (.leaf ⟨(27, 34746856112128), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record015_result⟩)
 (.leaf ⟨(27, 34747359363072), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record016_result⟩))
 (.branch 18
 (.leaf ⟨(27, 34763465294340), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record017_result⟩)
 (.leaf ⟨(27, 34763465428992), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record018_result⟩)))
 (.branch 21
 (.branch 20
 (.leaf ⟨(27, 34763482595328), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record019_result⟩)
 (.leaf ⟨(27, 34763515625472), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record020_result⟩))
 (.branch 22
 (.leaf ⟨(27, 34764539166720), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record021_result⟩)
 (.leaf ⟨(27, 34875134576896), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record022_result⟩))))
 (.branch 27
 (.branch 25
 (.branch 24
 (.leaf ⟨(27, 34875151548416), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record023_result⟩)
 (.leaf ⟨(27, 34875688353792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record024_result⟩))
 (.branch 26
 (.leaf ⟨(27, 34892314445824), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record025_result⟩)
 (.leaf ⟨(27, 35115652745224), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record026_result⟩)))
 (.branch 29
 (.branch 28
 (.leaf ⟨(27, 35115669522432), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record027_result⟩)
 (.leaf ⟨(27, 35115669782528), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record028_result⟩))
 (.branch 30
 (.leaf ⟨(27, 35150012483584), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record029_result⟩)
 (.leaf ⟨(27, 35150029389824), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record030_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (19273 + i))) 0 31 :=
  interval_of_check _ 0 31 (by decide +kernel)

public theorem complete : Block 19273 19304 :=
  block_of_table results 19273 31 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0419
