module
prelude
import GraphInputsRow24Part00061Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0177
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 22396981477376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_result⟩)
 (.leaf ⟨(24, 22443689312512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 22443957715200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record002_result⟩)
 (.leaf ⟨(24, 22443968184320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 22448252666112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record004_result⟩)
 (.leaf ⟨(24, 22448261054464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 22456846794752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 22457042878528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record007_result⟩)
 (.leaf ⟨(24, 22464895664384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 22465029931008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record009_result⟩)
 (.leaf ⟨(24, 22465038254080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 22465498595328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record011_result⟩)
 (.branch 13
 (.leaf ⟨(24, 22482619744256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record012_result⟩)
 (.leaf ⟨(24, 22550233055264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(24, 22584628363520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record014_result⟩)
 (.leaf ⟨(24, 22594493354048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record015_result⟩))
 (.branch 17
 (.leaf ⟨(24, 22617591980288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 22617856221440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record017_result⟩)
 (.leaf ⟨(24, 22617860440096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record018_result⟩))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf ⟨(24, 22618986021120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record019_result⟩)
 (.leaf ⟨(24, 22626446123264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record020_result⟩))
 (.branch 22
 (.leaf ⟨(24, 22686579892288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record021_result⟩)
 (.branch 23
 (.leaf ⟨(24, 22686579900448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record022_result⟩)
 (.leaf ⟨(24, 22687704432896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record023_result⟩))))
 (.branch 26
 (.branch 25
 (.leaf ⟨(24, 22697371242560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record024_result⟩)
 (.leaf ⟨(24, 22722056880384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record025_result⟩))
 (.branch 27
 (.leaf ⟨(24, 22730646782208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record026_result⟩)
 (.branch 28
 (.leaf ⟨(24, 22730657251328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record027_result⟩)
 (.leaf ⟨(24, 22732326633728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record028_result⟩)))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf ⟨(24, 22732599263232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record029_result⟩)
 (.leaf ⟨(24, 22732863504384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record030_result⟩))
 (.branch 32
 (.leaf ⟨(24, 22732871827456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record031_result⟩)
 (.branch 33
 (.leaf ⟨(24, 22732995624960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record032_result⟩)
 (.leaf ⟨(24, 22739236749312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record033_result⟩))))
 (.branch 36
 (.branch 35
 (.leaf ⟨(24, 22800509239296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record034_result⟩)
 (.leaf ⟨(24, 22804405747712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record035_result⟩))
 (.branch 37
 (.leaf ⟨(24, 22804942553088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036_result⟩)
 (.branch 38
 (.leaf ⟨(24, 22835378552832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_result⟩)
 (.leaf ⟨(24, 22850394161408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record038_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10130 + i))) 0 39 :=
  interval_of_check _ 0 39 (by decide +kernel)

public theorem complete : Block 10130 10169 :=
  block_of_table results 10130 39 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0177
