module
prelude
import GraphInputsRow24Part00050Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0166
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 19612768927744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 19619570286848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record001_result⟩)
 (.leaf ⟨(24, 19619974744192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 19623995048192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 19624003436544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record004_result⟩)
 (.leaf ⟨(24, 19624523466752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 19628287918336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 19628296306688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record007_result⟩)
 (.leaf ⟨(24, 19628403523840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 19628556321024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 19628560547840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record010_result⟩)
 (.leaf ⟨(24, 19628566790144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(24, 19628671926528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 19628684216320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record013_result⟩)
 (.leaf ⟨(24, 19628806127872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(24, 19632970858496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 19636733216896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record016_result⟩)
 (.leaf ⟨(24, 19645985718848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(24, 19646004592640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 19649744011264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record019_result⟩)
 (.leaf ⟨(24, 19649752334336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(24, 19650280686080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record021_result⟩)
 (.leaf ⟨(24, 19657404776448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record022_result⟩))
 (.branch 24
 (.leaf ⟨(24, 19657664790784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record023_result⟩)
 (.leaf ⟨(24, 19657675259904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00050.record024_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9739 + i))) 0 25 :=
  interval_of_check _ 0 25 (by decide +kernel)

public theorem complete : Block 9739 9764 :=
  block_of_table results 9739 25 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0166
