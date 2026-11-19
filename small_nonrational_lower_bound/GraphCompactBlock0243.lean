module
prelude
import GraphInputsRow24Part00127Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0243
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 31341764681984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 31345229762592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record001_result⟩)
 (.leaf ⟨(24, 31346321793280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 31374069268736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record003_result⟩)
 (.leaf ⟨(24, 31374077657088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 31376149643520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record005_result⟩)
 (.leaf ⟨(24, 31376158031872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 31376616227072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 31376627736576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record008_result⟩)
 (.leaf ⟨(24, 31377701474304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 31380310393088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record010_result⟩)
 (.leaf ⟨(24, 31380318781440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 31380450902016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record012_result⟩)
 (.leaf ⟨(24, 31380508573952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(24, 31380710916352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 31380715143168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record015_result⟩)
 (.leaf ⟨(24, 31380776976640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(24, 31380788486144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record017_result⟩)
 (.leaf ⟨(24, 31381581791488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record018_result⟩))
 (.branch 20
 (.leaf ⟨(24, 31381850194176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record019_result⟩)
 (.leaf ⟨(24, 31381862223872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record020_result⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨(24, 31384131870976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record021_result⟩)
 (.branch 23
 (.leaf ⟨(24, 31389036642304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022_result⟩)
 (.leaf ⟨(24, 31413684936960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record023_result⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨(24, 31413685002240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record024_result⟩)
 (.leaf ⟨(24, 31413949243392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025_result⟩))
 (.branch 27
 (.leaf ⟨(24, 31413957038112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record026_result⟩)
 (.leaf ⟨(24, 31414801203456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record027_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11577 + i))) 0 28 :=
  interval_of_check _ 0 28 (by decide +kernel)

public theorem complete : Block 11577 11605 :=
  block_of_table results 11577 28 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0243
