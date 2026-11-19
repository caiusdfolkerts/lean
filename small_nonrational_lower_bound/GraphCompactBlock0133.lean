module
prelude
import GraphInputsRow24Part00017Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0133
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 10379351572608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record000_result⟩)
 (.leaf ⟨(24, 10490067648512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 10493422997760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 10562142535680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record003_result⟩)
 (.leaf ⟨(24, 10602944663616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 10708171358208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record005_result⟩)
 (.leaf ⟨(24, 10716757098496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 10741480456192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 10741484617728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record008_result⟩)
 (.leaf ⟨(24, 10747184709888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 10781576036608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record010_result⟩)
 (.leaf ⟨(24, 10781580263424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 10781584424960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 10781588456448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record013_result⟩)
 (.leaf ⟨(24, 10781720577024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(24, 10781844308736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record015_result⟩)
 (.leaf ⟨(24, 10781978673280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record016_result⟩))
 (.branch 18
 (.leaf ⟨(24, 10781984818176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record017_result⟩)
 (.branch 19
 (.leaf ⟨(24, 10782112744064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record018_result⟩)
 (.leaf ⟨(24, 10859314167936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(24, 10860387385472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record020_result⟩)
 (.leaf ⟨(24, 10861313851392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record021_result⟩))
 (.branch 23
 (.leaf ⟨(24, 10875412430976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record022_result⟩)
 (.branch 24
 (.leaf ⟨(24, 10884858576896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record023_result⟩)
 (.leaf ⟨(24, 10884866899968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(24, 10892192579840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record025_result⟩)
 (.leaf ⟨(24, 10892196741376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record026_result⟩))
 (.branch 28
 (.leaf ⟨(24, 10892196806656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record027_result⟩)
 (.branch 29
 (.leaf ⟨(24, 10892200642816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record028_result⟩)
 (.leaf ⟨(24, 10892331008000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(24, 10892597004544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record030_result⟩)
 (.leaf ⟨(24, 10892599378048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record031_result⟩))
 (.branch 33
 (.leaf ⟨(24, 10892599410688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record032_result⟩)
 (.branch 34
 (.leaf ⟨(24, 10896608987392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record033_result⟩)
 (.leaf ⟨(24, 10896609052672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record034_result⟩))))
 (.branch 37
 (.branch 36
 (.leaf ⟨(24, 10896625697280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record035_result⟩)
 (.leaf ⟨(24, 10896629891072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record036_result⟩))
 (.branch 38
 (.leaf ⟨(24, 10896881484808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_result⟩)
 (.branch 39
 (.leaf ⟨(24, 10896898260993), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record038_result⟩)
 (.leaf ⟨(24, 10901310670848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record039_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8653 + i))) 0 40 :=
  interval_of_check _ 0 40 (by decide +kernel)

public theorem complete : Block 8653 8693 :=
  block_of_table results 8653 40 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0133
