module
prelude
import GraphInputsRow24Part00034Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0150
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 16777519055104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record000_result⟩)
 (.leaf ⟨(24, 16780840411392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 16785857331328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 16815199617792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record003_result⟩)
 (.leaf ⟨(24, 16846339244032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 16881779998720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 16906151035136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record006_result⟩)
 (.leaf ⟨(24, 16906155261952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 16906161504256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 16906351296768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record009_result⟩)
 (.leaf ⟨(24, 16906353442816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 16906359685120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record011_result⟩)
 (.leaf ⟨(24, 16906411051008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 16910565572608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 16913692362752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record014_result⟩)
 (.leaf ⟨(24, 16914135392320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(24, 16914136449024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 16914151907392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record017_result⟩)
 (.leaf ⟨(24, 16930778390592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(24, 16930812477440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record019_result⟩)
 (.branch 21
 (.leaf ⟨(24, 16930814558208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record020_result⟩)
 (.leaf ⟨(24, 16931902078976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(24, 16931904159744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record022_result⟩)
 (.leaf ⟨(24, 16939502305536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record023_result⟩))
 (.branch 25
 (.leaf ⟨(24, 16939506532352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record024_result⟩)
 (.branch 26
 (.leaf ⟨(24, 16939514595328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record025_result⟩)
 (.leaf ⟨(24, 16939636506880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(24, 16939644895232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record027_result⟩)
 (.branch 29
 (.leaf ⟨(24, 16939646715904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record028_result⟩)
 (.leaf ⟨(24, 16939753933056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(24, 16940156586048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record030_result⟩)
 (.branch 32
 (.leaf ⟨(24, 16943801237504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record031_result⟩)
 (.leaf ⟨(24, 16943914551552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record032_result⟩)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf ⟨(24, 16943922939904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record033_result⟩)
 (.branch 35
 (.leaf ⟨(24, 16943931196160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record034_result⟩)
 (.leaf ⟨(24, 16944451289608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record035_result⟩)))
 (.branch 37
 (.leaf ⟨(24, 16948083689472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record036_result⟩)
 (.branch 38
 (.leaf ⟨(24, 16948477954112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record037_result⟩)
 (.leaf ⟨(24, 16948494598720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record038_result⟩))))
 (.branch 42
 (.branch 40
 (.leaf ⟨(24, 16948612039176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record039_result⟩)
 (.branch 41
 (.leaf ⟨(24, 16969415787012), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record040_result⟩)
 (.leaf ⟨(24, 16969415918592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record041_result⟩)))
 (.branch 43
 (.leaf ⟨(24, 16975877144832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record042_result⟩)
 (.branch 44
 (.leaf ⟨(24, 16976013492224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043_result⟩)
 (.leaf ⟨(24, 16976021815296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record044_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9283 + i))) 0 45 :=
  interval_of_check _ 0 45 (by decide +kernel)

public theorem complete : Block 9283 9328 :=
  block_of_table results 9283 45 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0150
