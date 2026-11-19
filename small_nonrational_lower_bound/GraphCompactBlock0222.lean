module
prelude
import GraphInputsRow24Part00106Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0222
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 26428349448448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record000_result⟩)
 (.leaf ⟨(24, 26430530453504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 26432644399360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record002_result⟩)
 (.leaf ⟨(24, 26432912802048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 26463748325632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record004_result⟩)
 (.leaf ⟨(24, 26467003089152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 26467007250688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 26475592990976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record007_result⟩)
 (.leaf ⟨(24, 26500242915584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 26500507156736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record009_result⟩)
 (.leaf ⟨(24, 26501635391616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 26502504710400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record011_result⟩)
 (.leaf ⟨(24, 26502675579008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(24, 26503775551744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record013_result⟩)
 (.leaf ⟨(24, 26504658428160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record014_result⟩))
 (.branch 16
 (.leaf ⟨(24, 26512097050880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 26512365486208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record016_result⟩)
 (.leaf ⟨(24, 26512633921536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record017_result⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨(24, 26512638083072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record018_result⟩)
 (.leaf ⟨(24, 26519378362624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record019_result⟩))
 (.branch 21
 (.leaf ⟨(24, 26571425464576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record020_result⟩)
 (.leaf ⟨(24, 26580690698240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(24, 26598272155776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record022_result⟩)
 (.leaf ⟨(24, 26631507820672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record023_result⟩))
 (.branch 25
 (.leaf ⟨(24, 26648747474944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record024_result⟩)
 (.branch 26
 (.leaf ⟨(24, 26648751636480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record025_result⟩)
 (.leaf ⟨(24, 26657052229632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record026_result⟩)))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf ⟨(24, 26701150044288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record027_result⟩)
 (.leaf ⟨(24, 26703230419072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record028_result⟩))
 (.branch 30
 (.leaf ⟨(24, 26704303636608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record029_result⟩)
 (.branch 31
 (.leaf ⟨(24, 26710810566912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record030_result⟩)
 (.leaf ⟨(24, 26712651890944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record031_result⟩))))
 (.branch 34
 (.branch 33
 (.leaf ⟨(24, 26718121263232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record032_result⟩)
 (.leaf ⟨(24, 26718125457408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record033_result⟩))
 (.branch 35
 (.leaf ⟨(24, 26718321524864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record034_result⟩)
 (.branch 36
 (.leaf ⟨(24, 26721241825408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record035_result⟩)
 (.leaf ⟨(24, 26725604950016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00106.record036_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11063 + i))) 0 37 :=
  interval_of_check _ 0 37 (by decide +kernel)

public theorem complete : Block 11063 11100 :=
  block_of_table results 11063 37 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0222
