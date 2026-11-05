module
prelude
import GraphInputsRow24Part00072Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0188
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 23554155364416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 23554157461504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record001_result⟩)
 (.leaf ⟨(24, 23554204909632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 23554272010304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 23556419224128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record004_result⟩)
 (.leaf ⟨(24, 23573491105792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 23573532262656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 23590711853632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record007_result⟩)
 (.leaf ⟨(24, 23643033764096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 23643298005248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 23643302166784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record010_result⟩)
 (.leaf ⟨(24, 23643302232064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(24, 23643304247552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 23643404898560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record013_result⟩)
 (.leaf ⟨(24, 23649743552768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(24, 23649743618048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 23649778143488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record016_result⟩)
 (.leaf ⟨(24, 23658099642624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(24, 23658327277568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 23658329358336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record019_result⟩)
 (.leaf ⟨(24, 23658336624704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(24, 23658370175040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record021_result⟩)
 (.branch 23
 (.leaf ⟨(24, 23659511025680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record022_result⟩)
 (.leaf ⟨(24, 23678448894208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(24, 23678717296896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record024_result⟩)
 (.branch 26
 (.leaf ⟨(24, 23678717362176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record025_result⟩)
 (.leaf ⟨(24, 23678720938240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(24, 23679505465600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record027_result⟩)
 (.branch 29
 (.leaf ⟨(24, 23679773868288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record028_result⟩)
 (.leaf ⟨(24, 23679773933568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(24, 23679903793408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record030_result⟩)
 (.branch 32
 (.leaf ⟨(24, 23683012247808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record031_result⟩)
 (.leaf ⟨(24, 23683012313088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(24, 23683013808384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record033_result⟩)
 (.branch 35
 (.leaf ⟨(24, 23691597988096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record034_result⟩)
 (.leaf ⟨(24, 23691598053376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(24, 23691602214912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record036_result⟩)
 (.branch 38
 (.leaf ⟨(24, 23691723278352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record037_result⟩)
 (.leaf ⟨(24, 23692797018113), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(24, 23696006217984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record039_result⟩)
 (.branch 41
 (.leaf ⟨(24, 23727145255168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record040_result⟩)
 (.leaf ⟨(24, 23728218472704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(24, 23762581913600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record042_result⟩)
 (.branch 44
 (.leaf ⟨(24, 23779650572544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record043_result⟩)
 (.leaf ⟨(24, 23794681389120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record044_result⟩)))
 (.branch 46
 (.leaf ⟨(24, 23794681405440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record045_result⟩)
 (.branch 47
 (.leaf ⟨(24, 23794681909312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record046_result⟩)
 (.leaf ⟨(24, 23794733287440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record047_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10399 + i))) 0 48 :=
  interval_of_check _ 0 48 (by decide +kernel)

public theorem complete : Block 10399 10447 :=
  block_of_table results 10399 48 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0188
