module
prelude
import GraphInputsRow24Part00041Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0157
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 17524272138240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record000_result⟩)
 (.leaf ⟨(24, 17532056635648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 17532593506304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 17532610150912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record003_result⟩)
 (.leaf ⟨(24, 17549236371972), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 17557847343104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005_result⟩)
 (.leaf ⟨(24, 17566441406464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 17566969888768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 17583596240896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record008_result⟩)
 (.leaf ⟨(24, 17583612887040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 17706415915264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record010_result⟩)
 (.leaf ⟨(24, 17706617225344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 17748219478336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 17748220518720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record013_result⟩)
 (.leaf ⟨(24, 17775135375616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(24, 17777551310880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 17783721115904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record016_result⟩)
 (.leaf ⟨(24, 17783725326400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(24, 17786737819904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 17787778007296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record019_result⟩)
 (.leaf ⟨(24, 17839761162496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record020_result⟩))))))
 (.branch 31
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf ⟨(24, 17856395903232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record021_result⟩)
 (.leaf ⟨(24, 17856395968512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_result⟩))
 (.branch 24
 (.leaf ⟨(24, 17856532119808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record023_result⟩)
 (.branch 25
 (.leaf ⟨(24, 17856941031424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_result⟩)
 (.leaf ⟨(24, 17857068990464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_result⟩))))
 (.branch 28
 (.branch 27
 (.leaf ⟨(24, 17857077313536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record026_result⟩)
 (.leaf ⟨(24, 17976931680512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record027_result⟩))
 (.branch 29
 (.leaf ⟨(24, 17977200115840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record028_result⟩)
 (.branch 30
 (.leaf ⟨(24, 17993971040512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record029_result⟩)
 (.leaf ⟨(24, 17993979428864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record030_result⟩)))))
 (.branch 36
 (.branch 33
 (.branch 32
 (.leaf ⟨(24, 17994103161088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record031_result⟩)
 (.leaf ⟨(24, 17994107387904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_result⟩))
 (.branch 34
 (.leaf ⟨(24, 17994111549440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record033_result⟩)
 (.branch 35
 (.leaf ⟨(24, 17994371596416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record034_result⟩)
 (.leaf ⟨(24, 17994571858048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_result⟩))))
 (.branch 39
 (.branch 37
 (.leaf ⟨(24, 17998272299008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record036_result⟩)
 (.branch 38
 (.leaf ⟨(24, 18045516939520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record037_result⟩)
 (.leaf ⟨(24, 18186579820672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(24, 18194967380096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record039_result⟩)
 (.branch 41
 (.leaf ⟨(24, 18263889182848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record040_result⟩)
 (.leaf ⟨(24, 18266097484032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record041_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9448 + i))) 0 42 :=
  interval_of_check _ 0 42 (by decide +kernel)

public theorem complete : Block 9448 9490 :=
  block_of_table results 9448 42 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0157
