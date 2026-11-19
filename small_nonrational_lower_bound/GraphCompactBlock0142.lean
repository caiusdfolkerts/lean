module
prelude
import GraphInputsRow24Part00026Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0142
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 14794418618368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record000_result⟩)
 (.leaf ⟨(24, 14794625122304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 14805357297664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 14883944988928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record003_result⟩)
 (.leaf ⟨(24, 14883953377280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 14888114126848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 14891457511680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record006_result⟩)
 (.leaf ⟨(24, 14896435625984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 14896827760896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 14900047413504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record009_result⟩)
 (.leaf ⟨(24, 14900059443200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 14922406756352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record011_result⟩)
 (.leaf ⟨(24, 14922596548864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 14930728255488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 14931197960192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record014_result⟩)
 (.leaf ⟨(24, 14932259668224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(24, 14932271697920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 14938702094592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record017_result⟩)
 (.leaf ⟨(24, 14973061300992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(24, 14988094275840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record019_result⟩)
 (.branch 21
 (.leaf ⟨(24, 14999313514496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record020_result⟩)
 (.leaf ⟨(24, 14999783219200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(24, 15000856956928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record022_result⟩)
 (.leaf ⟨(24, 15003126604032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record023_result⟩))
 (.branch 25
 (.leaf ⟨(24, 15068435578880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record024_result⟩)
 (.branch 26
 (.leaf ⟨(24, 15068625436672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record025_result⟩)
 (.leaf ⟨(24, 15075369877760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(24, 15076484513792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record027_result⟩)
 (.branch 29
 (.leaf ⟨(24, 15077021319168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record028_result⟩)
 (.leaf ⟨(24, 15101671243776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(24, 15101910646784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record030_result⟩)
 (.branch 32
 (.leaf ⟨(24, 15125545226240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record031_result⟩)
 (.leaf ⟨(24, 15129705975808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record032_result⟩)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf ⟨(24, 15136953737216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record033_result⟩)
 (.branch 35
 (.leaf ⟨(24, 15138027474944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record034_result⟩)
 (.leaf ⟨(24, 15166334829312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record035_result⟩)))
 (.branch 37
 (.leaf ⟨(24, 15191035150336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record036_result⟩)
 (.branch 38
 (.leaf ⟨(24, 15191043473408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record037_result⟩)
 (.leaf ⟨(24, 15197284597760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record038_result⟩))))
 (.branch 42
 (.branch 40
 (.leaf ⟨(24, 15197474455552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record039_result⟩)
 (.branch 41
 (.leaf ⟨(24, 15212808798464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record040_result⟩)
 (.leaf ⟨(24, 15213579469344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record041_result⟩)))
 (.branch 43
 (.leaf ⟨(24, 15213580001280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record042_result⟩)
 (.branch 44
 (.leaf ⟨(24, 15213919272960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record043_result⟩)
 (.leaf ⟨(24, 15214191837184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9044 + i))) 0 45 :=
  interval_of_check _ 0 45 (by decide +kernel)

public theorem complete : Block 9044 9089 :=
  block_of_table results 9044 45 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0142
