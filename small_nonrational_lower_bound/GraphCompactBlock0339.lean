module
prelude
import GraphInputsRow26Part00023Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0339
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 15075369877760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 15077021319168), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record001_result⟩)
 (.leaf ⟨(26, 15101671243776), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 15138027474944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 15166334829312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record004_result⟩)
 (.leaf ⟨(26, 15191035150336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 15191043473408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 15197284597760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record007_result⟩)
 (.leaf ⟨(26, 15197474455552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(26, 15213580001280), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record009_result⟩)
 (.branch 11
 (.leaf ⟨(26, 15213919272960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record010_result⟩)
 (.leaf ⟨(26, 15214191837184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(26, 15214654259200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 15214720319488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record013_result⟩)
 (.leaf ⟨(26, 15230520262656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(26, 15230759665664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 15247955984384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record016_result⟩)
 (.leaf ⟨(26, 15259083538688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(26, 15259356168192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record018_result⟩)
 (.branch 20
 (.leaf ⟨(26, 15259620409344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record019_result⟩)
 (.leaf ⟨(26, 15259628732416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(26, 15261700784128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record021_result⟩)
 (.branch 23
 (.leaf ⟨(26, 15262740971520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record022_result⟩)
 (.leaf ⟨(26, 15262749294592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(26, 15266001977344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record024_result⟩)
 (.branch 26
 (.leaf ⟨(26, 15266059714560), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record025_result⟩)
 (.leaf ⟨(26, 15267042164736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(26, 15274046685440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record027_result⟩)
 (.branch 29
 (.leaf ⟨(26, 15274381213696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record028_result⟩)
 (.leaf ⟨(26, 15274587717632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(26, 15277233307904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 15278004510720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record031_result⟩)
 (.leaf ⟨(26, 15285823275008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(26, 15285897658368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record033_result⟩)
 (.branch 35
 (.leaf ⟨(26, 15286360080384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record034_result⟩)
 (.leaf ⟨(26, 15294936449024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(26, 15294944772096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record036_result⟩)
 (.branch 38
 (.leaf ⟨(26, 15299237642240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record037_result⟩)
 (.leaf ⟨(26, 15307666423808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(26, 15307823382528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record039_result⟩)
 (.branch 41
 (.leaf ⟨(26, 15309549404160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record040_result⟩)
 (.leaf ⟨(26, 15320685346816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(26, 15326611833088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record042_result⟩)
 (.branch 44
 (.leaf ⟨(26, 15327148703744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record043_result⟩)
 (.leaf ⟨(26, 15327157026816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(26, 15327396429824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record045_result⟩)
 (.leaf ⟨(26, 15333051138304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record046_result⟩))
 (.branch 48
 (.leaf ⟨(26, 15333588008960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record047_result⟩)
 (.leaf ⟨(26, 15333596332032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00023.record048_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (15277 + i))) 0 49 :=
  interval_of_check _ 0 49 (by decide +kernel)

public theorem complete : Block 15277 15326 :=
  block_of_table results 15277 49 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0339
