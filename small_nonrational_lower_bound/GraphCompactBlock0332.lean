module
prelude
import GraphInputsRow26Part00016Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0332
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 33
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 10741480456192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record000_result⟩)
 (.leaf ⟨(26, 10741484617728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 10747184709888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record002_result⟩)
 (.leaf ⟨(26, 10781576036608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 10781580263424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record004_result⟩)
 (.leaf ⟨(26, 10781584424960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 10781588456448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record006_result⟩)
 (.leaf ⟨(26, 10781720577024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(26, 10781844308736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record008_result⟩)
 (.leaf ⟨(26, 10781978673280), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record009_result⟩))
 (.branch 11
 (.leaf ⟨(26, 10781984818176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record010_result⟩)
 (.leaf ⟨(26, 10782112744064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(26, 10857729016064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record012_result⟩)
 (.leaf ⟨(26, 10859314167936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record013_result⟩))
 (.branch 15
 (.leaf ⟨(26, 10860387385472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record014_result⟩)
 (.leaf ⟨(26, 10861313851392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(26, 10884858576896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record016_result⟩)
 (.leaf ⟨(26, 10884866899968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record017_result⟩))
 (.branch 19
 (.leaf ⟨(26, 10892196806656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record018_result⟩)
 (.leaf ⟨(26, 10892331008000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(26, 10892599378048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record020_result⟩)
 (.leaf ⟨(26, 10892599410688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record021_result⟩))
 (.branch 23
 (.leaf ⟨(26, 10892601198720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record022_result⟩)
 (.leaf ⟨(26, 10892720736264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(26, 10896609052672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record024_result⟩)
 (.leaf ⟨(26, 10896881484808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record025_result⟩))
 (.branch 27
 (.leaf ⟨(26, 10901191131137), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record026_result⟩)
 (.leaf ⟨(26, 10909359671424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(26, 10909760095240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record028_result⟩)
 (.leaf ⟨(26, 10922512875520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record029_result⟩))
 (.branch 31
 (.leaf ⟨(26, 10940088123392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 10956805505024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record031_result⟩)
 (.leaf ⟨(26, 11035190853760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record032_result⟩)))))))
 (.branch 49
 (.branch 41
 (.branch 37
 (.branch 35
 (.branch 34
 (.leaf ⟨(26, 11040626671632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_result⟩)
 (.leaf ⟨(26, 11074919301136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record034_result⟩))
 (.branch 36
 (.leaf ⟨(26, 11125385101312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record035_result⟩)
 (.leaf ⟨(26, 11125645148288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record036_result⟩)))
 (.branch 39
 (.branch 38
 (.leaf ⟨(26, 11180947014912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record037_result⟩)
 (.leaf ⟨(26, 11189677490176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record038_result⟩))
 (.branch 40
 (.leaf ⟨(26, 11190269919360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record039_result⟩)
 (.leaf ⟨(26, 11193970360320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record040_result⟩))))
 (.branch 45
 (.branch 43
 (.branch 42
 (.leaf ⟨(26, 11197551231104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record041_result⟩)
 (.leaf ⟨(26, 11237945606144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record042_result⟩))
 (.branch 44
 (.leaf ⟨(26, 11238077726720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record043_result⟩)
 (.leaf ⟨(26, 11238341967872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(26, 11238465603712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record045_result⟩)
 (.leaf ⟨(26, 11247055536129), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record046_result⟩))
 (.branch 48
 (.leaf ⟨(26, 11307984191488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record047_result⟩)
 (.leaf ⟨(26, 11307990401152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record048_result⟩)))))
 (.branch 57
 (.branch 53
 (.branch 51
 (.branch 50
 (.leaf ⟨(26, 11310064566272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record049_result⟩)
 (.leaf ⟨(26, 11310070775936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record050_result⟩))
 (.branch 52
 (.leaf ⟨(26, 11331405119488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record051_result⟩)
 (.leaf ⟨(26, 11331601186944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record052_result⟩)))
 (.branch 55
 (.branch 54
 (.leaf ⟨(26, 11334521487488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record053_result⟩)
 (.leaf ⟨(26, 11334525681664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record054_result⟩))
 (.branch 56
 (.leaf ⟨(26, 11334591741952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record055_result⟩)
 (.leaf ⟨(26, 11334721749120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record056_result⟩))))
 (.branch 61
 (.branch 59
 (.branch 58
 (.leaf ⟨(26, 11342283030656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record057_result⟩)
 (.leaf ⟨(26, 11366733742208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record058_result⟩))
 (.branch 60
 (.leaf ⟨(26, 11375512485888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record059_result⟩)
 (.leaf ⟨(26, 11375636121728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record060_result⟩)))
 (.branch 63
 (.branch 62
 (.leaf ⟨(26, 11384226054145), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record061_result⟩)
 (.leaf ⟨(26, 11401125068928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record062_result⟩))
 (.branch 64
 (.leaf ⟨(26, 11401129263104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record063_result⟩)
 (.branch 65
 (.leaf ⟨(26, 11401265415168), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_result⟩)
 (.leaf ⟨(26, 11401393341056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (14876 + i))) 0 66 :=
  interval_of_check _ 0 66 (by decide +kernel)

public theorem complete : Block 14876 14942 :=
  block_of_table results 14876 66 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0332
