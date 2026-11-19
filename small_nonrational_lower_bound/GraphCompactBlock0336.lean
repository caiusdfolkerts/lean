module
prelude
import GraphInputsRow26Part00020Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0336
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 12465270162048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 12465340417024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record001_result⟩)
 (.leaf ⟨(26, 12508230322304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 12510575001600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 12512655376384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record004_result⟩)
 (.leaf ⟨(26, 12524295555200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 12541457891584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 12541465987200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record007_result⟩)
 (.leaf ⟨(26, 12545742211200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(26, 12545891041280), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record009_result⟩)
 (.leaf ⟨(26, 12554592060160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record010_result⟩))
 (.branch 12
 (.leaf ⟨(26, 12558620821632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record011_result⟩)
 (.leaf ⟨(26, 12575750521088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(26, 12575750586368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record013_result⟩)
 (.branch 15
 (.leaf ⟨(26, 12575752667136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record014_result⟩)
 (.leaf ⟨(26, 12575754422528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(26, 12575756796032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record016_result⟩)
 (.branch 18
 (.leaf ⟨(26, 12575756828672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record017_result⟩)
 (.leaf ⟨(26, 12575758616704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(26, 12575878154248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record019_result⟩)
 (.branch 21
 (.leaf ⟨(26, 12575958130688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record020_result⟩)
 (.leaf ⟨(26, 12576010274824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 12576221038720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record022_result⟩)
 (.leaf ⟨(26, 12577950271744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 12577950337024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record024_result⟩)
 (.leaf ⟨(26, 12577954465920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record025_result⟩))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf ⟨(26, 12577958528008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record026_result⟩)
 (.branch 28
 (.leaf ⟨(26, 12577975304193), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record027_result⟩)
 (.leaf ⟨(26, 12578090648584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record028_result⟩)))
 (.branch 30
 (.leaf ⟨(26, 12578103296000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record029_result⟩)
 (.branch 31
 (.leaf ⟨(26, 12578107424769), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record030_result⟩)
 (.leaf ⟨(26, 12578354889736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record031_result⟩))))
 (.branch 35
 (.branch 33
 (.leaf ⟨(26, 12578371665921), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record032_result⟩)
 (.branch 34
 (.leaf ⟨(26, 12580030711808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record033_result⟩)
 (.leaf ⟨(26, 12580249731072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record034_result⟩)))
 (.branch 37
 (.branch 36
 (.leaf ⟨(26, 12584323516672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record035_result⟩)
 (.leaf ⟨(26, 12584323581952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record036_result⟩))
 (.branch 38
 (.leaf ⟨(26, 12584794194952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record037_result⟩)
 (.leaf ⟨(26, 12584810971137), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record038_result⟩)))))
 (.branch 46
 (.branch 42
 (.branch 40
 (.leaf ⟨(26, 12588952911872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record039_result⟩)
 (.branch 41
 (.leaf ⟨(26, 12592913451136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record040_result⟩)
 (.leaf ⟨(26, 12645617467520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record041_result⟩)))
 (.branch 44
 (.branch 43
 (.leaf ⟨(26, 12645751668864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record042_result⟩)
 (.leaf ⟨(26, 12646017499152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record043_result⟩))
 (.branch 45
 (.leaf ⟨(26, 12648972910608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record044_result⟩)
 (.leaf ⟨(26, 12650062873216), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record045_result⟩))))
 (.branch 49
 (.branch 47
 (.leaf ⟨(26, 12653150146688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record046_result⟩)
 (.branch 48
 (.leaf ⟨(26, 12653150175248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record047_result⟩)
 (.leaf ⟨(26, 12653284376592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record048_result⟩)))
 (.branch 51
 (.branch 50
 (.leaf ⟨(26, 12653536264208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record049_result⟩)
 (.leaf ⟨(26, 12654592835600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record050_result⟩))
 (.branch 52
 (.leaf ⟨(26, 12713397157904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record051_result⟩)
 (.leaf ⟨(26, 12721970153488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record052_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (15097 + i))) 0 53 :=
  interval_of_check _ 0 53 (by decide +kernel)

public theorem complete : Block 15097 15150 :=
  block_of_table results 15097 53 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0336
