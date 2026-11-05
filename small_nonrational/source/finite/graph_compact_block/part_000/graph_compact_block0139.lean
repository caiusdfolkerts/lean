module
prelude
import GraphInputsRow24Part00023Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0139
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 41
 (.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 12586804314880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record000_result⟩)
 (.leaf ⟨(24, 12588952911872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 12592913451136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 12654462636288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record003_result⟩)
 (.leaf ⟨(24, 12723182174208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 12864232358656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record005_result⟩)
 (.leaf ⟨(24, 12898600484864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 13104356261888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 13125441226752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record008_result⟩)
 (.leaf ⟨(24, 13125709791232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 13134278560000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record010_result⟩)
 (.leaf ⟨(24, 13134412972032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 13136568516608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 13238779609152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record013_result⟩)
 (.leaf ⟨(24, 13304479121664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(24, 13306367672576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record015_result⟩)
 (.leaf ⟨(24, 13308371468544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record016_result⟩))
 (.branch 18
 (.leaf ⟨(24, 13308639871232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record017_result⟩)
 (.branch 19
 (.leaf ⟨(24, 13308639936512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record018_result⟩)
 (.leaf ⟨(24, 13310921548032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(24, 13350177177664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record020_result⟩)
 (.leaf ⟨(24, 13350178226208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record021_result⟩))
 (.branch 23
 (.leaf ⟨(24, 13377292222720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record022_result⟩)
 (.branch 24
 (.leaf ⟨(24, 13377357316096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record023_result⟩)
 (.leaf ⟨(24, 13379506807040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(24, 13384805269632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record025_result⟩)
 (.leaf ⟨(24, 13385678815232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record026_result⟩))
 (.branch 28
 (.leaf ⟨(24, 13386945429760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record027_result⟩)
 (.branch 29
 (.leaf ⟨(24, 13422590697504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record028_result⟩)
 (.leaf ⟨(24, 13513654288512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(24, 13516677325056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record030_result⟩)
 (.leaf ⟨(24, 13524115947776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record031_result⟩))
 (.branch 33
 (.leaf ⟨(24, 13524384383104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record032_result⟩)
 (.branch 34
 (.leaf ⟨(24, 13524652818432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record033_result⟩)
 (.leaf ⟨(24, 13524656979968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(24, 13610291052672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record035_result⟩)
 (.branch 37
 (.leaf ⟨(24, 13643526717568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record036_result⟩)
 (.leaf ⟨(24, 13651891257600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(24, 13652159660288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record038_result⟩)
 (.branch 40
 (.leaf ⟨(24, 13652170129408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record039_result⟩)
 (.leaf ⟨(24, 13669071126528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record040_result⟩)))))))
 (.branch 62
 (.branch 51
 (.branch 46
 (.branch 43
 (.branch 42
 (.leaf ⟨(24, 13669607931904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record041_result⟩)
 (.leaf ⟨(24, 13754142130208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record042_result⟩))
 (.branch 44
 (.leaf ⟨(24, 13822626693376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record043_result⟩)
 (.branch 45
 (.leaf ⟨(24, 13822895161344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record044_result⟩)
 (.leaf ⟨(24, 13823096398080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record045_result⟩))))
 (.branch 48
 (.branch 47
 (.leaf ⟨(24, 13839202521120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record046_result⟩)
 (.leaf ⟨(24, 13856130760960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record047_result⟩))
 (.branch 49
 (.leaf ⟨(24, 13856130826240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record048_result⟩)
 (.branch 50
 (.leaf ⟨(24, 13858521547008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record049_result⟩)
 (.leaf ⟨(24, 13858529935360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record050_result⟩)))))
 (.branch 56
 (.branch 53
 (.branch 52
 (.leaf ⟨(24, 13873550754048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record051_result⟩)
 (.leaf ⟨(24, 13873562255361), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record052_result⟩))
 (.branch 54
 (.leaf ⟨(24, 13890486894624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record053_result⟩)
 (.branch 55
 (.leaf ⟨(24, 13899934040064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record054_result⟩)
 (.leaf ⟨(24, 13900003156224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(24, 13903627030560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record056_result⟩)
 (.branch 58
 (.leaf ⟨(24, 13929385361664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record057_result⟩)
 (.leaf ⟨(24, 13935436693504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(24, 13935828828416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record059_result⟩)
 (.branch 61
 (.leaf ⟨(24, 13937975263488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record060_result⟩)
 (.leaf ⟨(24, 13937986764801), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record061_result⟩))))))
 (.branch 72
 (.branch 67
 (.branch 64
 (.branch 63
 (.leaf ⟨(24, 13937986772992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record062_result⟩)
 (.leaf ⟨(24, 13976629944576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record063_result⟩))
 (.branch 65
 (.leaf ⟨(24, 14004550434816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record064_result⟩)
 (.branch 66
 (.leaf ⟨(24, 14004558757888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record065_result⟩)
 (.leaf ⟨(24, 14010254688512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record066_result⟩))))
 (.branch 69
 (.branch 68
 (.leaf ⟨(24, 14010989740032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record067_result⟩)
 (.leaf ⟨(24, 14012607692800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record068_result⟩))
 (.branch 70
 (.leaf ⟨(24, 14013144498176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record069_result⟩)
 (.branch 71
 (.leaf ⟨(24, 14197287092480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record070_result⟩)
 (.leaf ⟨(24, 14197823963136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record071_result⟩)))))
 (.branch 77
 (.branch 74
 (.branch 73
 (.leaf ⟨(24, 14197832286208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record072_result⟩)
 (.leaf ⟨(24, 14201447842048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record073_result⟩))
 (.branch 75
 (.leaf ⟨(24, 14201720471552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record074_result⟩)
 (.branch 76
 (.leaf ⟨(24, 14201984712704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record075_result⟩)
 (.leaf ⟨(24, 14201993035776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record076_result⟩))))
 (.branch 80
 (.branch 78
 (.leaf ⟨(24, 14203528216832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record077_result⟩)
 (.branch 79
 (.leaf ⟨(24, 14204263268352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record078_result⟩)
 (.leaf ⟨(24, 14216410988800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record079_result⟩)))
 (.branch 81
 (.leaf ⟨(24, 14218627710976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record080_result⟩)
 (.branch 82
 (.leaf ⟨(24, 14218900275200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record081_result⟩)
 (.leaf ⟨(24, 14220708085760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00023.record082_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8892 + i))) 0 83 :=
  interval_of_check _ 0 83 (by decide +kernel)

public theorem complete : Block 8892 8975 :=
  block_of_table results 8892 83 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0139
