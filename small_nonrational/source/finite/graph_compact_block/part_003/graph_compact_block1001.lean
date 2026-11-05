module
prelude
import GraphInputsSix0Part00036Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1001
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 14440242683968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 14440242692128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record001_result⟩)
 (.leaf ⟨(32, 14441299255360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 14441299263520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 14441367224576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record004_result⟩)
 (.leaf ⟨(32, 14441368338432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 14441435373824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 14449688723712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record007_result⟩)
 (.leaf ⟨(32, 14449756872960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 14449954078720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 14451034034240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record010_result⟩)
 (.leaf ⟨(32, 14453248626720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 14469478547712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 14475719672064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record013_result⟩)
 (.leaf ⟨(32, 14476868911104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 14477403685120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 14477940555776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record016_result⟩)
 (.leaf ⟨(32, 14479006957824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 14483189743616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 14484309573888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record019_result⟩)
 (.leaf ⟨(32, 14484320043008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 14485190410240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record021_result⟩)
 (.leaf ⟨(32, 14485450424576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 14485989425408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record023_result⟩)
 (.leaf ⟨(32, 14486262054912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 14486526296064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 14486534619136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record026_result⟩)
 (.leaf ⟨(32, 14486658416640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 14487596859648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 14487608360961), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record029_result⟩)
 (.leaf ⟨(32, 14487608369152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 14492899540992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 14522090791168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record032_result⟩)
 (.leaf ⟨(32, 14540888670464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 14541425541120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 14545586290688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record035_result⟩)
 (.leaf ⟨(32, 14547129794816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 14549747040256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 14553635160320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record038_result⟩)
 (.leaf ⟨(32, 14553907789824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 14554172030976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 14554180354048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record041_result⟩)
 (.leaf ⟨(32, 14555715535104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 14556450586624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 14558068539392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record044_result⟩)
 (.leaf ⟨(32, 14558605344768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 14564309663744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record046_result⟩)
 (.leaf ⟨(32, 14564846469120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 14572330172544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record048_result⟩)
 (.leaf ⟨(32, 14579883053120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 14582097645600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 14587123482880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record051_result⟩)
 (.leaf ⟨(32, 14587191632128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 14589032956160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 14589569826816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record054_result⟩)
 (.leaf ⟨(32, 14589573988352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 14602940498176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 14604525650048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record057_result⟩)
 (.leaf ⟨(32, 14605598867584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 14606917468416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 14606927937536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record060_result⟩)
 (.leaf ⟨(32, 14612890190080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 14613158592768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 14613169061888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record063_result⟩)
 (.leaf ⟨(32, 14614198780160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 14616177475840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 14616445878528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record066_result⟩)
 (.leaf ⟨(32, 14616457379841), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 14616457388032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 14620623913088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record069_result⟩)
 (.leaf ⟨(32, 14622620942592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 14622625169408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record071_result⟩)
 (.leaf ⟨(32, 14623424282880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 14623428509696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record073_result⟩)
 (.leaf ⟨(32, 14623432671232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 14623436702720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 14623568823296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record076_result⟩)
 (.leaf ⟨(32, 14623692555008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 14623826919552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 14623833064448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record079_result⟩)
 (.leaf ⟨(32, 14623960990336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 14630070059008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 14630606864384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record082_result⟩)
 (.leaf ⟨(32, 14678323429632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 14678860300288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 14678868623360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record085_result⟩)
 (.leaf ⟨(32, 14682484179200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 14682756808704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 14683021049856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record088_result⟩)
 (.leaf ⟨(32, 14683029372928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 14684564553984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 14685299605504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record091_result⟩)
 (.leaf ⟨(32, 14697447325952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 14699664048128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 14699936612352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record094_result⟩)
 (.leaf ⟨(32, 14700465094656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 14701744422912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record096_result⟩)
 (.leaf ⟨(32, 14702016987136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 14702479409152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record098_result⟩)
 (.leaf ⟨(32, 14709526954240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00036.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (30386 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 30386 30486 :=
  block_of_table results 30386 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1001
