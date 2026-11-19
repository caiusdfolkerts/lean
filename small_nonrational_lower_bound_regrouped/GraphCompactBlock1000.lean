module
prelude
import GraphInputsSix0Part00035Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1000
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 13643526717568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 13651891257600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record001_result⟩)
 (.leaf ⟨(32, 13652159660288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 13652170129408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 13669071126528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record004_result⟩)
 (.leaf ⟨(32, 13669607931904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 13754142130208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 13822626693376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record007_result⟩)
 (.leaf ⟨(32, 13822895096064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 13822895161344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 13823096398080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record010_result⟩)
 (.leaf ⟨(32, 13839202521120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 13855862358272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 13856130760960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record013_result⟩)
 (.leaf ⟨(32, 13856130826240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 13858521547008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 13858529935360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record016_result⟩)
 (.leaf ⟨(32, 13873550754048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 13873562255361), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 13873562263552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record019_result⟩)
 (.leaf ⟨(32, 13890218434816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 13890486837504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record021_result⟩)
 (.leaf ⟨(32, 13890486894624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 13891344072960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record023_result⟩)
 (.leaf ⟨(32, 13891543408896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 13891543466016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 13891608314112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record026_result⟩)
 (.leaf ⟨(32, 13891612475648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 13891612540928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 13891681657088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record029_result⟩)
 (.leaf ⟨(32, 13892648501504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 13899933974784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 13899934040064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record032_result⟩)
 (.leaf ⟨(32, 13900003156224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 13903627030560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 13926842564864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record035_result⟩)
 (.leaf ⟨(32, 13927106806016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 13927115194368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 13929385361664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record038_result⟩)
 (.leaf ⟨(32, 13935428305152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 13935436693504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 13935828828416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record041_result⟩)
 (.leaf ⟨(32, 13937975263488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 13937986764801), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 13937986772992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record044_result⟩)
 (.leaf ⟨(32, 13976629944576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 13995427823872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record046_result⟩)
 (.leaf ⟨(32, 13995964694528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 14004013564160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record048_result⟩)
 (.leaf ⟨(32, 14004550434816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 14004558757888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 14010254688512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record051_result⟩)
 (.leaf ⟨(32, 14010989740032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 14012607692800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 14013144498176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record054_result⟩)
 (.leaf ⟨(32, 14197287092480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 14197823963136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 14197832286208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record057_result⟩)
 (.leaf ⟨(32, 14201447842048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 14201720471552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 14201984712704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record060_result⟩)
 (.leaf ⟨(32, 14201993035776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 14203528216832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 14204263268352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record063_result⟩)
 (.leaf ⟨(32, 14216410988800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 14218627710976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 14218900275200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record066_result⟩)
 (.leaf ⟨(32, 14219428757504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 14220708085760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 14220980649984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record069_result⟩)
 (.leaf ⟨(32, 14221443072000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 14235740471552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record071_result⟩)
 (.leaf ⟨(32, 14236013101056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 14236277342208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record073_result⟩)
 (.leaf ⟨(32, 14236285665280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 14236475523072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 14250769678592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record076_result⟩)
 (.leaf ⟨(32, 14251507851264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 14299602976800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 14303895846944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record079_result⟩)
 (.leaf ⟨(32, 14332050030848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 14338291155200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 14346612654336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record082_result⟩)
 (.leaf ⟨(32, 14348156145728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 14368557244672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 14371523231776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record085_result⟩)
 (.leaf ⟨(32, 14372717994240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 14380108972064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 14381039493376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record088_result⟩)
 (.leaf ⟨(32, 14403982393600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 14403990781952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 14407878902016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record091_result⟩)
 (.leaf ⟨(32, 14408143143168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 14408151531520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 14410421698816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record094_result⟩)
 (.leaf ⟨(32, 14416464642304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 14416473030656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record096_result⟩)
 (.leaf ⟨(32, 14416865165568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 14419011600640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record098_result⟩)
 (.leaf ⟨(32, 14419023110144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00035.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (30286 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 30286 30386 :=
  block_of_table results 30286 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1000
