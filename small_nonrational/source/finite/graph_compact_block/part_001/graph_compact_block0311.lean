module
prelude
import GraphInputsRow25Part00021Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0311
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(25, 30789649597184), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record000_result⟩)
 (.branch 2
 (.leaf ⟨(25, 30789658050560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record001_result⟩)
 (.leaf ⟨(25, 30789685415968), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(25, 30789724110848), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record003_result⟩)
 (.branch 5
 (.leaf ⟨(25, 30790126682240), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record004_result⟩)
 (.leaf ⟨(25, 30790126714880), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(25, 30790230478880), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record006_result⟩)
 (.branch 8
 (.leaf ⟨(25, 30792005722368), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record007_result⟩)
 (.leaf ⟨(25, 30792005787648), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(25, 30792038752512), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record009_result⟩)
 (.branch 11
 (.leaf ⟨(25, 30792038817792), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record010_result⟩)
 (.leaf ⟨(25, 30792274157696), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(25, 30792277303328), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record012_result⟩)
 (.branch 14
 (.leaf ⟨(25, 30792310853664), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record013_result⟩)
 (.leaf ⟨(25, 30793347375232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(25, 30805155913760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record015_result⟩)
 (.branch 17
 (.leaf ⟨(25, 30805189464096), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record016_result⟩)
 (.leaf ⟨(25, 30824009335040), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(25, 30825274417408), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record018_result⟩)
 (.branch 20
 (.leaf ⟨(25, 30825274482688), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record019_result⟩)
 (.leaf ⟨(25, 30825290997760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(25, 30825542852736), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record021_result⟩)
 (.leaf ⟨(25, 30826398024192), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record022_result⟩))
 (.branch 24
 (.leaf ⟨(25, 30826402217984), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record023_result⟩)
 (.leaf ⟨(25, 30826670587905), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(25, 30826871922688), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record025_result⟩)
 (.branch 27
 (.leaf ⟨(25, 30830965571584), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record026_result⟩)
 (.leaf ⟨(25, 30831032672256), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(25, 30839549198337), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record028_result⟩)
 (.branch 30
 (.leaf ⟨(25, 30840617189504), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record029_result⟩)
 (.leaf ⟨(25, 30857758773280), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(25, 30864197558304), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record031_result⟩)
 (.branch 33
 (.leaf ⟨(25, 30864198078496), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record032_result⟩)
 (.leaf ⟨(25, 30865053777920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(25, 30865254129696), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record034_result⟩)
 (.branch 36
 (.leaf ⟨(25, 30865322147841), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record035_result⟩)
 (.leaf ⟨(25, 30865325301760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(25, 30865515094272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record037_result⟩)
 (.branch 39
 (.leaf ⟨(25, 30866327867424), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record038_result⟩)
 (.leaf ⟨(25, 30866362335233), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(25, 30866588311808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record040_result⟩)
 (.branch 42
 (.leaf ⟨(25, 30873639518208), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record041_result⟩)
 (.leaf ⟨(25, 30881620697120), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(25, 30896656809984), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record043_result⟩)
 (.branch 45
 (.leaf ⟨(25, 30896665133056), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record044_result⟩)
 (.leaf ⟨(25, 30898560966656), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(25, 30900687601665), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record046_result⟩)
 (.leaf ⟨(25, 30900825882624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record047_result⟩))
 (.branch 49
 (.leaf ⟨(25, 30900947518208), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record048_result⟩)
 (.leaf ⟨(25, 30915979903520), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(25, 30931012821248), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record050_result⟩)
 (.branch 52
 (.leaf ⟨(25, 30934041640960), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record051_result⟩)
 (.leaf ⟨(25, 30942363140096), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(25, 30942824505408), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record053_result⟩)
 (.branch 55
 (.leaf ⟨(25, 30943897722944), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record054_result⟩)
 (.leaf ⟨(25, 30946045206560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(25, 30969467830272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record056_result⟩)
 (.branch 58
 (.leaf ⟨(25, 30978256929344), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record057_result⟩)
 (.leaf ⟨(25, 30980404412960), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(25, 31014765207552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record059_result⟩)
 (.branch 61
 (.leaf ⟨(25, 31063910912032), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record060_result⟩)
 (.leaf ⟨(25, 31065793105952), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(25, 31065842651168), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record062_result⟩)
 (.branch 64
 (.leaf ⟨(25, 31099390558208), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record063_result⟩)
 (.leaf ⟨(25, 31244345671680), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(25, 31336136249376), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record065_result⟩)
 (.branch 67
 (.leaf ⟨(25, 31337449267456), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record066_result⟩)
 (.leaf ⟨(25, 31337717702784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(25, 31346328084480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record068_result⟩)
 (.branch 70
 (.leaf ⟨(25, 31414808543232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record069_result⟩)
 (.leaf ⟨(25, 31415072784384), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(25, 31415081107456), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record071_result⟩)
 (.leaf ⟨(25, 31415270965248), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record072_result⟩))
 (.branch 74
 (.leaf ⟨(25, 31430605308160), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record073_result⟩)
 (.leaf ⟨(25, 31431376510976), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(25, 31448316772352), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record075_result⟩)
 (.branch 77
 (.leaf ⟨(25, 31450711719936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record076_result⟩)
 (.leaf ⟨(25, 31465001779200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(25, 31465736765440), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record078_result⟩)
 (.branch 80
 (.leaf ⟨(25, 31474082648096), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record079_result⟩)
 (.leaf ⟨(25, 31491505786912), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(25, 31492579263008), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record081_result⟩)
 (.branch 83
 (.leaf ⟨(25, 31495801020416), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record082_result⟩)
 (.leaf ⟨(25, 31519296978944), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(25, 31527345913856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record084_result⟩)
 (.branch 86
 (.leaf ⟨(25, 31527618478080), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record085_result⟩)
 (.leaf ⟨(25, 31530161274880), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(25, 31568077848576), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record087_result⟩)
 (.branch 89
 (.leaf ⟨(25, 31587882237952), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record088_result⟩)
 (.leaf ⟨(25, 31596203737088), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(25, 31596732219392), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record090_result⟩)
 (.branch 92
 (.leaf ⟨(25, 31602444861440), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record091_result⟩)
 (.leaf ⟨(25, 31605053718528), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(25, 31611253166112), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record093_result⟩)
 (.branch 95
 (.leaf ⟨(25, 31750614974720), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record094_result⟩)
 (.leaf ⟨(25, 31785043951616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(25, 31789477265408), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record096_result⟩)
 (.leaf ⟨(25, 31790005747712), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record097_result⟩))
 (.branch 99
 (.leaf ⟨(25, 31795718389760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record098_result⟩)
 (.leaf ⟨(25, 31812889870336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (13722 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 13722 13822 :=
  block_of_table results 13722 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0311
