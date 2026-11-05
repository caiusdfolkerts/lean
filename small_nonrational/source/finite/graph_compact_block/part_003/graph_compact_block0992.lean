module
prelude
import GraphInputsSix0Part00027Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0992
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 10353826087168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 10355972522240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record001_result⟩)
 (.leaf ⟨(32, 10359672932480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 10362017611776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 10370603352064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record004_result⟩)
 (.leaf ⟨(32, 10372683726848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 10372692049920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 10379351572608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record007_result⟩)
 (.leaf ⟨(32, 10387716112640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 10446522892672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 10446728372544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record010_result⟩)
 (.leaf ⟨(32, 10447795851648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 10447797948736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 10448066351424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record013_result⟩)
 (.leaf ⟨(32, 10454237253952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 10454505656640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 10484292159760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record016_result⟩)
 (.leaf ⟨(32, 10489799180544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 10490067583232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 10490067648512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record019_result⟩)
 (.leaf ⟨(32, 10490201784576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 10493422997760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record021_result⟩)
 (.leaf ⟨(32, 10562134147328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 10562142535680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record023_result⟩)
 (.leaf ⟨(32, 10593079673088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 10601399156736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 10601401172224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record026_result⟩)
 (.leaf ⟨(32, 10602944663616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 10630455165184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 10630719406336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record029_result⟩)
 (.leaf ⟨(32, 10630727794688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 10639451881473), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 10665210216704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record032_result⟩)
 (.leaf ⟨(32, 10699040424192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 10699577294848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 10707626164480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record035_result⟩)
 (.leaf ⟨(32, 10708163035136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 10708171358208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 10711786914048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record038_result⟩)
 (.leaf ⟨(32, 10716220293120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 10716757098496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 10741480456192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record041_result⟩)
 (.leaf ⟨(32, 10741484617728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 10747184709888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 10767889924352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record044_result⟩)
 (.leaf ⟨(32, 10767898312704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 10781576036608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record046_result⟩)
 (.leaf ⟨(32, 10781580263424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 10781584424960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record048_result⟩)
 (.leaf ⟨(32, 10781588456448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 10781720577024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 10781844308736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record051_result⟩)
 (.leaf ⟨(32, 10781978673280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 10781984818176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 10782112744064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record054_result⟩)
 (.leaf ⟨(32, 10857729016064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 10857732980744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 10859314167936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record057_result⟩)
 (.leaf ⟨(32, 10860387385472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 10861305463040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 10861313851392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record060_result⟩)
 (.leaf ⟨(32, 10867678707968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 10875412430976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 10884858576896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record063_result⟩)
 (.leaf ⟨(32, 10884866899968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 10892054282496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 10892056103168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record066_result⟩)
 (.leaf ⟨(32, 10892192579840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 10892196741376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 10892196806656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record069_result⟩)
 (.leaf ⟨(32, 10892200642816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 10892331008000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record071_result⟩)
 (.leaf ⟨(32, 10892332763392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 10892597004544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record073_result⟩)
 (.leaf ⟨(32, 10892599378048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 10892599410688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 10892601198720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record076_result⟩)
 (.leaf ⟨(32, 10892720736264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 10896608987392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 10896609052672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record079_result⟩)
 (.leaf ⟨(32, 10896621502720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 10896625697280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 10896629891072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record082_result⟩)
 (.leaf ⟨(32, 10896877422720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 10896881484808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 10896898260993), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record085_result⟩)
 (.leaf ⟨(32, 10900769736960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 10900914372864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 10900922761216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record088_result⟩)
 (.leaf ⟨(32, 10901029978368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 10901174354952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 10901187002368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record091_result⟩)
 (.leaf ⟨(32, 10901191131137), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 10901298381056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 10901310670848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record094_result⟩)
 (.leaf ⟨(32, 10901432582400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 10905060442368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record096_result⟩)
 (.leaf ⟨(32, 10905333071872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 10905727271680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record098_result⟩)
 (.leaf ⟨(32, 10909355477248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (29486 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 29486 29586 :=
  block_of_table results 29486 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0992
