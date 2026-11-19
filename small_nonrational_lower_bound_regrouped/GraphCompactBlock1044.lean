module
prelude
import GraphInputsSix0Part00079Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1044
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 45
 (.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(32, 31116031574144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record000_result⟩)
 (.leaf ⟨(32, 31175423885312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record001_result⟩))
 (.branch 3
 (.leaf ⟨(32, 31202208661504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record002_result⟩)
 (.branch 4
 (.leaf ⟨(32, 31235235676416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record003_result⟩)
 (.leaf ⟨(32, 31235246145536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(32, 31235444326400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record005_result⟩)
 (.branch 7
 (.leaf ⟨(32, 31235485483264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record006_result⟩)
 (.leaf ⟨(32, 31239650213888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(32, 31244343575104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record008_result⟩)
 (.branch 10
 (.leaf ⟨(32, 31260986720256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record009_result⟩)
 (.leaf ⟨(32, 31273872556288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(32, 31274141024256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record011_result⟩)
 (.leaf ⟨(32, 31274149347328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record012_result⟩))
 (.branch 14
 (.leaf ⟨(32, 31274610728960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record013_result⟩)
 (.branch 15
 (.leaf ⟨(32, 31280314982656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record014_result⟩)
 (.leaf ⟨(32, 31297494851584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(32, 31337218146336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record016_result⟩)
 (.branch 18
 (.leaf ⟨(32, 31337449357344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record017_result⟩)
 (.leaf ⟨(32, 31341764681984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(32, 31344965521440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record019_result⟩)
 (.branch 21
 (.leaf ⟨(32, 31345229762592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record020_result⟩)
 (.leaf ⟨(32, 31346321793280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(32, 31374069268736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record022_result⟩)
 (.leaf ⟨(32, 31374077657088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record023_result⟩))
 (.branch 25
 (.leaf ⟨(32, 31374469792000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record024_result⟩)
 (.branch 26
 (.leaf ⟨(32, 31376149643520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record025_result⟩)
 (.leaf ⟨(32, 31376158031872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(32, 31376616227072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record027_result⟩)
 (.branch 29
 (.leaf ⟨(32, 31376627736576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record028_result⟩)
 (.leaf ⟨(32, 31377689444608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(32, 31377701474304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record030_result⟩)
 (.branch 32
 (.leaf ⟨(32, 31380310393088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record031_result⟩)
 (.leaf ⟨(32, 31380318781440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record032_result⟩)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf ⟨(32, 31380450902016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record033_result⟩)
 (.branch 35
 (.leaf ⟨(32, 31380508573952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record034_result⟩)
 (.leaf ⟨(32, 31380710916352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record035_result⟩)))
 (.branch 37
 (.leaf ⟨(32, 31380715143168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record036_result⟩)
 (.branch 38
 (.leaf ⟨(32, 31380776976640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record037_result⟩)
 (.leaf ⟨(32, 31380788486144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record038_result⟩))))
 (.branch 42
 (.branch 40
 (.leaf ⟨(32, 31381581791488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record039_result⟩)
 (.branch 41
 (.leaf ⟨(32, 31381850194176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record040_result⟩)
 (.leaf ⟨(32, 31381862223872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record041_result⟩)))
 (.branch 43
 (.leaf ⟨(32, 31384131870976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record042_result⟩)
 (.branch 44
 (.leaf ⟨(32, 31389036642304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record043_result⟩)
 (.leaf ⟨(32, 31413684936960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record044_result⟩)))))))
 (.branch 68
 (.branch 56
 (.branch 50
 (.branch 47
 (.branch 46
 (.leaf ⟨(32, 31413685002240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record045_result⟩)
 (.leaf ⟨(32, 31413949243392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record046_result⟩))
 (.branch 48
 (.leaf ⟨(32, 31413957038112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record047_result⟩)
 (.branch 49
 (.leaf ⟨(32, 31414801203456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record048_result⟩)
 (.leaf ⟨(32, 31414809591808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record049_result⟩))))
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 31415069606144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 31415081107457), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record051_result⟩)
 (.leaf ⟨(32, 31415081115648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 31415270908160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 31415874420992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record054_result⟩)
 (.leaf ⟨(32, 31416142823680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record055_result⟩)))))
 (.branch 62
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 31416154853376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 31416344125696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record057_result⟩)
 (.leaf ⟨(32, 31423395332096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 31431376511008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 31442654527744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record060_result⟩)
 (.leaf ⟨(32, 31443191398400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record061_result⟩))))
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 31443199721472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 31448044208640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record063_result⟩)
 (.leaf ⟨(32, 31448316772353), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 31448895652096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 31449168281600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record066_result⟩)
 (.leaf ⟨(32, 31449432522752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record067_result⟩))))))
 (.branch 79
 (.branch 73
 (.branch 70
 (.branch 69
 (.leaf ⟨(32, 31449440845824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record068_result⟩)
 (.leaf ⟨(32, 31449630703616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record069_result⟩))
 (.branch 71
 (.leaf ⟨(32, 31450703332096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record070_result⟩)
 (.branch 72
 (.leaf ⟨(32, 31451248656384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record071_result⟩)
 (.leaf ⟨(32, 31451785461760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record072_result⟩))))
 (.branch 76
 (.branch 74
 (.leaf ⟨(32, 31464965046528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record073_result⟩)
 (.branch 75
 (.leaf ⟨(32, 31465735717408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record074_result⟩)
 (.leaf ⟨(32, 31465736249344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record075_result⟩)))
 (.branch 77
 (.leaf ⟨(32, 31466075521024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record076_result⟩)
 (.branch 78
 (.leaf ⟨(32, 31466348085248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record077_result⟩)
 (.leaf ⟨(32, 31466810507264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record078_result⟩)))))
 (.branch 85
 (.branch 82
 (.branch 80
 (.leaf ⟨(32, 31466876567552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record079_result⟩)
 (.branch 81
 (.leaf ⟨(32, 31478109446400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record080_result⟩)
 (.leaf ⟨(32, 31478381547552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record081_result⟩)))
 (.branch 83
 (.leaf ⟨(32, 31480298930432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record082_result⟩)
 (.branch 84
 (.leaf ⟨(32, 31480567333120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record083_result⟩)
 (.leaf ⟨(32, 31480579362816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record084_result⟩))))
 (.branch 88
 (.branch 86
 (.leaf ⟨(32, 31480768635136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record085_result⟩)
 (.branch 87
 (.leaf ⟨(32, 31483386462464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record086_result⟩)
 (.leaf ⟨(32, 31483394850816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record087_result⟩)))
 (.branch 89
 (.leaf ⟨(32, 31483798495232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record088_result⟩)
 (.branch 90
 (.leaf ⟨(32, 31483856167168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record089_result⟩)
 (.leaf ⟨(32, 31484872232960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00079.record090_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (34472 + i))) 0 91 :=
  interval_of_check _ 0 91 (by decide +kernel)

public theorem complete : Block 34472 34563 :=
  block_of_table results 34472 91 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1044
