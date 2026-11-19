module
prelude
import GraphInputsSix0Part00002Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0967
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 40
 (.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(32, 977315332352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record000_result⟩)
 (.leaf ⟨(32, 977315397632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record001_result⟩))
 (.branch 3
 (.leaf ⟨(32, 977410261248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record002_result⟩)
 (.branch 4
 (.leaf ⟨(32, 980532904192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record003_result⟩)
 (.leaf ⟨(32, 989120725248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(32, 990160912640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record005_result⟩)
 (.leaf ⟨(32, 998737281280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record006_result⟩))
 (.branch 8
 (.leaf ⟨(32, 998993133576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record007_result⟩)
 (.branch 9
 (.leaf ⟨(32, 999139885312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record008_result⟩)
 (.leaf ⟨(32, 1000883716352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(32, 1000941387784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record010_result⟩)
 (.leaf ⟨(32, 1001015836928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record011_result⟩))
 (.branch 13
 (.leaf ⟨(32, 1001017917696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 1001022079232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record013_result⟩)
 (.leaf ⟨(32, 1001073508360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(32, 1001286320384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record015_result⟩)
 (.leaf ⟨(32, 1003290165504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record016_result⟩))
 (.branch 18
 (.leaf ⟨(32, 1003558568192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record017_result⟩)
 (.branch 19
 (.leaf ⟨(32, 1003558633472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record018_result⟩)
 (.leaf ⟨(32, 1007851438336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(32, 1009729470720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record020_result⟩)
 (.leaf ⟨(32, 1009931813120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record021_result⟩))
 (.branch 23
 (.leaf ⟨(32, 1009931878400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record022_result⟩)
 (.branch 24
 (.leaf ⟨(32, 1016441372800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record023_result⟩)
 (.leaf ⟨(32, 1016443453568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(32, 1024486179072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record025_result⟩)
 (.leaf ⟨(32, 1025031307264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record026_result⟩))
 (.branch 28
 (.leaf ⟨(32, 1026566553856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record027_result⟩)
 (.branch 29
 (.leaf ⟨(32, 1026566619136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record028_result⟩)
 (.leaf ⟨(32, 1026570585344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(32, 1026702770432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record030_result⟩)
 (.leaf ⟨(32, 1026711093249), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record031_result⟩))
 (.branch 33
 (.leaf ⟨(32, 1026711158784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record032_result⟩)
 (.branch 34
 (.leaf ⟨(32, 1026843213825), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record033_result⟩)
 (.leaf ⟨(32, 1027103293696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record034_result⟩))))
 (.branch 37
 (.branch 36
 (.leaf ⟨(32, 1027111682048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record035_result⟩)
 (.leaf ⟨(32, 1050736083072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record036_result⟩))
 (.branch 38
 (.leaf ⟨(32, 1174214377856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 1208569921792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record038_result⟩)
 (.leaf ⟨(32, 1217163985152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record039_result⟩)))))))
 (.branch 60
 (.branch 50
 (.branch 45
 (.branch 42
 (.branch 41
 (.leaf ⟨(32, 1222599868544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record040_result⟩)
 (.leaf ⟨(32, 1225353363712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record041_result⟩))
 (.branch 43
 (.leaf ⟨(32, 1225353428992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record042_result⟩)
 (.branch 44
 (.leaf ⟨(32, 1225481322752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record043_result⟩)
 (.leaf ⟨(32, 1225485484288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record044_result⟩))))
 (.branch 47
 (.branch 46
 (.leaf ⟨(32, 1225485549568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record045_result⟩)
 (.leaf ⟨(32, 1225749725440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record046_result⟩))
 (.branch 48
 (.leaf ⟨(32, 1225749790720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record047_result⟩)
 (.branch 49
 (.leaf ⟨(32, 1226018193408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record048_result⟩)
 (.leaf ⟨(32, 1226026516480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record049_result⟩)))))
 (.branch 55
 (.branch 52
 (.branch 51
 (.leaf ⟨(32, 1229646233856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record050_result⟩)
 (.leaf ⟨(32, 1232828694784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record051_result⟩))
 (.branch 53
 (.leaf ⟨(32, 1232832921600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record052_result⟩)
 (.branch 54
 (.leaf ⟨(32, 1247228805504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record053_result⟩)
 (.leaf ⟨(32, 1255814545792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record054_result⟩))))
 (.branch 57
 (.branch 56
 (.leaf ⟨(32, 1284876894464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record055_result⟩)
 (.leaf ⟨(32, 1289050210688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record056_result⟩))
 (.branch 58
 (.leaf ⟨(32, 1291319328896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record057_result⟩)
 (.branch 59
 (.leaf ⟨(32, 1293468926016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record058_result⟩)
 (.leaf ⟨(32, 1294070743296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record059_result⟩))))))
 (.branch 70
 (.branch 65
 (.branch 62
 (.branch 61
 (.leaf ⟨(32, 1325611958400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record060_result⟩)
 (.leaf ⟨(32, 1327828664352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record061_result⟩))
 (.branch 63
 (.leaf ⟨(32, 1329403560192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 1329469620480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record063_result⟩)
 (.leaf ⟨(32, 1329502650624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record064_result⟩))))
 (.branch 67
 (.branch 66
 (.leaf ⟨(32, 1360038756608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record065_result⟩)
 (.leaf ⟨(32, 1363794886912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record066_result⟩))
 (.branch 68
 (.leaf ⟨(32, 1363794952192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record067_result⟩)
 (.branch 69
 (.leaf ⟨(32, 1363798918400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record068_result⟩)
 (.leaf ⟨(32, 1364327465216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record069_result⟩)))))
 (.branch 75
 (.branch 72
 (.branch 71
 (.leaf ⟨(32, 1422047412480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record070_result⟩)
 (.leaf ⟨(32, 1422317944896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record071_result⟩))
 (.branch 73
 (.leaf ⟨(32, 1422919762176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record072_result⟩)
 (.branch 74
 (.leaf ⟨(32, 1438984995072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record073_result⟩)
 (.leaf ⟨(32, 1458252579072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record074_result⟩))))
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 1458318639360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 1458351669504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record076_result⟩)
 (.leaf ⟨(32, 1458351734784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 1470157062400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 1471197249792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record079_result⟩)
 (.leaf ⟨(32, 1479773618432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00002.record080_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (27005 + i))) 0 81 :=
  interval_of_check _ 0 81 (by decide +kernel)

public theorem complete : Block 27005 27086 :=
  block_of_table results 27005 81 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0967
