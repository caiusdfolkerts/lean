module
prelude
import GraphInputsSix0Part00078Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1043
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 30824045183232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 30824179384576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record001_result⟩)
 (.leaf ⟨(32, 30824183546112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 30824183595072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 30824254685440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record004_result⟩)
 (.leaf ⟨(32, 30824315552000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 30824319713536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 30824319778816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record007_result⟩)
 (.leaf ⟨(32, 30824486420608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 30825270288640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 30825274507296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record010_result⟩)
 (.leaf ⟨(32, 30825538691328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 30826267967744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 30826268033024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record013_result⟩)
 (.leaf ⟨(32, 30826326860032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 30826331021568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 30826331078688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record016_result⟩)
 (.leaf ⟨(32, 30826395926784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 30826400088320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 30826400153600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record019_result⟩)
 (.leaf ⟨(32, 30826469269760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 30829569450048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record021_result⟩)
 (.leaf ⟨(32, 30829569458208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 30829833691200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record023_result⟩)
 (.leaf ⟨(32, 30829833699360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 30830693990656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 30832039301184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record026_result⟩)
 (.leaf ⟨(32, 30834253893664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 30839279730944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 30839347880192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record029_result⟩)
 (.leaf ⟨(32, 30841189204224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 30841726074880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 30841730236416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record032_result⟩)
 (.leaf ⟨(32, 30860754616576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 30860758778112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 30860758843392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record035_result⟩)
 (.leaf ⟨(32, 30860761899264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 30861231661088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 30862305398816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record038_result⟩)
 (.leaf ⟨(32, 30863929188384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 30864193429536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 30864915366144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record041_result⟩)
 (.leaf ⟨(32, 30864919527680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 30864919592960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 30864922648832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record044_result⟩)
 (.leaf ⟨(32, 30865319010560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 30865392410656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record046_result⟩)
 (.leaf ⟨(32, 30866466148384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 30873640509696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record048_result⟩)
 (.leaf ⟨(32, 30896187048192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 30896195436544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 30896653631744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record051_result⟩)
 (.leaf ⟨(32, 30896665133057), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 30896665141248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 30898271750176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record054_result⟩)
 (.leaf ⟨(32, 30898288394784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 30900545978624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 30900748321024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record057_result⟩)
 (.leaf ⟨(32, 30900752547840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 30900814381312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 30900825882625), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record060_result⟩)
 (.leaf ⟨(32, 30900825890816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 30903096058112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 30935115370560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record063_result⟩)
 (.leaf ⟨(32, 30942222647552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 30942222712832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 30961683202304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record066_result⟩)
 (.leaf ⟨(32, 30961951604992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 30961962074112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 30968401379328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record069_result⟩)
 (.leaf ⟨(32, 30970541572096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 30976722878464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record071_result⟩)
 (.leaf ⟨(32, 30978863071232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 30979399876608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record073_result⟩)
 (.leaf ⟨(32, 30986144382976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 31014765207584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 31033357566208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record076_result⟩)
 (.leaf ⟨(32, 31033630195712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 31033894436864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 31033902759936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record079_result⟩)
 (.leaf ⟨(32, 31034092617728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 31039796871424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 31041951694848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record082_result⟩)
 (.leaf ⟨(32, 31042488500224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 31046240338176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 31046574866432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record085_result⟩)
 (.leaf ⟨(32, 31046781370368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 31048386773248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 31049124945920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record088_result⟩)
 (.leaf ⟨(32, 31050537435136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 31050809999360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 31051272421376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record091_result⟩)
 (.leaf ⟨(32, 31051338481664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 31056976740352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 31057513545728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record094_result⟩)
 (.leaf ⟨(32, 31064534827136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 31096730304640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record096_result⟩)
 (.leaf ⟨(32, 31097803522176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 31098265944192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record098_result⟩)
 (.leaf ⟨(32, 31108851835136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00078.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (34372 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 34372 34472 :=
  block_of_table results 34372 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1043
