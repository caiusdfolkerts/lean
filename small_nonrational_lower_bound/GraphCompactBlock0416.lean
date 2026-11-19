module
prelude
import GraphInputsRow27Part00013Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0416
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(27, 30968401379328), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record000_result⟩)
 (.branch 2
 (.leaf ⟨(27, 30976722878464), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record001_result⟩)
 (.leaf ⟨(27, 30978863071232), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(27, 30979399876608), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record003_result⟩)
 (.branch 5
 (.leaf ⟨(27, 31033902759936), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record004_result⟩)
 (.leaf ⟨(27, 31042488500224), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(27, 31046781370368), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record006_result⟩)
 (.branch 8
 (.leaf ⟨(27, 31050809999360), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record007_result⟩)
 (.leaf ⟨(27, 31051272421376), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(27, 31057513545728), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record009_result⟩)
 (.branch 11
 (.leaf ⟨(27, 31064534827136), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record010_result⟩)
 (.leaf ⟨(27, 31098265944192), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(27, 31116031574144), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record012_result⟩)
 (.branch 14
 (.leaf ⟨(27, 31202208661504), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record013_result⟩)
 (.leaf ⟨(27, 31235444326400), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(27, 31239650213888), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record015_result⟩)
 (.branch 17
 (.leaf ⟨(27, 31244343575104), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record016_result⟩)
 (.leaf ⟨(27, 31260986720256), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(27, 31274149347328), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record018_result⟩)
 (.branch 20
 (.leaf ⟨(27, 31337449357344), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record019_result⟩)
 (.leaf ⟨(27, 31376158031872), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(27, 31376627736576), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record021_result⟩)
 (.leaf ⟨(27, 31380788486144), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record022_result⟩))
 (.branch 24
 (.leaf ⟨(27, 31413949243392), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record023_result⟩)
 (.leaf ⟨(27, 31413957038112), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(27, 31414809591808), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record025_result⟩)
 (.branch 27
 (.leaf ⟨(27, 31415081115648), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record026_result⟩)
 (.leaf ⟨(27, 31415270908160), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(27, 31416154853376), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record028_result⟩)
 (.branch 30
 (.leaf ⟨(27, 31416344125696), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record029_result⟩)
 (.leaf ⟨(27, 31423395332096), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(27, 31431376511008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record031_result⟩)
 (.branch 33
 (.leaf ⟨(27, 31443199721472), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record032_result⟩)
 (.leaf ⟨(27, 31449440845824), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(27, 31449630703616), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record034_result⟩)
 (.branch 36
 (.leaf ⟨(27, 31451785461760), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record035_result⟩)
 (.leaf ⟨(27, 31465736249344), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(27, 31466075521024), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record037_result⟩)
 (.branch 39
 (.leaf ⟨(27, 31466348085248), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record038_result⟩)
 (.leaf ⟨(27, 31466810507264), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(27, 31491987873792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record040_result⟩)
 (.branch 42
 (.leaf ⟨(27, 31511784980480), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record041_result⟩)
 (.leaf ⟨(27, 31513592791040), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(27, 31513857032192), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record043_result⟩)
 (.branch 45
 (.leaf ⟨(27, 31513865355264), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record044_result⟩)
 (.leaf ⟨(27, 31514055213056), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(27, 31522451095552), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record046_result⟩)
 (.leaf ⟨(27, 31526743965696), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record047_result⟩))
 (.branch 49
 (.leaf ⟨(27, 31528419655680), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record048_result⟩)
 (.leaf ⟨(27, 31528692219904), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(27, 31529220702208), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record050_result⟩)
 (.branch 52
 (.leaf ⟨(27, 31530160758784), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record051_result⟩)
 (.leaf ⟨(27, 31530772594688), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(27, 31531235016704), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record053_result⟩)
 (.branch 55
 (.leaf ⟨(27, 31537979523072), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record054_result⟩)
 (.leaf ⟨(27, 31538053906432), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(27, 31538516328448), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record056_result⟩)
 (.branch 58
 (.leaf ⟨(27, 31546077609984), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record057_result⟩)
 (.leaf ⟨(27, 31546267467776), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(27, 31552516915200), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record059_result⟩)
 (.branch 61
 (.leaf ⟨(27, 31560838414336), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record060_result⟩)
 (.leaf ⟨(27, 31561299795968), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(27, 31562373013504), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record062_result⟩)
 (.branch 64
 (.leaf ⟨(27, 31568044237056), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record063_result⟩)
 (.leaf ⟨(27, 31569151590400), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(27, 31569688395776), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record065_result⟩)
 (.branch 67
 (.leaf ⟨(27, 31570191777792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record066_result⟩)
 (.leaf ⟨(27, 31570266161152), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(27, 31570728583168), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record068_result⟩)
 (.branch 70
 (.leaf ⟨(27, 31579313274880), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record069_result⟩)
 (.leaf ⟨(27, 31585752580096), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(27, 31594115301376), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record071_result⟩)
 (.leaf ⟨(27, 31594338320384), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record072_result⟩))
 (.branch 74
 (.leaf ⟨(27, 31594585006080), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record073_result⟩)
 (.leaf ⟨(27, 31605053849600), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(27, 31722964320256), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record075_result⟩)
 (.branch 77
 (.leaf ⟨(27, 31751688716544), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record076_result⟩)
 (.leaf ⟨(27, 31751825063936), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(27, 31751833387008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record078_result⟩)
 (.branch 80
 (.leaf ⟨(27, 31752023244800), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record079_result⟩)
 (.leaf ⟨(27, 31753835151616), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(27, 31754103619584), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record081_result⟩)
 (.branch 83
 (.leaf ⟨(27, 31754111942656), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record082_result⟩)
 (.leaf ⟨(27, 31754573324288), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(27, 31754875339008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record084_result⟩)
 (.branch 86
 (.leaf ⟨(27, 31755646541824), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record085_result⟩)
 (.leaf ⟨(27, 31758264369152), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(27, 31758272692224), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record087_result⟩)
 (.branch 89
 (.leaf ⟨(27, 31763465306112), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record088_result⟩)
 (.leaf ⟨(27, 31763539689472), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(27, 31764002111488), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record090_result⟩)
 (.branch 92
 (.leaf ⟨(27, 31778564734976), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record091_result⟩)
 (.leaf ⟨(27, 31785060728832), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(27, 31785069051904), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record093_result⟩)
 (.branch 95
 (.leaf ⟨(27, 31787070816512), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record094_result⟩)
 (.leaf ⟨(27, 31787339284480), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(27, 31787347607552), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record096_result⟩)
 (.leaf ⟨(27, 31787388829696), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record097_result⟩))
 (.branch 99
 (.leaf ⟨(27, 31787858534400), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record098_result⟩)
 (.leaf ⟨(27, 31812890001408), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00013.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (18973 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 18973 19073 :=
  block_of_table results 18973 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0416
