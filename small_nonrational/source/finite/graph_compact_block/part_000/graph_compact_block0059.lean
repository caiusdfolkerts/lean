module
prelude
import GraphInputsRow19Part00019Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0059
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 22698676731904), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 22732326764800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record001_result⟩)
 (.leaf ⟨(19, 22732330991616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 22732465192960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 22732467078400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record004_result⟩)
 (.leaf ⟨(19, 22735078096896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 22735086419968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 22737616650496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record007_result⟩)
 (.leaf ⟨(19, 22749982523648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 22769874043136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 22769882431488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record010_result⟩)
 (.leaf ⟨(19, 22770072224000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 22770080612352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 22770340626688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record013_result⟩)
 (.leaf ⟨(19, 22770344853504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 22770352136192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 22770574958848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record016_result⟩)
 (.leaf ⟨(19, 22804405878784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 22804678312960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 22824841453632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record019_result⟩)
 (.leaf ⟨(19, 22827317100800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 22827321327616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record021_result⟩)
 (.leaf ⟨(19, 22827327569920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 22827525750784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record023_result⟩)
 (.leaf ⟨(19, 22842583826432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 22850594504768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 22858374389824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record026_result⟩)
 (.leaf ⟨(19, 22863856828672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 22863927115776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 22863935438848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record029_result⟩)
 (.leaf ⟨(19, 22864967303168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 22864975626240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 22872116494336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record032_result⟩)
 (.leaf ⟨(19, 22875084439808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 22876141011200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 22876347434048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record035_result⟩)
 (.leaf ⟨(19, 22876941976128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 22876944073216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 22879459639552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record038_result⟩)
 (.leaf ⟨(19, 22887417282816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 22887417348096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 22893862895616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record041_result⟩)
 (.leaf ⟨(19, 22898929631232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 22902184394752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 22913961959424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record044_result⟩)
 (.leaf ⟨(19, 22920256651264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 22920384545024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record046_result⟩)
 (.leaf ⟨(19, 22920652947712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 22920653012992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record048_result⟩)
 (.leaf ⟨(19, 22922535206912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 22922799382784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 22922799448064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record051_result⟩)
 (.leaf ⟨(19, 22923058350112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 22927094398976), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 22927098560512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record054_result⟩)
 (.leaf ⟨(19, 22927145699584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 22948081762304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 22948089955328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record057_result⟩)
 (.leaf ⟨(19, 22948278837504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 22948287225856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 22948288136192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record060_result⟩)
 (.leaf ⟨(19, 22948552377344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 22948815569440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 22953673695296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record063_result⟩)
 (.leaf ⟨(19, 22972456255488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 22976096403712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 22980265509952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record066_result⟩)
 (.leaf ⟨(19, 22986958905408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 23014590776384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 23014724862468), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record069_result⟩)
 (.leaf ⟨(19, 23014724993025), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 23023332655360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record071_result⟩)
 (.leaf ⟨(19, 23129749659968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 23147235516480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record073_result⟩)
 (.leaf ⟨(19, 23147492425984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 23147494572032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 23147500814336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record076_result⟩)
 (.leaf ⟨(19, 23151528386624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 23154748039232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 23179713069056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record079_result⟩)
 (.leaf ⟨(19, 23211900158208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 23211902304256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 23211908546560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record082_result⟩)
 (.leaf ⟨(19, 23219155771456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 23219742654464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 23230984306752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record085_result⟩)
 (.leaf ⟨(19, 23247695397120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 23247755215104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 23247761522688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record088_result⟩)
 (.leaf ⟨(19, 23248164110400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 23248165150784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 23248298328064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record091_result⟩)
 (.leaf ⟨(19, 23248300408832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 23249841832192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 23251384803392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record094_result⟩)
 (.leaf ⟨(19, 23263179784256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 23266400477248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record096_result⟩)
 (.leaf ⟨(19, 23266417786888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 23280419356928), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record098_result⟩)
 (.leaf ⟨(19, 23280427745280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (3965 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 3965 4065 :=
  block_of_table results 3965 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0059
