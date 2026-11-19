module
prelude
import GraphInputsRow28Part00011Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0431
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 38
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(28, 30873366855936), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record000_result⟩)
 (.leaf ⟨(28, 30873903726592), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record001_result⟩))
 (.branch 3
 (.leaf ⟨(28, 30874105028608), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record002_result⟩)
 (.leaf ⟨(28, 30875178246144), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(28, 30900687601664), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record004_result⟩)
 (.leaf ⟨(28, 30900955906048), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record005_result⟩))
 (.branch 7
 (.leaf ⟨(28, 30907139391488), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record006_result⟩)
 (.branch 8
 (.leaf ⟨(28, 30909537452544), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record007_result⟩)
 (.leaf ⟨(28, 30915245965312), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(28, 30915980951552), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record009_result⟩)
 (.leaf ⟨(28, 30969004359680), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record010_result⟩))
 (.branch 12
 (.leaf ⟨(28, 30969541165056), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record011_result⟩)
 (.branch 13
 (.leaf ⟨(28, 30977590099968), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record012_result⟩)
 (.leaf ⟨(28, 30977862664192), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(28, 30978259025920), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record014_result⟩)
 (.leaf ⟨(28, 30980405460992), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record015_result⟩))
 (.branch 17
 (.leaf ⟨(28, 30983963344896), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record016_result⟩)
 (.branch 18
 (.leaf ⟨(28, 31018322034688), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record017_result⟩)
 (.leaf ⟨(28, 31067680571648), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record018_result⟩))))))
 (.branch 28
 (.branch 23
 (.branch 21
 (.branch 20
 (.leaf ⟨(28, 31068451774464), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record019_result⟩)
 (.leaf ⟨(28, 31074122998016), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record020_result⟩))
 (.branch 22
 (.leaf ⟨(28, 31079525269632), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record021_result⟩)
 (.leaf ⟨(28, 31079860805632), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(28, 31080565457024), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record023_result⟩)
 (.leaf ⟨(28, 31080934023168), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record024_result⟩))
 (.branch 26
 (.leaf ⟨(28, 31082712932480), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record025_result⟩)
 (.branch 27
 (.leaf ⟨(28, 31114890723456), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record026_result⟩)
 (.leaf ⟨(28, 31115293229568), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record027_result⟩)))))
 (.branch 33
 (.branch 30
 (.branch 29
 (.leaf ⟨(28, 31200859160832), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record028_result⟩)
 (.leaf ⟨(28, 31224480415744), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record029_result⟩))
 (.branch 31
 (.leaf ⟨(28, 31337218056192), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record030_result⟩)
 (.branch 32
 (.leaf ⟨(28, 31337449267200), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record031_result⟩)
 (.leaf ⟨(28, 31346315493920), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record032_result⟩))))
 (.branch 35
 (.branch 34
 (.leaf ⟨(28, 31346316607488), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record033_result⟩)
 (.leaf ⟨(28, 31354906509312), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record034_result⟩))
 (.branch 36
 (.leaf ⟨(28, 31465207234560), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record035_result⟩)
 (.branch 37
 (.leaf ⟨(28, 31465735716864), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record036_result⟩)
 (.leaf ⟨(28, 31483796389888), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record037_result⟩)))))))
 (.branch 57
 (.branch 47
 (.branch 42
 (.branch 40
 (.branch 39
 (.leaf ⟨(28, 31491254394880), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record038_result⟩)
 (.leaf ⟨(28, 31492117889024), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record039_result⟩))
 (.branch 41
 (.leaf ⟨(28, 31492377936384), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record040_result⟩)
 (.leaf ⟨(28, 31492580311040), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record041_result⟩)))
 (.branch 44
 (.branch 43
 (.leaf ⟨(28, 31499324817408), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record042_result⟩)
 (.leaf ⟨(28, 31512451940352), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record043_result⟩))
 (.branch 45
 (.leaf ⟨(28, 31521310244864), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record044_result⟩)
 (.branch 46
 (.leaf ⟨(28, 31525613601280), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record045_result⟩)
 (.leaf ⟨(28, 31529631744000), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record046_result⟩)))))
 (.branch 52
 (.branch 49
 (.branch 48
 (.leaf ⟨(28, 31530160226304), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record047_result⟩)
 (.leaf ⟨(28, 31533650083840), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record048_result⟩))
 (.branch 50
 (.leaf ⟨(28, 31568085123072), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record049_result⟩)
 (.branch 51
 (.leaf ⟨(28, 31620103413760), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record050_result⟩)
 (.leaf ⟨(28, 31628156477568), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record051_result⟩))))
 (.branch 54
 (.branch 53
 (.leaf ⟨(28, 31750684213248), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record052_result⟩)
 (.leaf ⟨(28, 31774168195072), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record053_result⟩))
 (.branch 55
 (.leaf ⟨(28, 31964295921664), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record054_result⟩)
 (.branch 56
 (.leaf ⟨(28, 31972881661952), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record055_result⟩)
 (.leaf ⟨(28, 31973616648192), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record056_result⟩))))))
 (.branch 67
 (.branch 62
 (.branch 59
 (.branch 58
 (.leaf ⟨(28, 32041599041536), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record057_result⟩)
 (.leaf ⟨(28, 32042135846912), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record058_result⟩))
 (.branch 60
 (.leaf ⟨(28, 32042201907200), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record059_result⟩)
 (.branch 61
 (.leaf ⟨(28, 32044785664000), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record060_result⟩)
 (.leaf ⟨(28, 32075371511808), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record061_result⟩))))
 (.branch 64
 (.branch 63
 (.leaf ⟨(28, 32077105856512), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record062_result⟩)
 (.leaf ⟨(28, 32161858093312), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record063_result⟩))
 (.branch 65
 (.leaf ⟨(28, 32173634682880), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record064_result⟩)
 (.branch 66
 (.leaf ⟨(28, 32186519535616), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record065_result⟩)
 (.leaf ⟨(28, 32220844802048), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record066_result⟩)))))
 (.branch 72
 (.branch 69
 (.branch 68
 (.leaf ⟨(28, 32255204532224), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record067_result⟩)
 (.leaf ⟨(28, 32351975374848), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record068_result⟩))
 (.branch 70
 (.leaf ⟨(28, 32474524614656), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record069_result⟩)
 (.branch 71
 (.leaf ⟨(28, 32547807428608), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record070_result⟩)
 (.leaf ⟨(28, 32564978909184), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record071_result⟩))))
 (.branch 74
 (.branch 73
 (.leaf ⟨(28, 32644444192768), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record072_result⟩)
 (.leaf ⟨(28, 32693827928064), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record073_result⟩))
 (.branch 75
 (.leaf ⟨(28, 32749402456064), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record074_result⟩)
 (.branch 76
 (.leaf ⟨(28, 32758252437504), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record075_result⟩)
 (.leaf ⟨(28, 32781614710784), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00011.record076_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20300 + i))) 0 77 :=
  interval_of_check _ 0 77 (by decide +kernel)

public theorem complete : Block 20300 20377 :=
  block_of_table results 20300 77 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0431
