module
prelude
import GraphInputsSix0Part00069Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1034
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 42
 (.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(32, 25634244141120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record000_result⟩)
 (.leaf ⟨(32, 25641525452864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record001_result⟩))
 (.branch 3
 (.leaf ⟨(32, 25658186022912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record002_result⟩)
 (.branch 4
 (.leaf ⟨(32, 25659208507456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record003_result⟩)
 (.leaf ⟨(32, 25659275624448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(32, 25659277705216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record005_result⟩)
 (.leaf ⟨(32, 25659409695232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record006_result⟩))
 (.branch 8
 (.leaf ⟨(32, 25702244040960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record007_result⟩)
 (.branch 9
 (.leaf ⟨(32, 25702252429312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record008_result⟩)
 (.leaf ⟨(32, 25702310101248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(32, 25702312247296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record010_result⟩)
 (.leaf ⟨(32, 25702318489600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record011_result⟩))
 (.branch 13
 (.leaf ⟨(32, 25702359646464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 25702369855488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record013_result⟩)
 (.leaf ⟨(32, 25702712754240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(32, 25702714851328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 25702762299456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record016_result⟩)
 (.leaf ⟨(32, 25702829400128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(32, 25704976613952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 25705480208640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record019_result⟩)
 (.leaf ⟨(32, 25705490417664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record020_result⟩))))))
 (.branch 31
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 25705531899904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record021_result⟩)
 (.leaf ⟨(32, 25705556477952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 25705933447232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record023_result⟩)
 (.branch 25
 (.leaf ⟨(32, 25705934503936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record024_result⟩)
 (.leaf ⟨(32, 25705949962304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record025_result⟩))))
 (.branch 28
 (.branch 27
 (.leaf ⟨(32, 25706654335744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record026_result⟩)
 (.leaf ⟨(32, 25707056988736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record027_result⟩))
 (.branch 29
 (.leaf ⟨(32, 25718365110336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 25718432211008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record029_result⟩)
 (.leaf ⟨(32, 25718435088384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record030_result⟩)))))
 (.branch 36
 (.branch 33
 (.branch 32
 (.leaf ⟨(32, 25735595311360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record031_result⟩)
 (.leaf ⟨(32, 25735597457408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record032_result⟩))
 (.branch 34
 (.leaf ⟨(32, 25735603699712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record033_result⟩)
 (.branch 35
 (.leaf ⟨(32, 25735605520384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record034_result⟩)
 (.leaf ⟨(32, 25735997964352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record035_result⟩))))
 (.branch 39
 (.branch 37
 (.leaf ⟨(32, 25736115390528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record036_result⟩)
 (.branch 38
 (.leaf ⟨(32, 25739873356032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record037_result⟩)
 (.leaf ⟨(32, 25739881744384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(32, 25739890000640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record039_result⟩)
 (.branch 41
 (.leaf ⟨(32, 25740276009024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record040_result⟩)
 (.leaf ⟨(32, 25740292653632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record041_result⟩)))))))
 (.branch 63
 (.branch 52
 (.branch 47
 (.branch 44
 (.branch 43
 (.leaf ⟨(32, 25740410094088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record042_result⟩)
 (.leaf ⟨(32, 25752760354816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record043_result⟩))
 (.branch 45
 (.leaf ⟨(32, 25769887940864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record044_result⟩)
 (.branch 46
 (.leaf ⟨(32, 25769890086912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record045_result⟩)
 (.leaf ⟨(32, 25769896329216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record046_result⟩))))
 (.branch 49
 (.branch 48
 (.leaf ⟨(32, 25769898149888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record047_result⟩)
 (.leaf ⟨(32, 25769964210176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record048_result⟩))
 (.branch 50
 (.leaf ⟨(32, 25770005367040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record049_result⟩)
 (.branch 51
 (.leaf ⟨(32, 25770357694528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record050_result⟩)
 (.leaf ⟨(32, 25770360571904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record051_result⟩)))))
 (.branch 57
 (.branch 54
 (.branch 53
 (.leaf ⟨(32, 25770408020032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record052_result⟩)
 (.leaf ⟨(32, 25772085610752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record053_result⟩))
 (.branch 55
 (.leaf ⟨(32, 25772093999104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record054_result⟩)
 (.branch 56
 (.leaf ⟨(32, 25772102255360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record055_result⟩)
 (.leaf ⟨(32, 25772488263744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record056_result⟩))))
 (.branch 60
 (.branch 58
 (.leaf ⟨(32, 25772504908352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record057_result⟩)
 (.branch 59
 (.leaf ⟨(32, 25772622348808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record058_result⟩)
 (.leaf ⟨(32, 25774174373888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record059_result⟩)))
 (.branch 61
 (.leaf ⟨(32, 25774702723592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record060_result⟩)
 (.branch 62
 (.leaf ⟨(32, 25787052984320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record061_result⟩)
 (.leaf ⟨(32, 25787184972296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record062_result⟩))))))
 (.branch 73
 (.branch 68
 (.branch 65
 (.branch 64
 (.leaf ⟨(32, 25839653683456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record063_result⟩)
 (.leaf ⟨(32, 25839657844992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record064_result⟩))
 (.branch 66
 (.leaf ⟨(32, 25839657910272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 25839659925760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record066_result⟩)
 (.leaf ⟨(32, 25839752773888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record067_result⟩))))
 (.branch 70
 (.branch 69
 (.leaf ⟨(32, 25839756935424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record068_result⟩)
 (.leaf ⟨(32, 25839757000704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record069_result⟩))
 (.branch 71
 (.leaf ⟨(32, 25839760576768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record070_result⟩)
 (.branch 72
 (.leaf ⟨(32, 25839891136768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record071_result⟩)
 (.leaf ⟨(32, 25839891202048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record072_result⟩)))))
 (.branch 78
 (.branch 75
 (.branch 74
 (.leaf ⟨(32, 25839892697344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record073_result⟩)
 (.leaf ⟨(32, 25840156938496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record074_result⟩))
 (.branch 76
 (.leaf ⟨(32, 25840159604736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 25840163229760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record076_result⟩)
 (.leaf ⟨(32, 25840280668176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record077_result⟩))))
 (.branch 81
 (.branch 79
 (.leaf ⟨(32, 25843112349952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 25843112415232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record079_result⟩)
 (.leaf ⟨(32, 25843376591104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record080_result⟩)))
 (.branch 82
 (.leaf ⟨(32, 25843376656384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 25843384455184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record082_result⟩)
 (.leaf ⟨(32, 25843401230352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00069.record083_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (33536 + i))) 0 84 :=
  interval_of_check _ 0 84 (by decide +kernel)

public theorem complete : Block 33536 33620 :=
  block_of_table results 33536 84 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1034
