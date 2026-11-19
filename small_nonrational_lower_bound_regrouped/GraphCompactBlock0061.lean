module
prelude
import GraphInputsRow19Part00021Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0061
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 46
 (.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(19, 23425894727936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record000_result⟩)
 (.leaf ⟨(19, 23425894793216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record001_result⟩))
 (.branch 3
 (.leaf ⟨(19, 23425901019200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record002_result⟩)
 (.branch 4
 (.leaf ⟨(19, 23425902969920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record003_result⟩)
 (.leaf ⟨(19, 23425968119872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(19, 23425968136192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record005_result⟩)
 (.branch 7
 (.leaf ⟨(19, 23429081350400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record006_result⟩)
 (.leaf ⟨(19, 23429081415680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(19, 23429088682048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record008_result⟩)
 (.branch 10
 (.leaf ⟨(19, 23429088698368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record009_result⟩)
 (.leaf ⟨(19, 23434710032448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(19, 23436044369984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record011_result⟩)
 (.branch 13
 (.leaf ⟨(19, 23442486796352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record012_result⟩)
 (.leaf ⟨(19, 23453492592640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(19, 23459196846336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record014_result⟩)
 (.branch 16
 (.leaf ⟨(19, 23461301847104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record015_result⟩)
 (.leaf ⟨(19, 23461797299264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(19, 23468263645248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record017_result⟩)
 (.branch 19
 (.leaf ⟨(19, 23470125811776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record018_result⟩)
 (.leaf ⟨(19, 23484956852232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(19, 23503228190784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record020_result⟩)
 (.branch 22
 (.leaf ⟨(19, 23504763830336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record021_result⟩)
 (.leaf ⟨(19, 23504764870720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record022_result⟩))))))
 (.branch 34
 (.branch 28
 (.branch 25
 (.branch 24
 (.leaf ⟨(19, 23506911305792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record023_result⟩)
 (.leaf ⟨(19, 23522076794944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record024_result⟩))
 (.branch 26
 (.leaf ⟨(19, 23522077851648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 23525725446208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record026_result⟩)
 (.leaf ⟨(19, 23525752770560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record027_result⟩))))
 (.branch 31
 (.branch 29
 (.leaf ⟨(19, 23525759012864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 23526221808704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record029_result⟩)
 (.leaf ⟨(19, 23731071156480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record030_result⟩)))
 (.branch 32
 (.leaf ⟨(19, 23731339559168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 23731351068672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record032_result⟩)
 (.leaf ⟨(19, 23763655655424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record033_result⟩)))))
 (.branch 40
 (.branch 37
 (.branch 35
 (.leaf ⟨(19, 23766776217600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 23766784540672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record035_result⟩)
 (.leaf ⟨(19, 23795252347136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record036_result⟩)))
 (.branch 38
 (.leaf ⟨(19, 23795252412416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 23795789217792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record038_result⟩)
 (.leaf ⟨(19, 23932718055680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record039_result⟩))))
 (.branch 43
 (.branch 41
 (.leaf ⟨(19, 23937095336192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 23971290547456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record041_result⟩)
 (.leaf ⟨(19, 23971290612736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record042_result⟩)))
 (.branch 44
 (.leaf ⟨(19, 23971491807232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 23971563045380), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record044_result⟩)
 (.leaf ⟨(19, 23971563175937), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record045_result⟩)))))))
 (.branch 69
 (.branch 57
 (.branch 51
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 23972531994624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record046_result⟩)
 (.leaf ⟨(19, 23984331587840), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 23987947602176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record048_result⟩)
 (.branch 50
 (.leaf ⟨(19, 24004635140096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record049_result⟩)
 (.leaf ⟨(19, 24004866351104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record050_result⟩))))
 (.branch 54
 (.branch 52
 (.leaf ⟨(19, 24005377789984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record051_result⟩)
 (.branch 53
 (.leaf ⟨(19, 24005713232128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record052_result⟩)
 (.leaf ⟨(19, 24005717458944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record053_result⟩)))
 (.branch 55
 (.leaf ⟨(19, 24005725651968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record054_result⟩)
 (.branch 56
 (.leaf ⟨(19, 24005914534144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record055_result⟩)
 (.leaf ⟨(19, 24005922922496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record056_result⟩)))))
 (.branch 63
 (.branch 60
 (.branch 58
 (.leaf ⟨(19, 24005923832832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record057_result⟩)
 (.branch 59
 (.leaf ⟨(19, 24005981504256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record058_result⟩)
 (.leaf ⟨(19, 24006188073984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record059_result⟩)))
 (.branch 61
 (.leaf ⟨(19, 24006451266080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record060_result⟩)
 (.branch 62
 (.leaf ⟨(19, 24021353693184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record061_result⟩)
 (.leaf ⟨(19, 24024474255360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record062_result⟩))))
 (.branch 66
 (.branch 64
 (.leaf ⟨(19, 24025250201600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record063_result⟩)
 (.branch 65
 (.leaf ⟨(19, 24025787006976), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record064_result⟩)
 (.leaf ⟨(19, 24041356394496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record065_result⟩)))
 (.branch 67
 (.leaf ⟨(19, 24042430005248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record066_result⟩)
 (.branch 68
 (.leaf ⟨(19, 24042958487552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record067_result⟩)
 (.leaf ⟨(19, 24226053046592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record068_result⟩))))))
 (.branch 80
 (.branch 74
 (.branch 71
 (.branch 70
 (.leaf ⟨(19, 24232763875648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record069_result⟩)
 (.leaf ⟨(19, 24238414119168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record070_result⟩))
 (.branch 72
 (.leaf ⟨(19, 24238416265216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record071_result⟩)
 (.branch 73
 (.leaf ⟨(19, 24238422507520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record072_result⟩)
 (.leaf ⟨(19, 24250771578944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record073_result⟩))))
 (.branch 77
 (.branch 75
 (.leaf ⟨(19, 24251299020864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record074_result⟩)
 (.branch 76
 (.leaf ⟨(19, 24251301117952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record075_result⟩)
 (.leaf ⟨(19, 24270634762240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record076_result⟩)))
 (.branch 78
 (.leaf ⟨(19, 24302821851392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record077_result⟩)
 (.branch 79
 (.leaf ⟨(19, 24302823997440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record078_result⟩)
 (.leaf ⟨(19, 24302830239744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record079_result⟩)))))
 (.branch 86
 (.branch 83
 (.branch 81
 (.leaf ⟨(19, 24315225505792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record080_result⟩)
 (.branch 82
 (.leaf ⟨(19, 24318167752768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record081_result⟩)
 (.leaf ⟨(19, 24319248007168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record082_result⟩)))
 (.branch 84
 (.leaf ⟨(19, 24319250022656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record083_result⟩)
 (.branch 85
 (.leaf ⟨(19, 24319250087936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record084_result⟩)
 (.leaf ⟨(19, 24319251973376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record085_result⟩))))
 (.branch 89
 (.branch 87
 (.leaf ⟨(19, 24319258264640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record086_result⟩)
 (.branch 88
 (.leaf ⟨(19, 24319392481281), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record087_result⟩)
 (.leaf ⟨(19, 24319450154240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record088_result⟩)))
 (.branch 90
 (.leaf ⟨(19, 24319455535168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record089_result⟩)
 (.branch 91
 (.leaf ⟨(19, 24319455551488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record090_result⟩)
 (.leaf ⟨(19, 24319456445504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record091_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (4164 + i))) 0 92 :=
  interval_of_check _ 0 92 (by decide +kernel)

public theorem complete : Block 4164 4256 :=
  block_of_table results 4164 92 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0061
