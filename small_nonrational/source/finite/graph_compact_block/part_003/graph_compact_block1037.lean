module
prelude
import GraphInputsSix0Part00072Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1037
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 46
 (.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(32, 27527865270272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record000_result⟩)
 (.leaf ⟨(32, 27527867285760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record001_result⟩))
 (.branch 3
 (.leaf ⟨(32, 27529008124160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record002_result⟩)
 (.branch 4
 (.leaf ⟨(32, 27532021793024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record003_result⟩)
 (.leaf ⟨(32, 27532025954560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(32, 27532026019840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record005_result⟩)
 (.branch 7
 (.leaf ⟨(32, 27532028035328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record006_result⟩)
 (.leaf ⟨(32, 27532160155904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(32, 27532160221184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record008_result⟩)
 (.branch 10
 (.leaf ⟨(32, 27532424397056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record009_result⟩)
 (.leaf ⟨(32, 27532424462336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(32, 27532430688320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record011_result⟩)
 (.branch 13
 (.leaf ⟨(32, 27532497788992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record012_result⟩)
 (.leaf ⟨(32, 27533300994304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(32, 27535447429376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record014_result⟩)
 (.branch 16
 (.leaf ⟨(32, 27540745896192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record015_result⟩)
 (.leaf ⟨(32, 27562294124800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(32, 27566518845696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record017_result⟩)
 (.branch 19
 (.leaf ⟨(32, 27575104585984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record018_result⟩)
 (.leaf ⟨(32, 27597719273728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(32, 27602290999297), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record020_result⟩)
 (.branch 22
 (.leaf ⟨(32, 27618051162112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record021_result⟩)
 (.leaf ⟨(32, 27618059485184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record022_result⟩))))))
 (.branch 34
 (.branch 28
 (.branch 25
 (.branch 24
 (.leaf ⟨(32, 27632288665664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record023_result⟩)
 (.leaf ⟨(32, 27635104104704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record024_result⟩))
 (.branch 26
 (.leaf ⟨(32, 27635506757696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 27636581535808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record026_result⟩)
 (.leaf ⟨(32, 27643689844992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record027_result⟩))))
 (.branch 31
 (.branch 29
 (.leaf ⟨(32, 27643689910272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 27645167276096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record029_result⟩)
 (.leaf ⟨(32, 27663215427840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record030_result⟩)))
 (.branch 32
 (.leaf ⟨(32, 27663223816192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 27663483830528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record032_result⟩)
 (.leaf ⟨(32, 27663494299648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record033_result⟩)))))
 (.branch 40
 (.branch 37
 (.branch 35
 (.leaf ⟨(32, 27663618031872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 27665163682048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record035_result⟩)
 (.leaf ⟨(32, 27665172070400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record036_result⟩)))
 (.branch 38
 (.leaf ⟨(32, 27665295802624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 27665304190976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record038_result⟩)
 (.leaf ⟨(32, 27665564205312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record039_result⟩))))
 (.branch 43
 (.branch 41
 (.leaf ⟨(32, 27665568432128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 27665574674432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record041_result⟩)
 (.leaf ⟨(32, 27665764466944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record042_result⟩)))
 (.branch 44
 (.leaf ⟨(32, 27669859156224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 27669867544576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record044_result⟩)
 (.leaf ⟨(32, 27669925216512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record045_result⟩)))))))
 (.branch 69
 (.branch 57
 (.branch 51
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 27671536926976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record046_result⟩)
 (.leaf ⟨(32, 27672073797632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 27672082120704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record048_result⟩)
 (.branch 50
 (.leaf ⟨(32, 27674154172416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record049_result⟩)
 (.leaf ⟨(32, 27678246715648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record050_result⟩))))
 (.branch 54
 (.branch 52
 (.leaf ⟨(32, 27678453284864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record051_result⟩)
 (.branch 53
 (.leaf ⟨(32, 27678649368640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record052_result⟩)
 (.leaf ⟨(32, 27680395296768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record053_result⟩)))
 (.branch 55
 (.leaf ⟨(32, 27681870061632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record054_result⟩)
 (.branch 56
 (.leaf ⟨(32, 27682351874048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record055_result⟩)
 (.leaf ⟨(32, 27682475671552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record056_result⟩)))))
 (.branch 63
 (.branch 60
 (.branch 58
 (.leaf ⟨(32, 27682483994624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record057_result⟩)
 (.branch 59
 (.leaf ⟨(32, 27686502154496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record058_result⟩)
 (.leaf ⟨(32, 27686636421120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record059_result⟩)))
 (.branch 61
 (.leaf ⟨(32, 27686644744192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record060_result⟩)
 (.branch 62
 (.leaf ⟨(32, 27687039025152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record061_result⟩)
 (.leaf ⟨(32, 27687105085440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record062_result⟩))))
 (.branch 66
 (.branch 64
 (.leaf ⟨(32, 27689688776960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record063_result⟩)
 (.branch 65
 (.leaf ⟨(32, 27689756983296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record064_result⟩)
 (.leaf ⟨(32, 27689765306368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record065_result⟩)))
 (.branch 67
 (.leaf ⟨(32, 27690225647616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record066_result⟩)
 (.branch 68
 (.leaf ⟨(32, 27697508057344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record067_result⟩)
 (.leaf ⟨(32, 27697776460032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record068_result⟩))))))
 (.branch 81
 (.branch 75
 (.branch 72
 (.branch 70
 (.leaf ⟨(32, 27697786929152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record069_result⟩)
 (.branch 71
 (.leaf ⟨(32, 27704226234368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record070_result⟩)
 (.leaf ⟨(32, 27712547733504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record071_result⟩)))
 (.branch 73
 (.leaf ⟨(32, 27721969238016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record072_result⟩)
 (.branch 74
 (.leaf ⟨(32, 27721977561088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record073_result⟩)
 (.leaf ⟨(32, 27730743722240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record074_result⟩))))
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 27730752110592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 27730859327744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record076_result⟩)
 (.leaf ⟨(32, 27731012124928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 27731016351744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 27731022594048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record079_result⟩)
 (.leaf ⟨(32, 27731127730432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record080_result⟩)))))
 (.branch 87
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 27731140020224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 27731261931776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record082_result⟩)
 (.leaf ⟨(32, 27735426662400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 27737461899264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 27737503056128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record085_result⟩)
 (.leaf ⟨(32, 27745824555264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record086_result⟩))))
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 27746047639552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 27748441522752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record088_result⟩)
 (.leaf ⟨(32, 27756226298112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 27756360564736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 27756368887808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record091_result⟩)
 (.leaf ⟨(32, 27756763168768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072.record092_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (33820 + i))) 0 93 :=
  interval_of_check _ 0 93 (by decide +kernel)

public theorem complete : Block 33820 33913 :=
  block_of_table results 33820 93 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1037
