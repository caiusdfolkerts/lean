module
prelude
import GraphInputsSix0Part00015Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0980
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 6511841804544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 6511854094336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record001_result⟩)
 (.leaf ⟨(32, 6511976005888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 6516140736512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 6516270695168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record004_result⟩)
 (.leaf ⟨(32, 6524055519488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 6524592390144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 6524600713216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record007_result⟩)
 (.leaf ⟨(32, 6535069630720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 6535606501376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 6541310755072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record010_result⟩)
 (.leaf ⟨(32, 6547816120576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 6548088750080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 6548352991232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record013_result⟩)
 (.leaf ⟨(32, 6548361314304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 6549896495360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 6550631546880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record016_result⟩)
 (.leaf ⟨(32, 6558490624000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 6559027429376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 6600398029184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record019_result⟩)
 (.leaf ⟨(32, 6600462008704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 6600464089472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record021_result⟩)
 (.leaf ⟨(32, 6633730703744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 6633732784512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record023_result⟩)
 (.leaf ⟨(32, 6634787275136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 6634789355904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 6635063968000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record026_result⟩)
 (.leaf ⟨(32, 6635332403328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 6636018622848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 6637012222208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record029_result⟩)
 (.leaf ⟨(32, 6637075194240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 6637144342784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 6637210403072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record032_result⟩)
 (.leaf ⟨(32, 6637412778112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 6638555725840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 6641707729024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record035_result⟩)
 (.leaf ⟨(32, 6644928970768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 6649890832640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 6649895026816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record038_result⟩)
 (.leaf ⟨(32, 6650029228160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 6650092134656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 6650095288448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record041_result⟩)
 (.leaf ⟨(32, 6671503032576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 6671771467904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 6671975940128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record044_result⟩)
 (.leaf ⟨(32, 6672848355344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 6675663782144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record046_result⟩)
 (.leaf ⟨(32, 6675865084160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 6676066418816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record048_result⟩)
 (.leaf ⟨(32, 6676136689696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 6677141225488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 6679287660560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record051_result⟩)
 (.leaf ⟨(32, 6684249522432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 6684253716608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 6684384764160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record054_result⟩)
 (.leaf ⟨(32, 6684387917952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 6684455018624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 6684458188832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record057_result⟩)
 (.leaf ⟨(32, 6701436731400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 6701511180544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 6701513261312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record060_result⟩)
 (.leaf ⟨(32, 6701514301696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 6701568851976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 6701781664000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record063_result⟩)
 (.leaf ⟨(32, 6707409355008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 6707409420288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 6711301701888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record066_result⟩)
 (.leaf ⟨(32, 6711570104576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 6711570169856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 6711704305920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record069_result⟩)
 (.leaf ⟨(32, 6713650479360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 6726736683072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record071_result⟩)
 (.leaf ⟨(32, 6727061897472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 6727061962752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record073_result⟩)
 (.leaf ⟨(32, 6727065928960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 6727198114048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 6727206436865), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record076_result⟩)
 (.leaf ⟨(32, 6727206502400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 6727404683264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 6727598637312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record079_result⟩)
 (.leaf ⟨(32, 6727607025664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 6744854069280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 6752966902016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record082_result⟩)
 (.leaf ⟨(32, 6752973176960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 6753175568416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 6780019081472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record085_result⟩)
 (.leaf ⟨(32, 6780287484160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 6780287549440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 6780289564928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record088_result⟩)
 (.leaf ⟨(32, 6782165516544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 6782367858944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 6788609048576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record091_result⟩)
 (.leaf ⟨(32, 6788611064064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 6789013717056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 6790396870656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record094_result⟩)
 (.leaf ⟨(32, 6791161192512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 6791486406912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record096_result⟩)
 (.leaf ⟨(32, 6791486472192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 6791622623488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record098_result⟩)
 (.leaf ⟨(32, 6791630946305), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (28286 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 28286 28386 :=
  block_of_table results 28286 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0980
