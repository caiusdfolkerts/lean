module
prelude
import GraphInputsSix0Part00068Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1033
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 48
 (.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 25307234963520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 25307367084096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record001_result⟩)
 (.leaf ⟨(32, 25307594670080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 25307596734528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 25307597774912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record004_result⟩)
 (.leaf ⟨(32, 25307631325248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 25308507934736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 25327577923840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record007_result⟩)
 (.leaf ⟨(32, 25327582085376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 25327582150656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 25327585726720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record010_result⟩)
 (.leaf ⟨(32, 25327716286720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 25327716352000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 25327717847296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record013_result⟩)
 (.leaf ⟨(32, 25327732801792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 25327732867072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 25327982088448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record016_result⟩)
 (.leaf ⟨(32, 25327984754688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 25327988379712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 25328105818128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record019_result⟩)
 (.leaf ⟨(32, 25328772858112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(32, 25328772923392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record021_result⟩)
 (.branch 23
 (.leaf ⟨(32, 25329041326080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record022_result⟩)
 (.leaf ⟨(32, 25329179557889), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(32, 25332279689280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record024_result⟩)
 (.branch 26
 (.leaf ⟨(32, 25332281249856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record025_result⟩)
 (.leaf ⟨(32, 25332398688272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(32, 25333472428033), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record027_result⟩)
 (.branch 29
 (.leaf ⟨(32, 25340720187408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record028_result⟩)
 (.leaf ⟨(32, 25340865429568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(32, 25340866990144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record030_result⟩)
 (.branch 32
 (.leaf ⟨(32, 25341793927169), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record031_result⟩)
 (.leaf ⟨(32, 25359790178560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(32, 25359794340096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record033_result⟩)
 (.branch 35
 (.leaf ⟨(32, 25359794405376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record034_result⟩)
 (.leaf ⟨(32, 25359797981440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(32, 25359930102016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record036_result⟩)
 (.branch 38
 (.leaf ⟨(32, 25360194343168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record037_result⟩)
 (.leaf ⟨(32, 25360200634432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(32, 25362076082176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record039_result⟩)
 (.branch 41
 (.leaf ⟨(32, 25362076537088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record040_result⟩)
 (.leaf ⟨(32, 25362340778240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(32, 25362344484864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record042_result⟩)
 (.branch 44
 (.leaf ⟨(32, 25362398447632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record043_result⟩)
 (.leaf ⟨(32, 25363061211392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record044_result⟩)))
 (.branch 46
 (.leaf ⟨(32, 25363132653568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record045_result⟩)
 (.branch 47
 (.leaf ⟨(32, 25363401056256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record046_result⟩)
 (.leaf ⟨(32, 25363472187393), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record047_result⟩)))))))
 (.branch 72
 (.branch 60
 (.branch 54
 (.branch 51
 (.branch 49
 (.leaf ⟨(32, 25363527794944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record048_result⟩)
 (.branch 50
 (.leaf ⟨(32, 25364601012480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record049_result⟩)
 (.leaf ⟨(32, 25366633648384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record050_result⟩)))
 (.branch 52
 (.leaf ⟨(32, 25366639419456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record051_result⟩)
 (.branch 53
 (.leaf ⟨(32, 25366639435776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record052_result⟩)
 (.leaf ⟨(32, 25366639939648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record053_result⟩))))
 (.branch 57
 (.branch 55
 (.leaf ⟨(32, 25366691317776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record054_result⟩)
 (.branch 56
 (.leaf ⟨(32, 25367722082560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record055_result⟩)
 (.leaf ⟨(32, 25367765057537), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record056_result⟩)))
 (.branch 58
 (.leaf ⟨(32, 25374880696336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record057_result⟩)
 (.branch 59
 (.leaf ⟨(32, 25375012816912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record058_result⟩)
 (.leaf ⟨(32, 25375225159744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record059_result⟩)))))
 (.branch 66
 (.branch 63
 (.branch 61
 (.leaf ⟨(32, 25375225176064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record060_result⟩)
 (.branch 62
 (.leaf ⟨(32, 25375225679936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record061_result⟩)
 (.leaf ⟨(32, 25375277058064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record062_result⟩)))
 (.branch 64
 (.leaf ⟨(32, 25375954436097), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record063_result⟩)
 (.branch 65
 (.leaf ⟨(32, 25376086556673), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record064_result⟩)
 (.leaf ⟨(32, 25376350797825), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record065_result⟩))))
 (.branch 69
 (.branch 67
 (.leaf ⟨(32, 25384901951488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record066_result⟩)
 (.branch 68
 (.leaf ⟨(32, 25398964453376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record067_result⟩)
 (.leaf ⟨(32, 25428515361024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record068_result⟩)))
 (.branch 70
 (.leaf ⟨(32, 25428918014016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record069_result⟩)
 (.branch 71
 (.leaf ⟨(32, 25430661796096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record070_result⟩)
 (.leaf ⟨(32, 25431058157824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record071_result⟩))))))
 (.branch 84
 (.branch 78
 (.branch 75
 (.branch 73
 (.leaf ⟨(32, 25431064449088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record072_result⟩)
 (.branch 74
 (.leaf ⟨(32, 25432146592000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record073_result⟩)
 (.leaf ⟨(32, 25443598075920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record074_result⟩)))
 (.branch 76
 (.leaf ⟨(32, 25443943059520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 25444671815681), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record076_result⟩)
 (.leaf ⟨(32, 25445031493696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record077_result⟩))))
 (.branch 81
 (.branch 79
 (.leaf ⟨(32, 25449326460928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 25496554324224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record079_result⟩)
 (.leaf ⟨(32, 25512676433984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record080_result⟩)))
 (.branch 82
 (.leaf ⟨(32, 25565950120192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 25565956411456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record082_result⟩)
 (.leaf ⟨(32, 25566088532032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record083_result⟩)))))
 (.branch 90
 (.branch 87
 (.branch 85
 (.leaf ⟨(32, 25566352773184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 25568096555264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record085_result⟩)
 (.leaf ⟨(32, 25568228675840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record086_result⟩)))
 (.branch 88
 (.leaf ⟨(32, 25568234967104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 25568499208256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record088_result⟩)
 (.leaf ⟨(32, 25569317110016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record089_result⟩))))
 (.branch 93
 (.branch 91
 (.leaf ⟨(32, 25572792078400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 25573880512576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record091_result⟩)
 (.leaf ⟨(32, 25578175479808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record092_result⟩)))
 (.branch 95
 (.branch 94
 (.leaf ⟨(32, 25581032835088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record093_result⟩)
 (.leaf ⟨(32, 25582106574849), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record094_result⟩))
 (.branch 96
 (.leaf ⟨(32, 25590657728512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record095_result⟩)
 (.leaf ⟨(32, 25633724842240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00068.record096_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (33439 + i))) 0 97 :=
  interval_of_check _ 0 97 (by decide +kernel)

public theorem complete : Block 33439 33536 :=
  block_of_table results 33439 97 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1033
