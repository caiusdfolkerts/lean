module
prelude
import GraphInputsRow23Part00004Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0082
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 7598065715456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 7598074103808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record001_result⟩)
 (.leaf ⟨(23, 7598082360064), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(23, 7598090813440), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record003_result⟩)
 (.branch 5
 (.leaf ⟨(23, 7598355054592), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record004_result⟩)
 (.leaf ⟨(23, 7598363377664), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(23, 7598602453512), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 7598602780672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record007_result⟩)
 (.leaf ⟨(23, 7607200776192), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(23, 7611085029376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record009_result⟩)
 (.branch 11
 (.leaf ⟨(23, 7611237826560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record010_result⟩)
 (.leaf ⟨(23, 7611241988096), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(23, 7611353432064), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record012_result⟩)
 (.branch 14
 (.leaf ⟨(23, 7615782322688), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record013_result⟩)
 (.leaf ⟨(23, 7619410460672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(23, 7620079386624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 7623567082496), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record016_result⟩)
 (.leaf ⟨(23, 7623567147008), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(23, 7623843774464), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record018_result⟩)
 (.branch 20
 (.leaf ⟨(23, 7624103952384), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record019_result⟩)
 (.leaf ⟨(23, 7624372256768), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(23, 7699980910848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record021_result⟩)
 (.leaf ⟨(23, 7702523707648), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record022_result⟩))
 (.branch 24
 (.leaf ⟨(23, 7735412556032), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record023_result⟩)
 (.leaf ⟨(23, 7749876350976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(23, 7784168980480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record025_result⟩)
 (.branch 27
 (.leaf ⟨(23, 7821945012224), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record026_result⟩)
 (.leaf ⟨(23, 7821953335296), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(23, 7890538594304), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record028_result⟩)
 (.branch 30
 (.leaf ⟨(23, 7989924757504), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record029_result⟩)
 (.leaf ⟨(23, 8019387613184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(23, 8041454141696), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record031_result⟩)
 (.branch 33
 (.leaf ⟨(23, 8046155726848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record032_result⟩)
 (.leaf ⟨(23, 8046164049920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(23, 8066754953216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record034_result⟩)
 (.branch 36
 (.leaf ⟨(23, 8156822372352), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record035_result⟩)
 (.leaf ⟨(23, 8164871307264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(23, 8165540233216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record037_result⟩)
 (.branch 39
 (.leaf ⟨(23, 8173465370624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record038_result⟩)
 (.leaf ⟨(23, 8173993852928), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(23, 8179903693056), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record040_result⟩)
 (.branch 42
 (.leaf ⟨(23, 8184337072128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record041_result⟩)
 (.leaf ⟨(23, 8184873877504), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(23, 8188497821696), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record043_result⟩)
 (.branch 45
 (.leaf ⟨(23, 8189034627072), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record044_result⟩)
 (.leaf ⟨(23, 8197083561984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(23, 8197356126208), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record046_result⟩)
 (.leaf ⟨(23, 8197752487936), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record047_result⟩))
 (.branch 49
 (.leaf ⟨(23, 8203456806912), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record048_result⟩)
 (.leaf ⟨(23, 8247570956288), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(23, 8250926370816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record050_result⟩)
 (.branch 52
 (.leaf ⟨(23, 8251190611968), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record051_result⟩)
 (.leaf ⟨(23, 8252288991232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(23, 8265171763200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record053_result⟩)
 (.branch 55
 (.leaf ⟨(23, 8265274494976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record054_result⟩)
 (.leaf ⟨(23, 8324209246208), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(23, 8325265817600), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record056_result⟩)
 (.branch 58
 (.leaf ⟨(23, 8325534121984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record057_result⟩)
 (.leaf ⟨(23, 8332799148032), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(23, 8332802789376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record059_result⟩)
 (.branch 61
 (.leaf ⟨(23, 8334119862272), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record060_result⟩)
 (.leaf ⟨(23, 8334128185344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(23, 8341632385024), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record062_result⟩)
 (.branch 64
 (.leaf ⟨(23, 8402713444352), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record063_result⟩)
 (.leaf ⟨(23, 8402837241856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(23, 8406056894464), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record065_result⟩)
 (.branch 67
 (.leaf ⟨(23, 8474784169984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record066_result⟩)
 (.leaf ⟨(23, 8526064288000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(23, 8526076317696), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record068_result⟩)
 (.branch 70
 (.leaf ⟨(23, 8534905913344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record069_result⟩)
 (.leaf ⟨(23, 8538954928128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(23, 8539066339456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record071_result⟩)
 (.leaf ⟨(23, 8539883962368), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record072_result⟩))
 (.branch 74
 (.leaf ⟨(23, 8547790766080), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record073_result⟩)
 (.leaf ⟨(23, 8615842873344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(23, 8616509702656), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record075_result⟩)
 (.branch 77
 (.leaf ⟨(23, 8727398844416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record076_result⟩)
 (.leaf ⟨(23, 8727935844352), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(23, 8731945402368), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record078_result⟩)
 (.branch 80
 (.leaf ⟨(23, 8736525516800), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record079_result⟩)
 (.leaf ⟨(23, 8740803706880), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(23, 8744574451712), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record081_result⟩)
 (.branch 83
 (.leaf ⟨(23, 8745090418688), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record082_result⟩)
 (.leaf ⟨(23, 8745358983168), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(23, 8749125206016), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record084_result⟩)
 (.branch 86
 (.leaf ⟨(23, 8749653688320), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record085_result⟩)
 (.leaf ⟨(23, 8757975187456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(23, 8840733098048), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record087_result⟩)
 (.branch 89
 (.leaf ⟨(23, 8906432675840), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record088_result⟩)
 (.leaf ⟨(23, 8910593425408), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(23, 8918914924544), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record090_result⟩)
 (.branch 92
 (.leaf ⟨(23, 8944849354816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record091_result⟩)
 (.leaf ⟨(23, 8979310804992), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(23, 8987632304128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record093_result⟩)
 (.branch 95
 (.leaf ⟨(23, 9125067063296), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record094_result⟩)
 (.leaf ⟨(23, 9125073272960), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(23, 9424848650240), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record096_result⟩)
 (.leaf ⟨(23, 9433438519424), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record097_result⟩))
 (.branch 99
 (.leaf ⟨(23, 9502151770112), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record098_result⟩)
 (.leaf ⟨(23, 9502157979776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (5938 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 5938 6038 :=
  block_of_table results 5938 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0082
