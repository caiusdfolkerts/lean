module
prelude
import GraphInputsSix0Part00073Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1038
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 27756897239552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 27783240646656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record001_result⟩)
 (.leaf ⟨(32, 27798256255232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 27798313896064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 27799329472768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record004_result⟩)
 (.leaf ⟨(32, 27799354083456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 27800658575360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 27801434458240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record007_result⟩)
 (.leaf ⟨(32, 27801475907840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 27801500518528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 27801533548672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record010_result⟩)
 (.leaf ⟨(32, 27802738950144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 27807029674240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 27807095734528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record013_result⟩)
 (.leaf ⟨(32, 27811324690432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 27811333013504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 27814379128960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record016_result⟩)
 (.leaf ⟨(32, 27817565913088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 27868186869760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 27874673574144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record019_result⟩)
 (.leaf ⟨(32, 27903536463872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 27903666438400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record021_result⟩)
 (.leaf ⟨(32, 27903732498688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 27915242766336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record023_result⟩)
 (.leaf ⟨(32, 27915251089408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 27936772128768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 27936902103296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record026_result⟩)
 (.leaf ⟨(32, 27936910491648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 27937017708800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 27938918563840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record029_result⟩)
 (.leaf ⟨(32, 27939048538368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 27939050684416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 27939056926720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record032_result⟩)
 (.leaf ⟨(32, 27939098083584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 27941312398080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 27943258833152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record035_result⟩)
 (.leaf ⟨(32, 27943269042176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 27943661486144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 27943728586816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record038_result⟩)
 (.leaf ⟨(32, 27971269181440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 27971310338304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 28041076080896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record041_result⟩)
 (.leaf ⟨(32, 28041080242432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 28041080307712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 28041082323200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record044_result⟩)
 (.leaf ⟨(32, 28041182974208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 28047521628416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record046_result⟩)
 (.leaf ⟨(32, 28047785869568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 28047785934848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record048_result⟩)
 (.leaf ⟨(32, 28047826751552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 28048967602192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 28076495437824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record051_result⟩)
 (.leaf ⟨(32, 28076499013888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 28077681869056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 28077690257408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record054_result⟩)
 (.leaf ⟨(32, 28080790323456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 28080790388736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 28080791884032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record057_result⟩)
 (.leaf ⟨(32, 28081054564608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 28081054629888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 28081056125184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record060_result⟩)
 (.leaf ⟨(32, 28081179854864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 28082253594625), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 28085194391808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record063_result⟩)
 (.leaf ⟨(32, 28090568867840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 28111974498560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 28111982886912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record066_result⟩)
 (.leaf ⟨(32, 28116135248128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 28116143636480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 28116333428992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record069_result⟩)
 (.leaf ⟨(32, 28116539998208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 28117406646528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record071_result⟩)
 (.leaf ⟨(32, 28119956726016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 28124861497344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record073_result⟩)
 (.leaf ⟨(32, 28151501619456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 28152046813184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 28154315932416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record076_result⟩)
 (.leaf ⟨(32, 28177428648192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 28177692889344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 28177699180608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record079_result⟩)
 (.leaf ⟨(32, 28184138485824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 28193585102849), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 28247064641792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record082_result⟩)
 (.leaf ⟨(32, 28247337271296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 28247601512448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 28247609835520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record085_result⟩)
 (.leaf ⟨(32, 28249145016576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 28249417646080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 28249681887232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record088_result⟩)
 (.leaf ⟨(32, 28249690210304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 28249880068096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 28256624509184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record091_result⟩)
 (.leaf ⟨(32, 28257739145216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 28258275950592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 28262027788544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record094_result⟩)
 (.leaf ⟨(32, 28262362316800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 28262568820736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record096_result⟩)
 (.leaf ⟨(32, 28265214411008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 28265985613824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record098_result⟩)
 (.leaf ⟨(32, 28266597449728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00073.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (33913 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 33913 34013 :=
  block_of_table results 33913 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1038
