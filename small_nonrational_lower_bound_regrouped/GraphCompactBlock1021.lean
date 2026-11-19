module
prelude
import GraphInputsSix0Part00056Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1021
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 21383165772352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 21401822175296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record001_result⟩)
 (.leaf ⟨(32, 21401889292288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 21401891373056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 21402023363072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record004_result⟩)
 (.leaf ⟨(32, 21441611382912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 21441710473344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 21444931686528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record007_result⟩)
 (.leaf ⟨(32, 21444948201600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 21446021677696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 21446025838848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record010_result⟩)
 (.leaf ⟨(32, 21446025904128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 21446153797888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 21446157959424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record013_result⟩)
 (.leaf ⟨(32, 21446158024704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 21446160040192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 21446260691200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record016_result⟩)
 (.leaf ⟨(32, 21446663344192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 21450452910336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 21450452975616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record019_result⟩)
 (.leaf ⟨(32, 21450553561344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 21450717151488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record021_result⟩)
 (.leaf ⟨(32, 21450717216768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 21450723442752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record023_result⟩)
 (.leaf ⟨(32, 21450824093760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 21454045319184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 21459139301632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record026_result⟩)
 (.leaf ⟨(32, 21513781182720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 21513785344256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 21513785409536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record029_result⟩)
 (.leaf ⟨(32, 21513788985600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 21514309077008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 21514837754112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record032_result⟩)
 (.leaf ⟨(32, 21514841915648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 21514841980928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 21514971840768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record035_result⟩)
 (.leaf ⟨(32, 21515382816769), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 21518080295168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 21518080360448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record038_result⟩)
 (.leaf ⟨(32, 21518081855744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 21518344536320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 21518344601600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record041_result⟩)
 (.leaf ⟨(32, 21518346096896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 21518352388160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 21518469826576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record044_result⟩)
 (.leaf ⟨(32, 21519543566337), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 21522752766208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record046_result⟩)
 (.leaf ⟨(32, 21557116207104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 21582374244608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record048_result⟩)
 (.leaf ⟨(32, 21582506365184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 21582770606336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 21582776897600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record051_result⟩)
 (.leaf ⟨(32, 21587068207168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 21587069767744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 21587187206160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record054_result⟩)
 (.leaf ⟨(32, 21588124778560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 21588260945921), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 21595508705296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record057_result⟩)
 (.leaf ⟨(32, 21596582445057), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 21719941124352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 21724240285760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record060_result⟩)
 (.leaf ⟨(32, 21921664368896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 21921668595712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 21921676658688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record063_result⟩)
 (.leaf ⟨(32, 21921798570240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 21921806958592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 21921808779264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record066_result⟩)
 (.leaf ⟨(32, 21921915996416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 21922318649408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 21925963300864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record069_result⟩)
 (.leaf ⟨(32, 21926076614912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 21926085003264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record071_result⟩)
 (.leaf ⟨(32, 21926093259520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 21926613352968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record073_result⟩)
 (.leaf ⟨(32, 21930245752832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 21930640017472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 21930656662080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record076_result⟩)
 (.leaf ⟨(32, 21930774102536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 21951577850372), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 21951577981952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record079_result⟩)
 (.leaf ⟨(32, 22028226756864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 22028497289280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 22030175011072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record082_result⟩)
 (.leaf ⟨(32, 22030307131648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 22030571372800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 22030577664064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record085_result⟩)
 (.leaf ⟨(32, 22030644772896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 22034602082560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 22034866323712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record088_result⟩)
 (.leaf ⟨(32, 22034870534208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 22034937643040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 22043259142176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record091_result⟩)
 (.leaf ⟨(32, 22043456225536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 22043456274496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 22045164339456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record094_result⟩)
 (.leaf ⟨(32, 22064665821440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 22064937402400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record096_result⟩)
 (.leaf ⟨(32, 22065706008832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 22065970249984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record098_result⟩)
 (.leaf ⟨(32, 22065977589792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00056.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (32320 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 32320 32420 :=
  block_of_table results 32320 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1021
