module
prelude
import GraphInputsRow19Part00002Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0042
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 5829558370304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 5830095142913), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record001_result⟩)
 (.leaf ⟨(19, 5830162260032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 5830229377024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 5830231457792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record004_result⟩)
 (.leaf ⟨(19, 5833851240448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 5834323009600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 5834522247168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record007_result⟩)
 (.leaf ⟨(19, 5834579919104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 5834582065152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 5834588307456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record010_result⟩)
 (.leaf ⟨(19, 5868880936960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 5869184057344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 5899955601408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record013_result⟩)
 (.leaf ⟨(19, 5902108213504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 5902110359552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 5902116601856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record016_result⟩)
 (.leaf ⟨(19, 5903575384064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 5904380461568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 5933608566784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record019_result⟩)
 (.leaf ⟨(19, 5933707657216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 5934080335936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record021_result⟩)
 (.leaf ⟨(19, 5936929390592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 5937333018688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record023_result⟩)
 (.leaf ⟨(19, 5937903517696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 5937969577984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 5938002608128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record026_result⟩)
 (.leaf ⟨(19, 5938373206080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 5974375219200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 5974913974273), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record029_result⟩)
 (.leaf ⟨(19, 6379918196736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 6414344912896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 6415385100288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record032_result⟩)
 (.leaf ⟨(19, 6418703843328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 6449711284224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 6451871351296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record035_result⟩)
 (.leaf ⟨(19, 6453872033792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 6454136274944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 6455885300736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record038_result⟩)
 (.leaf ⟨(19, 6485460467712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 6524063908864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 6558961370112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record041_result⟩)
 (.leaf ⟨(19, 6582721052672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 6587146043392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 6595467542528), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record044_result⟩)
 (.leaf ⟨(19, 6637144342912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 6654820188160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record046_result⟩)
 (.leaf ⟨(19, 6727338655744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 6755617701888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record048_result⟩)
 (.leaf ⟨(19, 6787813179392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 6791631044608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 6792234934336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record051_result⟩)
 (.leaf ⟨(19, 6792302051328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 6792304132096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 6796654739456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record054_result⟩)
 (.leaf ⟨(19, 6796660981760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 6799516246080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 6862162362368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_result⟩)
 (.leaf ⟨(19, 6866453135872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 6868336386048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 6868593344512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record060_result⟩)
 (.leaf ⟨(19, 6868601667584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 6895371329536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 6899532079104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record063_result⟩)
 (.leaf ⟨(19, 6921153150976), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 6928606994432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 6960821329920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record066_result⟩)
 (.leaf ⟨(19, 7024530259968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 7036436824064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 7036576211008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record069_result⟩)
 (.leaf ⟨(19, 7037410951168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 7037477011456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record071_result⟩)
 (.leaf ⟨(19, 7037510041600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 7038243971136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record073_result⟩)
 (.leaf ⟨(19, 7038245027840), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 7046189645888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 7071802277888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record076_result⟩)
 (.leaf ⟨(19, 7071942575168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 7073880571904), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 7073882652672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record079_result⟩)
 (.leaf ⟨(19, 7074025046017), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 7074088099904), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 7074088116224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record082_result⟩)
 (.leaf ⟨(19, 7074157166593), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 7084894683136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 7108377509888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record085_result⟩)
 (.leaf ⟨(19, 7226966245392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 7261325983744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 7376350486528), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record088_result⟩)
 (.leaf ⟨(19, 7380511236096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 7380768194560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 7380776517632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record091_result⟩)
 (.leaf ⟨(19, 7383631798272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 7411783958528), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 7415944708096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record094_result⟩)
 (.leaf ⟨(19, 7416208949248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 7560562311176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record096_result⟩)
 (.leaf ⟨(19, 7562776903680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 7564857278464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record098_result⟩)
 (.leaf ⟨(19, 7584967901184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (2298 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 2298 2398 :=
  block_of_table results 2298 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0042
