module
prelude
import GraphInputsRow16Part00001Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0001
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 42
 (.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 5147327528960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record000_result⟩)
 (.leaf ⟨(16, 5337180635136), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 5354620518400), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record002_result⟩)
 (.branch 4
 (.leaf ⟨(16, 5354628841472), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record003_result⟩)
 (.leaf ⟨(16, 5356172410880), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(16, 5356630606080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record005_result⟩)
 (.leaf ⟨(16, 5422673248256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record006_result⟩))
 (.branch 8
 (.leaf ⟨(16, 5422675133696), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record007_result⟩)
 (.branch 9
 (.leaf ⟨(16, 5425215865088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record008_result⟩)
 (.leaf ⟨(16, 5425227374592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(16, 5425484333056), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record010_result⟩)
 (.leaf ⟨(16, 5425492656128), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record011_result⟩))
 (.branch 13
 (.leaf ⟨(16, 5440190644224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record012_result⟩)
 (.branch 14
 (.leaf ⟨(16, 5459248480256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record013_result⟩)
 (.leaf ⟨(16, 5459508494592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(16, 5459520004096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record015_result⟩)
 (.branch 17
 (.leaf ⟨(16, 5628095463424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record016_result⟩)
 (.leaf ⟨(16, 5828151083008), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(16, 5829558370304), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record018_result⟩)
 (.branch 20
 (.leaf ⟨(16, 5830229377024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record019_result⟩)
 (.leaf ⟨(16, 5830231457792), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record020_result⟩))))))
 (.branch 31
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf ⟨(16, 5833851240448), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record021_result⟩)
 (.leaf ⟨(16, 5834522247168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record022_result⟩))
 (.branch 24
 (.leaf ⟨(16, 5834582065152), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record023_result⟩)
 (.branch 25
 (.leaf ⟨(16, 5834588307456), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record024_result⟩)
 (.leaf ⟨(16, 5868880936960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record025_result⟩))))
 (.branch 28
 (.branch 27
 (.leaf ⟨(16, 5869184057344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record026_result⟩)
 (.leaf ⟨(16, 5899955601408), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record027_result⟩))
 (.branch 29
 (.leaf ⟨(16, 5902110359552), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record028_result⟩)
 (.branch 30
 (.leaf ⟨(16, 5902116601856), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record029_result⟩)
 (.leaf ⟨(16, 5903575384064), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record030_result⟩)))))
 (.branch 36
 (.branch 33
 (.branch 32
 (.leaf ⟨(16, 5904380461568), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record031_result⟩)
 (.leaf ⟨(16, 5933608566784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record032_result⟩))
 (.branch 34
 (.leaf ⟨(16, 5933610582272), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record033_result⟩)
 (.branch 35
 (.leaf ⟨(16, 5933707657216), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record034_result⟩)
 (.leaf ⟨(16, 5937903517696), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record035_result⟩))))
 (.branch 39
 (.branch 37
 (.leaf ⟨(16, 5937969577984), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record036_result⟩)
 (.branch 38
 (.leaf ⟨(16, 6379918196736), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record037_result⟩)
 (.leaf ⟨(16, 6414344912896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(16, 6415385100288), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record039_result⟩)
 (.branch 41
 (.leaf ⟨(16, 6418703843328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record040_result⟩)
 (.leaf ⟨(16, 6449711284224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record041_result⟩)))))))
 (.branch 63
 (.branch 52
 (.branch 47
 (.branch 44
 (.branch 43
 (.leaf ⟨(16, 6453872033792), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record042_result⟩)
 (.leaf ⟨(16, 6454136274944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record043_result⟩))
 (.branch 45
 (.leaf ⟨(16, 6455885300736), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record044_result⟩)
 (.branch 46
 (.leaf ⟨(16, 6485460467712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record045_result⟩)
 (.leaf ⟨(16, 6558961370112), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record046_result⟩))))
 (.branch 49
 (.branch 48
 (.leaf ⟨(16, 6582721052672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record047_result⟩)
 (.leaf ⟨(16, 6587146043392), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record048_result⟩))
 (.branch 50
 (.leaf ⟨(16, 6595467542528), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record049_result⟩)
 (.branch 51
 (.leaf ⟨(16, 6654820188160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record050_result⟩)
 (.leaf ⟨(16, 6727338655744), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record051_result⟩)))))
 (.branch 57
 (.branch 54
 (.branch 53
 (.leaf ⟨(16, 6791631044608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record052_result⟩)
 (.leaf ⟨(16, 6792234934336), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record053_result⟩))
 (.branch 55
 (.leaf ⟨(16, 6792302051328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record054_result⟩)
 (.branch 56
 (.leaf ⟨(16, 6792304132096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record055_result⟩)
 (.leaf ⟨(16, 6795923914752), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record056_result⟩))))
 (.branch 60
 (.branch 58
 (.leaf ⟨(16, 6796654739456), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record057_result⟩)
 (.branch 59
 (.leaf ⟨(16, 6862162362368), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record058_result⟩)
 (.leaf ⟨(16, 6868336386048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record059_result⟩)))
 (.branch 61
 (.leaf ⟨(16, 6868593344512), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record060_result⟩)
 (.branch 62
 (.leaf ⟨(16, 6868601667584), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record061_result⟩)
 (.leaf ⟨(16, 6921153150976), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record062_result⟩))))))
 (.branch 73
 (.branch 68
 (.branch 65
 (.branch 64
 (.leaf ⟨(16, 7024530259968), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record063_result⟩)
 (.leaf ⟨(16, 7037477011456), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record064_result⟩))
 (.branch 66
 (.leaf ⟨(16, 7038245027840), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record065_result⟩)
 (.branch 67
 (.leaf ⟨(16, 7084894683136), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record066_result⟩)
 (.leaf ⟨(16, 7108377509888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record067_result⟩))))
 (.branch 70
 (.branch 69
 (.leaf ⟨(16, 7225892503584), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record068_result⟩)
 (.leaf ⟨(16, 7226966245392), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record069_result⟩))
 (.branch 71
 (.leaf ⟨(16, 7261325983744), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record070_result⟩)
 (.branch 72
 (.leaf ⟨(16, 7376350486528), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record071_result⟩)
 (.leaf ⟨(16, 7380511236096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record072_result⟩)))))
 (.branch 78
 (.branch 75
 (.branch 74
 (.leaf ⟨(16, 7380768194560), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record073_result⟩)
 (.leaf ⟨(16, 7380776517632), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record074_result⟩))
 (.branch 76
 (.leaf ⟨(16, 7383631798272), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record075_result⟩)
 (.branch 77
 (.leaf ⟨(16, 7411783958528), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record076_result⟩)
 (.leaf ⟨(16, 7415944708096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record077_result⟩))))
 (.branch 81
 (.branch 79
 (.leaf ⟨(16, 7416208949248), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record078_result⟩)
 (.branch 80
 (.leaf ⟨(16, 7562776903680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record079_result⟩)
 (.leaf ⟨(16, 7564857278464), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record080_result⟩)))
 (.branch 82
 (.leaf ⟨(16, 7565897465856), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record081_result⟩)
 (.branch 83
 (.leaf ⟨(16, 7584967835904), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record082_result⟩)
 (.leaf ⟨(16, 7584967901184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record083_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (100 + i))) 0 84 :=
  interval_of_check _ 0 84 (by decide +kernel)

public theorem complete : Block 100 184 :=
  block_of_table results 100 84 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0001
