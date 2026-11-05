module
prelude
import GraphInputsRow23Part00014Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0092
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 47
 (.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(23, 23695372386560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record000_result⟩)
 (.leaf ⟨(23, 23696140468224), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record001_result⟩))
 (.branch 3
 (.leaf ⟨(23, 23764330938368), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record002_result⟩)
 (.branch 4
 (.leaf ⟨(23, 23795798704128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record003_result⟩)
 (.leaf ⟨(23, 23795807027200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(23, 23796937981952), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record005_result⟩)
 (.branch 7
 (.leaf ⟨(23, 23897760071680), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record006_result⟩)
 (.leaf ⟨(23, 23921626251264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(23, 23925787000832), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record008_result⟩)
 (.branch 10
 (.leaf ⟨(23, 23932700754176), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record009_result⟩)
 (.leaf ⟨(23, 23932837101568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(23, 23932845424640), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record011_result⟩)
 (.branch 13
 (.leaf ⟨(23, 23932969222144), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record012_result⟩)
 (.leaf ⟨(23, 23932977545216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(23, 23933437886464), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record014_result⟩)
 (.branch 16
 (.leaf ⟨(23, 23933740941568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record015_result⟩)
 (.leaf ⟨(23, 23934511104000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(23, 23940182327552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record017_result⟩)
 (.branch 19
 (.leaf ⟨(23, 23970212643072), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record018_result⟩)
 (.leaf ⟨(23, 23971017785856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(23, 23971563044864), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record020_result⟩)
 (.branch 22
 (.leaf ⟨(23, 23972091527168), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record021_result⟩)
 (.leaf ⟨(23, 24004643586048), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record022_result⟩))))))
 (.branch 35
 (.branch 29
 (.branch 26
 (.branch 24
 (.leaf ⟨(23, 24026609090560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record023_result⟩)
 (.branch 25
 (.leaf ⟨(23, 24034658025472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record024_result⟩)
 (.leaf ⟨(23, 24035442556928), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record025_result⟩)))
 (.branch 27
 (.leaf ⟨(23, 24039208779776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record026_result⟩)
 (.branch 28
 (.leaf ⟨(23, 24052959871232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record027_result⟩)
 (.leaf ⟨(23, 24055180754944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record028_result⟩))))
 (.branch 32
 (.branch 30
 (.leaf ⟨(23, 24055717560320), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record029_result⟩)
 (.branch 31
 (.leaf ⟨(23, 24058838122496), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record030_result⟩)
 (.leaf ⟨(23, 24070139740160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record031_result⟩)))
 (.branch 33
 (.leaf ⟨(23, 24070676545536), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record032_result⟩)
 (.branch 34
 (.leaf ⟨(23, 24090496794624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record033_result⟩)
 (.leaf ⟨(23, 24091033600000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record034_result⟩)))))
 (.branch 41
 (.branch 38
 (.branch 36
 (.leaf ⟨(23, 24103375405056), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record035_result⟩)
 (.branch 37
 (.leaf ⟨(23, 24103912210432), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record036_result⟩)
 (.leaf ⟨(23, 24104027815936), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(23, 24107651629056), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record038_result⟩)
 (.branch 40
 (.leaf ⟨(23, 24192647987456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record039_result⟩)
 (.leaf ⟨(23, 24225916682496), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record040_result⟩))))
 (.branch 44
 (.branch 42
 (.leaf ⟨(23, 24229598756864), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record041_result⟩)
 (.branch 43
 (.leaf ⟨(23, 24230729646336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record042_result⟩)
 (.leaf ⟨(23, 24242081005568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043_result⟩)))
 (.branch 45
 (.leaf ⟨(23, 24262832824448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record044_result⟩)
 (.branch 46
 (.leaf ⟨(23, 24263957446656), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record045_result⟩)
 (.leaf ⟨(23, 24265022275840), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record046_result⟩)))))))
 (.branch 70
 (.branch 58
 (.branch 52
 (.branch 49
 (.branch 48
 (.leaf ⟨(23, 24268322643968), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record047_result⟩)
 (.leaf ⟨(23, 24276439695360), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record048_result⟩))
 (.branch 50
 (.leaf ⟨(23, 24276632633600), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record049_result⟩)
 (.branch 51
 (.leaf ⟨(23, 24276644143104), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record050_result⟩)
 (.leaf ⟨(23, 24293610389760), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record051_result⟩))))
 (.branch 55
 (.branch 53
 (.leaf ⟨(23, 24299050172672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record052_result⟩)
 (.branch 54
 (.leaf ⟨(23, 24299587043328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record053_result⟩)
 (.leaf ⟨(23, 24299595366400), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record054_result⟩)))
 (.branch 56
 (.leaf ⟨(23, 24303747792896), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record055_result⟩)
 (.branch 57
 (.leaf ⟨(23, 24303756115968), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record056_result⟩)
 (.leaf ⟨(23, 24303879913472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record057_result⟩)))))
 (.branch 64
 (.branch 61
 (.branch 59
 (.leaf ⟨(23, 24305828167680), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record058_result⟩)
 (.branch 60
 (.leaf ⟨(23, 24335847268416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record059_result⟩)
 (.leaf ⟨(23, 24345352093952), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record060_result⟩)))
 (.branch 62
 (.leaf ⟨(23, 24345361522688), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record061_result⟩)
 (.branch 63
 (.leaf ⟨(23, 24345754746944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record062_result⟩)
 (.leaf ⟨(23, 24372473495552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record063_result⟩))))
 (.branch 67
 (.branch 65
 (.leaf ⟨(23, 24380786671616), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record064_result⟩)
 (.branch 66
 (.leaf ⟨(23, 24380794994688), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record065_result⟩)
 (.leaf ⟨(23, 24381189275648), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record066_result⟩)))
 (.branch 68
 (.leaf ⟨(23, 24414810833152), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record067_result⟩)
 (.branch 69
 (.leaf ⟨(23, 24436493320192), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record068_result⟩)
 (.leaf ⟨(23, 24437030125568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record069_result⟩))))))
 (.branch 82
 (.branch 76
 (.branch 73
 (.branch 71
 (.leaf ⟨(23, 24441190875136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record070_result⟩)
 (.branch 72
 (.leaf ⟨(23, 24443271249920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record071_result⟩)
 (.leaf ⟨(23, 24449239810048), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record072_result⟩)))
 (.branch 74
 (.leaf ⟨(23, 24449908736000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record073_result⟩)
 (.branch 75
 (.leaf ⟨(23, 24455613054976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record074_result⟩)
 (.leaf ⟨(23, 24457833873408), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record075_result⟩))))
 (.branch 79
 (.branch 77
 (.leaf ⟨(23, 24458362355712), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076_result⟩)
 (.branch 78
 (.leaf ⟨(23, 24470778052864), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record077_result⟩)
 (.leaf ⟨(23, 24477421805824), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record078_result⟩)))
 (.branch 80
 (.leaf ⟨(23, 24477824458816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record079_result⟩)
 (.branch 81
 (.leaf ⟨(23, 24482591834112), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record080_result⟩)
 (.leaf ⟨(23, 24482796281856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record081_result⟩)))))
 (.branch 88
 (.branch 85
 (.branch 83
 (.leaf ⟨(23, 24504067751936), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record082_result⟩)
 (.branch 84
 (.leaf ⟨(23, 24512184729600), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record083_result⟩)
 (.leaf ⟨(23, 24518229753856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record084_result⟩)))
 (.branch 86
 (.leaf ⟨(23, 24521247555584), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085_result⟩)
 (.branch 87
 (.leaf ⟨(23, 24569515671552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record086_result⟩)
 (.leaf ⟨(23, 24570031800320), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record087_result⟩))))
 (.branch 91
 (.branch 89
 (.leaf ⟨(23, 24572112175104), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record088_result⟩)
 (.branch 90
 (.leaf ⟨(23, 24573655548160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record089_result⟩)
 (.leaf ⟨(23, 24578361393152), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record090_result⟩)))
 (.branch 92
 (.leaf ⟨(23, 24584594423808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record091_result⟩)
 (.branch 93
 (.leaf ⟨(23, 24590835417088), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record092_result⟩)
 (.leaf ⟨(23, 24591103819776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record093_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (6912 + i))) 0 94 :=
  interval_of_check _ 0 94 (by decide +kernel)

public theorem complete : Block 6912 7006 :=
  block_of_table results 6912 94 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0092
