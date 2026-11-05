module
prelude
import GraphInputsSix0Part00071Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1036
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 26571425464576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 26580690698240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record001_result⟩)
 (.leaf ⟨(32, 26598272155776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 26631507820672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 26639872360704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record004_result⟩)
 (.leaf ⟨(32, 26648747474944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 26648751636480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 26657052229632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record007_result⟩)
 (.leaf ⟨(32, 26700951863424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 26701150044288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 26703230419072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record010_result⟩)
 (.leaf ⟨(32, 26704303636608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 26710810566912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 26712651890944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record013_result⟩)
 (.leaf ⟨(32, 26718121263232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 26718125457408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 26718321524864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record016_result⟩)
 (.leaf ⟨(32, 26721241825408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 26725604950016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 26735442673792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record019_result⟩)
 (.leaf ⟨(32, 26768480157824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 26768678338688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record021_result⟩)
 (.leaf ⟨(32, 26768942579840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 26794220732544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record023_result⟩)
 (.leaf ⟨(32, 26846030741760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 26871556227200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 26982406439168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record026_result⟩)
 (.leaf ⟨(32, 27015634297088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 27015902699776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 27016759935232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record029_result⟩)
 (.leaf ⟨(32, 27016833278208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 27049976858880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 27049995600128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record032_result⟩)
 (.leaf ⟨(32, 27052258427136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 27052266815488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 27079274938496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record035_result⟩)
 (.leaf ⟨(32, 27085482508544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 27094068248832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 27094136398080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record038_result⟩)
 (.leaf ⟨(32, 27095977722112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 27096514592768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 27096518754304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record041_result⟩)
 (.leaf ⟨(32, 27109885264128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 27111470416000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 27119834956032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record044_result⟩)
 (.leaf ⟨(32, 27120984195072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 27121783210240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record046_result⟩)
 (.leaf ⟨(32, 27122055839744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 27122320080896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record048_result⟩)
 (.leaf ⟨(32, 27122328403968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 27122452201472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 27123122241792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record051_result⟩)
 (.leaf ⟨(32, 27127568679040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 27128710070272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 27128714231808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record054_result⟩)
 (.leaf ⟨(32, 27129569935360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 27130369048832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 27130373275648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record057_result⟩)
 (.leaf ⟨(32, 27130377437184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 27130381468672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 27130637320960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record060_result⟩)
 (.leaf ⟨(32, 27130771685504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 27130777830400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 27130905756288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record063_result⟩)
 (.leaf ⟨(32, 27137014824960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 27157884576000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 27189428945152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record066_result⟩)
 (.leaf ⟨(32, 27189701574656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 27191509319936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 27192244371456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record069_result⟩)
 (.leaf ⟨(32, 27193862324224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 27194399129600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record071_result⟩)
 (.leaf ⟨(32, 27206881378304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 27208961753088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record073_result⟩)
 (.leaf ⟨(32, 27216247275648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 27216445456512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 27216478486656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record076_result⟩)
 (.leaf ⟨(32, 27224826740992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 27233416675456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 27248442753152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record079_result⟩)
 (.leaf ⟨(32, 27248640934016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 27248905175168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 27249714151552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record082_result⟩)
 (.leaf ⟨(32, 27249978392704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 27256417697920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 27267808002176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record085_result⟩)
 (.leaf ⟨(32, 27267812196352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 27267942203520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 27267948348416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record088_result⟩)
 (.leaf ⟨(32, 27268076274304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 27274183327872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 27351518822528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record091_result⟩)
 (.leaf ⟨(32, 27352592040064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 27353054462080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 27384804032640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record094_result⟩)
 (.leaf ⟨(32, 27393637236992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 27398000148480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record096_result⟩)
 (.leaf ⟨(32, 27430212403200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 27525780668672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record098_result⟩)
 (.leaf ⟨(32, 27525786910976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00071.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (33720 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 33720 33820 :=
  block_of_table results 33720 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1036
