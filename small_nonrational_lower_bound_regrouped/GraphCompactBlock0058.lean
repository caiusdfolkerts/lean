module
prelude
import GraphInputsRow19Part00018Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0058
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 21316612145152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 21333138366464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record001_result⟩)
 (.leaf ⟨(19, 21401823233024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 21557112504576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 21558189948928), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record004_result⟩)
 (.leaf ⟨(19, 21573792759808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 21669389336576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 21670429523968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record007_result⟩)
 (.leaf ⟨(19, 21927087374336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 21960323039232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 22114591637504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record010_result⟩)
 (.leaf ⟨(19, 22114597879808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 22120500314368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 22121037185024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record013_result⟩)
 (.leaf ⟨(19, 22121573531904), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 22177643512064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 22182640025856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record016_result⟩)
 (.leaf ⟨(19, 22182778454016), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 22182904267008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 22182912655360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record019_result⟩)
 (.leaf ⟨(19, 22183042629888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 22183042695168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record021_result⟩)
 (.leaf ⟨(19, 22183048921152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 22183176896512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record023_result⟩)
 (.leaf ⟨(19, 22183183138816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 22183306871040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 22183315259392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record026_result⟩)
 (.leaf ⟨(19, 22183381319680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 22185461694464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 22186229252352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record029_result⟩)
 (.leaf ⟨(19, 22186501881856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 22190158790912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 22190158856192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record032_result⟩)
 (.leaf ⟨(19, 22214989652032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 22237807673600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 22239903817792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record035_result⟩)
 (.leaf ⟨(19, 22254578630912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 22255045214464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 22255115501568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record038_result⟩)
 (.leaf ⟨(19, 22255123824640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 22258743656704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 22259214320704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record041_result⟩)
 (.leaf ⟨(19, 22313773842688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 22314814030080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 22315078271232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record044_result⟩)
 (.leaf ⟨(19, 22315350900736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 22318064681024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record046_result⟩)
 (.leaf ⟨(19, 22320343187712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 22320347414528), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record048_result⟩)
 (.leaf ⟨(19, 22320353656832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 22322359582976), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 22323168170112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record051_result⟩)
 (.leaf ⟨(19, 22326520332544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 22326658744384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 22327187226688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record054_result⟩)
 (.leaf ⟨(19, 22327189323776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 22327558504448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 22327560519936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record057_result⟩)
 (.leaf ⟨(19, 22327560585216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 22327564746752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 22327597776896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record060_result⟩)
 (.leaf ⟨(19, 22327698931776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 22327963172928), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 22328328601600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record063_result⟩)
 (.leaf ⟨(19, 22352424411200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 22362621231104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 22374978191616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record066_result⟩)
 (.leaf ⟨(19, 22377338576960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 22392153899008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 22396186657856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record069_result⟩)
 (.leaf ⟨(19, 22396384838720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 22396979380800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record071_result⟩)
 (.leaf ⟨(19, 22396981477888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 22406115704896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record073_result⟩)
 (.leaf ⟨(19, 22408263180352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 22417691918592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 22426277658880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record076_result⟩)
 (.leaf ⟨(19, 22427045740544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 22430570529024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 22439351369792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record079_result⟩)
 (.leaf ⟨(19, 22439615610944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 22441763086400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 22443563450624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record082_result⟩)
 (.leaf ⟨(19, 22464895860736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 22464904037440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 22464963806464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record085_result⟩)
 (.leaf ⟨(19, 22464969203712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 22465038254081), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 22465366459456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record088_result⟩)
 (.leaf ⟨(19, 22602039967744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 22664412463104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 22664420786176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record091_result⟩)
 (.leaf ⟨(19, 22666492837888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 22666501160960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 22687670935616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record094_result⟩)
 (.leaf ⟨(19, 22689878180096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 22689886568448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record096_result⟩)
 (.leaf ⟨(19, 22697941680384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 22698139861248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record098_result⟩)
 (.leaf ⟨(19, 22698478551040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (3865 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 3865 3965 :=
  block_of_table results 3865 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0058
