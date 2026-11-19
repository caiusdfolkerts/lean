module
prelude
import GraphInputsRow19Part00014Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0054
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 17924715724928), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 17924715757568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record001_result⟩)
 (.leaf ⟨(19, 17925219106944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 17976927551744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 17981222502656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record004_result⟩)
 (.leaf ⟨(19, 17993841164416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 17994307649540), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 17994639999616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record007_result⟩)
 (.leaf ⟨(19, 17998402306304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 18000548741376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 18045647012096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record010_result⟩)
 (.leaf ⟨(19, 18066987630592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 18067193077824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 18067720519744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record013_result⟩)
 (.leaf ⟨(19, 18067722616832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 18069134000384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 18069134065664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record016_result⟩)
 (.leaf ⟨(19, 18069273452608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 18199161684096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 18231710482560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record019_result⟩)
 (.leaf ⟨(19, 18263910154240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 18272751714304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record021_result⟩)
 (.leaf ⟨(19, 18299893137536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 18300498116608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record023_result⟩)
 (.leaf ⟨(19, 18324014579968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 18328313692416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 18328313757696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record026_result⟩)
 (.leaf ⟨(19, 18328441651456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 18328450039808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 18328582160384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record029_result⟩)
 (.leaf ⟨(19, 18332693594112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 18333766811648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 18335087525888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record032_result⟩)
 (.leaf ⟨(19, 18335095848960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 18335275237504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 18335913246720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record035_result⟩)
 (.leaf ⟨(19, 18337031586304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 18337035715200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 18337167900672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record038_result⟩)
 (.leaf ⟨(19, 18337176223744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 18338208088064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 18338216411136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record041_result⟩)
 (.leaf ⟨(19, 18341194448896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 18341533073408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 18344116764928), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record044_result⟩)
 (.leaf ⟨(19, 18344116830208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 18344382111744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record046_result⟩)
 (.leaf ⟨(19, 18368577093760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 18368847446272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record048_result⟩)
 (.leaf ⟨(19, 18376128758016), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 18376128823296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 18400271433728), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record051_result⟩)
 (.leaf ⟨(19, 18402479505920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 18406900367360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 18407026130944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record054_result⟩)
 (.leaf ⟨(19, 18407034454016), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 18410654351360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 18411325227520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record057_result⟩)
 (.leaf ⟨(19, 18437930795008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 18465484275712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 18472709996672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record060_result⟩)
 (.leaf ⟨(19, 18472743026816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 18550305652736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 18569602613248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record063_result⟩)
 (.leaf ⟨(19, 18582283042816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 18583117119488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 18591057527040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record066_result⟩)
 (.leaf ⟨(19, 18616948883457), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 18617475269184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 18617477366272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record069_result⟩)
 (.leaf ⟨(19, 18618754679040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 18618754744320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record071_result⟩)
 (.leaf ⟨(19, 18618756629760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 18618961101888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record073_result⟩)
 (.leaf ⟨(19, 18619029258241), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 18736331440448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 18748783280256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record076_result⟩)
 (.leaf ⟨(19, 18813721542912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 18817667367168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 18817935769856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record079_result⟩)
 (.leaf ⟨(19, 18817935835136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 18822230786048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 18822561022208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record082_result⟩)
 (.leaf ⟨(19, 18822569410560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 18825424674880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 18869475426560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record085_result⟩)
 (.leaf ⟨(19, 18878069555200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 18878195368192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 18878203756544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record088_result⟩)
 (.leaf ⟨(19, 18884310614272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 18884310679552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 18886252626176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record091_result⟩)
 (.leaf ⟨(19, 18886655230208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 18886655295488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 18886789496832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record094_result⟩)
 (.leaf ⟨(19, 18886797819904), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 18886985531648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record096_result⟩)
 (.leaf ⟨(19, 18886987677696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 18886993920000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record098_result⟩)
 (.leaf ⟨(19, 18893738361088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00014.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (3465 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 3465 3565 :=
  block_of_table results 3465 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0054
