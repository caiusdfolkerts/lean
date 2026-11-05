module
prelude
import GraphInputsRow19Part00001Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0041
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 2126956724736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 2160974659840), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record001_result⟩)
 (.leaf ⟨(19, 2329888719104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 2329891905536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 2329894994048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record004_result⟩)
 (.leaf ⟨(19, 2393578242304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 2394313228544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 2394313293824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record007_result⟩)
 (.leaf ⟨(19, 2426525483264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 2426525548544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 2428605923328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record010_result⟩)
 (.leaf ⟨(19, 2432766672896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 2455257579520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 2461841522944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record013_result⟩)
 (.leaf ⟨(19, 2461841588224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 2461844709376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 2468404592640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record016_result⟩)
 (.leaf ⟨(19, 2469683888132), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 2469954339072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 2470146310148), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record019_result⟩)
 (.leaf ⟨(19, 2531754295296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 2539267858432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record021_result⟩)
 (.leaf ⟨(19, 2557859168512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 2570207674368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record023_result⟩)
 (.leaf ⟨(19, 2571480113152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 2571482193920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 2605839319552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record026_result⟩)
 (.leaf ⟨(19, 2626483732608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 2676106477824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 2710465167616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record029_result⟩)
 (.leaf ⟨(19, 2845187317760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 2909608706048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 2974016438272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record032_result⟩)
 (.leaf ⟨(19, 2974019559424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 2982129189120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 3047049707520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record035_result⟩)
 (.leaf ⟨(19, 3118302011648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 3120094544384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 3183394471936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record038_result⟩)
 (.leaf ⟨(19, 3183395512320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 3188281327872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 3191699193860), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record041_result⟩)
 (.leaf ⟨(19, 3191700234244), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 3226459963906), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 3260222078976), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record044_result⟩)
 (.leaf ⟨(19, 3459230236928), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 3459230302208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record046_result⟩)
 (.leaf ⟨(19, 3523637969152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 3523638034432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record048_result⟩)
 (.leaf ⟨(19, 3528059789376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 3531882971136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 3532479594496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record051_result⟩)
 (.leaf ⟨(19, 3672239136896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 3737902989312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 3738108436544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record054_result⟩)
 (.leaf ⟨(19, 3738635878464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 3738637975552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 3741089611776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record057_result⟩)
 (.leaf ⟨(19, 3775414878208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 3775555175488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 3775689392129), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record060_result⟩)
 (.leaf ⟨(19, 3786426843392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 3788717998336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 3788720128064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record063_result⟩)
 (.leaf ⟨(19, 3809912954944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 3809912971264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 3964938518784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record066_result⟩)
 (.leaf ⟨(19, 4111091138816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 4119012114688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 4119548985344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record069_result⟩)
 (.leaf ⟨(19, 4119557308416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 4119821549568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record071_result⟩)
 (.leaf ⟨(19, 4336176398592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 4336184786944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record073_result⟩)
 (.leaf ⟨(19, 4336576921856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 4338193991744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 4359597391872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record076_result⟩)
 (.leaf ⟨(19, 4359605714944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 4376710152448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 4377247023104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record079_result⟩)
 (.leaf ⟨(19, 4377255346176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 4393890021376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 4394162585600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record082_result⟩)
 (.leaf ⟨(19, 4522409820160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 4803996631168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 4804805935104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record085_result⟩)
 (.leaf ⟨(19, 4872852307968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 5106290491392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 5138485968896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record088_result⟩)
 (.leaf ⟨(19, 5138490130432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 5337180635136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 5354620518400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record091_result⟩)
 (.leaf ⟨(19, 5354628841472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 5422673248256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 5425227374592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record094_result⟩)
 (.leaf ⟨(19, 5425492656128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 5793545027584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record096_result⟩)
 (.leaf ⟨(19, 5828149002240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 5828151083008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record098_result⟩)
 (.leaf ⟨(19, 5828357226752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (2198 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 2198 2298 :=
  block_of_table results 2198 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0041
