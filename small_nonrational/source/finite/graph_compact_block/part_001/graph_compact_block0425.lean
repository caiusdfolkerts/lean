module
prelude
import GraphInputsRow28Part00005Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0425
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(28, 14483193856000), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record000_result⟩)
 (.branch 2
 (.leaf ⟨(28, 14487738384384), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record001_result⟩)
 (.leaf ⟨(28, 14573109780736), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(28, 14587388788736), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record003_result⟩)
 (.branch 5
 (.leaf ⟨(28, 14587392950272), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record004_result⟩)
 (.leaf ⟨(28, 14587454849024), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(28, 14590809743360), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record006_result⟩)
 (.branch 8
 (.leaf ⟨(28, 14606248509440), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record007_result⟩)
 (.leaf ⟨(28, 14616587403264), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(28, 14622354636800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record009_result⟩)
 (.branch 11
 (.leaf ⟨(28, 14625168949760), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record010_result⟩)
 (.leaf ⟨(28, 14628797087744), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(28, 14629466013696), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record012_result⟩)
 (.branch 14
 (.leaf ⟨(28, 14663089717248), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record013_result⟩)
 (.leaf ⟨(28, 14663824703488), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(28, 15213050986496), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record015_result⟩)
 (.branch 17
 (.leaf ⟨(28, 15213579468800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record016_result⟩)
 (.leaf ⟨(28, 15403138949120), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(28, 15472352362496), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record018_result⟩)
 (.branch 20
 (.leaf ⟨(28, 15480207212800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record019_result⟩)
 (.leaf ⟨(28, 15480942264320), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(28, 15548924592384), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record021_result⟩)
 (.leaf ⟨(28, 15549259120640), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record022_result⟩))
 (.branch 24
 (.leaf ⟨(28, 15549527523328), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record023_result⟩)
 (.leaf ⟨(28, 15584427311104), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(28, 15680960233728), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record025_result⟩)
 (.branch 27
 (.leaf ⟨(28, 15681731436544), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record026_result⟩)
 (.leaf ⟨(28, 15686698041344), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(28, 15721866231808), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record028_result⟩)
 (.branch 30
 (.leaf ⟨(28, 15851247894528), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record029_result⟩)
 (.leaf ⟨(28, 15859305152512), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(28, 16495931326720), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record031_result⟩)
 (.branch 33
 (.leaf ⟨(28, 16496067674112), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record032_result⟩)
 (.leaf ⟨(28, 16496075997184), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(28, 16496298885120), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record034_result⟩)
 (.branch 36
 (.leaf ⟨(28, 16499150979328), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record035_result⟩)
 (.leaf ⟨(28, 16499922702336), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(28, 16531346456832), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record037_result⟩)
 (.branch 39
 (.leaf ⟨(28, 16531601817856), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record038_result⟩)
 (.leaf ⟨(28, 16531614924800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(28, 16531623247872), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record040_result⟩)
 (.branch 42
 (.leaf ⟨(28, 16532134694912), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record041_result⟩)
 (.leaf ⟨(28, 16532403028224), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(28, 16532679753728), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record043_result⟩)
 (.branch 45
 (.leaf ⟨(28, 16533208171008), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record044_result⟩)
 (.leaf ⟨(28, 16533216559104), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(28, 16537377308672), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record046_result⟩)
 (.leaf ⟨(28, 16545426243584), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record047_result⟩))
 (.branch 49
 (.leaf ⟨(28, 16545698807808), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record048_result⟩)
 (.leaf ⟨(28, 16545963048960), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(28, 16548546805760), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record050_result⟩)
 (.branch 52
 (.leaf ⟨(28, 16549314822144), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record051_result⟩)
 (.leaf ⟨(28, 16604620455936), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(28, 16621800259584), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record053_result⟩)
 (.branch 55
 (.leaf ⟨(28, 16622328741888), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record054_result⟩)
 (.leaf ⟨(28, 16648576696320), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(28, 16650112335872), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record056_result⟩)
 (.branch 58
 (.leaf ⟨(28, 16669044965376), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record057_result⟩)
 (.leaf ⟨(28, 16677903269888), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(28, 16686224769024), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record059_result⟩)
 (.branch 61
 (.leaf ⟨(28, 16686753251328), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record060_result⟩)
 (.leaf ⟨(28, 16690385518592), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(28, 16768695304448), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record062_result⟩)
 (.branch 64
 (.leaf ⟨(28, 16774032588800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record063_result⟩)
 (.leaf ⟨(28, 16774800605184), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(28, 16778961354752), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record065_result⟩)
 (.branch 67
 (.leaf ⟨(28, 16785875173376), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record066_result⟩)
 (.leaf ⟨(28, 16786011455488), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(28, 16786915360768), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record068_result⟩)
 (.branch 70
 (.leaf ⟨(28, 16823387062272), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record069_result⟩)
 (.leaf ⟨(28, 16907277238272), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(28, 16930830286848), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record071_result⟩)
 (.leaf ⟨(28, 16943922806784), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record072_result⟩))
 (.branch 74
 (.leaf ⟨(28, 16952772788224), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record073_result⟩)
 (.leaf ⟨(28, 16965255036928), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(28, 16969415786496), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record075_result⟩)
 (.branch 77
 (.leaf ⟨(28, 17043521306880), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record076_result⟩)
 (.leaf ⟨(28, 17043558563840), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(28, 17043566886912), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record078_result⟩)
 (.branch 80
 (.leaf ⟨(28, 17043789774848), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record079_result⟩)
 (.leaf ⟨(28, 17043798097920), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(28, 17044309544960), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record081_result⟩)
 (.branch 83
 (.leaf ⟨(28, 17051037470976), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record082_result⟩)
 (.leaf ⟨(28, 17051574341632), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(28, 17051590856704), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record084_result⟩)
 (.branch 86
 (.leaf ⟨(28, 17052094042368), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record085_result⟩)
 (.leaf ⟨(28, 17052135915520), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(28, 17052664332800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record087_result⟩)
 (.branch 89
 (.leaf ⟨(28, 17052672720896), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record088_result⟩)
 (.leaf ⟨(28, 17060721655808), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(28, 17061258461184), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record090_result⟩)
 (.branch 92
 (.leaf ⟨(28, 17061489672192), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record091_result⟩)
 (.leaf ⟨(28, 17068200169488), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(28, 17068234178560), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record093_result⟩)
 (.branch 95
 (.leaf ⟨(28, 17120016531456), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record094_result⟩)
 (.leaf ⟨(28, 17181219815424), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(28, 17190078119936), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record096_result⟩)
 (.leaf ⟨(28, 17197049186320), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record097_result⟩))
 (.branch 99
 (.leaf ⟨(28, 17197066420224), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record098_result⟩)
 (.leaf ⟨(28, 17197603225600), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00005.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (19804 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 19804 19904 :=
  block_of_table results 19804 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0425
