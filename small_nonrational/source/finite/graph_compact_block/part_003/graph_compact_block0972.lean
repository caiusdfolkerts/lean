module
prelude
import GraphInputsSix0Part00007Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0972
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 2693557928064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 2788922851584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record001_result⟩)
 (.leaf ⟨(32, 2789191286912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 2793215721728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 2793484157056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record004_result⟩)
 (.leaf ⟨(32, 2796707479568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 2801801462016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 2801805656192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record007_result⟩)
 (.leaf ⟨(32, 2823215481088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 2823483916416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 2824758984720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record010_result⟩)
 (.leaf ⟨(32, 2827376230656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 2827508351232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 2827574411520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record013_result⟩)
 (.leaf ⟨(32, 2827776786560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 2828919734288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 2831000109072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record016_result⟩)
 (.leaf ⟨(32, 2835966165120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 2836094091520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 2836098285696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record019_result⟩)
 (.leaf ⟨(32, 2836164345984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 2893344243728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record021_result⟩)
 (.leaf ⟨(32, 2896093610240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 2896227811584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record023_result⟩)
 (.leaf ⟨(32, 2896293871872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 2896496246912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 2897637113872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record026_result⟩)
 (.leaf ⟨(32, 2899717488656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 2904679350528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 2904683544704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record029_result⟩)
 (.leaf ⟨(32, 2904813551872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 2904817746048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 2904880652544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record032_result⟩)
 (.leaf ⟨(32, 2904883806336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 2933877965056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 2934280569088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record035_result⟩)
 (.leaf ⟨(32, 2956299698432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 2956301779200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 2956302819584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record038_result⟩)
 (.leaf ⟨(32, 2956570181888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 2963704741896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 2981854446848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record041_result⟩)
 (.leaf ⟨(32, 2981986631936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 2981995020288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 2982193201152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record044_result⟩)
 (.leaf ⟨(32, 2982387155200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 2982395543552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record046_result⟩)
 (.leaf ⟨(32, 3030514761744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 3034807631888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record048_result⟩)
 (.leaf ⟨(32, 3036954066960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 3042118303872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 3042252472576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record051_result⟩)
 (.leaf ⟨(32, 3042252505216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 3042319605888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 3093740699904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record054_result⟩)
 (.leaf ⟨(32, 3096012947712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 3096013012992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 3096281383040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record057_result⟩)
 (.leaf ⟨(32, 3096415584384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 3098093322496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 3098093387776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record060_result⟩)
 (.leaf ⟨(32, 3098361757824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 3101253222656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 3101254263040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record063_result⟩)
 (.leaf ⟨(32, 3102382031104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 3102386192640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 3102386257920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record066_result⟩)
 (.leaf ⟨(32, 3102452252928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 3102452318208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 3102654627968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record069_result⟩)
 (.leaf ⟨(32, 3102656708736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 3105841250432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record071_result⟩)
 (.leaf ⟨(32, 3115801673728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 3119425552640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record073_result⟩)
 (.leaf ⟨(32, 3119433940992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 3119557673216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 3119561900032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record076_result⟩)
 (.leaf ⟨(32, 3119566061568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 3119632121856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 3119826108544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record079_result⟩)
 (.leaf ⟨(32, 3120026370176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 3120094543872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 3120098705408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record082_result⟩)
 (.leaf ⟨(32, 3127025910016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 3131303954688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 3131328987392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record085_result⟩)
 (.leaf ⟨(32, 3131329052672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 3131597422720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 3131849050240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record088_result⟩)
 (.leaf ⟨(32, 3135617696000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 3135621857536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 3135621922816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record091_result⟩)
 (.leaf ⟨(32, 3135741364480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 3135886098688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 3135886163968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record094_result⟩)
 (.leaf ⟨(32, 3135890292864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 3135892373632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record096_result⟩)
 (.leaf ⟨(32, 3136009799808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 3140438982657), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record098_result⟩)
 (.leaf ⟨(32, 3144331298944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00007.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (27486 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 27486 27586 :=
  block_of_table results 27486 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0972
