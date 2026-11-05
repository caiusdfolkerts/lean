module
prelude
import GraphInputsRow23Part00010Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0088
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 17519171600384), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 17523487604736), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record001_result⟩)
 (.leaf ⟨(23, 17532081668096), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(23, 17532610150400), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record003_result⟩)
 (.branch 5
 (.leaf ⟨(23, 17549236502528), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record004_result⟩)
 (.leaf ⟨(23, 17566953111552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(23, 17583596109824), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 17636824006784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record007_result⟩)
 (.leaf ⟨(23, 17640010629248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(23, 17702053773568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record009_result⟩)
 (.branch 11
 (.leaf ⟨(23, 17702391415040), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record010_result⟩)
 (.leaf ⟨(23, 17702525632768), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(23, 17702525698048), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record012_result⟩)
 (.branch 14
 (.leaf ⟨(23, 17704418361472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record013_result⟩)
 (.leaf ⟨(23, 17706684285184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(23, 17706686382336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 17706686447616), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record016_result⟩)
 (.leaf ⟨(23, 17715005784320), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(23, 17743089836096), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record018_result⟩)
 (.branch 20
 (.leaf ⟨(23, 17775403761920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record019_result⟩)
 (.leaf ⟨(23, 17775403827200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(23, 17777484136704), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record021_result⟩)
 (.leaf ⟨(23, 17783725326336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record022_result⟩))
 (.branch 24
 (.leaf ⟨(23, 17839352250624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record023_result⟩)
 (.leaf ⟨(23, 17856532119552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(23, 17914990174336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record025_result⟩)
 (.branch 27
 (.leaf ⟨(23, 18182012207360), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record026_result⟩)
 (.leaf ⟨(23, 18182016434176), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(23, 18220939510016), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record028_result⟩)
 (.branch 30
 (.leaf ⟨(23, 18229529444480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record029_result⟩)
 (.leaf ⟨(23, 18229598625920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(23, 18255030845440), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record031_result⟩)
 (.branch 33
 (.leaf ⟨(23, 18255290859776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record032_result⟩)
 (.leaf ⟨(23, 18257507581952), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(23, 18265023742208), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record034_result⟩)
 (.branch 36
 (.leaf ⟨(23, 18265032130560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record035_result⟩)
 (.leaf ⟨(23, 18271933858048), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(23, 18272070205440), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record037_result⟩)
 (.branch 39
 (.leaf ⟨(23, 18272078528512), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record038_result⟩)
 (.leaf ⟨(23, 18288533381184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(23, 18289658986752), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record040_result⟩)
 (.branch 42
 (.leaf ⟨(23, 18289659052032), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record041_result⟩)
 (.leaf ⟨(23, 18297980485888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(23, 18297980551168), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record043_result⟩)
 (.branch 45
 (.leaf ⟨(23, 18298316005504), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record044_result⟩)
 (.leaf ⟨(23, 18319314845952), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(23, 18327300800768), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record046_result⟩)
 (.leaf ⟨(23, 18327309189120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record047_result⟩))
 (.branch 49
 (.leaf ⟨(23, 18333749510144), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record048_result⟩)
 (.leaf ⟨(23, 18336494714880), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(23, 18336503037952), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record050_result⟩)
 (.branch 52
 (.leaf ⟨(23, 18370381512960), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record051_result⟩)
 (.leaf ⟨(23, 18370393022464), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(23, 18384762765568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record053_result⟩)
 (.branch 55
 (.leaf ⟨(23, 18384771153920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record054_result⟩)
 (.leaf ⟨(23, 18385278894336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(23, 18402462728192), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record056_result⟩)
 (.branch 58
 (.leaf ⟨(23, 18406082511104), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record057_result⟩)
 (.leaf ⟨(23, 18406350979072), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(23, 18406359236608), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record059_result⟩)
 (.branch 61
 (.leaf ⟨(23, 18406359302144), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record060_result⟩)
 (.leaf ⟨(23, 18406887653888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(23, 18406896041984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record062_result⟩)
 (.branch 64
 (.leaf ⟨(23, 18471180075136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record063_result⟩)
 (.leaf ⟨(23, 18522338033664), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(23, 18526614126848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record065_result⟩)
 (.branch 67
 (.leaf ⟨(23, 18527150997504), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record066_result⟩)
 (.leaf ⟨(23, 18527159320576), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(23, 18530774876416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record068_result⟩)
 (.branch 70
 (.leaf ⟨(23, 18531039052544), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record069_result⟩)
 (.leaf ⟨(23, 18531047505920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(23, 18531311747072), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record071_result⟩)
 (.leaf ⟨(23, 18531320070144), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record072_result⟩))
 (.branch 74
 (.leaf ⟨(23, 18539364778240), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record073_result⟩)
 (.leaf ⟨(23, 18539901648896), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(23, 18540033769472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record075_result⟩)
 (.branch 77
 (.leaf ⟨(23, 18543793995776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record076_result⟩)
 (.leaf ⟨(23, 18544330801152), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(23, 18545738023168), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record078_result⟩)
 (.branch 80
 (.leaf ⟨(23, 18548491550720), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record079_result⟩)
 (.leaf ⟨(23, 18595736256512), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(23, 18731637965056), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record081_result⟩)
 (.branch 83
 (.leaf ⟨(23, 18778875265280), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record082_result⟩)
 (.leaf ⟨(23, 18779352342656), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(23, 18801894686976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record084_result⟩)
 (.branch 86
 (.leaf ⟨(23, 18814785847296), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record085_result⟩)
 (.leaf ⟨(23, 18817531052032), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(23, 18839414849536), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record087_result⟩)
 (.branch 89
 (.leaf ⟨(23, 18848000524544), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record088_result⟩)
 (.leaf ⟨(23, 18848000589824), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(23, 18848006815808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record090_result⟩)
 (.branch 92
 (.leaf ⟨(23, 18877062905856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record091_result⟩)
 (.leaf ⟨(23, 18881236254720), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(23, 18920003109120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record093_result⟩)
 (.branch 95
 (.leaf ⟨(23, 18920014618624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record094_result⟩)
 (.leaf ⟨(23, 19014233423872), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(23, 19014493438208), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record096_result⟩)
 (.leaf ⟨(23, 19014503907328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record097_result⟩))
 (.branch 99
 (.leaf ⟨(23, 19074151383296), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record098_result⟩)
 (.leaf ⟨(23, 19076772593664), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00010.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (6512 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 6512 6612 :=
  block_of_table results 6512 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0088
