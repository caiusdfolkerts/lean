module
prelude
import GraphInputsSix0Part00029Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0994
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 11253160347776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 11253371142272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record001_result⟩)
 (.leaf ⟨(32, 11253373223040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 11253373255680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 11276778569744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record004_result⟩)
 (.leaf ⟨(32, 11281073520656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 11288454414464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 11307984126208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record007_result⟩)
 (.leaf ⟨(32, 11307984191488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 11307988320384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 11307990401152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record010_result⟩)
 (.leaf ⟨(32, 11309936574592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 11310064500992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 11310064566272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record013_result⟩)
 (.leaf ⟨(32, 11310068695168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 11310070775936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 11310134755456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record016_result⟩)
 (.leaf ⟨(32, 11314359517184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 11314363646080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 11314426617856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record019_result⟩)
 (.leaf ⟨(32, 11314429706368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 11325159800960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record021_result⟩)
 (.leaf ⟨(32, 11325163995136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 11327108055168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record023_result⟩)
 (.leaf ⟨(32, 11327240175744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 11327244369920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 11331400925312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record026_result⟩)
 (.leaf ⟨(32, 11331405119488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 11331601186944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 11334521487488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record029_result⟩)
 (.leaf ⟨(32, 11334525681664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 11334591741952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 11334721749120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record032_result⟩)
 (.leaf ⟨(32, 11342283030656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 11348722335872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 11349795553408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record035_result⟩)
 (.leaf ⟨(32, 11366733742208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 11375384494208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 11375512420608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record038_result⟩)
 (.leaf ⟨(32, 11375512485888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 11375516614784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 11375518695552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record041_result⟩)
 (.leaf ⟨(32, 11375636121728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 11375780855936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 11381877246080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record044_result⟩)
 (.leaf ⟨(32, 11381951725824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 11381951791104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record046_result⟩)
 (.leaf ⟨(32, 11381953871872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 11381958000768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record048_result⟩)
 (.leaf ⟨(32, 11382005172480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 11382009366656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 11382220161152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record051_result⟩)
 (.leaf ⟨(32, 11382222241920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 11382222274560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 11384226054145), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record054_result⟩)
 (.leaf ⟨(32, 11390595106944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 11396964319360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 11396968513536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record057_result⟩)
 (.leaf ⟨(32, 11401125068928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 11401129263104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 11401259270272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record060_result⟩)
 (.leaf ⟨(32, 11401265415168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 11401393341056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 11410862014720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record063_result⟩)
 (.leaf ⟨(32, 11410862080000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 11410866208896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 11410868289664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record066_result⟩)
 (.leaf ⟨(32, 11410996281344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 11411000410240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 11411066470528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record069_result⟩)
 (.leaf ⟨(32, 11413142716416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 11413146845312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record071_result⟩)
 (.leaf ⟨(32, 11414085861504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 11414217494528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record073_result⟩)
 (.leaf ⟨(32, 11414220062848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 11417301319936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 11417301385216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record076_result⟩)
 (.leaf ⟨(32, 11417303465984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 11417307594880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 11422568317184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record079_result⟩)
 (.leaf ⟨(32, 11422572544000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 11422576705536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 11422671634432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record082_result⟩)
 (.leaf ⟨(32, 11423037014144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 11431158251648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 11431162445824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record085_result⟩)
 (.leaf ⟨(32, 11431261536256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 11431358513280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 11434481188864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record088_result⟩)
 (.leaf ⟨(32, 11435521376256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 11444097679616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 11444097744896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record091_result⟩)
 (.leaf ⟨(32, 11444101873792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 11444103954560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 11444231946240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record094_result⟩)
 (.leaf ⟨(32, 11444236075136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 11444349307136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record096_result⟩)
 (.leaf ⟨(32, 11444353501312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 11444500316288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record098_result⟩)
 (.leaf ⟨(32, 11444500348928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00029.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (29686 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 29686 29786 :=
  block_of_table results 29686 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0994
