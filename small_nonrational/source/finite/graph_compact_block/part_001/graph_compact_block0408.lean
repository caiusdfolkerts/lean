module
prelude
import GraphInputsRow27Part00005Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0408
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(27, 11472058974848), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record000_result⟩)
 (.branch 2
 (.leaf ⟨(27, 11472129229824), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record001_result⟩)
 (.leaf ⟨(27, 11548508651536), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(27, 11563467636752), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record003_result⟩)
 (.branch 5
 (.leaf ⟨(27, 11583824691216), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record004_result⟩)
 (.leaf ⟨(27, 11588381802512), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(27, 11709726081152), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record006_result⟩)
 (.branch 8
 (.leaf ⟨(27, 11931716943873), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record007_result⟩)
 (.leaf ⟨(27, 11958352904448), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(27, 11958352969728), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record009_result⟩)
 (.branch 11
 (.leaf ⟨(27, 11958553231360), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record010_result⟩)
 (.leaf ⟨(27, 11958604531968), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(27, 11958608726144), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record012_result⟩)
 (.branch 14
 (.leaf ⟨(27, 11958821601408), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record013_result⟩)
 (.leaf ⟨(27, 11958821634048), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(27, 11966334124160), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record015_result⟩)
 (.branch 17
 (.leaf ⟨(27, 11966334156800), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record016_result⟩)
 (.leaf ⟨(27, 11966335717376), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(27, 11974475778176), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record018_result⟩)
 (.branch 20
 (.leaf ⟨(27, 11974574868608), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record019_result⟩)
 (.leaf ⟨(27, 11983045296128), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(27, 11984099754112), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record021_result⟩)
 (.leaf ⟨(27, 11984101867520), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record022_result⟩))
 (.branch 24
 (.leaf ⟨(27, 11984105899008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record023_result⟩)
 (.leaf ⟨(27, 11984233824896), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(27, 11984304079872), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record025_result⟩)
 (.branch 27
 (.leaf ⟨(27, 11991704240128), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record026_result⟩)
 (.leaf ⟨(27, 11991838441472), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(27, 11991842603008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record028_result⟩)
 (.branch 30
 (.leaf ⟨(27, 11991844391040), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record029_result⟩)
 (.leaf ⟨(27, 11991963928584), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(27, 11992108632192), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record031_result⟩)
 (.branch 33
 (.leaf ⟨(27, 11996120615040), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record032_result⟩)
 (.leaf ⟨(27, 11996124677128), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(27, 11996141453313), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record034_result⟩)
 (.branch 36
 (.leaf ⟨(27, 12000277235712), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record035_result⟩)
 (.leaf ⟨(27, 12000417547272), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(27, 12000434323457), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record037_result⟩)
 (.branch 39
 (.leaf ⟨(27, 12000698564609), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record038_result⟩)
 (.leaf ⟨(27, 12021613593728), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(27, 12021617787904), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record040_result⟩)
 (.branch 42
 (.leaf ⟨(27, 12021881897476), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record041_result⟩)
 (.leaf ⟨(27, 12098425929856), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(27, 12138137600016), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record043_result⟩)
 (.branch 45
 (.leaf ⟨(27, 12234374332544), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record044_result⟩)
 (.leaf ⟨(27, 12255186927744), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(27, 12371810680848), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record046_result⟩)
 (.leaf ⟨(27, 12372213284880), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record047_result⟩))
 (.branch 49
 (.leaf ⟨(27, 12439857938560), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record048_result⟩)
 (.leaf ⟨(27, 12439857971200), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(27, 12465136091264), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record050_result⟩)
 (.branch 52
 (.leaf ⟨(27, 12465138204672), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record051_result⟩)
 (.leaf ⟨(27, 12465142236160), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(27, 12510575001600), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record053_result⟩)
 (.branch 55
 (.leaf ⟨(27, 12541465987200), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record054_result⟩)
 (.leaf ⟨(27, 12575756796032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(27, 12575756828672), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record056_result⟩)
 (.branch 58
 (.leaf ⟨(27, 12577954465920), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record057_result⟩)
 (.leaf ⟨(27, 12578103296000), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(27, 12578354889736), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record059_result⟩)
 (.branch 61
 (.leaf ⟨(27, 12580030711808), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record060_result⟩)
 (.leaf ⟨(27, 12584323581952), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(27, 12588952911872), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record062_result⟩)
 (.branch 64
 (.leaf ⟨(27, 12592913451136), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record063_result⟩)
 (.leaf ⟨(27, 12648972910608), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(27, 12653150175248), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record065_result⟩)
 (.branch 67
 (.leaf ⟨(27, 12653536264208), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record066_result⟩)
 (.leaf ⟨(27, 12713397157904), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(27, 12721970153488), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record068_result⟩)
 (.branch 70
 (.leaf ⟨(27, 13125441226752), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record069_result⟩)
 (.leaf ⟨(27, 13125697013768), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(27, 13125697143816), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record071_result⟩)
 (.leaf ⟨(27, 13125709791232), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record072_result⟩))
 (.branch 74
 (.leaf ⟨(27, 13125713920001), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record073_result⟩)
 (.leaf ⟨(27, 13134278560000), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(27, 13134412972032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record075_result⟩)
 (.branch 77
 (.leaf ⟨(27, 13136568516608), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record076_result⟩)
 (.leaf ⟨(27, 13340378468640), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(27, 13524656979968), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record078_result⟩)
 (.branch 80
 (.leaf ⟨(27, 13669607931904), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record079_result⟩)
 (.leaf ⟨(27, 13890486894624), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(27, 14220708085760), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record081_result⟩)
 (.branch 83
 (.leaf ⟨(27, 14220980649984), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record082_result⟩)
 (.leaf ⟨(27, 14221443072000), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(27, 14235740471552), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record084_result⟩)
 (.branch 86
 (.leaf ⟨(27, 14236277342208), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record085_result⟩)
 (.leaf ⟨(27, 14236285665280), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(27, 14236475523072), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record087_result⟩)
 (.branch 89
 (.leaf ⟨(27, 14250769678592), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record088_result⟩)
 (.leaf ⟨(27, 14486534619136), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(27, 14554180354048), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record090_result⟩)
 (.branch 92
 (.leaf ⟨(27, 14558605344768), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record091_result⟩)
 (.leaf ⟨(27, 14564846469120), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(27, 14589569826816), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record093_result⟩)
 (.branch 95
 (.leaf ⟨(27, 14589573988352), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record094_result⟩)
 (.leaf ⟨(27, 14613169061888), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(27, 14623424282880), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record096_result⟩)
 (.leaf ⟨(27, 14623428509696), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record097_result⟩))
 (.branch 99
 (.leaf ⟨(27, 14623432671232), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record098_result⟩)
 (.leaf ⟨(27, 14623436702720), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00005.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (18173 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 18173 18273 :=
  block_of_table results 18173 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0408
