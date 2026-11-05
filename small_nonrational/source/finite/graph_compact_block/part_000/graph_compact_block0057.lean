module
prelude
import GraphInputsRow19Part00017Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0057
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 19913233170560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 19913235283968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record001_result⟩)
 (.leaf ⟨(19, 19936872268032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 19951300722816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 19951401373824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record004_result⟩)
 (.leaf ⟨(19, 19977178480896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 19977178546176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 19977312747520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record007_result⟩)
 (.leaf ⟨(19, 19977576988672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 19977717432320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 19977719513088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record010_result⟩)
 (.leaf ⟨(19, 19977849552896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 19977909370880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 19977915613184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record013_result⟩)
 (.leaf ⟨(19, 20003077308672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 20012511297792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 20012511363072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record016_result⟩)
 (.leaf ⟨(19, 20012711624704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 20012744654848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 20020257112320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record019_result⟩)
 (.leaf ⟨(19, 20025458114560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 20034166538496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record021_result⟩)
 (.leaf ⟨(19, 20034170748992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 20036312973568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record023_result⟩)
 (.leaf ⟨(19, 20040605843712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 20040663515144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 20040927756296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record026_result⟩)
 (.leaf ⟨(19, 20047036891136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 20047038776576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 20047707767296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record029_result⟩)
 (.leaf ⟨(19, 20055622566144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 20055624516864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 20059783380992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record032_result⟩)
 (.leaf ⟨(19, 20059923678272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 20061863690496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 20061863755776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record035_result⟩)
 (.leaf ⟨(19, 20061930856448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 20062063822080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 20062070113344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record038_result⟩)
 (.leaf ⟨(19, 20073776496768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 20138369794304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 20141556416768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record041_result⟩)
 (.leaf ⟨(19, 20149873885312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 20149881168000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 20149981819008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record044_result⟩)
 (.leaf ⟨(19, 20150146318592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 20171605459200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record046_result⟩)
 (.leaf ⟨(19, 20173751894272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 20274549408000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record048_result⟩)
 (.leaf ⟨(19, 20274681528576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 20276829004032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 20428530696192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record051_result⟩)
 (.leaf ⟨(19, 20492535791872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 20492539953408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 20492540018688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record054_result⟩)
 (.leaf ⟨(19, 20493204783104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 20493211025408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 20548353622272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record057_result⟩)
 (.leaf ⟨(19, 20548487823616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 20548491985152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 20548543414280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record060_result⟩)
 (.leaf ⟨(19, 20548756226304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 20561962992128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 20570014023680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record063_result⟩)
 (.leaf ⟨(19, 20572948939008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 20572949004288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 20573049135104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record066_result⟩)
 (.leaf ⟨(19, 20574038540544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 20574038605824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 20574040491264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record069_result⟩)
 (.leaf ⟨(19, 20574105706496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 20574106551552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record071_result⟩)
 (.leaf ⟨(19, 20597191016448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 20685926744320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record073_result⟩)
 (.leaf ⟨(19, 20694635127040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 20727921117440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 20730068664320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record076_result⟩)
 (.leaf ⟨(19, 20754445943040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 20754512003328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 20755717341440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record079_result⟩)
 (.leaf ⟨(19, 20822089842944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 20822156943616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 20824287512832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record082_result⟩)
 (.leaf ⟨(19, 21042826379264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 21042832621568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 21051285184576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record085_result⟩)
 (.leaf ⟨(19, 21058401345600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 21110913712128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 21118648328256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record088_result⟩)
 (.leaf ⟨(19, 21119497371648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 21119499387136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 21119499452416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record091_result⟩)
 (.leaf ⟨(19, 21119566553088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 21119699518720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 21119704899648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record094_result⟩)
 (.leaf ⟨(19, 21119704915968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 21122709987392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record096_result⟩)
 (.leaf ⟨(19, 21123792322560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 21126986211392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record098_result⟩)
 (.leaf ⟨(19, 21316611088448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00017.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (3765 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 3765 3865 :=
  block_of_table results 3765 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0057
