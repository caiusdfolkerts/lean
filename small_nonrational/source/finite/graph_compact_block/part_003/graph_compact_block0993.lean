module
prelude
import GraphInputsSix0Part00028Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0993
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 10909359671424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 10909760095240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record001_result⟩)
 (.leaf ⟨(32, 10909776871425), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 10922512875520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 10937272697088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record004_result⟩)
 (.leaf ⟨(32, 10937545326592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 10939353071872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 10940088123392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record007_result⟩)
 (.leaf ⟨(32, 10956805505024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 11033106284800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 11033110478976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record010_result⟩)
 (.leaf ⟨(32, 11035058733184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 11035186659584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 11035190853760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record013_result⟩)
 (.leaf ⟨(32, 11036333801488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 11039347409152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 11039351603328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record016_result⟩)
 (.leaf ⟨(32, 11039481610496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 11039485804672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 11039551864960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record019_result⟩)
 (.leaf ⟨(32, 11040626671632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 11047937343616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record021_result⟩)
 (.leaf ⟨(32, 11048071512320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 11048071544960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record023_result⟩)
 (.leaf ⟨(32, 11073840300288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 11074919301136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 11082430234752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record026_result⟩)
 (.leaf ⟨(32, 11099559739648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 11125244592384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 11125252980736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record029_result⟩)
 (.leaf ⟨(32, 11125376712960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 11125380939776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 11125385101312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record032_result⟩)
 (.leaf ⟨(32, 11125645148288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 11125845409920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 11139211690000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record035_result⟩)
 (.leaf ⟨(32, 11139343810576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 11142423478528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 11142425559296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record038_result⟩)
 (.leaf ⟨(32, 11142429753472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 11143638761488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 11143704821776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record041_result⟩)
 (.leaf ⟨(32, 11151013412992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 11151015461120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 11151015493760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record044_result⟩)
 (.leaf ⟨(32, 11168144998656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 11178061398272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record046_result⟩)
 (.leaf ⟨(32, 11178067640576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 11180947014912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record048_result⟩)
 (.leaf ⟨(32, 11181079200000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 11181087588352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 11181219708928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record051_result⟩)
 (.leaf ⟨(32, 11181479723264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 11181488111616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 11189669101824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record054_result⟩)
 (.leaf ⟨(32, 11189677490176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 11189801222400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 11189805449216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record057_result⟩)
 (.leaf ⟨(32, 11189809610752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 11190069657728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 11190269919360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record060_result⟩)
 (.leaf ⟨(32, 11193970360320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 11197551231104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 11205112512640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record063_result⟩)
 (.leaf ⟨(32, 11211551817856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 11212592005248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 11214574854400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record066_result⟩)
 (.leaf ⟨(32, 11222013477120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 11222021865472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 11222281912448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record069_result⟩)
 (.leaf ⟨(32, 11235722838272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 11235924140288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record071_result⟩)
 (.leaf ⟨(32, 11237920508160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 11237937152768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record073_result⟩)
 (.leaf ⟨(32, 11237945540864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 11237945606144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 11238073499904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record076_result⟩)
 (.leaf ⟨(32, 11238077661440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 11238077726720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 11238197168384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record079_result⟩)
 (.leaf ⟨(32, 11238341902592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 11238341967872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 11238346096768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record082_result⟩)
 (.leaf ⟨(32, 11238348177536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 11238465603712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 11242894786561), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record085_result⟩)
 (.leaf ⟨(32, 11244438292736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 11244512805120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 11244519112704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record088_result⟩)
 (.leaf ⟨(32, 11244570413312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 11244781207808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 11244781273088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record091_result⟩)
 (.leaf ⟨(32, 11244783353856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 11244787482752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 11244838848640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record094_result⟩)
 (.leaf ⟨(32, 11246778777856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 11246787166208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record096_result⟩)
 (.leaf ⟨(32, 11247055536129), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 11253028227200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record098_result⟩)
 (.leaf ⟨(32, 11253156153600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00028.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (29586 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 29586 29686 :=
  block_of_table results 29586 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0993
