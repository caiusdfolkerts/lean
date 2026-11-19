module
prelude
import GraphInputsSix0Part00057Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1022
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 22068960772352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 22069229175040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record001_result⟩)
 (.leaf ⟨(32, 22069229224000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 22069230272544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 22077546512640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record004_result⟩)
 (.leaf ⟨(32, 22077550674176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 22077550723136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 22077551771680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record007_result⟩)
 (.leaf ⟨(32, 22077816012832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 22100031275264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 22100437926144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record010_result⟩)
 (.leaf ⟨(32, 22102196437248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 22102460678400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 22102464839936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record013_result⟩)
 (.leaf ⟨(32, 22102464888896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 22102465937440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 22104665768192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record016_result⟩)
 (.leaf ⟨(32, 22104730796288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 22111050580224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 22111050629184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record019_result⟩)
 (.leaf ⟨(32, 22111051677728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 22113052295424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record021_result⟩)
 (.leaf ⟨(32, 22137948684352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 22137949732896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record023_result⟩)
 (.leaf ⟨(32, 22146270183488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 22146271232032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 22146535473184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record026_result⟩)
 (.leaf ⟨(32, 22146538586176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 22173383147776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 22181968888064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record029_result⟩)
 (.leaf ⟨(32, 22181975179328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 22242094285056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 22250684186880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record032_result⟩)
 (.leaf ⟨(32, 22250694656000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 22259274153984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 22283704942656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record035_result⟩)
 (.leaf ⟨(32, 22283705991200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 22283709104192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 22283974393888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record038_result⟩)
 (.leaf ⟨(32, 22302903271680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 22320083140608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 22323203702784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record041_result⟩)
 (.leaf ⟨(32, 22379264803072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 22379533205760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 22379543674880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record044_result⟩)
 (.leaf ⟨(32, 22396444672000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 22396981477376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record046_result⟩)
 (.leaf ⟨(32, 22443689312512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 22443957715200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record048_result⟩)
 (.leaf ⟨(32, 22443968184320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 22448252666112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 22448261054464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record051_result⟩)
 (.leaf ⟨(32, 22456846794752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 22457042878528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 22464895664384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record054_result⟩)
 (.leaf ⟨(32, 22465029931008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 22465038254080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 22465432535040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record057_result⟩)
 (.leaf ⟨(32, 22465498595328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 22482619744256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 22545940185120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record060_result⟩)
 (.leaf ⟨(32, 22550233055264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 22558818795552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 22578387239168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record063_result⟩)
 (.leaf ⟨(32, 22584628363520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 22592949862656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 22594493354048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record066_result⟩)
 (.leaf ⟨(32, 22614693150976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 22617591980288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 22617856221440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record069_result⟩)
 (.leaf ⟨(32, 22617860440096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 22618986021120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record071_result⟩)
 (.leaf ⟨(32, 22626446123264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 22626446180384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record073_result⟩)
 (.leaf ⟨(32, 22627571761408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 22650319601920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 22651934542080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record076_result⟩)
 (.leaf ⟨(32, 22651951186688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 22652221686016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 22654480351488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record079_result⟩)
 (.leaf ⟨(32, 22660807426304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 22662801850624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 22665348808960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record082_result⟩)
 (.leaf ⟨(32, 22686579892288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 22686579900448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 22687636463680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record085_result⟩)
 (.leaf ⟨(32, 22687636471840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 22687704432896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 22695169794112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record088_result⟩)
 (.leaf ⟨(32, 22695169802272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 22696025932032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 22697371242560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record091_result⟩)
 (.leaf ⟨(32, 22715815756032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 22722056880384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 22723740893440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record094_result⟩)
 (.leaf ⟨(32, 22724277764096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 22730378379520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record096_result⟩)
 (.leaf ⟨(32, 22730646782208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 22730657251328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record098_result⟩)
 (.leaf ⟨(32, 22732326633728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00057.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (32420 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 32420 32520 :=
  block_of_table results 32420 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1022
