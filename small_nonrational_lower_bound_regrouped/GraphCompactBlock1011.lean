module
prelude
import GraphInputsSix0Part00046Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1011
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 18400196722944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 18400254363776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record001_result⟩)
 (.leaf ⟨(32, 18402479505408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 18402487828480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 18402594816256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record004_result⟩)
 (.leaf ⟨(32, 18402605285376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 18406086673664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 18406086738944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record007_result⟩)
 (.leaf ⟨(32, 18406094930948), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 18406350979328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 18406355042560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record010_result⟩)
 (.leaf ⟨(32, 18406359171588), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 18406359302145), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 18406359367680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record013_result⟩)
 (.leaf ⟨(32, 18406619382016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 18406627770368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 18406631801856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record016_result⟩)
 (.leaf ⟨(32, 18406887654144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 18406891913216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 18406900236288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record019_result⟩)
 (.leaf ⟨(32, 18409036202240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 18410515792128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record021_result⟩)
 (.leaf ⟨(32, 18410788421632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 18411052662784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record023_result⟩)
 (.leaf ⟨(32, 18411060985856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 18411184783360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 18411325227008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record026_result⟩)
 (.leaf ⟨(32, 18435277947008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 18435280027776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 18435415261440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record029_result⟩)
 (.leaf ⟨(32, 18452409532672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 18454813901056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 18455082336384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record032_result⟩)
 (.leaf ⟨(32, 18455630225664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 18456762155264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 18456894275840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record035_result⟩)
 (.leaf ⟨(32, 18456960336128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 18457162711168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 18458033553664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record038_result⟩)
 (.leaf ⟨(32, 18458202898560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 18461055025408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 18471993769984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record041_result⟩)
 (.leaf ⟨(32, 18472253816960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 18473933635840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 18473942024192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record044_result⟩)
 (.leaf ⟨(32, 18474065756416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 18474069983232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record046_result⟩)
 (.leaf ⟨(32, 18474074144768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 18474334191744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record048_result⟩)
 (.leaf ⟨(32, 18474470506496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 18474534453376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 18478234894336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record051_result⟩)
 (.leaf ⟨(32, 18481355456512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 18481454546944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 18489377046656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record054_result⟩)
 (.leaf ⟨(32, 18495816351872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 18496856539264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 18513567711232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record057_result⟩)
 (.leaf ⟨(32, 18519987372288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 18520188674304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 18522185042176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record060_result⟩)
 (.leaf ⟨(32, 18522201686784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 18522210074880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 18522210140160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record063_result⟩)
 (.leaf ⟨(32, 18522338033920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 18522342195456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 18522342260736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record066_result⟩)
 (.leaf ⟨(32, 18522461702400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 18522606436608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 18522606501888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record069_result⟩)
 (.leaf ⟨(32, 18522610630784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 18522612711552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record071_result⟩)
 (.leaf ⟨(32, 18522730137728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 18527159320577), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record073_result⟩)
 (.leaf ⟨(32, 18528702826752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 18528777339136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 18528783646720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record076_result⟩)
 (.leaf ⟨(32, 18528834947328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 18529045741824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 18529045807104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record079_result⟩)
 (.leaf ⟨(32, 18529047887872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 18529052016768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 18529103382656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record082_result⟩)
 (.leaf ⟨(32, 18531043311872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 18531051700224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 18531320070145), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record085_result⟩)
 (.leaf ⟨(32, 18537292761216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 18537420687616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 18537424881792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record088_result⟩)
 (.leaf ⟨(32, 18537635676288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 18537637757056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 18537637789696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record091_result⟩)
 (.leaf ⟨(32, 18543789900032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 18543794126848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 18543798288384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record094_result⟩)
 (.leaf ⟨(32, 18543802319872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 18544058335360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record096_result⟩)
 (.leaf ⟨(32, 18544326607488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 18547950649600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record098_result⟩)
 (.leaf ⟨(32, 18547959037952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (31350 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 31350 31450 :=
  block_of_table results 31350 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1011
