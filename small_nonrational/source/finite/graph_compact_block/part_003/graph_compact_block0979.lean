module
prelude
import GraphInputsSix0Part00014Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0979
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 6333612953856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 6339928621072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record001_result⟩)
 (.leaf ⟨(32, 6339934314624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 6340498981120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 6340499046400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record004_result⟩)
 (.leaf ⟨(32, 6340532011264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 6340659413248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 6340659478528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record007_result⟩)
 (.leaf ⟨(32, 6340787372288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 6340791533824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 6340791599104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record010_result⟩)
 (.leaf ⟨(32, 6340793614592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 6341263368256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 6342337105984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record013_result⟩)
 (.leaf ⟨(32, 6343301857280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 6343310180352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 6369847607552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record016_result⟩)
 (.leaf ⟨(32, 6370111848704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 6370120237056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 6378833871104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record019_result⟩)
 (.leaf ⟨(32, 6378844323841), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 6379104503040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record021_result⟩)
 (.leaf ⟨(32, 6379104568320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 6379112760324), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record023_result⟩)
 (.leaf ⟨(32, 6379368808704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 6379372871936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 6379377000964), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record026_result⟩)
 (.leaf ⟨(32, 6379377131521), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 6379377197056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 6379637211392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record029_result⟩)
 (.leaf ⟨(32, 6379645599744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 6379649631232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 6379905483520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record032_result⟩)
 (.leaf ⟨(32, 6379909742592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 6379918065664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 6413192560896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record035_result⟩)
 (.leaf ⟨(32, 6413204062209), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 6413204070400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 6425288343808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record038_result⟩)
 (.leaf ⟨(32, 6425292245248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 6425296470024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 6425548097544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record041_result⟩)
 (.leaf ⟨(32, 6425565004032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 6425816500232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 6425833406720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record044_result⟩)
 (.leaf ⟨(32, 6425833472000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 6425837308160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record046_result⟩)
 (.leaf ⟨(32, 6433869595656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 6434154676480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record048_result⟩)
 (.leaf ⟨(32, 6434406402304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 6434406467584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 6434418917632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record051_result⟩)
 (.leaf ⟨(32, 6434427305984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 6434666643712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 6438432866560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record054_result⟩)
 (.leaf ⟨(32, 6438969737216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 6442455335944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 6442727901440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record057_result⟩)
 (.leaf ⟨(32, 6442996336768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 6443000398856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 6443017175041), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record060_result⟩)
 (.leaf ⟨(32, 6443256545536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 6443268835328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 6447018606848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record063_result⟩)
 (.leaf ⟨(32, 6447555477504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 6447563800576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 6451179356416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record066_result⟩)
 (.leaf ⟨(32, 6451846185728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 6451871350784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 6455612735488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record069_result⟩)
 (.leaf ⟨(32, 6456149540864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 6463263146240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record071_result⟩)
 (.leaf ⟨(32, 6463527387392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 6463535775744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record073_result⟩)
 (.leaf ⟨(32, 6463659507968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 6466383708416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 6466647949568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record076_result⟩)
 (.leaf ⟨(32, 6466656337920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 6469900632320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 6469909020672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record079_result⟩)
 (.leaf ⟨(32, 6478222131456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 6478230519808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 6478490534144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record082_result⟩)
 (.leaf ⟨(32, 6478501003264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 6478690795776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 6486543630592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record085_result⟩)
 (.leaf ⟨(32, 6486684139520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 6487080501248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 6487088824320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record088_result⟩)
 (.leaf ⟨(32, 6498579185920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 6498843427072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 6498851815424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record091_result⟩)
 (.leaf ⟨(32, 6499091153152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 6503136297216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 6503144685568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record094_result⟩)
 (.leaf ⟨(32, 6503251902720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 6511573401856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record096_result⟩)
 (.leaf ⟨(32, 6511726199040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 6511730425856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record098_result⟩)
 (.leaf ⟨(32, 6511736668160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (28186 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 28186 28286 :=
  block_of_table results 28186 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0979
