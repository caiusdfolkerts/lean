module
prelude
import GraphInputsRow27Part00002Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0405
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(27, 3226057457792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record000_result⟩)
 (.branch 2
 (.leaf ⟨(27, 3226063602688), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record001_result⟩)
 (.leaf ⟨(27, 3234669363200), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(27, 3234673492096), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record003_result⟩)
 (.branch 5
 (.leaf ⟨(27, 3238965354496), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record004_result⟩)
 (.leaf ⟨(27, 3454439342208), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(27, 3527311261952), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record006_result⟩)
 (.branch 8
 (.leaf ⟨(27, 3527311327232), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record007_result⟩)
 (.leaf ⟨(27, 3665026908160), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(27, 3669187657728), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record009_result⟩)
 (.branch 11
 (.leaf ⟨(27, 3758509588480), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record010_result⟩)
 (.leaf ⟨(27, 3758769602816), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(27, 3758780071936), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record012_result⟩)
 (.branch 14
 (.leaf ⟨(27, 3775412601088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record013_result⟩)
 (.leaf ⟨(27, 3775681069056), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(27, 3775689392128), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record015_result⟩)
 (.branch 17
 (.leaf ⟨(27, 3776083673088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record016_result⟩)
 (.leaf ⟨(27, 3776217874432), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(27, 3796962904192), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record018_result⟩)
 (.branch 20
 (.leaf ⟨(27, 3799307583488), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record019_result⟩)
 (.leaf ⟨(27, 3809841577984), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(27, 3809982021632), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record021_result⟩)
 (.leaf ⟨(27, 3852741448064), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record022_result⟩))
 (.branch 24
 (.leaf ⟨(27, 3852873568640), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record023_result⟩)
 (.leaf ⟨(27, 3921577969936), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(27, 3921582131472), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record025_result⟩)
 (.branch 27
 (.leaf ⟨(27, 3921867800704), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record026_result⟩)
 (.leaf ⟨(27, 4004396498944), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(27, 4076731400448), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record028_result⟩)
 (.branch 30
 (.leaf ⟨(27, 4329465645064), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record029_result⟩)
 (.leaf ⟨(27, 4329889349760), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(27, 4333626393608), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record031_result⟩)
 (.branch 33
 (.leaf ⟨(27, 4333899024384), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record032_result⟩)
 (.leaf ⟨(27, 4338472747264), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(27, 4338476974080), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record034_result⟩)
 (.branch 36
 (.leaf ⟨(27, 4338483216384), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record035_result⟩)
 (.leaf ⟨(27, 4342350414080), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(27, 4342887284736), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record037_result⟩)
 (.branch 39
 (.leaf ⟨(27, 4342895607808), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record038_result⟩)
 (.leaf ⟨(27, 4346649643136), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(27, 4347050066952), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record040_result⟩)
 (.branch 42
 (.leaf ⟨(27, 4359530283008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record041_result⟩)
 (.leaf ⟨(27, 4359668760576), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(27, 4728161370112), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record043_result⟩)
 (.branch 45
 (.leaf ⟨(27, 4728169693184), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record044_result⟩)
 (.leaf ⟨(27, 4803994322176), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(27, 5120769229056), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record046_result⟩)
 (.leaf ⟨(27, 5138481741824), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record047_result⟩))
 (.branch 49
 (.leaf ⟨(27, 5140144947200), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record048_result⟩)
 (.leaf ⟨(27, 5140685783041), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(27, 5140941636352), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record050_result⟩)
 (.branch 52
 (.leaf ⟨(27, 5140950024704), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record051_result⟩)
 (.leaf ⟨(27, 5283956917504), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(27, 5394573393928), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record053_result⟩)
 (.branch 55
 (.leaf ⟨(27, 5396769243144), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record054_result⟩)
 (.leaf ⟨(27, 5397190639616), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(27, 5828357161216), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record056_result⟩)
 (.branch 58
 (.leaf ⟨(27, 5829413732608), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record057_result⟩)
 (.leaf ⟨(27, 5829413797888), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(27, 5830095142912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record059_result⟩)
 (.branch 61
 (.leaf ⟨(27, 5875601604864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record060_result⟩)
 (.leaf ⟨(27, 5877805580296), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(27, 5899150164996), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record062_result⟩)
 (.branch 64
 (.leaf ⟨(27, 5899414405636), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record063_result⟩)
 (.leaf ⟨(27, 5899414536193), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(27, 5899687035904), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record065_result⟩)
 (.branch 67
 (.leaf ⟨(27, 5904380461056), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record066_result⟩)
 (.leaf ⟨(27, 5972833599488), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(27, 5974913974272), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record068_result⟩)
 (.branch 70
 (.leaf ⟨(27, 5998538407936), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record069_result⟩)
 (.leaf ⟨(27, 6048447545728), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(27, 6048480575872), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record071_result⟩)
 (.leaf ⟨(27, 6050017776000), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record072_result⟩))
 (.branch 74
 (.leaf ⟨(27, 6086245681424), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record073_result⟩)
 (.leaf ⟨(27, 6340499046400), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(27, 6340532011264), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record075_result⟩)
 (.branch 77
 (.leaf ⟨(27, 6343310180352), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record076_result⟩)
 (.leaf ⟨(27, 6378844323841), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(27, 6379104503040), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record078_result⟩)
 (.branch 80
 (.leaf ⟨(27, 6379104568320), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record079_result⟩)
 (.leaf ⟨(27, 6379112760324), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(27, 6379377000964), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record081_result⟩)
 (.branch 83
 (.leaf ⟨(27, 6379377131521), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record082_result⟩)
 (.leaf ⟨(27, 6379905483520), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(27, 6379918065664), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record084_result⟩)
 (.branch 86
 (.leaf ⟨(27, 6425296470024), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record085_result⟩)
 (.leaf ⟨(27, 6425548097544), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(27, 6433869595656), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record087_result⟩)
 (.branch 89
 (.leaf ⟨(27, 6442455335944), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record088_result⟩)
 (.leaf ⟨(27, 6447563800576), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(27, 6451871350784), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record090_result⟩)
 (.branch 92
 (.leaf ⟨(27, 6456149540864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record091_result⟩)
 (.leaf ⟨(27, 6487088824320), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(27, 6524600713216), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record093_result⟩)
 (.branch 95
 (.leaf ⟨(27, 6548361314304), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record094_result⟩)
 (.leaf ⟨(27, 6559027429376), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(27, 6633730703744), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record096_result⟩)
 (.leaf ⟨(27, 6701436731400), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record097_result⟩))
 (.branch 99
 (.leaf ⟨(27, 6701514301696), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record098_result⟩)
 (.leaf ⟨(27, 6701568851976), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17873 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 17873 17973 :=
  block_of_table results 17873 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0405
