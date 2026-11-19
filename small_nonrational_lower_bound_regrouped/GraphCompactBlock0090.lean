module
prelude
import GraphInputsRow23Part00012Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0090
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 20690279333888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 20690539413504), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record001_result⟩)
 (.leaf ⟨(23, 20694295412992), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(23, 20694572204032), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record003_result⟩)
 (.branch 5
 (.leaf ⟨(23, 20694638264320), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004_result⟩)
 (.leaf ⟨(23, 20694832283648), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(23, 20702885347456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 20710366920832), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record007_result⟩)
 (.leaf ⟨(23, 20711611564032), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(23, 20723238207744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record009_result⟩)
 (.branch 11
 (.leaf ⟨(23, 20723506675712), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record010_result⟩)
 (.leaf ⟨(23, 20723514998784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(23, 20723775078400), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record012_result⟩)
 (.branch 14
 (.leaf ⟨(23, 20724022804480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record013_result⟩)
 (.leaf ⟨(23, 20727531077888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(23, 20727807868928), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 20727915151360), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record016_result⟩)
 (.leaf ⟨(23, 20728067948544), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(23, 20728072110080), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record018_result⟩)
 (.branch 20
 (.leaf ⟨(23, 20728183554048), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record019_result⟩)
 (.leaf ⟨(23, 20731807301888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(23, 20732612444672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record021_result⟩)
 (.leaf ⟨(23, 20736505053184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record022_result⟩))
 (.branch 24
 (.leaf ⟨(23, 20748987170816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record023_result⟩)
 (.leaf ⟨(23, 20749255573504), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(23, 20758856269824), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record025_result⟩)
 (.branch 27
 (.leaf ⟨(23, 20792091934720), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record026_result⟩)
 (.leaf ⟨(23, 20792608063488), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(23, 20800937656320), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record028_result⟩)
 (.branch 30
 (.leaf ⟨(23, 20824304189440), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record029_result⟩)
 (.leaf ⟨(23, 20824820318208), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(23, 20826900692992), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record031_result⟩)
 (.branch 33
 (.leaf ⟨(23, 20833149911040), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record032_result⟩)
 (.leaf ⟨(23, 20839382941696), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(23, 20931130982400), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record034_result⟩)
 (.branch 36
 (.leaf ⟨(23, 20965423611904), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record035_result⟩)
 (.leaf ⟨(23, 20966554501376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(23, 20977905860608), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record037_result⟩)
 (.branch 39
 (.leaf ⟨(23, 21007360393216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record038_result⟩)
 (.leaf ⟨(23, 21007368716288), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(23, 21076077772800), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record040_result⟩)
 (.branch 42
 (.leaf ⟨(23, 21076086095872), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record041_result⟩)
 (.leaf ⟨(23, 21118423433472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(23, 21119160565760), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record043_result⟩)
 (.branch 45
 (.leaf ⟨(23, 21257072410624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record044_result⟩)
 (.leaf ⟨(23, 21350955614208), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(23, 21367598612480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record046_result⟩)
 (.leaf ⟨(23, 21374041096448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record047_result⟩))
 (.branch 49
 (.leaf ⟨(23, 21378338193408), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record048_result⟩)
 (.leaf ⟨(23, 21378610757632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(23, 21379007119360), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record050_result⟩)
 (.branch 52
 (.leaf ⟨(23, 21382631063552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record051_result⟩)
 (.leaf ⟨(23, 21383167868928), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(23, 21384711438336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record053_result⟩)
 (.branch 55
 (.leaf ⟨(23, 21397596291072), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record054_result⟩)
 (.leaf ⟨(23, 21401891241984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(23, 21402023362560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record056_result⟩)
 (.branch 58
 (.leaf ⟨(23, 21446017483008), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record057_result⟩)
 (.leaf ⟨(23, 21446426394624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(23, 21446517096704), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record059_result⟩)
 (.branch 61
 (.leaf ⟨(23, 21462623195264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record060_result⟩)
 (.leaf ⟨(23, 21514045391104), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(23, 21514053779456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record062_result⟩)
 (.branch 64
 (.leaf ⟨(23, 21514837623040), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record063_result⟩)
 (.leaf ⟨(23, 21515110350848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(23, 21515374493696), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record065_result⟩)
 (.branch 67
 (.leaf ⟨(23, 21515382816768), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record066_result⟩)
 (.leaf ⟨(23, 21518998372608), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(23, 21519271002112), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record068_result⟩)
 (.branch 70
 (.leaf ⟨(23, 21519535243264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record069_result⟩)
 (.leaf ⟨(23, 21519543566336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(23, 21519667363840), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record071_result⟩)
 (.leaf ⟨(23, 21522118934784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record072_result⟩))
 (.branch 74
 (.leaf ⟨(23, 21522887016448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record073_result⟩)
 (.leaf ⟨(23, 21527047442560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(23, 21528120918656), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record075_result⟩)
 (.branch 77
 (.leaf ⟨(23, 21535001706752), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record076_result⟩)
 (.leaf ⟨(23, 21535771869184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(23, 21588252622848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record078_result⟩)
 (.branch 80
 (.leaf ⟨(23, 21588260945920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record079_result⟩)
 (.leaf ⟨(23, 21591472275456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(23, 21596305654016), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record081_result⟩)
 (.branch 83
 (.leaf ⟨(23, 21596574121984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record082_result⟩)
 (.leaf ⟨(23, 21596582445056), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(23, 21596976726016), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record084_result⟩)
 (.branch 86
 (.leaf ⟨(23, 21599426216192), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record085_result⟩)
 (.leaf ⟨(23, 21600196378624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(23, 21668110172416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record087_result⟩)
 (.branch 89
 (.leaf ⟨(23, 21668915315200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record088_result⟩)
 (.leaf ⟨(23, 21728642793472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(23, 21921531986176), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record090_result⟩)
 (.branch 92
 (.leaf ⟨(23, 21925829083136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record091_result⟩)
 (.leaf ⟨(23, 21926101647360), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(23, 21926613614592), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record093_result⟩)
 (.branch 95
 (.leaf ⟨(23, 21930121953280), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record094_result⟩)
 (.leaf ⟨(23, 21930658758656), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(23, 21930774364160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record096_result⟩)
 (.leaf ⟨(23, 21934398177280), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record097_result⟩))
 (.branch 99
 (.leaf ⟨(23, 21947283030016), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record098_result⟩)
 (.leaf ⟨(23, 21951577980928), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (6712 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 6712 6812 :=
  block_of_table results 6712 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0090
