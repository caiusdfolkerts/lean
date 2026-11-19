module
prelude
import GraphInputsRow19Part00010Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0050
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 16175992078336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 16356651043072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record001_result⟩)
 (.leaf ⟨(19, 16359837665536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 16398323681536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 16401817403392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record004_result⟩)
 (.leaf ⟨(19, 16424245397760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 16432616311040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 16496472408320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record007_result⟩)
 (.leaf ⟨(19, 16498354602240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 16502650650656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 16532675560196), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010_result⟩)
 (.leaf ⟨(19, 16532744765696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 16532748927232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 16532748992512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record013_result⟩)
 (.leaf ⟨(19, 16536180408576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 16536184111120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 16540331151616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record016_result⟩)
 (.leaf ⟨(19, 16565978865920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 16570542276640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 16570542800912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record019_result⟩)
 (.leaf ⟨(19, 16575655641344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 16576192512000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record021_result⟩)
 (.leaf ⟨(19, 16576200835072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 16605763403776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record023_result⟩)
 (.leaf ⟨(19, 16606894293248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 16607162695936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 16607174725632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record026_result⟩)
 (.leaf ⟨(19, 16607975899136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 16608240140288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 16608248463360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record029_result⟩)
 (.leaf ⟨(19, 16608512704512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 16610823831808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 16611096461312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record032_result⟩)
 (.leaf ⟨(19, 16611360702464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 16611369025536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 16611591913472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record035_result⟩)
 (.leaf ⟨(19, 16614349144064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 16623706603776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 16623842951168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record038_result⟩)
 (.leaf ⟨(19, 16623851274240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 16624074162176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 16624610967552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record041_result⟩)
 (.leaf ⟨(19, 16632556634128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 16634703069200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 16640339615808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record044_result⟩)
 (.leaf ⟨(19, 16640365314304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 16640367460352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record046_result⟩)
 (.leaf ⟨(19, 16640373702656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 16644777771008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record048_result⟩)
 (.leaf ⟨(19, 16644786094080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 16648661114944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 16652842311680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record051_result⟩)
 (.leaf ⟨(19, 16652974432256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 16655942426688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 16687227273216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record054_result⟩)
 (.leaf ⟨(19, 16687499837440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 16688267460608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 16688275783680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record057_result⟩)
 (.leaf ⟨(19, 16700062892288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 16700067053824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 16700067119104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record060_result⟩)
 (.leaf ⟨(19, 16700195012864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 16700201320448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 16700202295552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record063_result⟩)
 (.leaf ⟨(19, 16700465561600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 16700469723136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 16700516862208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record066_result⟩)
 (.leaf ⟨(19, 16702660182272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 16703421948160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 16707979059456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record069_result⟩)
 (.leaf ⟨(19, 16708003694624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 16711769194752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record071_result⟩)
 (.leaf ⟨(19, 16711777583104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 16712280317952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record073_result⟩)
 (.leaf ⟨(19, 16716589434912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 16720359096576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 16720363323392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record076_result⟩)
 (.leaf ⟨(19, 16720370606080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 16720601817088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 16721448698112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record079_result⟩)
 (.leaf ⟨(19, 16721452924928), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 16721461117952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 16721650000128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record082_result⟩)
 (.leaf ⟨(19, 16721658388480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 16721659298816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 16728939700224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record085_result⟩)
 (.leaf ⟨(19, 16728940610560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 16735495323904), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 16735503712256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record088_result⟩)
 (.leaf ⟨(19, 16735743049984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 16735900073984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 16748225167616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record091_result⟩)
 (.leaf ⟨(19, 16748762038272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 16748770361344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 16750718486528), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record094_result⟩)
 (.leaf ⟨(19, 16751515435264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 16757083537408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record096_result⟩)
 (.leaf ⟨(19, 16757091860480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 16781823451136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record098_result⟩)
 (.leaf ⟨(19, 16781948289024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (3096 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 3096 3196 :=
  block_of_table results 3096 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0050
