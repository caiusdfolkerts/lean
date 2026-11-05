module
prelude
import GraphInputsRow16Part00002Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0002
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 42
 (.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 7584998850560), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record000_result⟩)
 (.leaf ⟨(16, 7585000931328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 7585735917568), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record002_result⟩)
 (.branch 4
 (.leaf ⟨(16, 7589310005504), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record003_result⟩)
 (.leaf ⟨(16, 7589314232320), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(16, 7589376065792), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record005_result⟩)
 (.leaf ⟨(16, 7589380292608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record006_result⟩))
 (.branch 8
 (.leaf ⟨(16, 7589387575296), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record007_result⟩)
 (.branch 9
 (.leaf ⟨(16, 7589783937024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record008_result⟩)
 (.leaf ⟨(16, 7590147268608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(16, 7590148308992), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record010_result⟩)
 (.leaf ⟨(16, 7598092943360), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record011_result⟩))
 (.branch 13
 (.leaf ⟨(16, 7623636189440), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record012_result⟩)
 (.branch 14
 (.leaf ⟨(16, 7623701332224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record013_result⟩)
 (.leaf ⟨(16, 7623705559040), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(16, 7623713752064), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record015_result⟩)
 (.branch 17
 (.leaf ⟨(16, 7623772536832), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record016_result⟩)
 (.leaf ⟨(16, 7623780859904), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(16, 7623912980480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record018_result⟩)
 (.branch 20
 (.leaf ⟨(16, 7624110113792), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record019_result⟩)
 (.leaf ⟨(16, 7630173012224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record020_result⟩))))))
 (.branch 31
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf ⟨(16, 7630305198080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record021_result⟩)
 (.leaf ⟨(16, 7630569439232), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record022_result⟩))
 (.branch 24
 (.leaf ⟨(16, 7632451633152), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record023_result⟩)
 (.branch 25
 (.leaf ⟨(16, 7632505014528), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record024_result⟩)
 (.leaf ⟨(16, 7632715874304), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record025_result⟩))))
 (.branch 28
 (.branch 27
 (.leaf ⟨(16, 7632974776352), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record026_result⟩)
 (.leaf ⟨(16, 7637008744448), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record027_result⟩))
 (.branch 29
 (.leaf ⟨(16, 7657993961728), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record028_result⟩)
 (.branch 30
 (.leaf ⟨(16, 7657998188544), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record029_result⟩)
 (.leaf ⟨(16, 7658006381568), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record030_result⟩)))))
 (.branch 36
 (.branch 33
 (.branch 32
 (.leaf ⟨(16, 7658203652096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record031_result⟩)
 (.leaf ⟨(16, 7658468803584), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record032_result⟩))
 (.branch 34
 (.leaf ⟨(16, 7669473673216), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record033_result⟩)
 (.branch 35
 (.leaf ⟨(16, 7669481996288), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record034_result⟩)
 (.leaf ⟨(16, 7673642745856), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record035_result⟩))))
 (.branch 39
 (.branch 37
 (.leaf ⟨(16, 7678067736576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record036_result⟩)
 (.branch 38
 (.leaf ⟨(16, 7688060698880), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record037_result⟩)
 (.leaf ⟨(16, 7690277421056), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(16, 7690549985280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record039_result⟩)
 (.branch 41
 (.leaf ⟨(16, 7694710734848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record040_result⟩)
 (.leaf ⟨(16, 7857151942720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record041_result⟩)))))))
 (.branch 63
 (.branch 52
 (.branch 47
 (.branch 44
 (.branch 43
 (.leaf ⟨(16, 7857408852224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record042_result⟩)
 (.leaf ⟨(16, 7857410998272), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record043_result⟩))
 (.branch 45
 (.leaf ⟨(16, 7857417240576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record044_result⟩)
 (.branch 46
 (.leaf ⟨(16, 8066011504704), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record045_result⟩)
 (.leaf ⟨(16, 8067091759104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record046_result⟩))))
 (.branch 49
 (.branch 48
 (.leaf ⟨(16, 8067093839872), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record047_result⟩)
 (.leaf ⟨(16, 8067299303424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record048_result⟩))
 (.branch 50
 (.leaf ⟨(16, 8070416629760), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record049_result⟩)
 (.branch 51
 (.leaf ⟨(16, 8070423912448), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record050_result⟩)
 (.leaf ⟨(16, 8104808873984), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record051_result⟩)))))
 (.branch 57
 (.branch 54
 (.branch 53
 (.leaf ⟨(16, 8131195707456), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record052_result⟩)
 (.leaf ⟨(16, 8131196764160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record053_result⟩))
 (.branch 55
 (.leaf ⟨(16, 8134721617920), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record054_result⟩)
 (.branch 56
 (.leaf ⟨(16, 8134728884288), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record055_result⟩)
 (.leaf ⟨(16, 8138997841920), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record056_result⟩))))
 (.branch 60
 (.branch 58
 (.leaf ⟨(16, 8139005124608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record057_result⟩)
 (.branch 59
 (.leaf ⟨(16, 8219095269376), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record058_result⟩)
 (.leaf ⟨(16, 8286749360384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record059_result⟩)))
 (.branch 61
 (.leaf ⟨(16, 8286749425664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record060_result⟩)
 (.branch 62
 (.leaf ⟨(16, 8299363794944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record061_result⟩)
 (.leaf ⟨(16, 8325334925312), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record062_result⟩))))))
 (.branch 73
 (.branch 68
 (.branch 65
 (.branch 64
 (.leaf ⟨(16, 8326477779200), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record063_result⟩)
 (.leaf ⟨(16, 8333656424448), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record064_result⟩))
 (.branch 66
 (.leaf ⟨(16, 8371697123584), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record065_result⟩)
 (.branch 67
 (.leaf ⟨(16, 8371709149185), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record066_result⟩)
 (.leaf ⟨(16, 8371709153280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record067_result⟩))))
 (.branch 70
 (.branch 69
 (.leaf ⟨(16, 8372774567936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record068_result⟩)
 (.leaf ⟨(16, 8372782891008), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record069_result⟩))
 (.branch 71
 (.leaf ⟨(16, 8376935317504), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record070_result⟩)
 (.branch 72
 (.leaf ⟨(16, 8376943640576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record071_result⟩)
 (.leaf ⟨(16, 8377207881728), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record072_result⟩)))))
 (.branch 78
 (.branch 75
 (.branch 74
 (.leaf ⟨(16, 8379519009024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record073_result⟩)
 (.leaf ⟨(16, 8380055879680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record074_result⟩))
 (.branch 76
 (.leaf ⟨(16, 8380064202752), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record075_result⟩)
 (.branch 77
 (.leaf ⟨(16, 8380287090688), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record076_result⟩)
 (.leaf ⟨(16, 8475925020672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record077_result⟩))))
 (.branch 81
 (.branch 79
 (.leaf ⟨(16, 8476700966912), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record078_result⟩)
 (.branch 80
 (.leaf ⟨(16, 8504718919680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record079_result⟩)
 (.leaf ⟨(16, 8517457215488), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record080_result⟩)))
 (.branch 82
 (.leaf ⟨(16, 8517465538560), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record081_result⟩)
 (.branch 83
 (.leaf ⟨(16, 8569143431168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record082_result⟩)
 (.leaf ⟨(16, 8570217168896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record083_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (184 + i))) 0 84 :=
  interval_of_check _ 0 84 (by decide +kernel)

public theorem complete : Block 184 268 :=
  block_of_table results 184 84 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0002
