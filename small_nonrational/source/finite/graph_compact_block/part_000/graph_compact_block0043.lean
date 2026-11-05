module
prelude
import GraphInputsRow19Part00003Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0043
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 7584998850560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 7585000931328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record001_result⟩)
 (.leaf ⟨(19, 7585734860864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 7585735917568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 7586055356672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record004_result⟩)
 (.leaf ⟨(19, 7586055421952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 7586057437440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 7586057502720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record007_result⟩)
 (.leaf ⟨(19, 7586065679424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 7586262949952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 7586262966272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record010_result⟩)
 (.leaf ⟨(19, 7586332016641), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 7586858402368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 7586860499456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record013_result⟩)
 (.leaf ⟨(19, 7589314232320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 7589380292608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 7589387575296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record016_result⟩)
 (.leaf ⟨(19, 7590147268608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 7590148308992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 7623571342336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record019_result⟩)
 (.leaf ⟨(19, 7623713752064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 7623772536832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record021_result⟩)
 (.leaf ⟨(19, 7623780859904), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 7623843905537), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record023_result⟩)
 (.leaf ⟨(19, 7630305198080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 7630569439232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 7632715874304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record026_result⟩)
 (.leaf ⟨(19, 7632974776352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 7637008744448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 7658006381568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record029_result⟩)
 (.leaf ⟨(19, 7658203652096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 7658468803584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 7669473673216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record032_result⟩)
 (.leaf ⟨(19, 7669481996288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 7678067736576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 7688060698880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record035_result⟩)
 (.leaf ⟨(19, 7690277421056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 7690549985280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 7694710734848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record038_result⟩)
 (.leaf ⟨(19, 7857151942720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 7857410998272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 7857417240576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record041_result⟩)
 (.leaf ⟨(19, 7864664465472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 7929659080704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 7998615330880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record044_result⟩)
 (.leaf ⟨(19, 8066506956864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 8067091759104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record046_result⟩)
 (.leaf ⟨(19, 8067093774592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 8067093839872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record048_result⟩)
 (.leaf ⟨(19, 8067160940544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 8067293906176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 8067299287104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record051_result⟩)
 (.leaf ⟨(19, 8067299303424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 8067300197440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 8070423912448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record054_result⟩)
 (.leaf ⟨(19, 8104808873984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 8110266728512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 8110318108680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record057_result⟩)
 (.leaf ⟨(19, 8117599420424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 8117665480712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 8131195707456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record060_result⟩)
 (.leaf ⟨(19, 8131196764160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 8134721617920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 8135811219456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record063_result⟩)
 (.leaf ⟨(19, 8135819396160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 8138997841920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 8139005124608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record066_result⟩)
 (.leaf ⟨(19, 8173325059072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 8180042252296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 8219095269376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record069_result⟩)
 (.leaf ⟨(19, 8286749360384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 8286749425664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record071_result⟩)
 (.leaf ⟨(19, 8299363794944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 8326477779200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record073_result⟩)
 (.leaf ⟨(19, 8333656424448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 8371697123584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 8371709153280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record076_result⟩)
 (.leaf ⟨(19, 8372782891008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 8376935317504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 8377207881728), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record079_result⟩)
 (.leaf ⟨(19, 8379519009024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 8380055879680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 8380064202752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record082_result⟩)
 (.leaf ⟨(19, 8380287090688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 8475925020672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 8476700966912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record085_result⟩)
 (.leaf ⟨(19, 8504718919680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 8517457215488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 8517465538560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record088_result⟩)
 (.leaf ⟨(19, 8569143431168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 8570217168896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 8570481410048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record091_result⟩)
 (.leaf ⟨(19, 8585675309312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 8585811656704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 8585819979776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record094_result⟩)
 (.leaf ⟨(19, 8586042867712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 8586216341504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record096_result⟩)
 (.leaf ⟨(19, 8586579673088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 8593571119104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record098_result⟩)
 (.leaf ⟨(19, 8597194936320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00003.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (2398 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 2398 2498 :=
  block_of_table results 2398 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0043
