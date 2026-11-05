module
prelude
import GraphInputsSix0Part00059Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1024
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 23164377858080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 23167616237600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record001_result⟩)
 (.leaf ⟨(32, 23168740770048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 23176201977888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 23176206139424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record004_result⟩)
 (.leaf ⟨(32, 23177062269184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 23178407579712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 23199941198080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record007_result⟩)
 (.leaf ⟨(32, 23211883380992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 23212834422785), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 23214970405120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record010_result⟩)
 (.leaf ⟨(32, 23219736215808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 23219876724736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 23220273086464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record013_result⟩)
 (.leaf ⟨(32, 23220281409536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 23234240057600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 23245641285888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record016_result⟩)
 (.leaf ⟨(32, 23245647528192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 23245647593472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 23246050181184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record019_result⟩)
 (.leaf ⟨(32, 23246051221568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 23247124959296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record021_result⟩)
 (.leaf ⟨(32, 23265437352192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 23265445740544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record023_result⟩)
 (.leaf ⟨(32, 23267121365248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 23267517726976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 23267526115328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record026_result⟩)
 (.leaf ⟨(32, 23280402579712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 23280410968064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 23280468640000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record029_result⟩)
 (.leaf ⟨(32, 23281551802369), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 23282080350464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 23282617221120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record032_result⟩)
 (.leaf ⟨(32, 23282625544192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 23284160725248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 23284301234176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record035_result⟩)
 (.leaf ⟨(32, 23284697595904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 23284705918976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 23284838039552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record038_result⟩)
 (.leaf ⟨(32, 23299729981696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 23314769657856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 23332569284864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record041_result⟩)
 (.leaf ⟨(32, 23332965646592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 23332974034944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 23333081252096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record044_result⟩)
 (.leaf ⟨(32, 23347643875584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 23347996934400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record046_result⟩)
 (.leaf ⟨(32, 23347999080448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 23348005322752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record048_result⟩)
 (.leaf ⟨(32, 23348046479616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 23348056688640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 23350260794112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record051_result⟩)
 (.leaf ⟨(32, 23350285959168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 23353884868864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 23354421739520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record054_result⟩)
 (.leaf ⟨(32, 23354430062592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 23371278455040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 23371410575616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record057_result⟩)
 (.leaf ⟨(32, 23371681108032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 23375973978176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 23383080206592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record060_result⟩)
 (.leaf ⟨(32, 23383080271872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 23383082287360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 23383082352640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record063_result⟩)
 (.leaf ⟨(32, 23383089619008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 23383220699200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 23383221739584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record066_result⟩)
 (.leaf ⟨(32, 23384559718464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 23402607870208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 23402616258560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record069_result⟩)
 (.leaf ⟨(32, 23402876272896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 23402886742016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record071_result⟩)
 (.leaf ⟨(32, 23403010474240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 23404556124416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record073_result⟩)
 (.leaf ⟨(32, 23404564512768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 23404688244992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 23404696633344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record076_result⟩)
 (.leaf ⟨(32, 23404956647680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 23404960874496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 23404967116800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record079_result⟩)
 (.leaf ⟨(32, 23405156909312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 23409251598592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 23409259986944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record082_result⟩)
 (.leaf ⟨(32, 23409317658880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 23410291785984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 23410300174336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record085_result⟩)
 (.leaf ⟨(32, 23413546614784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 23417639158016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 23417845727232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record088_result⟩)
 (.leaf ⟨(32, 23418041811008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 23419519271168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 23419787739136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record091_result⟩)
 (.leaf ⟨(32, 23419796062208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 23420190343168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 23420324544512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record094_result⟩)
 (.leaf ⟨(32, 23421262504000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 23421599645952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record096_result⟩)
 (.leaf ⟨(32, 23421735993344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 23421744316416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record098_result⟩)
 (.leaf ⟨(32, 23421868113920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00059.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (32620 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 32620 32720 :=
  block_of_table results 32620 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1024
