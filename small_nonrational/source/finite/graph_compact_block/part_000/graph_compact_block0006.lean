module
prelude
import GraphInputsRow16Part00006Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0006
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 13942743171328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 13942751559680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record001_result⟩)
 (.leaf ⟨(16, 13942883680256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(16, 13942941352192), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record003_result⟩)
 (.branch 5
 (.leaf ⟨(16, 13943143694592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record004_result⟩)
 (.leaf ⟨(16, 13943147921408), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(16, 13943209754880), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record006_result⟩)
 (.branch 8
 (.leaf ⟨(16, 13943221264384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record007_result⟩)
 (.leaf ⟨(16, 13943478222848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(16, 13943486545920), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record009_result⟩)
 (.branch 11
 (.leaf ⟨(16, 13946103332864), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record010_result⟩)
 (.leaf ⟨(16, 13946330317056), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(16, 13946341826560), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record012_result⟩)
 (.branch 14
 (.leaf ⟨(16, 13953891598592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record013_result⟩)
 (.leaf ⟨(16, 13960330969088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(16, 13968652468224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record015_result⟩)
 (.branch 17
 (.leaf ⟨(16, 13968655524096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record016_result⟩)
 (.leaf ⟨(16, 13970199023648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(16, 13977233981696), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record018_result⟩)
 (.branch 20
 (.leaf ⟨(16, 13977242370048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record019_result⟩)
 (.leaf ⟨(16, 13977502384384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(16, 13977513893888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record021_result⟩)
 (.leaf ⟨(16, 13977703686400), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record022_result⟩))
 (.branch 24
 (.leaf ⟨(16, 13977770852352), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record023_result⟩)
 (.leaf ⟨(16, 13977779175424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(16, 13978075988224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record025_result⟩)
 (.branch 27
 (.leaf ⟨(16, 13978084376576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record026_result⟩)
 (.leaf ⟨(16, 13978282557440), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(16, 13978542571776), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record028_result⟩)
 (.branch 30
 (.leaf ⟨(16, 13978546798592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record029_result⟩)
 (.leaf ⟨(16, 13978554081280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(16, 13978776903936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record031_result⟩)
 (.branch 33
 (.leaf ⟨(16, 13987127328768), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record032_result⟩)
 (.leaf ⟨(16, 13993566633984), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(16, 14012599435520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record034_result⟩)
 (.branch 36
 (.leaf ⟨(16, 14012607823872), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record035_result⟩)
 (.leaf ⟨(16, 14012880258048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(16, 14063211913472), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record037_result⟩)
 (.branch 39
 (.leaf ⟨(16, 14067439828992), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record038_result⟩)
 (.leaf ⟨(16, 14080318439424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(16, 14083505061888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record040_result⟩)
 (.branch 42
 (.leaf ⟨(16, 14097504542976), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record041_result⟩)
 (.leaf ⟨(16, 14114677129216), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(16, 14115717316608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record043_result⟩)
 (.branch 45
 (.leaf ⟨(16, 14159775334656), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record044_result⟩)
 (.leaf ⟨(16, 14159779496192), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(16, 14159779561472), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record046_result⟩)
 (.leaf ⟨(16, 14159848677632), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record047_result⟩))
 (.branch 49
 (.leaf ⟨(16, 14161921769728), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record048_result⟩)
 (.leaf ⟨(16, 14166086746112), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(16, 14166220947456), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record050_result⟩)
 (.branch 52
 (.leaf ⟨(16, 14171349516544), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record051_result⟩)
 (.leaf ⟨(16, 14171357904896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(16, 14171556085760), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record053_result⟩)
 (.branch 55
 (.leaf ⟨(16, 14171820326912), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record054_result⟩)
 (.leaf ⟨(16, 14171827609600), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(16, 14172050432256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record056_result⟩)
 (.branch 58
 (.leaf ⟨(16, 14174806687744), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record057_result⟩)
 (.leaf ⟨(16, 14180141826048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(16, 14183262388224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record059_result⟩)
 (.branch 61
 (.leaf ⟨(16, 14183269670912), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record060_result⟩)
 (.leaf ⟨(16, 14183401791488), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(16, 14183526629376), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record062_result⟩)
 (.branch 64
 (.leaf ⟨(16, 14183534952448), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record063_result⟩)
 (.leaf ⟨(16, 14183996334080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(16, 14184232288512), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record065_result⟩)
 (.branch 67
 (.leaf ⟨(16, 14184236515328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record066_result⟩)
 (.leaf ⟨(16, 14184302575616), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(16, 14184434696192), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record068_result⟩)
 (.branch 70
 (.leaf ⟨(16, 14184441978880), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record069_result⟩)
 (.leaf ⟨(16, 14185069551616), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(16, 14185070592000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record071_result⟩)
 (.leaf ⟨(16, 14186378723584), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record072_result⟩))
 (.branch 74
 (.leaf ⟨(16, 14186382950400), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record073_result⟩)
 (.leaf ⟨(16, 14186390233088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(16, 14186588413952), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record075_result⟩)
 (.branch 77
 (.leaf ⟨(16, 14186613055744), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record076_result⟩)
 (.leaf ⟨(16, 14187082817568), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(16, 14193010999552), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record078_result⟩)
 (.branch 80
 (.leaf ⟨(16, 14193015161088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record079_result⟩)
 (.leaf ⟨(16, 14193015226368), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(16, 14195157434624), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record081_result⟩)
 (.branch 83
 (.leaf ⟨(16, 14195161661440), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record082_result⟩)
 (.leaf ⟨(16, 14195164717312), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(16, 14199375792384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record084_result⟩)
 (.branch 86
 (.leaf ⟨(16, 14199718707456), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record085_result⟩)
 (.leaf ⟨(16, 14199718772736), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(16, 14199720853504), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record087_result⟩)
 (.branch 89
 (.leaf ⟨(16, 14199721828608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record088_result⟩)
 (.leaf ⟨(16, 14201915474176), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(16, 14220708216832), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record090_result⟩)
 (.branch 92
 (.leaf ⟨(16, 14220905292032), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record091_result⟩)
 (.leaf ⟨(16, 14220913680384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(16, 14220914590720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record093_result⟩)
 (.branch 95
 (.leaf ⟨(16, 14227373916160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record094_result⟩)
 (.leaf ⟨(16, 14234080583680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(16, 14355702759424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record096_result⟩)
 (.leaf ⟨(16, 14369429749776), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record097_result⟩))
 (.branch 99
 (.leaf ⟨(16, 14372245176576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record098_result⟩)
 (.leaf ⟨(16, 14411305648128), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00006.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (504 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 504 604 :=
  block_of_table results 504 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0006
