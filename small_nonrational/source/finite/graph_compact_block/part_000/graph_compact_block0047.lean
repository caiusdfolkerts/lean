module
prelude
import GraphInputsRow19Part00007Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0047
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 14171556085760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 14171816100096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record001_result⟩)
 (.leaf ⟨(19, 14171820326912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 14171827609600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 14174806687744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record004_result⟩)
 (.leaf ⟨(19, 14180141826048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 14183258161408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 14183262388224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record007_result⟩)
 (.leaf ⟨(19, 14183269670912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 14183401791488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 14183459463424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record010_result⟩)
 (.leaf ⟨(19, 14183526629376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 14183534952448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 14183996334080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record013_result⟩)
 (.leaf ⟨(19, 14184232288512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 14184236515328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 14185070592000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record016_result⟩)
 (.leaf ⟨(19, 14186378723584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 14186382950400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 14186580025600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record019_result⟩)
 (.leaf ⟨(19, 14186588413952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 14193010999552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record021_result⟩)
 (.leaf ⟨(19, 14199718707456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 14199718772736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record023_result⟩)
 (.leaf ⟨(19, 14199720853504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 14199721828608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 14220708216832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record026_result⟩)
 (.leaf ⟨(19, 14220913680384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 14234080518400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 14234080583680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record029_result⟩)
 (.leaf ⟨(19, 14333989978368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 14355702759424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 14382308360208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record032_result⟩)
 (.leaf ⟨(19, 14424184258560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 14424522883072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 14452141342720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record035_result⟩)
 (.leaf ⟨(19, 14452339523584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 14484336820224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 14485993783296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record038_result⟩)
 (.leaf ⟨(19, 14488749211648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 14488947392512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 14503645380608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record041_result⟩)
 (.leaf ⟨(19, 14505791815680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 14505794871552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 14518274064384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record044_result⟩)
 (.leaf ⟨(19, 14519820619808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 14522974740480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record046_result⟩)
 (.leaf ⟨(19, 14523231698944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 14523240022016), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record048_result⟩)
 (.leaf ⟨(19, 14524014927872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 14524237750528), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 14527400771584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record051_result⟩)
 (.leaf ⟨(19, 14529984528384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 14530454233088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 14530478874880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record054_result⟩)
 (.leaf ⟨(19, 14539027480576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 14558341104640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 14564780409856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record057_result⟩)
 (.leaf ⟨(19, 14581188542464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 14589569827328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 14596246618112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record060_result⟩)
 (.leaf ⟨(19, 14604059115584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 14608471523328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 14617061425152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record063_result⟩)
 (.leaf ⟨(19, 14617531129856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 14617788088320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 14617796411392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record066_result⟩)
 (.leaf ⟨(19, 14629482283008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 14629803802880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 14630010225728), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record069_result⟩)
 (.leaf ⟨(19, 14630606864896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 14633126658048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record071_result⟩)
 (.leaf ⟨(19, 14633133940736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 14633159688192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record073_result⟩)
 (.leaf ⟨(19, 14633266061312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 14633893634048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 14633894674432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record076_result⟩)
 (.leaf ⟨(19, 14647123083264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 14664571289600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 14665268625664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record079_result⟩)
 (.leaf ⟨(19, 14665272852480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 14665346195456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 14665471033344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record082_result⟩)
 (.leaf ⟨(19, 14665478316032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 14666105888768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 14666106929152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record085_result⟩)
 (.leaf ⟨(19, 14667624751104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 14673919442944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 14674051563520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record088_result⟩)
 (.leaf ⟨(19, 14676197998592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 14680755109888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 14680881891360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record091_result⟩)
 (.leaf ⟨(19, 14699659952384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 14699664179200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 14699672372224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record094_result⟩)
 (.leaf ⟨(19, 14699804492800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 14700465095168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record096_result⟩)
 (.leaf ⟨(19, 14701740327168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 14701744553984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record098_result⟩)
 (.leaf ⟨(19, 14701752747008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00007.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (2798 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 2798 2898 :=
  block_of_table results 2798 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0047
