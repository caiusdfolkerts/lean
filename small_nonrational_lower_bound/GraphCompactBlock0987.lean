module
prelude
import GraphInputsSix0Part00022Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0987
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 8019387613185), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 8041321892096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record001_result⟩)
 (.leaf ⟨(32, 8041321955336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 8041408823552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 8041412985088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record004_result⟩)
 (.leaf ⟨(32, 8041413050368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 8041466431744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 8041809346816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record007_result⟩)
 (.leaf ⟨(32, 8041809412096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 8041866987648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 8044785174784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record010_result⟩)
 (.leaf ⟨(32, 8045032185856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 8046164049921), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 8050648826112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record013_result⟩)
 (.leaf ⟨(32, 8057531664640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 8057535858816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 8057914957824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record016_result⟩)
 (.leaf ⟨(32, 8067091562752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 8067227910144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 8067236233216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record019_result⟩)
 (.leaf ⟨(32, 8067360030720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 8067368353792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record021_result⟩)
 (.leaf ⟨(32, 8067632594944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 8067828695040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record023_result⟩)
 (.leaf ⟨(32, 8112524296448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 8112532684800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 8112792699136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record026_result⟩)
 (.leaf ⟨(32, 8112803168256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 8112926900480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 8114472550656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record029_result⟩)
 (.leaf ⟨(32, 8114480939008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 8114604671232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 8114613059584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record032_result⟩)
 (.leaf ⟨(32, 8114873073920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 8114877300736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 8114883543040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record035_result⟩)
 (.leaf ⟨(32, 8115073335552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 8119168024832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 8119176413184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record038_result⟩)
 (.leaf ⟨(32, 8119234085120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 8127555584256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 8127762153472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record041_result⟩)
 (.leaf ⟨(32, 8127958237248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 8131178930240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 8135811023104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record044_result⟩)
 (.leaf ⟨(32, 8135945289728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 8135953612800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record046_result⟩)
 (.leaf ⟨(32, 8136347893760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 8136413954048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record048_result⟩)
 (.leaf ⟨(32, 8138997645568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 8139065851904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 8139074174976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record051_result⟩)
 (.leaf ⟨(32, 8139140235264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 8139534516224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 8147708215552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record054_result⟩)
 (.leaf ⟨(32, 8147716603904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 8147840336128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 8147848724480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record057_result⟩)
 (.leaf ⟨(32, 8147955941632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 8148108738816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 8148112965632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record060_result⟩)
 (.leaf ⟨(32, 8148119207936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 8148224344320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 8148236634112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record063_result⟩)
 (.leaf ⟨(32, 8148358545664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 8152403689728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 8152412078080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record066_result⟩)
 (.leaf ⟨(32, 8152519295232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 8152529504256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 8156813984512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record069_result⟩)
 (.leaf ⟨(32, 8160840794368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 8160851003392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record071_result⟩)
 (.leaf ⟨(32, 8160997818368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 8161243447360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record073_result⟩)
 (.leaf ⟨(32, 8165538136640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 8173322912000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 8173457178624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record076_result⟩)
 (.leaf ⟨(32, 8173465501696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 8173859782656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 8173993853440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record079_result⟩)
 (.leaf ⟨(32, 8179920470272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 8179928858624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 8180052590848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record082_result⟩)
 (.leaf ⟨(32, 8180060979200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 8180168196352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 8180320993536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record085_result⟩)
 (.leaf ⟨(32, 8180325220352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 8180331462656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 8180436599040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record088_result⟩)
 (.leaf ⟨(32, 8180448888832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 8180570800384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 8182207414272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record091_result⟩)
 (.leaf ⟨(32, 8182248571136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 8182471655424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 8182516973824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record094_result⟩)
 (.leaf ⟨(32, 8182529263616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 8184735531008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record096_result⟩)
 (.leaf ⟨(32, 8184865489664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 8186409320704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record098_result⟩)
 (.leaf ⟨(32, 8186762379520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00022.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (28986 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 28986 29086 :=
  block_of_table results 28986 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0987
