module
prelude
import GraphInputsRow25Part00016Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0306
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 49
 (.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(25, 24643182264320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record000_result⟩)
 (.branch 2
 (.leaf ⟨(25, 24646806208512), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record001_result⟩)
 (.leaf ⟨(25, 24647343013888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(25, 24648886583296), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record003_result⟩)
 (.branch 5
 (.leaf ⟨(25, 24655664513024), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record004_result⟩)
 (.leaf ⟨(25, 24663986012160), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(25, 24666066386944), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record006_result⟩)
 (.branch 8
 (.leaf ⟨(25, 24666198507520), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record007_result⟩)
 (.leaf ⟨(25, 24681635643392), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(25, 24740171972608), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record009_result⟩)
 (.branch 11
 (.leaf ⟨(25, 24741314891776), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record010_result⟩)
 (.leaf ⟨(25, 24741322690576), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(25, 24741339465744), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record012_result⟩)
 (.branch 14
 (.leaf ⟨(25, 24742413205505), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record013_result⟩)
 (.leaf ⟨(25, 24757838839808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(25, 24777943287824), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record015_result⟩)
 (.branch 17
 (.leaf ⟨(25, 24778228924416), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record016_result⟩)
 (.leaf ⟨(25, 24779557961728), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(25, 24783718711296), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record018_result⟩)
 (.branch 20
 (.leaf ⟨(25, 24783842508800), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record019_result⟩)
 (.leaf ⟨(25, 24894918098944), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(25, 24895510560768), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record021_result⟩)
 (.branch 23
 (.leaf ⟨(25, 24896583778304), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record022_result⟩)
 (.leaf ⟨(25, 25031270994048), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(25, 25117262610432), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record024_result⟩)
 (.branch 26
 (.leaf ⟨(25, 25117774317568), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record025_result⟩)
 (.leaf ⟨(25, 25126095685632), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(25, 25142738551300), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record027_result⟩)
 (.branch 29
 (.leaf ⟨(25, 25152471466240), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record028_result⟩)
 (.leaf ⟨(25, 25154688188416), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(25, 25154960752640), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record030_result⟩)
 (.branch 32
 (.leaf ⟨(25, 25155357114368), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record031_result⟩)
 (.leaf ⟨(25, 25158081314816), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(25, 25161061433344), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record033_result⟩)
 (.branch 35
 (.leaf ⟨(25, 25161598238720), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record034_result⟩)
 (.leaf ⟨(25, 25169919737856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(25, 25177132908544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record036_result⟩)
 (.branch 38
 (.leaf ⟨(25, 25178241236992), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record037_result⟩)
 (.leaf ⟨(25, 25178373357568), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(25, 25190276792320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record039_result⟩)
 (.branch 41
 (.leaf ⟨(25, 25190788759552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record040_result⟩)
 (.leaf ⟨(25, 25194297098240), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(25, 25194833903616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record042_result⟩)
 (.branch 44
 (.leaf ⟨(25, 25194949509120), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record043_result⟩)
 (.leaf ⟨(25, 25215753125888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(25, 25226767237120), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record045_result⟩)
 (.leaf ⟨(25, 25329179557888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record046_result⟩))
 (.branch 48
 (.leaf ⟨(25, 25329303355392), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record047_result⟩)
 (.leaf ⟨(25, 25332927234304), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record048_result⟩)))))))
 (.branch 73
 (.branch 61
 (.branch 55
 (.branch 52
 (.branch 50
 (.leaf ⟨(25, 25333464104960), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record049_result⟩)
 (.branch 51
 (.leaf ⟨(25, 25333472428032), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record050_result⟩)
 (.leaf ⟨(25, 25341785604096), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record051_result⟩)))
 (.branch 53
 (.leaf ⟨(25, 25341793927168), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record052_result⟩)
 (.branch 54
 (.leaf ⟨(25, 25363472187392), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record053_result⟩)
 (.leaf ⟨(25, 25364735262720), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record054_result⟩))))
 (.branch 58
 (.branch 56
 (.leaf ⟨(25, 25367360372736), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record055_result⟩)
 (.branch 57
 (.leaf ⟨(25, 25367756734464), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record056_result⟩)
 (.leaf ⟨(25, 25367765057536), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record057_result⟩)))
 (.branch 59
 (.leaf ⟨(25, 25375809765632), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record058_result⟩)
 (.branch 60
 (.leaf ⟨(25, 25375946113024), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record059_result⟩)
 (.leaf ⟨(25, 25375954436096), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record060_result⟩)))))
 (.branch 67
 (.branch 64
 (.branch 62
 (.leaf ⟨(25, 25376078233600), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record061_result⟩)
 (.branch 63
 (.leaf ⟨(25, 25376086556672), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record062_result⟩)
 (.leaf ⟨(25, 25376350797824), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record063_result⟩)))
 (.branch 65
 (.leaf ⟨(25, 25376546897920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record064_result⟩)
 (.branch 66
 (.leaf ⟨(25, 25377620115456), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record065_result⟩)
 (.leaf ⟨(25, 25432684560640), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record066_result⟩))))
 (.branch 70
 (.branch 68
 (.leaf ⟨(25, 25433320521728), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record067_result⟩)
 (.branch 69
 (.leaf ⟨(25, 25444529225984), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record068_result⟩)
 (.leaf ⟨(25, 25444663492608), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record069_result⟩)))
 (.branch 71
 (.leaf ⟨(25, 25444671815680), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record070_result⟩)
 (.branch 72
 (.leaf ⟨(25, 25445066096640), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record071_result⟩)
 (.leaf ⟨(25, 25445132156928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record072_result⟩))))))
 (.branch 85
 (.branch 79
 (.branch 76
 (.branch 74
 (.leaf ⟨(25, 25445569413376), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record073_result⟩)
 (.branch 75
 (.leaf ⟨(25, 25446205374464), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record074_result⟩)
 (.leaf ⟨(25, 25447715848448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record075_result⟩)))
 (.branch 77
 (.leaf ⟨(25, 25513248751616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record076_result⟩)
 (.branch 78
 (.leaf ⟨(25, 25570491039744), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record077_result⟩)
 (.leaf ⟨(25, 25576564867328), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record078_result⟩))))
 (.branch 82
 (.branch 80
 (.leaf ⟨(25, 25582106574848), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record079_result⟩)
 (.branch 81
 (.leaf ⟨(25, 25582302674944), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record080_result⟩)
 (.leaf ⟨(25, 25583375892480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record081_result⟩)))
 (.branch 83
 (.leaf ⟨(25, 25642097770496), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record082_result⟩)
 (.branch 84
 (.leaf ⟨(25, 25659277574144), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record083_result⟩)
 (.leaf ⟨(25, 25659409694720), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record084_result⟩)))))
 (.branch 91
 (.branch 88
 (.branch 86
 (.leaf ⟨(25, 25702227263744), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record085_result⟩)
 (.branch 87
 (.leaf ⟨(25, 25704441905152), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record086_result⟩)
 (.leaf ⟨(25, 25704978710528), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record087_result⟩)))
 (.branch 89
 (.leaf ⟨(25, 25706522279936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record088_result⟩)
 (.branch 90
 (.leaf ⟨(25, 25706662723584), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record089_result⟩)
 (.leaf ⟨(25, 25707059085312), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record090_result⟩))))
 (.branch 94
 (.branch 92
 (.leaf ⟨(25, 25719407132672), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record091_result⟩)
 (.branch 93
 (.leaf ⟨(25, 25722593755136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record092_result⟩)
 (.leaf ⟨(25, 25739757944832), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record093_result⟩)))
 (.branch 96
 (.branch 95
 (.leaf ⟨(25, 25739898388480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record094_result⟩)
 (.leaf ⟨(25, 25740294750208), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record095_result⟩))
 (.branch 97
 (.leaf ⟨(25, 25740410355712), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record096_result⟩)
 (.leaf ⟨(25, 25769821618432), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00016.record097_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (13408 + i))) 0 98 :=
  interval_of_check _ 0 98 (by decide +kernel)

public theorem complete : Block 13408 13506 :=
  block_of_table results 13408 98 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0306
