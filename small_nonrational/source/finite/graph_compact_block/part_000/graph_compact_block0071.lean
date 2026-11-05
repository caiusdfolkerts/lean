module
prelude
import GraphInputsRow19Part00031Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0071
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 49
 (.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 31529406333184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 31529410560000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record001_result⟩)
 (.leaf ⟨(19, 31529417842688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 31529460105216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 31529649053696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record004_result⟩)
 (.leaf ⟨(19, 31529913294848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 31530177536000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 31530178576384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record007_result⟩)
 (.leaf ⟨(19, 31530500161536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 31530508354560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 31530697236736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record010_result⟩)
 (.leaf ⟨(19, 31530705625088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 31530706535424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 31537978548480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record013_result⟩)
 (.leaf ⟨(19, 31537979654144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 31537986936832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 31537987847168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record016_result⟩)
 (.leaf ⟨(19, 31538515280416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 31543402758400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 31543406919936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record019_result⟩)
 (.leaf ⟨(19, 31543406985216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(19, 31543410041088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record021_result⟩)
 (.branch 23
 (.leaf ⟨(19, 31543872463104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record022_result⟩)
 (.leaf ⟨(19, 31543872528384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(19, 31543879802912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record024_result⟩)
 (.branch 26
 (.leaf ⟨(19, 31543930128416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record025_result⟩)
 (.leaf ⟨(19, 31544500553984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(19, 31544674156800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record027_result⟩)
 (.branch 29
 (.leaf ⟨(19, 31544681504768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record028_result⟩)
 (.leaf ⟨(19, 31544698734848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(19, 31544942559488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record030_result⟩)
 (.branch 32
 (.leaf ⟨(19, 31544942624768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record031_result⟩)
 (.leaf ⟨(19, 31544945680640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(19, 31544945745920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record033_result⟩)
 (.branch 35
 (.leaf ⟨(19, 31544949907456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record034_result⟩)
 (.leaf ⟨(19, 31544953540640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(19, 31546077609985), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record036_result⟩)
 (.branch 38
 (.leaf ⟨(19, 31551385051136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record037_result⟩)
 (.leaf ⟨(19, 31551392325664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(19, 31551392845856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record039_result⟩)
 (.branch 41
 (.leaf ⟨(19, 31553531420928), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record040_result⟩)
 (.leaf ⟨(19, 31559532939296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(19, 31559731120160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record042_result⟩)
 (.branch 44
 (.leaf ⟨(19, 31559974952960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record043_result⟩)
 (.leaf ⟨(19, 31559978586144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(19, 31559995361312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record045_result⟩)
 (.leaf ⟨(19, 31561852920064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record046_result⟩))
 (.branch 48
 (.leaf ⟨(19, 31562389790720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record047_result⟩)
 (.leaf ⟨(19, 31562390831104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record048_result⟩)))))))
 (.branch 73
 (.branch 61
 (.branch 55
 (.branch 52
 (.branch 50
 (.leaf ⟨(19, 31568061014272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record049_result⟩)
 (.branch 51
 (.leaf ⟨(19, 31568069402624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record050_result⟩)
 (.leaf ⟨(19, 31568094044416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record051_result⟩)))
 (.branch 53
 (.leaf ⟨(19, 31568095150080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record052_result⟩)
 (.branch 54
 (.leaf ⟨(19, 31568102432768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record053_result⟩)
 (.leaf ⟨(19, 31568563806240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record054_result⟩))))
 (.branch 58
 (.branch 56
 (.leaf ⟨(19, 31568613871648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record055_result⟩)
 (.branch 57
 (.leaf ⟨(19, 31569159004160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record056_result⟩)
 (.leaf ⟨(19, 31569159914496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record057_result⟩)))
 (.branch 59
 (.leaf ⟨(19, 31569620377632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record058_result⟩)
 (.branch 60
 (.leaf ⟨(19, 31569687347744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record059_result⟩)
 (.leaf ⟨(19, 31570190803200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record060_result⟩)))))
 (.branch 67
 (.branch 64
 (.branch 62
 (.leaf ⟨(19, 31570191908864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record061_result⟩)
 (.branch 63
 (.leaf ⟨(19, 31570199191552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record062_result⟩)
 (.leaf ⟨(19, 31570200101888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record063_result⟩)))
 (.branch 65
 (.leaf ⟨(19, 31570233132032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record064_result⟩)
 (.branch 66
 (.leaf ⟨(19, 31570257773312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record065_result⟩)
 (.leaf ⟨(19, 31570694115360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record066_result⟩))))
 (.branch 70
 (.branch 68
 (.leaf ⟨(19, 31570695554048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record067_result⟩)
 (.branch 69
 (.leaf ⟨(19, 31570727535136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record068_result⟩)
 (.leaf ⟨(19, 31576687968512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record069_result⟩)))
 (.branch 71
 (.leaf ⟨(19, 31576692130048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record070_result⟩)
 (.branch 72
 (.leaf ⟨(19, 31576692195328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record071_result⟩)
 (.leaf ⟨(19, 31576893432064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record072_result⟩))))))
 (.branch 85
 (.branch 79
 (.branch 76
 (.branch 74
 (.leaf ⟨(19, 31576893497344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record073_result⟩)
 (.branch 75
 (.leaf ⟨(19, 31576894212352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record074_result⟩)
 (.leaf ⟨(19, 31577158453504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record075_result⟩)))
 (.branch 77
 (.leaf ⟨(19, 31577161900032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record076_result⟩)
 (.branch 78
 (.leaf ⟨(19, 31579024066560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record077_result⟩)
 (.leaf ⟨(19, 31579292469248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record078_result⟩))))
 (.branch 82
 (.branch 80
 (.leaf ⟨(19, 31585265125632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record079_result⟩)
 (.branch 81
 (.leaf ⟨(19, 31585735803912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record080_result⟩)
 (.leaf ⟨(19, 31585752580097), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record081_result⟩)))
 (.branch 83
 (.leaf ⟨(19, 31594056386592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record082_result⟩)
 (.branch 84
 (.leaf ⟨(19, 31594321544200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record083_result⟩)
 (.leaf ⟨(19, 31604516979968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record084_result⟩)))))
 (.branch 91
 (.branch 88
 (.branch 86
 (.leaf ⟨(19, 31604525368320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record085_result⟩)
 (.branch 87
 (.leaf ⟨(19, 31605053719044), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record086_result⟩)
 (.leaf ⟨(19, 31618782789632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record087_result⟩)))
 (.branch 89
 (.leaf ⟨(19, 31620928119040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record088_result⟩)
 (.branch 90
 (.leaf ⟨(19, 31622877478912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record089_result⟩)
 (.leaf ⟨(19, 31622943539200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record090_result⟩))))
 (.branch 94
 (.branch 92
 (.leaf ⟨(19, 31623075659776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record091_result⟩)
 (.branch 93
 (.leaf ⟨(19, 31623207780352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record092_result⟩)
 (.leaf ⟨(19, 31623216103424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record093_result⟩)))
 (.branch 96
 (.branch 95
 (.leaf ⟨(19, 31625023913984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record094_result⟩)
 (.leaf ⟨(19, 31649903943936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record095_result⟩))
 (.branch 97
 (.leaf ⟨(19, 31649921239296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record096_result⟩)
 (.leaf ⟨(19, 31658259578880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00031.record097_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (5115 + i))) 0 98 :=
  interval_of_check _ 0 98 (by decide +kernel)

public theorem complete : Block 5115 5213 :=
  block_of_table results 5115 98 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0071
