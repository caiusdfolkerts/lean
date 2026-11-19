module
prelude
import GraphInputsRow25Part00011Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0301
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 45
 (.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(25, 13900394299648), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record000_result⟩)
 (.leaf ⟨(25, 13900405809152), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record001_result⟩))
 (.branch 3
 (.leaf ⟨(25, 14027929423904), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record002_result⟩)
 (.branch 4
 (.leaf ⟨(25, 14294884909088), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record003_result⟩)
 (.leaf ⟨(25, 14295019110432), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(25, 14298240323616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record005_result⟩)
 (.branch 7
 (.leaf ⟨(25, 14298504564768), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record006_result⟩)
 (.leaf ⟨(25, 14302797434912), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(25, 14311387336736), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record008_result⟩)
 (.branch 10
 (.leaf ⟨(25, 14372579778560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record009_result⟩)
 (.leaf ⟨(25, 14448834121760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(25, 14449958191105), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record011_result⟩)
 (.leaf ⟨(25, 14449960304640), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record012_result⟩))
 (.branch 14
 (.leaf ⟨(25, 14450027405312), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record013_result⟩)
 (.branch 15
 (.leaf ⟨(25, 14453370790144), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record014_result⟩)
 (.leaf ⟨(25, 14571853086976), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(25, 14588460941440), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record016_result⟩)
 (.branch 18
 (.leaf ⟨(25, 14604048564480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record017_result⟩)
 (.leaf ⟨(25, 14604052791296), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(25, 14616457379840), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record019_result⟩)
 (.branch 21
 (.leaf ⟨(25, 14621748527104), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record020_result⟩)
 (.leaf ⟨(25, 14623428378624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(25, 14623700942848), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record022_result⟩)
 (.leaf ⟨(25, 14623965184000), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record023_result⟩))
 (.branch 25
 (.leaf ⟨(25, 14759793590272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record024_result⟩)
 (.branch 26
 (.leaf ⟨(25, 14760462516224), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record025_result⟩)
 (.leaf ⟨(25, 14768387653632), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(25, 14768916135936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record027_result⟩)
 (.branch 29
 (.leaf ⟨(25, 15037494198272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record028_result⟩)
 (.leaf ⟨(25, 15212845531136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(25, 15213580517376), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record030_result⟩)
 (.branch 32
 (.leaf ⟨(25, 15247410724864), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record031_result⟩)
 (.leaf ⟨(25, 15311835234304), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record032_result⟩)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf ⟨(25, 15312363716608), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record033_result⟩)
 (.branch 35
 (.leaf ⟨(25, 15320685215744), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record034_result⟩)
 (.leaf ⟨(25, 15326867685376), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record035_result⟩)))
 (.branch 37
 (.leaf ⟨(25, 15335725989888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record036_result⟩)
 (.branch 38
 (.leaf ⟨(25, 15344047489024), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record037_result⟩)
 (.leaf ⟨(25, 15350288613376), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record038_result⟩))))
 (.branch 42
 (.branch 40
 (.leaf ⟨(25, 15399114514560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record039_result⟩)
 (.branch 41
 (.leaf ⟨(25, 15411993124992), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record040_result⟩)
 (.leaf ⟨(25, 15471034769536), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record041_result⟩)))
 (.branch 43
 (.leaf ⟨(25, 15576506368000), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record042_result⟩)
 (.branch 44
 (.leaf ⟨(25, 15672633462816), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record043_result⟩)
 (.leaf ⟨(25, 15677190574112), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record044_result⟩)))))))
 (.branch 68
 (.branch 56
 (.branch 50
 (.branch 47
 (.branch 46
 (.leaf ⟨(25, 15679382634624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record045_result⟩)
 (.leaf ⟨(25, 15712410140672), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record046_result⟩))
 (.branch 48
 (.leaf ⟨(25, 15712670220288), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record047_result⟩)
 (.branch 49
 (.leaf ⟨(25, 15723208376320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record048_result⟩)
 (.leaf ⟨(25, 15809306984448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record049_result⟩))))
 (.branch 53
 (.branch 51
 (.leaf ⟨(25, 15842282569728), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record050_result⟩)
 (.branch 52
 (.leaf ⟨(25, 15842542649344), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record051_result⟩)
 (.leaf ⟨(25, 15842546810880), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(25, 15842658254848), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record053_result⟩)
 (.branch 55
 (.leaf ⟨(25, 15851247895040), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record054_result⟩)
 (.leaf ⟨(25, 16128415891456), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record055_result⟩)))))
 (.branch 62
 (.branch 59
 (.branch 57
 (.leaf ⟨(25, 16493834699008), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record056_result⟩)
 (.branch 58
 (.leaf ⟨(25, 16493834764288), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record057_result⟩)
 (.leaf ⟨(25, 16494977618176), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(25, 16494977683456), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record059_result⟩)
 (.branch 61
 (.leaf ⟨(25, 16494985482256), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record060_result⟩)
 (.leaf ⟨(25, 16495002257424), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record061_result⟩))))
 (.branch 65
 (.branch 63
 (.leaf ⟨(25, 16495109738752), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record062_result⟩)
 (.branch 64
 (.leaf ⟨(25, 16496075997185), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record063_result⟩)
 (.leaf ⟨(25, 16496476585984), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(25, 16502952562688), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record065_result⟩)
 (.branch 67
 (.leaf ⟨(25, 16511499518080), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record066_result⟩)
 (.leaf ⟨(25, 16511501631488), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record067_result⟩))))))
 (.branch 79
 (.branch 73
 (.branch 70
 (.branch 69
 (.leaf ⟨(25, 16512673386624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record068_result⟩)
 (.leaf ⟨(25, 16527189610752), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record069_result⟩))
 (.branch 71
 (.leaf ⟨(25, 16531606079504), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record070_result⟩)
 (.branch 72
 (.leaf ⟨(25, 16531623247873), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record071_result⟩)
 (.leaf ⟨(25, 16531891716096), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record072_result⟩))))
 (.branch 76
 (.branch 74
 (.leaf ⟨(25, 16532675559680), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record073_result⟩)
 (.branch 75
 (.leaf ⟨(25, 16532948287488), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record074_result⟩)
 (.leaf ⟨(25, 16533212430336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record075_result⟩)))
 (.branch 77
 (.leaf ⟨(25, 16533220753408), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record076_result⟩)
 (.branch 78
 (.leaf ⟨(25, 16536188227584), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record077_result⟩)
 (.leaf ⟨(25, 16537373179904), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record078_result⟩)))))
 (.branch 85
 (.branch 82
 (.branch 80
 (.leaf ⟨(25, 16537381502976), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record079_result⟩)
 (.branch 81
 (.leaf ⟨(25, 16544885379200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record080_result⟩)
 (.leaf ⟨(25, 16632420827136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record081_result⟩)))
 (.branch 83
 (.leaf ⟨(25, 16640391512064), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record082_result⟩)
 (.branch 84
 (.leaf ⟨(25, 16648436220160), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record083_result⟩)
 (.leaf ⟨(25, 16648572567552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record084_result⟩))))
 (.branch 88
 (.branch 86
 (.leaf ⟨(25, 16648580890624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record085_result⟩)
 (.branch 87
 (.leaf ⟨(25, 16648704688128), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record086_result⟩)
 (.leaf ⟨(25, 16648713011200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record087_result⟩)))
 (.branch 89
 (.leaf ⟨(25, 16649173352448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record088_result⟩)
 (.branch 90
 (.leaf ⟨(25, 16650111812112), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record089_result⟩)
 (.leaf ⟨(25, 16678037487616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00011.record090_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12981 + i))) 0 91 :=
  interval_of_check _ 0 91 (by decide +kernel)

public theorem complete : Block 12981 13072 :=
  block_of_table results 12981 91 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0301
