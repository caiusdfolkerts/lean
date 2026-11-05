module
prelude
import GraphInputsRow23Part00008Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0086
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 15247410724864), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 15247939207168), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record001_result⟩)
 (.leaf ⟨(23, 15258009796864), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(23, 15294655430656), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record003_result⟩)
 (.branch 5
 (.leaf ⟨(23, 15303513735168), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record004_result⟩)
 (.leaf ⟨(23, 15311835234304), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(23, 15312363716608), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 15320685215744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record007_result⟩)
 (.leaf ⟨(23, 15326867685376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(23, 15335725989888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record009_result⟩)
 (.branch 11
 (.leaf ⟨(23, 15344047489024), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record010_result⟩)
 (.leaf ⟨(23, 15344575971328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(23, 15350288613376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record012_result⟩)
 (.branch 14
 (.leaf ⟨(23, 15403138949376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record013_result⟩)
 (.leaf ⟨(23, 15411993124992), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(23, 15437792313600), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 15446113812736), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record016_result⟩)
 (.leaf ⟨(23, 15446382248064), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(23, 15471034769536), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record018_result⟩)
 (.branch 20
 (.leaf ⟨(23, 15535190843648), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record019_result⟩)
 (.leaf ⟨(23, 15550533615744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(23, 15576506368000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record021_result⟩)
 (.leaf ⟨(23, 15613012541440), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record022_result⟩))
 (.branch 24
 (.leaf ⟨(23, 15672633462816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record023_result⟩)
 (.leaf ⟨(23, 15677190574112), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(23, 15679382634624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record025_result⟩)
 (.branch 27
 (.leaf ⟨(23, 15705760104704), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record026_result⟩)
 (.leaf ⟨(23, 15706296975360), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(23, 15706429095936), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record028_result⟩)
 (.branch 30
 (.leaf ⟨(23, 15712410140672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record029_result⟩)
 (.leaf ⟨(23, 15712670220288), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(23, 15722939973632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record031_result⟩)
 (.branch 33
 (.leaf ⟨(23, 15723208376320), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record032_result⟩)
 (.leaf ⟨(23, 15809306984448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(23, 15842005778688), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record034_result⟩)
 (.branch 36
 (.leaf ⟨(23, 15842282569728), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record035_result⟩)
 (.leaf ⟨(23, 15842389852160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(23, 15842542649344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record037_result⟩)
 (.branch 39
 (.leaf ⟨(23, 15842546810880), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record038_result⟩)
 (.leaf ⟨(23, 15842658254848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(23, 15851247895040), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record040_result⟩)
 (.branch 42
 (.leaf ⟨(23, 16128415891456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record041_result⟩)
 (.leaf ⟨(23, 16493834699008), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(23, 16493834764288), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record043_result⟩)
 (.branch 45
 (.leaf ⟨(23, 16494977618176), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record044_result⟩)
 (.leaf ⟨(23, 16494977683456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(23, 16494985482256), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record046_result⟩)
 (.leaf ⟨(23, 16495109738752), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record047_result⟩))
 (.branch 49
 (.leaf ⟨(23, 16496208183296), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record048_result⟩)
 (.leaf ⟨(23, 16496468197632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(23, 16496472424448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record050_result⟩)
 (.branch 52
 (.leaf ⟨(23, 16496476585984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record051_result⟩)
 (.leaf ⟨(23, 16496579317760), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(23, 16502952562688), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record053_result⟩)
 (.branch 55
 (.leaf ⟨(23, 16511274061824), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record054_result⟩)
 (.leaf ⟨(23, 16511499518080), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(23, 16511501631488), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record056_result⟩)
 (.branch 58
 (.leaf ⟨(23, 16511532548224), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record057_result⟩)
 (.leaf ⟨(23, 16527189610752), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(23, 16531606079504), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record059_result⟩)
 (.branch 61
 (.leaf ⟨(23, 16531623313408), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record060_result⟩)
 (.leaf ⟨(23, 16531891716096), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(23, 16531895357440), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record062_result⟩)
 (.branch 64
 (.leaf ⟨(23, 16532948287488), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record063_result⟩)
 (.leaf ⟨(23, 16533212430336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(23, 16533220753408), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record065_result⟩)
 (.branch 67
 (.leaf ⟨(23, 16536188227584), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record066_result⟩)
 (.leaf ⟨(23, 16536836309248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(23, 16537108938752), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record068_result⟩)
 (.branch 70
 (.leaf ⟨(23, 16537373179904), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record069_result⟩)
 (.leaf ⟨(23, 16537381502976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(23, 16537505300480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record071_result⟩)
 (.leaf ⟨(23, 16540724953088), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record072_result⟩))
 (.branch 74
 (.leaf ⟨(23, 16544773967872), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record073_result⟩)
 (.leaf ⟨(23, 16608915423232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(23, 16609452228608), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record075_result⟩)
 (.branch 77
 (.leaf ⟨(23, 16632420827136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record076_result⟩)
 (.leaf ⟨(23, 16632824991744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(23, 16640383188992), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record078_result⟩)
 (.branch 80
 (.leaf ⟨(23, 16640391512064), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record079_result⟩)
 (.leaf ⟨(23, 16641522466816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(23, 16648436220160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record081_result⟩)
 (.branch 83
 (.leaf ⟨(23, 16648572567552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record082_result⟩)
 (.leaf ⟨(23, 16648580890624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(23, 16648704688128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record084_result⟩)
 (.branch 86
 (.leaf ⟨(23, 16648713011200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record085_result⟩)
 (.leaf ⟨(23, 16649173352448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(23, 16649476407552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record087_result⟩)
 (.branch 89
 (.leaf ⟨(23, 16650246569984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record088_result⟩)
 (.leaf ⟨(23, 16678037487616), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(23, 16686086422528), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record090_result⟩)
 (.branch 92
 (.leaf ⟨(23, 16701118808320), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record091_result⟩)
 (.leaf ⟨(23, 16711793311744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(23, 16720379052032), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record093_result⟩)
 (.branch 95
 (.leaf ⟨(23, 16721114038272), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record094_result⟩)
 (.leaf ⟨(23, 16769851359488), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(23, 16769863389184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record096_result⟩)
 (.leaf ⟨(23, 16769995509760), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record097_result⟩))
 (.branch 99
 (.leaf ⟨(23, 16770253996160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record098_result⟩)
 (.leaf ⟨(23, 16770259750912), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (6338 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 6338 6438 :=
  block_of_table results 6338 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0086
