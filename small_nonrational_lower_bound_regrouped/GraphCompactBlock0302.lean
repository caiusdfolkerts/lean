module
prelude
import GraphInputsRow25Part00012Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0302
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(25, 16720379052032), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record000_result⟩)
 (.branch 2
 (.leaf ⟨(25, 16721114038272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record001_result⟩)
 (.leaf ⟨(25, 16769851359488), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(25, 16769863389184), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record003_result⟩)
 (.branch 5
 (.leaf ⟨(25, 16769995509760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record004_result⟩)
 (.leaf ⟨(25, 16770253996160), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(25, 16770259750912), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record006_result⟩)
 (.branch 8
 (.leaf ⟨(25, 16776699056128), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record007_result⟩)
 (.leaf ⟨(25, 16778692984832), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(25, 16784933785728), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record009_result⟩)
 (.branch 11
 (.leaf ⟨(25, 16906134257920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record010_result⟩)
 (.leaf ⟨(25, 16908350980096), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(25, 16908623544320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record012_result⟩)
 (.branch 14
 (.leaf ⟨(25, 16909019906048), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record013_result⟩)
 (.leaf ⟨(25, 16914724225024), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(25, 16915261030400), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record015_result⟩)
 (.branch 17
 (.leaf ⟨(25, 16930795700224), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record016_result⟩)
 (.leaf ⟨(25, 16931904028672), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(25, 16932036149248), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record018_result⟩)
 (.branch 20
 (.leaf ⟨(25, 16943667019776), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record019_result⟩)
 (.leaf ⟨(25, 16943939584000), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(25, 16944451551232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record021_result⟩)
 (.leaf ⟨(25, 16948496695296), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record022_result⟩))
 (.branch 24
 (.leaf ⟨(25, 16948612300800), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record023_result⟩)
 (.leaf ⟨(25, 16969415917568), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(25, 16975996715008), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record025_result⟩)
 (.branch 27
 (.leaf ⟨(25, 16980430028800), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record026_result⟩)
 (.leaf ⟨(25, 16985119260672), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(25, 16986671153152), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record028_result⟩)
 (.branch 30
 (.leaf ⟨(25, 17003842633728), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record029_result⟩)
 (.leaf ⟨(25, 17042481381632), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(25, 17042481446912), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record031_result⟩)
 (.branch 33
 (.leaf ⟨(25, 17042485022976), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record032_result⟩)
 (.leaf ⟨(25, 17042485088256), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(25, 17042493147152), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record034_result⟩)
 (.branch 36
 (.leaf ⟨(25, 17042724098064), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record035_result⟩)
 (.leaf ⟨(25, 17042724358160), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(25, 17043558564352), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record037_result⟩)
 (.branch 39
 (.leaf ⟨(25, 17043780929552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record038_result⟩)
 (.leaf ⟨(25, 17043798097921), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(25, 17043798163456), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record040_result⟩)
 (.branch 42
 (.leaf ⟨(25, 17044058177792), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record041_result⟩)
 (.leaf ⟨(25, 17044066566144), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(25, 17044070207488), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record043_result⟩)
 (.branch 45
 (.leaf ⟨(25, 17051062241296), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record044_result⟩)
 (.leaf ⟨(25, 17051574341888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(25, 17051582730240), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record046_result⟩)
 (.leaf ⟨(25, 17051590856960), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record047_result⟩))
 (.branch 49
 (.leaf ⟨(25, 17052131721472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record048_result⟩)
 (.leaf ⟨(25, 17052404350976), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(25, 17052639301632), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record050_result⟩)
 (.branch 52
 (.leaf ⟨(25, 17052664333056), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record051_result⟩)
 (.leaf ⟨(25, 17052668592128), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(25, 17052676915200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record053_result⟩)
 (.branch 55
 (.leaf ⟨(25, 17052899803136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record054_result⟩)
 (.leaf ⟨(25, 17060164276352), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(25, 17060180791424), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record056_result⟩)
 (.branch 58
 (.leaf ⟨(25, 17060415672336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record057_result⟩)
 (.leaf ⟨(25, 17061254267520), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(25, 17061489148432), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record059_result⟩)
 (.branch 61
 (.leaf ⟨(25, 17068234146048), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record060_result⟩)
 (.leaf ⟨(25, 17069005869056), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(25, 17081357631744), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record062_result⟩)
 (.branch 64
 (.leaf ⟨(25, 17112496144640), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record063_result⟩)
 (.leaf ⟨(25, 17121090273280), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(25, 17121627078656), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record065_result⟩)
 (.branch 67
 (.leaf ⟨(25, 17136957325312), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record066_result⟩)
 (.leaf ⟨(25, 17137725341696), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(25, 17154376269824), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record068_result⟩)
 (.branch 70
 (.leaf ⟨(25, 17171556073472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record069_result⟩)
 (.leaf ⟨(25, 17180431486976), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(25, 17188476485888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record071_result⟩)
 (.leaf ⟨(25, 17189013356544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record072_result⟩))
 (.branch 74
 (.leaf ⟨(25, 17189021679616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record073_result⟩)
 (.leaf ⟨(25, 17190078251008), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(25, 17190212337664), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record075_result⟩)
 (.branch 77
 (.leaf ⟨(25, 17197586057232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record076_result⟩)
 (.leaf ⟨(25, 17197602701840), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(25, 17197854625792), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record078_result⟩)
 (.branch 80
 (.leaf ⟨(25, 17198122959104), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record079_result⟩)
 (.leaf ⟨(25, 17198261272576), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(25, 17198533836800), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record081_result⟩)
 (.branch 83
 (.leaf ⟨(25, 17198928101888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record082_result⟩)
 (.leaf ⟨(25, 17201381834752), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(25, 17202149851136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record084_result⟩)
 (.branch 86
 (.leaf ⟨(25, 17205639123200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record085_result⟩)
 (.leaf ⟨(25, 17218800779264), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(25, 17227659083776), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record087_result⟩)
 (.branch 89
 (.leaf ⟨(25, 17235980582912), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record088_result⟩)
 (.leaf ⟨(25, 17236509065216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(25, 17292083593216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record090_result⟩)
 (.branch 92
 (.leaf ⟨(25, 17309255073792), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record091_result⟩)
 (.leaf ⟨(25, 17317602004992), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(25, 17326451720720), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record093_result⟩)
 (.branch 95
 (.leaf ⟨(25, 17457033052160), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record094_result⟩)
 (.leaf ⟨(25, 17480516895236), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(25, 17493678620672), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record096_result⟩)
 (.leaf ⟨(25, 17502528602112), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record097_result⟩))
 (.branch 99
 (.leaf ⟨(25, 17523487604736), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record098_result⟩)
 (.leaf ⟨(25, 17532081668096), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (13072 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 13072 13172 :=
  block_of_table results 13072 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0302
