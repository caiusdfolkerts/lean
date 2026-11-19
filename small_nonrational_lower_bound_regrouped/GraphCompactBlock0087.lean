module
prelude
import GraphInputsRow23Part00009Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0087
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 37
 (.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(23, 16776699056128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record000_result⟩)
 (.leaf ⟨(23, 16778692984832), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record001_result⟩))
 (.branch 3
 (.leaf ⟨(23, 16815208005632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record002_result⟩)
 (.leaf ⟨(23, 16906134257920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(23, 16908350980096), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record004_result⟩)
 (.leaf ⟨(23, 16908623544320), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record005_result⟩))
 (.branch 7
 (.leaf ⟨(23, 16909019906048), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 16914724225024), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record007_result⟩)
 (.leaf ⟨(23, 16915261030400), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(23, 16930795700224), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record009_result⟩)
 (.leaf ⟨(23, 16931904028672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record010_result⟩))
 (.branch 12
 (.leaf ⟨(23, 16932036149248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record011_result⟩)
 (.leaf ⟨(23, 16943667019776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(23, 16943939584000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record013_result⟩)
 (.leaf ⟨(23, 16944451551232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record014_result⟩))
 (.branch 16
 (.leaf ⟨(23, 16947959889920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 16948496695296), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record016_result⟩)
 (.leaf ⟨(23, 16948612300800), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record017_result⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨(23, 16952236113920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record018_result⟩)
 (.leaf ⟨(23, 16969415917568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record019_result⟩))
 (.branch 21
 (.leaf ⟨(23, 16975996715008), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record020_result⟩)
 (.leaf ⟨(23, 16980430028800), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(23, 16980958511104), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record022_result⟩)
 (.leaf ⟨(23, 16985119260672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record023_result⟩))
 (.branch 25
 (.leaf ⟨(23, 16986671153152), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record024_result⟩)
 (.branch 26
 (.leaf ⟨(23, 17003842633728), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record025_result⟩)
 (.leaf ⟨(23, 17043798163456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record026_result⟩)))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf ⟨(23, 17044066566144), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record027_result⟩)
 (.leaf ⟨(23, 17044070207488), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record028_result⟩))
 (.branch 30
 (.leaf ⟨(23, 17051582730240), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record029_result⟩)
 (.branch 31
 (.leaf ⟨(23, 17052404350976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record030_result⟩)
 (.leaf ⟨(23, 17052639301632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record031_result⟩))))
 (.branch 34
 (.branch 33
 (.leaf ⟨(23, 17052668592128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record032_result⟩)
 (.leaf ⟨(23, 17052676915200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record033_result⟩))
 (.branch 35
 (.leaf ⟨(23, 17052899803136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record034_result⟩)
 (.branch 36
 (.leaf ⟨(23, 17059912356096), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record035_result⟩)
 (.leaf ⟨(23, 17060180791424), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record036_result⟩)))))))
 (.branch 55
 (.branch 46
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf ⟨(23, 17060415672336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record037_result⟩)
 (.leaf ⟨(23, 17069005869056), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record038_result⟩))
 (.branch 40
 (.leaf ⟨(23, 17081357631744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record039_result⟩)
 (.leaf ⟨(23, 17121090273280), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record040_result⟩)))
 (.branch 43
 (.branch 42
 (.leaf ⟨(23, 17121627078656), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record041_result⟩)
 (.leaf ⟨(23, 17136957325312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record042_result⟩))
 (.branch 44
 (.leaf ⟨(23, 17137725341696), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record043_result⟩)
 (.branch 45
 (.leaf ⟨(23, 17154376269824), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record044_result⟩)
 (.leaf ⟨(23, 17171556073472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045_result⟩)))))
 (.branch 50
 (.branch 48
 (.branch 47
 (.leaf ⟨(23, 17172084555776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record046_result⟩)
 (.leaf ⟨(23, 17180431486976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record047_result⟩))
 (.branch 49
 (.leaf ⟨(23, 17181081403648), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record048_result⟩)
 (.leaf ⟨(23, 17189013356544), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record049_result⟩)))
 (.branch 52
 (.branch 51
 (.leaf ⟨(23, 17189021679616), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record050_result⟩)
 (.leaf ⟨(23, 17190078251008), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record051_result⟩))
 (.branch 53
 (.leaf ⟨(23, 17190212337664), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record052_result⟩)
 (.branch 54
 (.leaf ⟨(23, 17192796094464), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record053_result⟩)
 (.leaf ⟨(23, 17197586057232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record054_result⟩))))))
 (.branch 64
 (.branch 59
 (.branch 57
 (.branch 56
 (.leaf ⟨(23, 17197854625792), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record055_result⟩)
 (.leaf ⟨(23, 17198261272576), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record056_result⟩))
 (.branch 58
 (.leaf ⟨(23, 17198533836800), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record057_result⟩)
 (.leaf ⟨(23, 17198928101888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record058_result⟩)))
 (.branch 61
 (.branch 60
 (.leaf ⟨(23, 17201381834752), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record059_result⟩)
 (.leaf ⟨(23, 17202149851136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record060_result⟩))
 (.branch 62
 (.leaf ⟨(23, 17218800779264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record061_result⟩)
 (.branch 63
 (.leaf ⟨(23, 17227659083776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record062_result⟩)
 (.leaf ⟨(23, 17235980582912), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record063_result⟩)))))
 (.branch 69
 (.branch 66
 (.branch 65
 (.leaf ⟨(23, 17236509065216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record064_result⟩)
 (.leaf ⟨(23, 17274358661120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record065_result⟩))
 (.branch 67
 (.leaf ⟨(23, 17292083593216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record066_result⟩)
 (.branch 68
 (.leaf ⟨(23, 17309255073792), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record067_result⟩)
 (.leaf ⟨(23, 17317602004992), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record068_result⟩))))
 (.branch 71
 (.branch 70
 (.leaf ⟨(23, 17326183874560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record069_result⟩)
 (.leaf ⟨(23, 17326451720720), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record070_result⟩))
 (.branch 72
 (.leaf ⟨(23, 17457033052160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071_result⟩)
 (.branch 73
 (.leaf ⟨(23, 17493678620672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072_result⟩)
 (.leaf ⟨(23, 17502528602112), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record073_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (6438 + i))) 0 74 :=
  interval_of_check _ 0 74 (by decide +kernel)

public theorem complete : Block 6438 6512 :=
  block_of_table results 6438 74 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0087
