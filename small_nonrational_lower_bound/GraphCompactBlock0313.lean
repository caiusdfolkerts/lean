module
prelude
import GraphInputsRow25Part00023Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0313
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 29
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(25, 32806101057536), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record000_result⟩)
 (.branch 2
 (.leaf ⟨(25, 32822165241856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record001_result⟩)
 (.leaf ⟨(25, 32822693724160), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(25, 32839320076288), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record003_result⟩)
 (.leaf ⟨(25, 32916647247872), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record004_result⟩))
 (.branch 6
 (.leaf ⟨(25, 32918802006016), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record005_result⟩)
 (.leaf ⟨(25, 32919330488320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(25, 32933827051520), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record007_result⟩)
 (.branch 9
 (.leaf ⟨(25, 32935956840448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record008_result⟩)
 (.leaf ⟨(25, 32986582491264), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(25, 32988672852224), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record010_result⟩)
 (.leaf ⟨(25, 32989174579328), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record011_result⟩))
 (.branch 13
 (.leaf ⟨(25, 32995315564800), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record012_result⟩)
 (.leaf ⟨(25, 32995324993536), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(25, 33022410244224), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record014_result⟩)
 (.branch 16
 (.leaf ⟨(25, 33029709955072), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record015_result⟩)
 (.leaf ⟨(25, 33064135753728), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(25, 33099576508416), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record017_result⟩)
 (.leaf ⟨(25, 33167417278464), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record018_result⟩))
 (.branch 20
 (.leaf ⟨(25, 33204460388352), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record019_result⟩)
 (.leaf ⟨(25, 33238827401216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record020_result⟩))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf ⟨(25, 33260382195744), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record021_result⟩)
 (.leaf ⟨(25, 33262458650752), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record022_result⟩))
 (.branch 24
 (.leaf ⟨(25, 33263550758912), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record023_result⟩)
 (.leaf ⟨(25, 33295746236416), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record024_result⟩)))
 (.branch 27
 (.branch 26
 (.leaf ⟨(25, 33295750397952), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record025_result⟩)
 (.leaf ⟨(25, 33297807851648), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record026_result⟩))
 (.branch 28
 (.leaf ⟨(25, 33298210357760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record027_result⟩)
 (.leaf ⟨(25, 33579539103744), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record028_result⟩))))))
 (.branch 44
 (.branch 36
 (.branch 32
 (.branch 30
 (.leaf ⟨(25, 33613831733248), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record029_result⟩)
 (.branch 31
 (.leaf ⟨(25, 33682416992256), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record030_result⟩)
 (.leaf ⟨(25, 33685463171072), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record031_result⟩)))
 (.branch 34
 (.branch 33
 (.leaf ⟨(25, 33751002251264), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record032_result⟩)
 (.leaf ⟨(25, 33751530733568), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record033_result⟩))
 (.branch 35
 (.leaf ⟨(25, 34088117371136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record034_result⟩)
 (.leaf ⟨(25, 34088253718528), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record035_result⟩))))
 (.branch 40
 (.branch 38
 (.branch 37
 (.leaf ⟨(25, 34088262041600), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record036_result⟩)
 (.leaf ⟨(25, 34088385839104), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record037_result⟩))
 (.branch 39
 (.leaf ⟨(25, 34088394162176), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record038_result⟩)
 (.leaf ⟨(25, 34088484929536), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record039_result⟩)))
 (.branch 42
 (.branch 41
 (.leaf ⟨(25, 34088887533568), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record040_result⟩)
 (.leaf ⟨(25, 34091337023744), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record041_result⟩))
 (.branch 43
 (.leaf ⟨(25, 34092108746752), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record042_result⟩)
 (.leaf ⟨(25, 34094558757120), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record043_result⟩)))))
 (.branch 51
 (.branch 47
 (.branch 45
 (.leaf ⟨(25, 34094726053888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record044_result⟩)
 (.branch 46
 (.leaf ⟨(25, 34095095627776), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record045_result⟩)
 (.leaf ⟨(25, 34095097708544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record046_result⟩)))
 (.branch 49
 (.branch 48
 (.leaf ⟨(25, 34095128657920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record047_result⟩)
 (.leaf ⟨(25, 34095631974656), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record048_result⟩))
 (.branch 50
 (.leaf ⟨(25, 34096269496320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record049_result⟩)
 (.leaf ⟨(25, 34110664351808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record050_result⟩))))
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf ⟨(25, 34123532501248), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record051_result⟩)
 (.leaf ⟨(25, 34123800969216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record052_result⟩))
 (.branch 54
 (.leaf ⟨(25, 34123809292288), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record053_result⟩)
 (.leaf ⟨(25, 34124320739328), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record054_result⟩)))
 (.branch 57
 (.branch 56
 (.leaf ⟨(25, 34124589072640), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record055_result⟩)
 (.leaf ⟨(25, 34124865863680), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record056_result⟩))
 (.branch 58
 (.leaf ⟨(25, 34125394215424), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record057_result⟩)
 (.leaf ⟨(25, 34127827452160), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00023.record058_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (13887 + i))) 0 59 :=
  interval_of_check _ 0 59 (by decide +kernel)

public theorem complete : Block 13887 13946 :=
  block_of_table results 13887 59 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0313
