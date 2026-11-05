module
prelude
import GraphInputsRow16Part00007Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0007
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 27
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 14424180031744), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 14424184258560), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record001_result⟩)
 (.leaf ⟨(16, 14424522883072), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(16, 14451604472064), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record003_result⟩)
 (.branch 5
 (.leaf ⟨(16, 14452141342720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record004_result⟩)
 (.leaf ⟨(16, 14452339523584), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(16, 14484336820224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record006_result⟩)
 (.branch 8
 (.leaf ⟨(16, 14488749211648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record007_result⟩)
 (.leaf ⟨(16, 14488947392512), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(16, 14503645380608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record009_result⟩)
 (.leaf ⟨(16, 14505791815680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record010_result⟩))
 (.branch 12
 (.leaf ⟨(16, 14518274064384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record011_result⟩)
 (.leaf ⟨(16, 14522974740480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record012_result⟩)))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ⟨(16, 14523231698944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record013_result⟩)
 (.branch 15
 (.leaf ⟨(16, 14523240022016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record014_result⟩)
 (.leaf ⟨(16, 14524014927872), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record015_result⟩)))
 (.branch 18
 (.branch 17
 (.leaf ⟨(16, 14524237750528), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record016_result⟩)
 (.leaf ⟨(16, 14527392448512), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record017_result⟩))
 (.branch 19
 (.leaf ⟨(16, 14527400771584), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record018_result⟩)
 (.leaf ⟨(16, 14529984528384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record019_result⟩))))
 (.branch 23
 (.branch 21
 (.leaf ⟨(16, 14530454233088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record020_result⟩)
 (.branch 22
 (.leaf ⟨(16, 14539027480576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record021_result⟩)
 (.leaf ⟨(16, 14558341104640), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(16, 14581188542464), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record023_result⟩)
 (.leaf ⟨(16, 14596246618112), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record024_result⟩))
 (.branch 26
 (.leaf ⟨(16, 14608471523328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record025_result⟩)
 (.leaf ⟨(16, 14608603643904), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record026_result⟩))))))
 (.branch 40
 (.branch 33
 (.branch 30
 (.branch 28
 (.leaf ⟨(16, 14608672760064), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record027_result⟩)
 (.branch 29
 (.leaf ⟨(16, 14617061425152), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record028_result⟩)
 (.leaf ⟨(16, 14617531129856), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(16, 14617598230528), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record030_result⟩)
 (.branch 32
 (.leaf ⟨(16, 14617788088320), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record031_result⟩)
 (.leaf ⟨(16, 14617796411392), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record032_result⟩))))
 (.branch 36
 (.branch 34
 (.leaf ⟨(16, 14630606864896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record033_result⟩)
 (.branch 35
 (.leaf ⟨(16, 14633122431232), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record034_result⟩)
 (.leaf ⟨(16, 14633126658048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record035_result⟩)))
 (.branch 38
 (.branch 37
 (.leaf ⟨(16, 14633133940736), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record036_result⟩)
 (.leaf ⟨(16, 14633159688192), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record037_result⟩))
 (.branch 39
 (.leaf ⟨(16, 14633266061312), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record038_result⟩)
 (.leaf ⟨(16, 14633893634048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record039_result⟩)))))
 (.branch 47
 (.branch 43
 (.branch 41
 (.leaf ⟨(16, 14633894674432), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record040_result⟩)
 (.branch 42
 (.leaf ⟨(16, 14647123083264), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record041_result⟩)
 (.leaf ⟨(16, 14664571289600), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record042_result⟩)))
 (.branch 45
 (.branch 44
 (.leaf ⟨(16, 14665268625664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record043_result⟩)
 (.leaf ⟨(16, 14665272852480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record044_result⟩))
 (.branch 46
 (.leaf ⟨(16, 14665346195456), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record045_result⟩)
 (.leaf ⟨(16, 14665471033344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record046_result⟩))))
 (.branch 50
 (.branch 48
 (.leaf ⟨(16, 14665478316032), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record047_result⟩)
 (.branch 49
 (.leaf ⟨(16, 14666105888768), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record048_result⟩)
 (.leaf ⟨(16, 14666106929152), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record049_result⟩)))
 (.branch 52
 (.branch 51
 (.leaf ⟨(16, 14667624751104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record050_result⟩)
 (.leaf ⟨(16, 14673919377664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record051_result⟩))
 (.branch 53
 (.leaf ⟨(16, 14673919442944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record052_result⟩)
 (.leaf ⟨(16, 14674051563520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00007.record053_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (604 + i))) 0 54 :=
  interval_of_check _ 0 54 (by decide +kernel)

public theorem complete : Block 604 658 :=
  block_of_table results 604 54 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0007
