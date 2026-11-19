module
prelude
import GraphInputsRow30Part00055Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0783
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 32782688452608), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record000_result⟩)
 (.leaf ⟨(30, 32783216934912), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 32788929576960), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record002_result⟩)
 (.leaf ⟨(30, 32804960207364), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(30, 32804960346112), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record004_result⟩)
 (.leaf ⟨(30, 32804994809856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record005_result⟩))
 (.branch 7
 (.leaf ⟨(30, 32806101057536), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record006_result⟩)
 (.leaf ⟨(30, 32822165241856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(30, 32822693724160), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record008_result⟩)
 (.leaf ⟨(30, 32839320076288), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record009_result⟩))
 (.branch 11
 (.leaf ⟨(30, 32916647247872), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record010_result⟩)
 (.leaf ⟨(30, 32918802006016), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(30, 32919330488320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record012_result⟩)
 (.leaf ⟨(30, 32933827051520), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record013_result⟩))
 (.branch 15
 (.leaf ⟨(30, 32935956840448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record014_result⟩)
 (.leaf ⟨(30, 32986582491264), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(30, 32988672852224), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record016_result⟩)
 (.leaf ⟨(30, 32989174579328), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record017_result⟩))
 (.branch 19
 (.leaf ⟨(30, 32995315564800), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record018_result⟩)
 (.leaf ⟨(30, 32995324993536), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(30, 33022410244224), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record020_result⟩)
 (.leaf ⟨(30, 33029709955072), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record021_result⟩))
 (.branch 23
 (.leaf ⟨(30, 33064135753728), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record022_result⟩)
 (.leaf ⟨(30, 33099576508416), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(30, 33167417278464), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record024_result⟩)
 (.leaf ⟨(30, 33204460388352), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record025_result⟩))
 (.branch 27
 (.leaf ⟨(30, 33238827401216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record026_result⟩)
 (.leaf ⟨(30, 33260382195744), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(30, 33262458650752), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record028_result⟩)
 (.leaf ⟨(30, 33263550758912), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record029_result⟩))
 (.branch 31
 (.leaf ⟨(30, 33295746236416), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record030_result⟩)
 (.branch 32
 (.leaf ⟨(30, 33295750397952), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record031_result⟩)
 (.leaf ⟨(30, 33297807851648), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00055.record032_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25305 + i))) 0 33 :=
  interval_of_check _ 0 33 (by decide +kernel)

public theorem complete : Block 25305 25338 :=
  block_of_table results 25305 33 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0783
