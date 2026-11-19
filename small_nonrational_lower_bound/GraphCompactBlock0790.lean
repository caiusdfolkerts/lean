module
prelude
import GraphInputsRow31Part00002Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0790
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 110067155072), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record000_result⟩)
 (.leaf ⟨(31, 110339588352), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 114227741440), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record002_result⟩)
 (.leaf ⟨(31, 114231935232), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 114362105984), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record004_result⟩)
 (.leaf ⟨(31, 114500337920), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 114500403200), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 114634539264), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record007_result⟩)
 (.leaf ⟨(31, 123090272512), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(31, 123090337792), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record009_result⟩)
 (.leaf ⟨(31, 129666916416), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record010_result⟩))
 (.branch 12
 (.leaf ⟨(31, 144461348992), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record011_result⟩)
 (.branch 13
 (.leaf ⟨(31, 182949314816), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record012_result⟩)
 (.leaf ⟨(31, 183217717504), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(31, 183217782784), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record014_result⟩)
 (.leaf ⟨(31, 183219798272), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record015_result⟩))
 (.branch 17
 (.leaf ⟨(31, 185298092288), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record016_result⟩)
 (.branch 18
 (.leaf ⟨(31, 191539281920), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record017_result⟩)
 (.leaf ⟨(31, 191541297408), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record018_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25451 + i))) 0 19 :=
  interval_of_check _ 0 19 (by decide +kernel)

public theorem complete : Block 25451 25470 :=
  block_of_table results 25451 19 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0790
