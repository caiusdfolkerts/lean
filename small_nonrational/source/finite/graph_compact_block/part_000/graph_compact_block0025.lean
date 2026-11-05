module
prelude
import GraphInputsRow16Part00025Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0025
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 25260850315520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record000_result⟩)
 (.leaf ⟨(16, 25260871188480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 25261143752704), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002_result⟩)
 (.leaf ⟨(16, 25261655458304), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(16, 25261655719936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004_result⟩)
 (.leaf ⟨(16, 25328707731712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record005_result⟩))
 (.branch 7
 (.leaf ⟨(16, 25367741005824), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record006_result⟩)
 (.leaf ⟨(16, 25398960750848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(16, 25400038195200), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record008_result⟩)
 (.leaf ⟨(16, 25414600818688), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record009_result⟩))
 (.branch 11
 (.leaf ⟨(16, 25415641006080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record010_result⟩)
 (.leaf ⟨(16, 25633592738048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(16, 25639009157376), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record012_result⟩)
 (.leaf ⟨(16, 25671221149952), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record013_result⟩))
 (.branch 15
 (.leaf ⟨(16, 25841922769152), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record014_result⟩)
 (.branch 16
 (.leaf ⟨(16, 25877354414336), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record015_result⟩)
 (.leaf ⟨(16, 25878423732480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record016_result⟩))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(16, 25878923346176), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record017_result⟩)
 (.leaf ⟨(16, 25895603601408), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record018_result⟩))
 (.branch 20
 (.leaf ⟨(16, 25915333607424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record019_result⟩)
 (.leaf ⟨(16, 25915341930496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(16, 25925698224384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record021_result⟩)
 (.leaf ⟨(16, 25927815856128), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record022_result⟩))
 (.branch 24
 (.leaf ⟨(16, 25931175952384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record023_result⟩)
 (.leaf ⟨(16, 25942831464704), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record024_result⟩))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf ⟨(16, 25943347593472), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record025_result⟩)
 (.leaf ⟨(16, 25946451640576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record026_result⟩))
 (.branch 28
 (.leaf ⟨(16, 25946468155648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record027_result⟩)
 (.leaf ⟨(16, 25963094638848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record028_result⟩)))
 (.branch 31
 (.branch 30
 (.leaf ⟨(16, 25963131895808), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029_result⟩)
 (.leaf ⟨(16, 25963140218880), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record030_result⟩))
 (.branch 32
 (.leaf ⟨(16, 25963363106816), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record031_result⟩)
 (.branch 33
 (.leaf ⟨(16, 25963371429888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record032_result⟩)
 (.leaf ⟨(16, 25963387944960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record033_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1496 + i))) 0 34 :=
  interval_of_check _ 0 34 (by decide +kernel)

public theorem complete : Block 1496 1530 :=
  block_of_table results 1496 34 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0025
