module
prelude
import GraphInputsRow16Part00037Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0037
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 32231737860096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record000_result⟩)
 (.leaf ⟨(16, 32236162785536), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 32236699656192), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record002_result⟩)
 (.leaf ⟨(16, 32236700696576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(16, 32450131009536), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record004_result⟩)
 (.leaf ⟨(16, 32458452508672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record005_result⟩))
 (.branch 7
 (.leaf ⟨(16, 32473746538752), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record006_result⟩)
 (.leaf ⟨(16, 32490389537024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(16, 32490525884416), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record008_result⟩)
 (.leaf ⟨(16, 32490534207488), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record009_result⟩))
 (.branch 11
 (.leaf ⟨(16, 32490757095424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record010_result⟩)
 (.leaf ⟨(16, 32490930569216), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(16, 32514538741760), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record012_result⟩)
 (.leaf ⟨(16, 32514564489216), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record013_result⟩))
 (.branch 15
 (.leaf ⟨(16, 32514572812288), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record014_result⟩)
 (.leaf ⟨(16, 32522860240896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(16, 32523124482048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record016_result⟩)
 (.leaf ⟨(16, 32530141552640), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record017_result⟩))
 (.branch 19
 (.leaf ⟨(16, 32531198124032), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record018_result⟩)
 (.leaf ⟨(16, 32713794945280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(16, 32724471652352), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record020_result⟩)
 (.leaf ⟨(16, 32745990422784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record021_result⟩))
 (.branch 23
 (.leaf ⟨(16, 33034104537088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record022_result⟩)
 (.leaf ⟨(16, 33034112860160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(16, 33064037130496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record024_result⟩)
 (.leaf ⟨(16, 33066316791808), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record025_result⟩))
 (.branch 27
 (.leaf ⟨(16, 33066325114880), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record026_result⟩)
 (.leaf ⟨(16, 33068132925440), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(16, 33093012955392), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record028_result⟩)
 (.leaf ⟨(16, 33101368590336), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record029_result⟩))
 (.branch 31
 (.leaf ⟨(16, 33102458191872), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record030_result⟩)
 (.leaf ⟨(16, 33198235459840), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00037.record031_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (2019 + i))) 0 32 :=
  interval_of_check _ 0 32 (by decide +kernel)

public theorem complete : Block 2019 2051 :=
  block_of_table results 2019 32 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0037
