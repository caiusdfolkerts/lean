module
prelude
import GraphInputsRow29Part00110Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0544
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 18848000524544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 18848000589824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record001_result⟩)
 (.leaf ⟨(29, 18848006815808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 18848073916480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record003_result⟩)
 (.leaf ⟨(29, 18877054517504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 18877062905856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record005_result⟩)
 (.leaf ⟨(29, 18881236189440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(29, 18881236254720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record007_result⟩)
 (.leaf ⟨(29, 18881242480704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record008_result⟩))
 (.branch 10
 (.leaf ⟨(29, 18885654872065), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record009_result⟩)
 (.leaf ⟨(29, 18911413207296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(29, 18920003109120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record011_result⟩)
 (.leaf ⟨(29, 18920014618624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record012_result⟩))
 (.branch 14
 (.leaf ⟨(29, 18920137310464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record013_result⟩)
 (.leaf ⟨(29, 18985244434496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record014_result⟩)))))
 (.branch 23
 (.branch 19
 (.branch 17
 (.branch 16
 (.leaf ⟨(29, 19014233423872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record015_result⟩)
 (.leaf ⟨(29, 19014493438208), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record016_result⟩))
 (.branch 18
 (.leaf ⟨(29, 19014503890945), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record017_result⟩)
 (.leaf ⟨(29, 19014503907328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record018_result⟩)))
 (.branch 21
 (.branch 20
 (.leaf ⟨(29, 19074151383296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record019_result⟩)
 (.leaf ⟨(29, 19076772593664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record020_result⟩))
 (.branch 22
 (.leaf ⟨(29, 19093952397312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record021_result⟩)
 (.leaf ⟨(29, 19244853002496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record022_result⟩))))
 (.branch 27
 (.branch 25
 (.branch 24
 (.leaf ⟨(29, 19246999437568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record023_result⟩)
 (.leaf ⟨(29, 19247395799296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record024_result⟩))
 (.branch 26
 (.leaf ⟨(29, 19280268132608), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record025_result⟩)
 (.leaf ⟨(29, 19280284647680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record026_result⟩)))
 (.branch 29
 (.branch 28
 (.leaf ⟨(29, 19281857282304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record027_result⟩)
 (.leaf ⟨(29, 19294748442624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record028_result⟩))
 (.branch 30
 (.leaf ⟨(29, 19297959706880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record029_result⟩)
 (.leaf ⟨(29, 19329041072128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00110.record030_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22097 + i))) 0 31 :=
  interval_of_check _ 0 31 (by decide +kernel)

public theorem complete : Block 22097 22128 :=
  block_of_table results 22097 31 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0544
