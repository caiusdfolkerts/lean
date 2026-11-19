module
prelude
import GraphInputsRow26Part00048Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0364
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 24640522043392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048.record000_result⟩)
 (.leaf ⟨(26, 24640573409280), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 24640837650432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048.record002_result⟩)
 (.leaf ⟨(26, 24642777514752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 24643180167744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048.record004_result⟩)
 (.leaf ⟨(26, 24644723949824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 24644734158848), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048.record006_result⟩)
 (.leaf ⟨(26, 24645077057600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(26, 24645079154688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048.record008_result⟩)
 (.leaf ⟨(26, 24645126602816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048.record009_result⟩))
 (.branch 11
 (.leaf ⟨(26, 24645193703488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048.record010_result⟩)
 (.leaf ⟨(26, 24655662416448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(26, 24663849844800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048.record012_result⟩)
 (.leaf ⟨(26, 24663984062464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048.record013_result⟩))
 (.branch 15
 (.leaf ⟨(26, 24663986143232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 24665997320256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048.record015_result⟩)
 (.leaf ⟨(26, 24666064437248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048.record016_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16547 + i))) 0 17 :=
  interval_of_check _ 0 17 (by decide +kernel)

public theorem complete : Block 16547 16564 :=
  block_of_table results 16547 17 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0364
