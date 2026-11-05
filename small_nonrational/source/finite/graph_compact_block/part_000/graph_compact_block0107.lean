module
prelude
import GraphInputsRow23Part00029Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0107
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(23, 32530116968448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record000_result⟩)
 (.leaf ⟨(23, 32564442234880), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record001_result⟩))
 (.branch 3
 (.leaf ⟨(23, 32642900754432), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record002_result⟩)
 (.leaf ⟨(23, 32645517934592), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(23, 32660080558080), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record004_result⟩)
 (.leaf ⟨(23, 32660609040384), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record005_result⟩))
 (.branch 7
 (.leaf ⟨(23, 32693316222976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record006_result⟩)
 (.leaf ⟨(23, 32693844705280), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(23, 32711613907200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record008_result⟩)
 (.leaf ⟨(23, 32716951191552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record009_result⟩))
 (.branch 11
 (.leaf ⟨(23, 32717719207936), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record010_result⟩)
 (.leaf ⟨(23, 32723390496768), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(23, 32729128239104), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record012_result⟩)
 (.leaf ⟨(23, 32730201456640), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record013_result⟩))
 (.branch 15
 (.leaf ⟨(23, 32779208261888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record014_result⟩)
 (.leaf ⟨(23, 32780335513600), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record015_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7644 + i))) 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)

public theorem complete : Block 7644 7660 :=
  block_of_table results 7644 16 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0107
