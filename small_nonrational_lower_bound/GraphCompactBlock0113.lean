module
prelude
import GraphInputsRow23Part00035Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0113
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 34498268905472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 34498337046528), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001_result⟩)
 (.leaf ⟨(23, 34498452652032), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(23, 34500398694400), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record003_result⟩)
 (.branch 5
 (.leaf ⟨(23, 34531554115584), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record004_result⟩)
 (.leaf ⟨(23, 34531688316928), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(23, 34535832160256), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 34635707351296), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record007_result⟩)
 (.leaf ⟨(23, 34635725701376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(23, 34635744608256), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record009_result⟩)
 (.branch 11
 (.leaf ⟨(23, 34635752931328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record010_result⟩)
 (.leaf ⟨(23, 34635759255808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(23, 34635975819264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record012_result⟩)
 (.branch 14
 (.leaf ⟨(23, 34635984142336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record013_result⟩)
 (.leaf ⟨(23, 34636495589376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(23, 34640022798336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 34640295362560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record016_result⟩)
 (.leaf ⟨(23, 34640790814720), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(23, 34643760386048), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record018_result⟩)
 (.branch 20
 (.leaf ⟨(23, 34643776901120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record019_result⟩)
 (.leaf ⟨(23, 34644850377216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(23, 34647535321088), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record021_result⟩)
 (.leaf ⟨(23, 34670188232704), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_result⟩))
 (.branch 24
 (.leaf ⟨(23, 34674621546496), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023_result⟩)
 (.leaf ⟨(23, 34675150028800), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7744 + i))) 0 25 :=
  interval_of_check _ 0 25 (by decide +kernel)

public theorem complete : Block 7744 7769 :=
  block_of_table results 7744 25 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0113
