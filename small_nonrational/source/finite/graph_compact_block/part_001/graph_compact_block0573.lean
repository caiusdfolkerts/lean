module
prelude
import GraphInputsRow29Part00139Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0573
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 23933740941568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00139.record000_result⟩)
 (.leaf ⟨(29, 23934511104000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00139.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 23940182327552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00139.record002_result⟩)
 (.leaf ⟨(29, 23970212643072), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00139.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 23971017785856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00139.record004_result⟩)
 (.leaf ⟨(29, 23971563044864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00139.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 23972091527168), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00139.record006_result⟩)
 (.leaf ⟨(29, 23974507593984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00139.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(29, 24004643586048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00139.record008_result⟩)
 (.leaf ⟨(29, 24026609090560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00139.record009_result⟩))
 (.branch 11
 (.leaf ⟨(29, 24034658025472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00139.record010_result⟩)
 (.leaf ⟨(29, 24035442556928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00139.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(29, 24039208779776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00139.record012_result⟩)
 (.leaf ⟨(29, 24052959871232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00139.record013_result⟩))
 (.branch 15
 (.leaf ⟨(29, 24055180754944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00139.record014_result⟩)
 (.leaf ⟨(29, 24055717560320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00139.record015_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22513 + i))) 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)

public theorem complete : Block 22513 22529 :=
  block_of_table results 22513 16 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0573
