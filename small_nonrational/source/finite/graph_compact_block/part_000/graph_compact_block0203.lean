module
prelude
import GraphInputsRow24Part00087Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0203
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 24640513655040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 24640515801088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record001_result⟩)
 (.leaf ⟨(24, 24640522043392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 24640563200256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record003_result⟩)
 (.leaf ⟨(24, 24640573409280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 24640837650432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record005_result⟩)
 (.leaf ⟨(24, 24641032953920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 24642777514752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 24643180167744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record008_result⟩)
 (.leaf ⟨(24, 24644723949824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 24644734158848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record010_result⟩)
 (.leaf ⟨(24, 24645077057600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 24645079154688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record012_result⟩)
 (.leaf ⟨(24, 24645126602816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10711 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 10711 10725 :=
  block_of_table results 10711 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0203
