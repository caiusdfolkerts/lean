module
prelude
import GraphInputsRow24Part00160Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0276
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 32933809358880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00160.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 32935956709892), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00160.record001_result⟩)
 (.leaf ⟨(24, 32988877308160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00160.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 32991025832192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00160.record003_result⟩)
 (.leaf ⟨(24, 33022146003200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00160.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 33023338807296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00160.record005_result⟩)
 (.leaf ⟨(24, 33025419182080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00160.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(24, 33032996659456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00160.record007_result⟩)
 (.leaf ⟨(24, 33058653217024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00160.record008_result⟩))
 (.branch 10
 (.leaf ⟨(24, 33059777871872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00160.record009_result⟩)
 (.leaf ⟨(24, 33063938621440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00160.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 33064135696640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00160.record011_result⟩)
 (.leaf ⟨(24, 33065208914176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00160.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 33098495492096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00160.record013_result⟩)
 (.leaf ⟨(24, 33102730625024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00160.record014_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11978 + i))) 0 15 :=
  interval_of_check _ 0 15 (by decide +kernel)

public theorem complete : Block 11978 11993 :=
  block_of_table results 11978 15 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0276
