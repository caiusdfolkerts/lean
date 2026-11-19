module
prelude
import GraphInputsRow24Part00073Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0189
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 23795807027201), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00073.record000_result⟩)
 (.leaf ⟨(24, 23916688969984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00073.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 23916821090560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00073.record002_result⟩)
 (.leaf ⟨(24, 23917085331712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00073.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 23917091622976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00073.record004_result⟩)
 (.leaf ⟨(24, 23923530928192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00073.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 23924613071104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00073.record006_result⟩)
 (.leaf ⟨(24, 23931903805456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00073.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 23941792940032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00073.record008_result⟩)
 (.leaf ⟨(24, 23971286384896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00073.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 23971554852864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00073.record010_result⟩)
 (.leaf ⟨(24, 23971563175936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00073.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 23972091527680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00073.record012_result⟩)
 (.leaf ⟨(24, 23986993954816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00073.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 23988537458944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00073.record014_result⟩)
 (.leaf ⟨(24, 23989074329600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00073.record015_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10447 + i))) 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)

public theorem complete : Block 10447 10463 :=
  block_of_table results 10447 16 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0189
