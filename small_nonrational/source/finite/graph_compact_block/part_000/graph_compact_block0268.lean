module
prelude
import GraphInputsRow24Part00152Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0268
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 32643388276736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00152.record000_result⟩)
 (.leaf ⟨(24, 32643429498880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00152.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 32644972871936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00152.record002_result⟩)
 (.leaf ⟨(24, 32658948628736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00152.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 32659032309760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00152.record004_result⟩)
 (.leaf ⟨(24, 32659485499392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00152.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 32659486539776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00152.record006_result⟩)
 (.leaf ⟨(24, 32659502014464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00152.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 32660005200128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00152.record008_result⟩)
 (.leaf ⟨(24, 32660609040896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00152.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 32676128293120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00152.record010_result⟩)
 (.leaf ⟨(24, 32676665163776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00152.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 32676673486848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00152.record012_result⟩)
 (.leaf ⟨(24, 32693291190528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00152.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 32693828061184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00152.record014_result⟩)
 (.leaf ⟨(24, 32693844705792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00152.record015_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11912 + i))) 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)

public theorem complete : Block 11912 11928 :=
  block_of_table results 11912 16 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0268
