module
prelude
import GraphInputsRow24Part00092Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0208
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 25020735193344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record000_result⟩)
 (.leaf ⟨(24, 25022774120512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 25023856263424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record002_result⟩)
 (.leaf ⟨(24, 25092676452352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 25116989917184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record004_result⟩)
 (.leaf ⟨(24, 25117258481664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 25125827250432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_result⟩)
 (.leaf ⟨(24, 25125843895040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 25125961662464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record008_result⟩)
 (.leaf ⟨(24, 25128117207040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 25152488243456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record010_result⟩)
 (.leaf ⟨(24, 25152492470272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 25152498712576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record012_result⟩)
 (.leaf ⟨(24, 25152616138752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 25152688505088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 25152690651136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record015_result⟩)
 (.leaf ⟨(24, 25152696893440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10796 + i))) 0 17 :=
  interval_of_check _ 0 17 (by decide +kernel)

public theorem complete : Block 10796 10813 :=
  block_of_table results 10796 17 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0208
