module
prelude
import GraphInputsRow24Part00090Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0206
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 24782527533120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record000_result⟩)
 (.leaf ⟨(24, 24786927911168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 24810172743936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002_result⟩)
 (.leaf ⟨(24, 24826388447488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 24827461665024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record004_result⟩)
 (.leaf ⟨(24, 24849342857216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 24849351180288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record006_result⟩)
 (.leaf ⟨(24, 24855583981568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 24867929882880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008_result⟩)
 (.leaf ⟨(24, 24878761644288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 24878893764864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record010_result⟩)
 (.leaf ⟨(24, 24879158006016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 24879164297280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record012_result⟩)
 (.leaf ⟨(24, 24885597311232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 24885603082304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014_result⟩)
 (.leaf ⟨(24, 24885603098624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record015_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10765 + i))) 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)

public theorem complete : Block 10765 10781 :=
  block_of_table results 10765 16 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0206
