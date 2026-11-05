module
prelude
import GraphInputsRow29Part00116Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0550
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 19733369913344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record000_result⟩)
 (.leaf ⟨(29, 19733906718720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 19741955653632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 19742228217856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003_result⟩)
 (.leaf ⟨(29, 19742624579584), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 19748328898560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005_result⟩)
 (.leaf ⟨(29, 19870274035840), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 19878595534976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 19901406281984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record008_result⟩)
 (.leaf ⟨(29, 19901414670336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(29, 19905707540480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record010_result⟩)
 (.leaf ⟨(29, 19907787915264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011_result⟩))
 (.branch 13
 (.leaf ⟨(29, 19914289086592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record012_result⟩)
 (.branch 14
 (.leaf ⟨(29, 20038845267968), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record013_result⟩)
 (.leaf ⟨(29, 20175747318016), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(29, 20176015785984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record015_result⟩)
 (.leaf ⟨(29, 20176284188672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record016_result⟩))
 (.branch 18
 (.leaf ⟨(29, 20190710497408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record017_result⟩)
 (.branch 19
 (.leaf ⟨(29, 20192927186944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record018_result⟩)
 (.leaf ⟨(29, 20193195589632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22174 + i))) 0 20 :=
  interval_of_check _ 0 20 (by decide +kernel)

public theorem complete : Block 22174 22194 :=
  block_of_table results 22174 20 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0550
