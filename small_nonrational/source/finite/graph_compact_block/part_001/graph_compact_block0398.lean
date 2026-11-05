module
prelude
import GraphInputsRow26Part00082Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0398
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 34194419941376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record000_result⟩)
 (.leaf ⟨(26, 34195732692992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 34196261175296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record002_result⟩)
 (.leaf ⟨(26, 34222385664256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 34222391955520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004_result⟩)
 (.leaf ⟨(26, 34223943852096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 34239548622864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 34240604422144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record007_result⟩)
 (.leaf ⟨(26, 34497227923520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(26, 34497228980224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record009_result⟩)
 (.leaf ⟨(26, 34497230800896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record010_result⟩))
 (.branch 12
 (.leaf ⟨(26, 34497278249024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record011_result⟩)
 (.branch 13
 (.leaf ⟨(26, 34498318305344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_result⟩)
 (.leaf ⟨(26, 34498320402432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(26, 34498334949952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record014_result⟩)
 (.leaf ⟨(26, 34498452390408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_result⟩))
 (.branch 17
 (.leaf ⟨(26, 34531556067328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record016_result⟩)
 (.branch 18
 (.leaf ⟨(26, 34531671410696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record017_result⟩)
 (.leaf ⟨(26, 34531688055304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record018_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17592 + i))) 0 19 :=
  interval_of_check _ 0 19 (by decide +kernel)

public theorem complete : Block 17592 17611 :=
  block_of_table results 17592 19 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0398
