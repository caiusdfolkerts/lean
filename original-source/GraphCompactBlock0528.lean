module
prelude
import GraphInputsRow29Part00094Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0528
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 16536295444736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_result⟩)
 (.leaf ⟨(29, 16536836309248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 16537108938752), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record002_result⟩)
 (.leaf ⟨(29, 16537368920832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 16537373179904), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record004_result⟩)
 (.leaf ⟨(29, 16537381502976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 16537505300480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 16539956871424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record007_result⟩)
 (.leaf ⟨(29, 16540724953088), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 16544616943872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record009_result⟩)
 (.leaf ⟨(29, 16544768213120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 16544773967872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record011_result⟩)
 (.leaf ⟨(29, 16544885379200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(29, 16545958855296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record013_result⟩)
 (.leaf ⟨(29, 16549314298384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record014_result⟩))
 (.branch 16
 (.leaf ⟨(29, 16608915423232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record015_result⟩)
 (.branch 17
 (.leaf ⟨(29, 16609452228608), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record016_result⟩)
 (.leaf ⟨(29, 16632420827136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record017_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21816 + i))) 0 18 :=
  interval_of_check _ 0 18 (by decide +kernel)

public theorem complete : Block 21816 21834 :=
  block_of_table results 21816 18 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0528
