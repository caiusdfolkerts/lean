module
prelude
import GraphInputsRow29Part00026Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0460
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 6443256578048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record000_result⟩)
 (.leaf ⟨(29, 6451854573568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 6516279083008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record002_result⟩)
 (.leaf ⟨(29, 6524600582144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 6602618929184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record004_result⟩)
 (.leaf ⟨(29, 6602751049760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 6603015290912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 6635063902464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record007_result⟩)
 (.leaf ⟨(29, 6635063967744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 6637012221952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009_result⟩)
 (.leaf ⟨(29, 6637140115712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 6637144342528), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011_result⟩)
 (.branch 13
 (.leaf ⟨(29, 6637210337536), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record012_result⟩)
 (.leaf ⟨(29, 6638287196416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(29, 6641305026816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record014_result⟩)
 (.leaf ⟨(29, 6670378434592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record015_result⟩))
 (.branch 17
 (.leaf ⟨(29, 6674941788192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record016_result⟩)
 (.branch 18
 (.leaf ⟨(29, 6707409321985), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record017_result⟩)
 (.leaf ⟨(29, 6711570071553), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record018_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20894 + i))) 0 19 :=
  interval_of_check _ 0 19 (by decide +kernel)

public theorem complete : Block 20894 20913 :=
  block_of_table results 20894 19 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0460
