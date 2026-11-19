module
prelude
import GraphInputsRow30Part00010Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0738
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 6637144342528), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record000_result⟩)
 (.leaf ⟨(30, 6637210337536), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 6644726501632), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record002_result⟩)
 (.leaf ⟨(30, 6674941788192), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(30, 6707409321985), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record004_result⟩)
 (.leaf ⟨(30, 6711570071553), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record005_result⟩))
 (.branch 7
 (.leaf ⟨(30, 6727198113792), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 6727206436864), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record007_result⟩)
 (.leaf ⟨(30, 6752966836480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(30, 6791622623232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record009_result⟩)
 (.leaf ⟨(30, 6791630946304), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record010_result⟩))
 (.branch 12
 (.leaf ⟨(30, 6807055532288), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record011_result⟩)
 (.leaf ⟨(30, 6823834877952), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(30, 6839899062272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record013_result⟩)
 (.leaf ⟨(30, 6840406802688), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record014_result⟩))
 (.branch 16
 (.leaf ⟨(30, 6840419092480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record015_result⟩)
 (.branch 17
 (.leaf ⟨(30, 6844835693312), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record016_result⟩)
 (.leaf ⟨(30, 6851076817664), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record017_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23918 + i))) 0 18 :=
  interval_of_check _ 0 18 (by decide +kernel)

public theorem complete : Block 23918 23936 :=
  block_of_table results 23918 18 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0738
