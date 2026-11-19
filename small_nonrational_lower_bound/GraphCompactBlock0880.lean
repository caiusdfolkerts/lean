module
prelude
import GraphInputsRow31Part00092Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0880
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 18254177239041), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00092.record000_result⟩)
 (.leaf ⟨(31, 18270860116224), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00092.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 18271608766464), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00092.record002_result⟩)
 (.leaf ⟨(31, 18289658953729), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00092.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 18297980452865), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00092.record004_result⟩)
 (.leaf ⟨(31, 18298251001856), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00092.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 18331486666752), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00092.record006_result⟩)
 (.leaf ⟨(31, 18336020693760), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00092.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(31, 18336033275904), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00092.record008_result⟩)
 (.leaf ⟨(31, 18340317822976), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00092.record009_result⟩))
 (.branch 11
 (.leaf ⟨(31, 18406359171072), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00092.record010_result⟩)
 (.leaf ⟨(31, 18406887653376), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00092.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(31, 18473459647104), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00092.record012_result⟩)
 (.leaf ⟨(31, 18477754614336), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00092.record013_result⟩))
 (.branch 15
 (.leaf ⟨(31, 18507820466176), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00092.record014_result⟩)
 (.leaf ⟨(31, 18531047440384), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00092.record015_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26260 + i))) 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)

public theorem complete : Block 26260 26276 :=
  block_of_table results 26260 16 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0880
