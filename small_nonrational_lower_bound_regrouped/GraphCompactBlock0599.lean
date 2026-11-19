module
prelude
import GraphInputsRow29Part00165Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0599
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 25376546897920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00165.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 25376849953024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00165.record001_result⟩)
 (.leaf ⟨(29, 25377217511424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00165.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 25377620115456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00165.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 25383291339008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00165.record004_result⟩)
 (.leaf ⟨(29, 25404731752704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00165.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 25414126797312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00165.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 25417616605440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00165.record007_result⟩)
 (.leaf ⟨(29, 25432684560640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00165.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 25433320521728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00165.record009_result⟩)
 (.leaf ⟨(29, 25444529225984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00165.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 25444663492608), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00165.record011_result⟩)
 (.leaf ⟨(29, 25444671815680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00165.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22725 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 22725 22738 :=
  block_of_table results 22725 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0599
