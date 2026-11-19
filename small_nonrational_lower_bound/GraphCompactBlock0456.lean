module
prelude
import GraphInputsRow29Part00022Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0456
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 5241617522816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 5244972961824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record001_result⟩)
 (.leaf ⟨(29, 5267309756672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 5275631255808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 5279332696065), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record004_result⟩)
 (.leaf ⟨(29, 5317975900416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 5317987409920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 5363946520832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record007_result⟩)
 (.leaf ⟨(29, 5397029388544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 5397182185728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record009_result⟩)
 (.leaf ⟨(29, 5397186412544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 5397297791232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record011_result⟩)
 (.leaf ⟨(29, 5397310081024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(29, 5535820710144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record013_result⟩)
 (.branch 15
 (.leaf ⟨(29, 5537901084928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record014_result⟩)
 (.leaf ⟨(29, 5550383333632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(29, 5571135242272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record016_result⟩)
 (.branch 18
 (.leaf ⟨(29, 5812370080000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record017_result⟩)
 (.leaf ⟨(29, 5829088509953), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(29, 5829088526336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record019_result⟩)
 (.branch 21
 (.leaf ⟨(29, 5829549948928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record020_result⟩)
 (.leaf ⟨(29, 5863448256512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(29, 5867731697920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record022_result⟩)
 (.leaf ⟨(29, 5877817999616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record023_result⟩))
 (.branch 25
 (.leaf ⟨(29, 5877826387968), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record024_result⟩)
 (.leaf ⟨(29, 5878334128384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00022.record025_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20824 + i))) 0 26 :=
  interval_of_check _ 0 26 (by decide +kernel)

public theorem complete : Block 20824 20850 :=
  block_of_table results 20824 26 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0456
