module
prelude
import GraphInputsRow30Part00007Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0735
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 5140685783040), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 5140950024192), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record001_result⟩)
 (.leaf ⟨(30, 5279332696065), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(30, 5317987409920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record003_result⟩)
 (.branch 5
 (.leaf ⟨(30, 5363946520832), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record004_result⟩)
 (.leaf ⟨(30, 5397029388544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(30, 5397186412544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 5397297791232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record007_result⟩)
 (.leaf ⟨(30, 5397310081024), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(30, 5535820710144), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record009_result⟩)
 (.leaf ⟨(30, 5537901084928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record010_result⟩))
 (.branch 12
 (.leaf ⟨(30, 5571135242272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record011_result⟩)
 (.leaf ⟨(30, 5829088509953), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(30, 5829549948928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record013_result⟩)
 (.branch 15
 (.leaf ⟨(30, 5863448256512), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record014_result⟩)
 (.leaf ⟨(30, 5877817999616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(30, 5877826387968), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record016_result⟩)
 (.branch 18
 (.leaf ⟨(30, 5878334128384), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record017_result⟩)
 (.leaf ⟨(30, 5899137745152), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(30, 5899406213120), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record019_result⟩)
 (.branch 21
 (.leaf ⟨(30, 5899414536192), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record020_result⟩)
 (.leaf ⟨(30, 5899942887936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(30, 5899951276032), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record022_result⟩)
 (.leaf ⟨(30, 6051116122368), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record023_result⟩))
 (.branch 25
 (.leaf ⟨(30, 6051116187648), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record024_result⟩)
 (.leaf ⟨(30, 6051218854144), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00007.record025_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23854 + i))) 0 26 :=
  interval_of_check _ 0 26 (by decide +kernel)

public theorem complete : Block 23854 23880 :=
  block_of_table results 23854 26 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0735
