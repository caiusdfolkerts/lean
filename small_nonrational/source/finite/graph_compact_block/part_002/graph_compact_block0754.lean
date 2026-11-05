module
prelude
import GraphInputsRow30Part00026Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0754
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 13199819767840), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record000_result⟩)
 (.leaf ⟨(30, 13200888766720), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 13204114718752), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record002_result⟩)
 (.branch 4
 (.leaf ⟨(30, 13204376879136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record003_result⟩)
 (.leaf ⟨(30, 13204378959904), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(30, 13233084244224), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record005_result⟩)
 (.leaf ⟨(30, 13237377114368), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record006_result⟩))
 (.branch 8
 (.leaf ⟨(30, 13237645517056), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record007_result⟩)
 (.branch 9
 (.leaf ⟨(30, 13237645574176), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record008_result⟩)
 (.leaf ⟨(30, 13237647654944), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(30, 13238777511936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record010_result⟩)
 (.leaf ⟨(30, 13271743143968), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record011_result⟩))
 (.branch 13
 (.leaf ⟨(30, 13272007385120), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 13273136201728), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record013_result⟩)
 (.leaf ⟨(30, 13281726070912), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(30, 13314961735808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record015_result⟩)
 (.branch 17
 (.leaf ⟨(30, 13338600833280), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record016_result⟩)
 (.leaf ⟨(30, 13338600898560), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(30, 13340731007008), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record018_result⟩)
 (.branch 20
 (.leaf ⟨(30, 13341787578400), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record019_result⟩)
 (.leaf ⟨(30, 13342895849472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00026.record020_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24373 + i))) 0 21 :=
  interval_of_check _ 0 21 (by decide +kernel)

public theorem complete : Block 24373 24394 :=
  block_of_table results 24373 21 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0754
