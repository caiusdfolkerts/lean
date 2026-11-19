module
prelude
import GraphInputsRow30Part00047Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0775
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 29550650359808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00047.record000_result⟩)
 (.leaf ⟨(30, 29552596369536), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00047.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 29552998875648), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00047.record002_result⟩)
 (.leaf ⟨(30, 29583751790720), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00047.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(30, 29583886024704), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00047.record004_result⟩)
 (.leaf ⟨(30, 29583890186240), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00047.record005_result⟩))
 (.branch 7
 (.leaf ⟨(30, 29584137652224), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00047.record006_result⟩)
 (.leaf ⟨(30, 29588029835392), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00047.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(30, 29588298270720), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00047.record008_result⟩)
 (.leaf ⟨(30, 29588314915328), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00047.record009_result⟩))
 (.branch 11
 (.leaf ⟨(30, 29596619637252), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00047.record010_result⟩)
 (.leaf ⟨(30, 29690213466112), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00047.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(30, 29692359901184), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00047.record012_result⟩)
 (.leaf ⟨(30, 29692756262912), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00047.record013_result⟩))
 (.branch 15
 (.leaf ⟨(30, 29693928018048), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00047.record014_result⟩)
 (.leaf ⟨(30, 29725628596224), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00047.record015_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25088 + i))) 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)

public theorem complete : Block 25088 25104 :=
  block_of_table results 25088 16 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0775
