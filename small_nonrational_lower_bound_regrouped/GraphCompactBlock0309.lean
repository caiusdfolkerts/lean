module
prelude
import GraphInputsRow25Part00019Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0309
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(25, 29176002838528), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record000_result⟩)
 (.leaf ⟨(25, 29176007000064), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record001_result⟩))
 (.branch 3
 (.leaf ⟨(25, 29176010641408), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record002_result⟩)
 (.leaf ⟨(25, 29176518414464), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(25, 29177591890560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record004_result⟩)
 (.leaf ⟨(25, 29185108083216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record005_result⟩))
 (.branch 7
 (.leaf ⟨(25, 29276808155136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record006_result⟩)
 (.leaf ⟨(25, 29276940275712), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(25, 29277198762112), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record008_result⟩)
 (.leaf ⟨(25, 29277204516864), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record009_result⟩))
 (.branch 11
 (.leaf ⟨(25, 29281744847376), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record010_result⟩)
 (.leaf ⟨(25, 29283288617216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(25, 29283643822080), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record012_result⟩)
 (.leaf ⟨(25, 29291878551680), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record013_result⟩))
 (.branch 15
 (.leaf ⟨(25, 29414369280128), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record014_result⟩)
 (.leaf ⟨(25, 29414375034880), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(25, 29420814340096), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record016_result⟩)
 (.leaf ⟨(25, 29515304927232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record017_result⟩))
 (.branch 19
 (.leaf ⟨(25, 29523873761280), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record018_result⟩)
 (.leaf ⟨(25, 29550466580608), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(25, 29550534754304), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record020_result⟩)
 (.leaf ⟨(25, 29550538915840), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record021_result⟩))
 (.branch 23
 (.leaf ⟨(25, 29550650359808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_result⟩)
 (.leaf ⟨(25, 29552596369536), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(25, 29552998875648), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record024_result⟩)
 (.leaf ⟨(25, 29583751790720), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record025_result⟩))
 (.branch 27
 (.leaf ⟨(25, 29583886024704), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record026_result⟩)
 (.leaf ⟨(25, 29583890186240), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(25, 29584137652224), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record028_result⟩)
 (.leaf ⟨(25, 29588029835392), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record029_result⟩))
 (.branch 31
 (.leaf ⟨(25, 29588298270720), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record030_result⟩)
 (.leaf ⟨(25, 29588314915328), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (13642 + i))) 0 32 :=
  interval_of_check _ 0 32 (by decide +kernel)

public theorem complete : Block 13642 13674 :=
  block_of_table results 13642 32 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0309
