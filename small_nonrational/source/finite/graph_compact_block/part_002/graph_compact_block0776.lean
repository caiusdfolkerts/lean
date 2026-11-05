module
prelude
import GraphInputsRow30Part00048Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0776
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 29726140010624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00048.record000_result⟩)
 (.leaf ⟨(30, 29727213486720), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00048.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 29757832462592), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00048.record002_result⟩)
 (.leaf ⟨(30, 29757840850944), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00048.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(30, 29760432640128), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00048.record004_result⟩)
 (.leaf ⟨(30, 29765534810112), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00048.record005_result⟩))
 (.branch 7
 (.leaf ⟨(30, 29772914888832), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00048.record006_result⟩)
 (.leaf ⟨(30, 29902705328128), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00048.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(30, 30031686696960), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00048.record008_result⟩)
 (.leaf ⟨(30, 30237799284736), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00048.record009_result⟩))
 (.branch 11
 (.leaf ⟨(30, 30237803446272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00048.record010_result⟩)
 (.leaf ⟨(30, 30237807087616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00048.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(30, 30238197694592), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00048.record012_result⟩)
 (.leaf ⟨(30, 30238203449344), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00048.record013_result⟩))
 (.branch 15
 (.leaf ⟨(30, 30241150472448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00048.record014_result⟩)
 (.branch 16
 (.leaf ⟨(30, 30241158860800), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00048.record015_result⟩)
 (.leaf ⟨(30, 30241166987520), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00048.record016_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25104 + i))) 0 17 :=
  interval_of_check _ 0 17 (by decide +kernel)

public theorem complete : Block 25104 25121 :=
  block_of_table results 25104 17 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0776
