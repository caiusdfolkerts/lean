module
prelude
import GraphInputsRow30Part00022Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0750
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 11960548622592), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record000_result⟩)
 (.leaf ⟨(30, 11960817090560), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 11960825413632), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record002_result⟩)
 (.branch 4
 (.leaf ⟨(30, 11961085493248), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record003_result⟩)
 (.leaf ⟨(30, 11961217613824), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(30, 11963937652736), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record005_result⟩)
 (.branch 7
 (.leaf ⟨(30, 11963945975808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record006_result⟩)
 (.leaf ⟨(30, 11966921867520), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(30, 11967198658560), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record008_result⟩)
 (.branch 10
 (.leaf ⟨(30, 11967458738176), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record009_result⟩)
 (.leaf ⟨(30, 11984101736448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(30, 11984238018560), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record011_result⟩)
 (.branch 13
 (.leaf ⟨(30, 11995864662272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record012_result⟩)
 (.leaf ⟨(30, 11996133130240), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(30, 11996141453312), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record014_result⟩)
 (.branch 16
 (.leaf ⟨(30, 11996401532928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record015_result⟩)
 (.leaf ⟨(30, 11996649259008), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(30, 12000434323456), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record017_result⟩)
 (.branch 19
 (.leaf ⟨(30, 12000541605888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record018_result⟩)
 (.leaf ⟨(30, 12000694403072), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(30, 12000698564608), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record020_result⟩)
 (.branch 22
 (.leaf ⟨(30, 12000810008576), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record021_result⟩)
 (.leaf ⟨(30, 12004433756416), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00022.record022_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24232 + i))) 0 23 :=
  interval_of_check _ 0 23 (by decide +kernel)

public theorem complete : Block 24232 24255 :=
  block_of_table results 24232 23 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0750
