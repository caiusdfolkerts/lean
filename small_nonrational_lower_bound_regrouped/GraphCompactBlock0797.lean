module
prelude
import GraphInputsRow31Part00009Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0797
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 1774639382528), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record000_result⟩)
 (.leaf ⟨(31, 1778254938368), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 1843216318464), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record002_result⟩)
 (.leaf ⟨(31, 1873151199232), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 1873172037632), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record004_result⟩)
 (.leaf ⟨(31, 1877706015488), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 1877714468864), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 1894357467392), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record007_result⟩)
 (.leaf ⟨(31, 1903215837184), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(31, 1911537336320), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record009_result⟩)
 (.leaf ⟨(31, 1912074141696), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record010_result⟩))
 (.branch 12
 (.leaf ⟨(31, 1920395640832), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record011_result⟩)
 (.branch 13
 (.leaf ⟨(31, 1941887795328), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record012_result⟩)
 (.leaf ⟨(31, 1943082631169), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(31, 1943082663936), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record014_result⟩)
 (.leaf ⟨(31, 1943206396160), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record015_result⟩))
 (.branch 17
 (.leaf ⟨(31, 1943216865280), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record016_result⟩)
 (.branch 18
 (.leaf ⟨(31, 1971528466688), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record017_result⟩)
 (.leaf ⟨(31, 1972065337344), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00009.record018_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25534 + i))) 0 19 :=
  interval_of_check _ 0 19 (by decide +kernel)

public theorem complete : Block 25534 25553 :=
  block_of_table results 25534 19 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0797
