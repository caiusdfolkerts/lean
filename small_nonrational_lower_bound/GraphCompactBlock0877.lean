module
prelude
import GraphInputsRow31Part00089Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0877
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 17670914195712), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record000_result⟩)
 (.leaf ⟨(31, 17671987413248), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 17701984763904), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record002_result⟩)
 (.leaf ⟨(31, 17702525599745), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 17702525665280), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record004_result⟩)
 (.leaf ⟨(31, 17704149925888), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 17704414167040), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record006_result⟩)
 (.leaf ⟨(31, 17704421433408), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(31, 17706686349313), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record008_result⟩)
 (.leaf ⟨(31, 17706686414848), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record009_result⟩))
 (.branch 11
 (.leaf ⟨(31, 17715276316672), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record010_result⟩)
 (.leaf ⟨(31, 17715410518016), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(31, 17721841434880), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record012_result⟩)
 (.leaf ⟨(31, 17739902107712), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record013_result⟩))
 (.branch 15
 (.leaf ⟨(31, 17739903148096), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record014_result⟩)
 (.leaf ⟨(31, 17748223606848), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record015_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26226 + i))) 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)

public theorem complete : Block 26226 26242 :=
  block_of_table results 26226 16 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0877
