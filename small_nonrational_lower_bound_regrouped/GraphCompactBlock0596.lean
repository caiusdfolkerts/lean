module
prelude
import GraphInputsRow29Part00162Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0596
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 25333472428032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162.record000_result⟩)
 (.leaf ⟨(29, 25336047796480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 25336683757568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162.record002_result⟩)
 (.leaf ⟨(29, 25341517136128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 25341785604096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162.record004_result⟩)
 (.leaf ⟨(29, 25341793927168), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 25342188208128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162.record006_result⟩)
 (.leaf ⟨(29, 25345407860736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(29, 25348932649216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162.record008_result⟩)
 (.leaf ⟨(29, 25363463864320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162.record009_result⟩))
 (.branch 11
 (.leaf ⟨(29, 25363472187392), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162.record010_result⟩)
 (.leaf ⟨(29, 25363967181056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(29, 25364735262720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162.record012_result⟩)
 (.leaf ⟨(29, 25367219863808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162.record013_result⟩))
 (.branch 15
 (.leaf ⟨(29, 25367360372736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162.record014_result⟩)
 (.branch 16
 (.leaf ⟨(29, 25367756734464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162.record015_result⟩)
 (.leaf ⟨(29, 25367765057536), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162.record016_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22701 + i))) 0 17 :=
  interval_of_check _ 0 17 (by decide +kernel)

public theorem complete : Block 22701 22718 :=
  block_of_table results 22701 17 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0596
