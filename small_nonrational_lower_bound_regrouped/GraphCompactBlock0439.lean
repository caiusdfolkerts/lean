module
prelude
import GraphInputsRow29Part00005Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0439
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 1919850578176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record000_result⟩)
 (.leaf ⟨(29, 1920387448832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 1920395771904), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record002_result⟩)
 (.leaf ⟨(29, 1942606610688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 1942606675968), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record004_result⟩)
 (.leaf ⟨(29, 1972073660417), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 1980663627776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 1980787360000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record007_result⟩)
 (.leaf ⟨(29, 1996492964096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 1996501352448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009_result⟩)
 (.leaf ⟨(29, 1996893487360), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 1998573338880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record011_result⟩)
 (.leaf ⟨(29, 1998581727232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(29, 1999613526272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record013_result⟩)
 (.leaf ⟨(29, 1999621914624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014_result⟩))
 (.branch 16
 (.leaf ⟨(29, 2002874597376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record015_result⟩)
 (.branch 17
 (.leaf ⟨(29, 2002940657664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record016_result⟩)
 (.leaf ⟨(29, 2003134611712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20566 + i))) 0 18 :=
  interval_of_check _ 0 18 (by decide +kernel)

public theorem complete : Block 20566 20584 :=
  block_of_table results 20566 18 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0439
