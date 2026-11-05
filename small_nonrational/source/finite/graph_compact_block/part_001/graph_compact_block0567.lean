module
prelude
import GraphInputsRow29Part00133Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0567
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 22326046376000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record000_result⟩)
 (.leaf ⟨(29, 22360406106176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 22558822899840), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record002_result⟩)
 (.leaf ⟨(29, 22618715521280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 22618979762432), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record004_result⟩)
 (.leaf ⟨(29, 22618988150784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 22619177943296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record006_result⟩)
 (.leaf ⟨(29, 22626450284672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(29, 22627767845120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record008_result⟩)
 (.leaf ⟨(29, 22627779354624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record009_result⟩))
 (.branch 11
 (.leaf ⟨(29, 22635283489024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record010_result⟩)
 (.leaf ⟨(29, 22687697142016), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(29, 22687705530368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record012_result⟩)
 (.leaf ⟨(29, 22687763202304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record013_result⟩))
 (.branch 15
 (.leaf ⟨(29, 22696027029504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record014_result⟩)
 (.leaf ⟨(29, 22696287043840), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(29, 22696291270656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record016_result⟩)
 (.leaf ⟨(29, 22696297512960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record017_result⟩))
 (.branch 19
 (.leaf ⟨(29, 22696353104128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record018_result⟩)
 (.leaf ⟨(29, 22696364613632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(29, 22699707998464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record020_result⟩)
 (.leaf ⟨(29, 22731252891904), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record021_result⟩))
 (.branch 23
 (.leaf ⟨(29, 22731921883136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record022_result⟩)
 (.leaf ⟨(29, 22767693005056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(29, 22833461788672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record024_result⟩)
 (.leaf ⟨(29, 22833468030976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record025_result⟩))
 (.branch 27
 (.leaf ⟨(29, 22833523622144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026_result⟩)
 (.leaf ⟨(29, 22833535131648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(29, 22853122588672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record028_result⟩)
 (.leaf ⟨(29, 22862786265088), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record029_result⟩))
 (.branch 31
 (.leaf ⟨(29, 22862916223744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record030_result⟩)
 (.leaf ⟨(29, 22870302392320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record031_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22388 + i))) 0 32 :=
  interval_of_check _ 0 32 (by decide +kernel)

public theorem complete : Block 22388 22420 :=
  block_of_table results 22388 32 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0567
