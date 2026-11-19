module
prelude
import GraphInputsRow26Part00011Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0327
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 7147988009344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 7149128847744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001_result⟩)
 (.leaf ⟨(26, 7149260968320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(26, 7149263065408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record003_result⟩)
 (.leaf ⟨(26, 7149531468096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record004_result⟩))
 (.branch 6
 (.leaf ⟨(26, 7155970756992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005_result⟩)
 (.leaf ⟨(26, 7155970773312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(26, 7186046615568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record007_result⟩)
 (.leaf ⟨(26, 7186826724100), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record008_result⟩))
 (.branch 10
 (.leaf ⟨(26, 7190339485712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record009_result⟩)
 (.leaf ⟨(26, 7191532765184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(26, 7207773016128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record011_result⟩)
 (.leaf ⟨(26, 7224698175504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record012_result⟩))
 (.branch 14
 (.leaf ⟨(26, 7289122684944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record013_result⟩)
 (.leaf ⟨(26, 7302571720704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record014_result⟩)))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨(26, 7375276744704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 7424014647312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record016_result⟩)
 (.leaf ⟨(26, 7448724275200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record017_result⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨(26, 7518138925568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record018_result⟩)
 (.leaf ⟨(26, 7525076664320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record019_result⟩))
 (.branch 21
 (.leaf ⟨(26, 7525348935808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record020_result⟩)
 (.leaf ⟨(26, 7533922092040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record021_result⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 7533938868225), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record022_result⟩)
 (.leaf ⟨(26, 7551374590464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 7559194132736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_result⟩)
 (.leaf ⟨(26, 7559196016648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record025_result⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨(26, 7559198097416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record026_result⟩)
 (.leaf ⟨(26, 7560285554944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record027_result⟩))
 (.branch 29
 (.leaf ⟨(26, 7560285618184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record028_result⟩)
 (.leaf ⟨(26, 7560302199552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (14619 + i))) 0 30 :=
  interval_of_check _ 0 30 (by decide +kernel)

public theorem complete : Block 14619 14649 :=
  block_of_table results 14619 30 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0327
