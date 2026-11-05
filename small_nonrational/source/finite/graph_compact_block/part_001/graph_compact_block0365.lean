module
prelude
import GraphInputsRow26Part00049Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0365
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 24666066518016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 24666198508032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record001_result⟩)
 (.leaf ⟨(26, 24672734298112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(26, 24676940185600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record003_result⟩)
 (.leaf ⟨(26, 24681633546816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record004_result⟩))
 (.branch 6
 (.leaf ⟨(26, 24739097907472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record005_result⟩)
 (.leaf ⟨(26, 24740154738960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(26, 24740245348480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record007_result⟩)
 (.branch 9
 (.leaf ⟨(26, 24741319086208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record008_result⟩)
 (.leaf ⟨(26, 24743415976064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(26, 24748986745088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record010_result⟩)
 (.leaf ⟨(26, 24748986810368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record011_result⟩))
 (.branch 13
 (.leaf ⟨(26, 24749087396096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record012_result⟩)
 (.leaf ⟨(26, 24779017060608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(26, 24779017125888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 24779146985728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record015_result⟩)
 (.leaf ⟨(26, 24782519681280), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(26, 24782519746560), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record017_result⟩)
 (.leaf ⟨(26, 24782521241856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record018_result⟩))
 (.branch 20
 (.leaf ⟨(26, 24810172743936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record019_result⟩)
 (.leaf ⟨(26, 24826388447488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record020_result⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨(26, 24827461665024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record021_result⟩)
 (.branch 23
 (.leaf ⟨(26, 24855583981568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record022_result⟩)
 (.leaf ⟨(26, 24885603082304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record023_result⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨(26, 24885603098624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record024_result⟩)
 (.leaf ⟨(26, 24885603602496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record025_result⟩))
 (.branch 27
 (.leaf ⟨(26, 24885654980624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record026_result⟩)
 (.leaf ⟨(26, 24894042540048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049.record027_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16564 + i))) 0 28 :=
  interval_of_check _ 0 28 (by decide +kernel)

public theorem complete : Block 16564 16592 :=
  block_of_table results 16564 28 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0365
