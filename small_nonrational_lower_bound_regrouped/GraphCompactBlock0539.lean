module
prelude
import GraphInputsRow29Part00105Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0539
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 18151917043968), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 18181884248320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record001_result⟩)
 (.leaf ⟨(29, 18181884313600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 18182012207360), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record003_result⟩)
 (.leaf ⟨(29, 18182016434176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 18186177118464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record005_result⟩)
 (.leaf ⟨(29, 18220939510016), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(29, 18229529444480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record007_result⟩)
 (.leaf ⟨(29, 18229598625920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record008_result⟩))
 (.branch 10
 (.leaf ⟨(29, 18248649212160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record009_result⟩)
 (.leaf ⟨(29, 18248657600512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(29, 18249049735424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record011_result⟩)
 (.leaf ⟨(29, 18252809961728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record012_result⟩))
 (.branch 14
 (.leaf ⟨(29, 18253346832384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record013_result⟩)
 (.leaf ⟨(29, 18253355155456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record014_result⟩)))))
 (.branch 23
 (.branch 19
 (.branch 17
 (.branch 16
 (.leaf ⟨(29, 18255030845440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record015_result⟩)
 (.leaf ⟨(29, 18255290859776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record016_result⟩))
 (.branch 18
 (.leaf ⟨(29, 18257507581952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record017_result⟩)
 (.leaf ⟨(29, 18262765109376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record018_result⟩)))
 (.branch 21
 (.branch 20
 (.leaf ⟨(29, 18265023742208), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record019_result⟩)
 (.leaf ⟨(29, 18265032130560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record020_result⟩))
 (.branch 22
 (.leaf ⟨(29, 18271933858048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record021_result⟩)
 (.leaf ⟨(29, 18272070205440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record022_result⟩))))
 (.branch 27
 (.branch 25
 (.branch 24
 (.leaf ⟨(29, 18272078528512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record023_result⟩)
 (.leaf ⟨(29, 18288533381184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record024_result⟩))
 (.branch 26
 (.leaf ⟨(29, 18289390584064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record025_result⟩)
 (.leaf ⟨(29, 18289589952576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record026_result⟩)))
 (.branch 29
 (.branch 28
 (.leaf ⟨(29, 18289658986752), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record027_result⟩)
 (.leaf ⟨(29, 18289659052032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record028_result⟩))
 (.branch 30
 (.leaf ⟨(29, 18289661067520), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record029_result⟩)
 (.leaf ⟨(29, 18297838928128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105.record030_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22013 + i))) 0 31 :=
  interval_of_check _ 0 31 (by decide +kernel)

public theorem complete : Block 22013 22044 :=
  block_of_table results 22013 31 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0539
