module
prelude
import GraphInputsRow16Part00023Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0023
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 24783246885120), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record000_result⟩)
 (.leaf ⟨(16, 24817971503360), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 24822261252352), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record002_result⟩)
 (.branch 4
 (.leaf ⟨(16, 24822272761856), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record003_result⟩)
 (.leaf ⟨(16, 24834743501056), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(16, 24838106783744), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record005_result⟩)
 (.branch 7
 (.leaf ⟨(16, 24845718978816), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record006_result⟩)
 (.leaf ⟨(16, 24845727367168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(16, 24846119502080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record008_result⟩)
 (.branch 10
 (.leaf ⟨(16, 24849339154688), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record009_result⟩)
 (.leaf ⟨(16, 24849351184384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(16, 24849879728384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record011_result⟩)
 (.leaf ⟨(16, 24850416599040), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record012_result⟩))
 (.branch 14
 (.leaf ⟨(16, 24850424922112), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record013_result⟩)
 (.branch 15
 (.leaf ⟨(16, 24851960103168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record014_result⟩)
 (.leaf ⟨(16, 24851968491520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(16, 24852100612096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record016_result⟩)
 (.branch 18
 (.leaf ⟨(16, 24852166672384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record017_result⟩)
 (.leaf ⟨(16, 24852360626432), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(16, 24853231501568), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record019_result⟩)
 (.branch 21
 (.leaf ⟨(16, 24853499904256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record020_result⟩)
 (.leaf ⟨(16, 24853511933952), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(16, 24854577348608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record022_result⟩)
 (.leaf ⟨(16, 24855580279040), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record023_result⟩))
 (.branch 25
 (.leaf ⟨(16, 24857161040128), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record024_result⟩)
 (.branch 26
 (.leaf ⟨(16, 24857433669632), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record025_result⟩)
 (.leaf ⟨(16, 24857697910784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(16, 24857706233856), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027_result⟩)
 (.branch 29
 (.leaf ⟨(16, 24857929121792), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record028_result⟩)
 (.leaf ⟨(16, 24860686352384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(16, 24869003624704), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030_result⟩)
 (.branch 32
 (.leaf ⟨(16, 24869139972096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031_result⟩)
 (.leaf ⟨(16, 24869148295168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record032_result⟩)))))
 (.branch 38
 (.branch 35
 (.branch 34
 (.leaf ⟨(16, 24870043812096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record033_result⟩)
 (.leaf ⟨(16, 24870180159488), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_result⟩))
 (.branch 36
 (.leaf ⟨(16, 24870188482560), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_result⟩)
 (.branch 37
 (.leaf ⟨(16, 24870411370496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record036_result⟩)
 (.leaf ⟨(16, 24870948175872), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record037_result⟩))))
 (.branch 41
 (.branch 39
 (.leaf ⟨(16, 24894908694784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record038_result⟩)
 (.branch 40
 (.leaf ⟨(16, 24916384612608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record039_result⟩)
 (.leaf ⟨(16, 24917924413696), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record040_result⟩)))
 (.branch 42
 (.leaf ⟨(16, 24933564481536), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record041_result⟩)
 (.branch 43
 (.leaf ⟨(16, 24933572804608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record042_result⟩)
 (.leaf ⟨(16, 24934604668928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record043_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1419 + i))) 0 44 :=
  interval_of_check _ 0 44 (by decide +kernel)

public theorem complete : Block 1419 1463 :=
  block_of_table results 1419 44 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0023
