module
prelude
import GraphInputsRow26Part00007Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0323
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 4347050066952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record000_result⟩)
 (.leaf ⟨(26, 4359530283008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 4359668760576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record002_result⟩)
 (.leaf ⟨(26, 4359802847232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 4522405593088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record004_result⟩)
 (.leaf ⟨(26, 4722427789312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 4728157143296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 4728161370112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record007_result⟩)
 (.leaf ⟨(26, 4728169693184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(26, 4803994322176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record009_result⟩)
 (.leaf ⟨(26, 5120769229056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record010_result⟩))
 (.branch 12
 (.leaf ⟨(26, 5138477515008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record011_result⟩)
 (.branch 13
 (.leaf ⟨(26, 5138481741824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record012_result⟩)
 (.leaf ⟨(26, 5140140720384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(26, 5140144947200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record014_result⟩)
 (.leaf ⟨(26, 5140148913408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record015_result⟩))
 (.branch 17
 (.leaf ⟨(26, 5140685783041), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record016_result⟩)
 (.branch 18
 (.leaf ⟨(26, 5140685848576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record017_result⟩)
 (.leaf ⟨(26, 5140941636352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record018_result⟩))))))
 (.branch 28
 (.branch 23
 (.branch 21
 (.branch 20
 (.leaf ⟨(26, 5140950024704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record019_result⟩)
 (.leaf ⟨(26, 5258203988224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record020_result⟩))
 (.branch 22
 (.leaf ⟨(26, 5260944965632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record021_result⟩)
 (.leaf ⟨(26, 5268358397952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(26, 5278124769280), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record023_result⟩)
 (.leaf ⟨(26, 5283956917504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record024_result⟩))
 (.branch 26
 (.leaf ⟨(26, 5394571510016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record025_result⟩)
 (.branch 27
 (.leaf ⟨(26, 5394573393928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record026_result⟩)
 (.leaf ⟨(26, 5396769243144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record027_result⟩)))))
 (.branch 33
 (.branch 30
 (.branch 29
 (.leaf ⟨(26, 5397190639616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record028_result⟩)
 (.leaf ⟨(26, 5411734470664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record029_result⟩))
 (.branch 31
 (.leaf ⟨(26, 5423071559680), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 5780063420672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record031_result⟩)
 (.leaf ⟨(26, 5828357161216), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record032_result⟩))))
 (.branch 35
 (.branch 34
 (.leaf ⟨(26, 5829413732608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record033_result⟩)
 (.leaf ⟨(26, 5829413797888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record034_result⟩))
 (.branch 36
 (.leaf ⟨(26, 5830095142912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record035_result⟩)
 (.branch 37
 (.leaf ⟨(26, 5875601604864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record036_result⟩)
 (.leaf ⟨(26, 5877805580296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record037_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (14474 + i))) 0 38 :=
  interval_of_check _ 0 38 (by decide +kernel)

public theorem complete : Block 14474 14512 :=
  block_of_table results 14474 38 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0323
