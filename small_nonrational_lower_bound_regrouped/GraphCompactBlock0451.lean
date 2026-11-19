module
prelude
import GraphInputsRow29Part00017Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0451
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 3923196772353), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record000_result⟩)
 (.leaf ⟨(29, 3926160052480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 3926283782160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002_result⟩)
 (.leaf ⟨(29, 3927357521921), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 3927357587456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record004_result⟩)
 (.leaf ⟨(29, 3935670698240), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 3935679086592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record006_result⟩)
 (.leaf ⟨(29, 3935939100928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(29, 3935947489280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record008_result⟩)
 (.leaf ⟨(29, 3936071221504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record009_result⟩))
 (.branch 11
 (.leaf ⟨(29, 3939290874112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record010_result⟩)
 (.leaf ⟨(29, 3939302903808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(29, 3990188200192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record012_result⟩)
 (.leaf ⟨(29, 4004664868864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record013_result⟩))
 (.branch 15
 (.leaf ⟨(29, 4076729271040), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record014_result⟩)
 (.leaf ⟨(29, 4076733530112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(29, 4076741853184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record016_result⟩)
 (.leaf ⟨(29, 4080357409024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record017_result⟩))
 (.branch 19
 (.leaf ⟨(29, 4081026400256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record018_result⟩)
 (.leaf ⟨(29, 4127755079936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(29, 4136456749312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record020_result⟩)
 (.leaf ⟨(29, 4136725152000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record021_result⟩))
 (.branch 23
 (.leaf ⟨(29, 4136737181696), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record022_result⟩)
 (.leaf ⟨(29, 4141826998528), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(29, 4141831225344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record024_result⟩)
 (.leaf ⟨(29, 4141835386880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record025_result⟩))
 (.branch 27
 (.leaf ⟨(29, 4142095433856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record026_result⟩)
 (.leaf ⟨(29, 4145315086464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(29, 4145449287808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record028_result⟩)
 (.leaf ⟨(29, 4214168224384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record029_result⟩))
 (.branch 31
 (.leaf ⟨(29, 4286513709312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record030_result⟩)
 (.branch 32
 (.leaf ⟨(29, 4329478324480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record031_result⟩)
 (.leaf ⟨(29, 4329482551296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20732 + i))) 0 33 :=
  interval_of_check _ 0 33 (by decide +kernel)

public theorem complete : Block 20732 20765 :=
  block_of_table results 20732 33 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0451
