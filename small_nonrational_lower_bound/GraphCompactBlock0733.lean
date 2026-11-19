module
prelude
import GraphInputsRow30Part00005Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0733
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 3921602941184), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 3922123032592), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record001_result⟩)
 (.leaf ⟨(30, 3922655871232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(30, 3922655936512), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record003_result⟩)
 (.branch 5
 (.leaf ⟨(30, 3923196772353), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record004_result⟩)
 (.leaf ⟨(30, 3926160052480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(30, 3926283782160), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 3927357521921), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record007_result⟩)
 (.leaf ⟨(30, 3935679086592), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(30, 3935939100928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record009_result⟩)
 (.leaf ⟨(30, 3935947489280), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record010_result⟩))
 (.branch 12
 (.leaf ⟨(30, 3936071221504), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record011_result⟩)
 (.leaf ⟨(30, 3990188200192), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(30, 4004664868864), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record013_result⟩)
 (.branch 15
 (.leaf ⟨(30, 4076733530112), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record014_result⟩)
 (.leaf ⟨(30, 4076741853184), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(30, 4080357409024), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record016_result⟩)
 (.branch 18
 (.leaf ⟨(30, 4081026400256), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record017_result⟩)
 (.leaf ⟨(30, 4136737181696), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(30, 4141826998528), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record019_result⟩)
 (.branch 21
 (.leaf ⟨(30, 4141831225344), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record020_result⟩)
 (.leaf ⟨(30, 4141835386880), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(30, 4142095433856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record022_result⟩)
 (.leaf ⟨(30, 4145315086464), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record023_result⟩))
 (.branch 25
 (.leaf ⟨(30, 4145449287808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record024_result⟩)
 (.leaf ⟨(30, 4286513709312), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record025_result⟩))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf ⟨(30, 4329478324480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record026_result⟩)
 (.branch 28
 (.leaf ⟨(30, 4329482551296), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record027_result⟩)
 (.leaf ⟨(30, 4329490614272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record028_result⟩)))
 (.branch 30
 (.leaf ⟨(30, 4329729952000), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record029_result⟩)
 (.branch 31
 (.leaf ⟨(30, 4333890570496), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record030_result⟩)
 (.leaf ⟨(30, 4333894697216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record031_result⟩))))
 (.branch 35
 (.branch 33
 (.leaf ⟨(30, 4333898958848), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record032_result⟩)
 (.branch 34
 (.leaf ⟨(30, 4333907215104), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record033_result⟩)
 (.leaf ⟨(30, 4334179909632), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record034_result⟩)))
 (.branch 37
 (.branch 36
 (.leaf ⟨(30, 4334188232704), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record035_result⟩)
 (.leaf ⟨(30, 4334427308552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record036_result⟩))
 (.branch 38
 (.leaf ⟨(30, 4342488825856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record037_result⟩)
 (.leaf ⟨(30, 4343025631232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record038_result⟩)))))
 (.branch 45
 (.branch 42
 (.branch 40
 (.leaf ⟨(30, 4346525810944), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record039_result⟩)
 (.branch 41
 (.leaf ⟨(30, 4346909884416), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record040_result⟩)
 (.leaf ⟨(30, 4347062681600), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record041_result⟩)))
 (.branch 43
 (.leaf ⟨(30, 4347066843136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record042_result⟩)
 (.branch 44
 (.leaf ⟨(30, 4347178287104), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record043_result⟩)
 (.leaf ⟨(30, 4355235315712), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record044_result⟩))))
 (.branch 48
 (.branch 46
 (.leaf ⟨(30, 4355904241664), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record045_result⟩)
 (.branch 47
 (.leaf ⟨(30, 4359391805956), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record046_result⟩)
 (.leaf ⟨(30, 4359928807424), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record047_result⟩)))
 (.branch 50
 (.branch 49
 (.leaf ⟨(30, 4438121087232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record048_result⟩)
 (.leaf ⟨(30, 4438385328384), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record049_result⟩))
 (.branch 51
 (.leaf ⟨(30, 4438458728480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record050_result⟩)
 (.leaf ⟨(30, 4451073097760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record051_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23780 + i))) 0 52 :=
  interval_of_check _ 0 52 (by decide +kernel)

public theorem complete : Block 23780 23832 :=
  block_of_table results 23780 52 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0733
