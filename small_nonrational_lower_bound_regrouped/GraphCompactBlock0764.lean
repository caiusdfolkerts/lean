module
prelude
import GraphInputsRow30Part00036Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0764
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 21378610757632), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 21379007119360), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record001_result⟩)
 (.leaf ⟨(30, 21382631063552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(30, 21383167868928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record003_result⟩)
 (.branch 5
 (.leaf ⟨(30, 21384711438336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record004_result⟩)
 (.leaf ⟨(30, 21397596291072), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(30, 21401891241984), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 21446426394624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record007_result⟩)
 (.leaf ⟨(30, 21462623195264), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(30, 21514053779456), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record009_result⟩)
 (.branch 11
 (.leaf ⟨(30, 21515382816768), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record010_result⟩)
 (.leaf ⟨(30, 21519543566336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(30, 21519667363840), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 21522887016448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record013_result⟩)
 (.leaf ⟨(30, 21527047442560), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(30, 21528120918656), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record015_result⟩)
 (.branch 17
 (.leaf ⟨(30, 21535771869184), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record016_result⟩)
 (.leaf ⟨(30, 21588260945920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(30, 21591472275456), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record018_result⟩)
 (.branch 20
 (.leaf ⟨(30, 21596582445056), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record019_result⟩)
 (.leaf ⟨(30, 21596976726016), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(30, 21600196378624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record021_result⟩)
 (.branch 23
 (.leaf ⟨(30, 21603721167104), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record022_result⟩)
 (.leaf ⟨(30, 21668915315200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(30, 21672405123328), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record024_result⟩)
 (.branch 26
 (.leaf ⟨(30, 21728642793472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record025_result⟩)
 (.leaf ⟨(30, 21878563553344), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(30, 21921531986176), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record027_result⟩)
 (.branch 29
 (.leaf ⟨(30, 21925829083136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record028_result⟩)
 (.leaf ⟨(30, 21926101647360), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(30, 21926613614592), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record030_result⟩)
 (.branch 32
 (.leaf ⟨(30, 21930121953280), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record031_result⟩)
 (.leaf ⟨(30, 21930658758656), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(30, 21930774364160), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record033_result⟩)
 (.branch 35
 (.leaf ⟨(30, 21934398177280), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record034_result⟩)
 (.leaf ⟨(30, 21947283030016), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(30, 21951577980928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record036_result⟩)
 (.branch 38
 (.leaf ⟨(30, 21994033741888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record037_result⟩)
 (.leaf ⟨(30, 22000476168256), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(30, 22100572176384), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record039_result⟩)
 (.branch 41
 (.leaf ⟨(30, 22319212806144), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record040_result⟩)
 (.leaf ⟨(30, 22618988150784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(30, 22627779354624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record042_result⟩)
 (.branch 44
 (.leaf ⟨(30, 22635283489024), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record043_result⟩)
 (.leaf ⟨(30, 22696297512960), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(30, 22731921883136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record045_result⟩)
 (.leaf ⟨(30, 22870302392320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record046_result⟩))
 (.branch 48
 (.leaf ⟨(30, 22997545058304), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record047_result⟩)
 (.leaf ⟨(30, 23006130798592), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00036.record048_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24721 + i))) 0 49 :=
  interval_of_check _ 0 49 (by decide +kernel)

public theorem complete : Block 24721 24770 :=
  block_of_table results 24721 49 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0764
