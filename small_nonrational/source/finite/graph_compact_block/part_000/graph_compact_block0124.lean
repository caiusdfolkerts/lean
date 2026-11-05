module
prelude
import GraphInputsRow24Part00008Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0124
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 4735372394752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 5104178659360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record001_result⟩)
 (.leaf ⟨(24, 5106282037504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 5106286264320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 5138477515008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record004_result⟩)
 (.leaf ⟨(24, 5138481741824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 5140144947200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 5140685848576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record007_result⟩)
 (.leaf ⟨(24, 5140950024704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 5140950089728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 5260944900352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record010_result⟩)
 (.leaf ⟨(24, 5260944965632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(24, 5268358397952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 5278124769280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record013_result⟩)
 (.leaf ⟨(24, 5397190574336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(24, 5397190639616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 5397310081280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record016_result⟩)
 (.leaf ⟨(24, 5423071559680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(24, 5423079882752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 5620648476672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record019_result⟩)
 (.leaf ⟨(24, 5780063420672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(24, 5828357161216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record021_result⟩)
 (.branch 23
 (.leaf ⟨(24, 5829088518208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record022_result⟩)
 (.leaf ⟨(24, 5829413797888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(24, 5829558337536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record024_result⟩)
 (.branch 26
 (.leaf ⟨(24, 5830095142912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record025_result⟩)
 (.leaf ⟨(24, 5893252022272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(24, 5895660519424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record027_result⟩)
 (.branch 29
 (.leaf ⟨(24, 5899141907712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record028_result⟩)
 (.leaf ⟨(24, 5899150164996), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(24, 5899414405636), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record030_result⟩)
 (.branch 32
 (.leaf ⟨(24, 5899414536193), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record031_result⟩)
 (.leaf ⟨(24, 5899687035904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(24, 5899942888192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record033_result⟩)
 (.branch 35
 (.leaf ⟨(24, 5902091436288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record034_result⟩)
 (.leaf ⟨(24, 5904116219904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(24, 5904240017408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record036_result⟩)
 (.branch 38
 (.leaf ⟨(24, 5904380461056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record037_result⟩)
 (.leaf ⟨(24, 5951360925696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(24, 5964245778432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record039_result⟩)
 (.branch 41
 (.leaf ⟨(24, 5966515945728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record040_result⟩)
 (.leaf ⟨(24, 5972833599488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(24, 5974368780544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record042_result⟩)
 (.branch 44
 (.leaf ⟨(24, 5974509289472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record043_result⟩)
 (.leaf ⟨(24, 5974905651200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record044_result⟩)))
 (.branch 46
 (.leaf ⟨(24, 5974913974272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record045_result⟩)
 (.branch 47
 (.leaf ⟨(24, 5998538407936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record046_result⟩)
 (.leaf ⟨(24, 6343310180352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record047_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8204 + i))) 0 48 :=
  interval_of_check _ 0 48 (by decide +kernel)

public theorem complete : Block 8204 8252 :=
  block_of_table results 8204 48 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0124
