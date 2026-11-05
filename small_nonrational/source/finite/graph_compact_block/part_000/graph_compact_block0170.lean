module
prelude
import GraphInputsRow24Part00054Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0170
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 20150016311296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 20158531797120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record001_result⟩)
 (.leaf ⟨(24, 20158535991296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 20158602051584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 20158635081728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record004_result⟩)
 (.leaf ⟨(24, 20158732058752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 20161854734336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 20162894921728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record007_result⟩)
 (.leaf ⟨(24, 20171471225088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 20171475419264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record009_result⟩)
 (.leaf ⟨(24, 20171727046784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 20173749780736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record011_result⟩)
 (.leaf ⟨(24, 20173807421568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(24, 20174018216064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 20177968171136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record014_result⟩)
 (.leaf ⟨(24, 20180312850432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(24, 20186553911424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 20192923123840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record017_result⟩)
 (.leaf ⟨(24, 20192927318016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(24, 20193063470080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record019_result⟩)
 (.branch 21
 (.leaf ⟨(24, 20193191395968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record020_result⟩)
 (.leaf ⟨(24, 20199300562944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(24, 20199432520320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022_result⟩)
 (.leaf ⟨(24, 20227319431168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record023_result⟩))
 (.branch 25
 (.leaf ⟨(24, 20274547294464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record024_result⟩)
 (.leaf ⟨(24, 20274604935296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record025_result⟩))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf ⟨(24, 20279029989376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record026_result⟩)
 (.branch 28
 (.leaf ⟨(24, 20283320713472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record027_result⟩)
 (.leaf ⟨(24, 20283386773760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record028_result⟩)))
 (.branch 30
 (.leaf ⟨(24, 20289629980800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record029_result⟩)
 (.branch 31
 (.leaf ⟨(24, 20344763138176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record030_result⟩)
 (.leaf ⟨(24, 20346909573248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record031_result⟩))))
 (.branch 35
 (.branch 33
 (.leaf ⟨(24, 20379914027136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record032_result⟩)
 (.branch 34
 (.leaf ⟨(24, 20380182429824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record033_result⟩)
 (.leaf ⟨(24, 20385397539072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record034_result⟩)))
 (.branch 37
 (.branch 36
 (.leaf ⟨(24, 20385403781376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record035_result⟩)
 (.leaf ⟨(24, 20388624994560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record036_result⟩))
 (.branch 38
 (.leaf ⟨(24, 20412126281856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record037_result⟩)
 (.leaf ⟨(24, 20414542160000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record038_result⟩)))))
 (.branch 45
 (.branch 42
 (.branch 40
 (.leaf ⟨(24, 20419690168576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record039_result⟩)
 (.branch 41
 (.leaf ⟨(24, 20420837249280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record040_result⟩)
 (.leaf ⟨(24, 20480711540864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record041_result⟩)))
 (.branch 43
 (.leaf ⟨(24, 20488275427584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record042_result⟩)
 (.branch 44
 (.leaf ⟨(24, 20488678031616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record043_result⟩)
 (.leaf ⟨(24, 20489554628864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record044_result⟩))))
 (.branch 48
 (.branch 46
 (.leaf ⟨(24, 20496999530752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record045_result⟩)
 (.branch 47
 (.leaf ⟨(24, 20498140369152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record046_result⟩)
 (.leaf ⟨(24, 20552832057600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record047_result⟩)))
 (.branch 50
 (.branch 49
 (.leaf ⟨(24, 20552840445952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record048_result⟩)
 (.leaf ⟨(24, 20557403799552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record049_result⟩))
 (.branch 51
 (.leaf ⟨(24, 20557593592064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record050_result⟩)
 (.leaf ⟨(24, 20561962991616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9858 + i))) 0 52 :=
  interval_of_check _ 0 52 (by decide +kernel)

public theorem complete : Block 9858 9910 :=
  block_of_table results 9858 52 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0170
