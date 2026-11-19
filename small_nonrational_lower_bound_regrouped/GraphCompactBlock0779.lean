module
prelude
import GraphInputsRow30Part00051Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0779
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 30792005787648), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record000_result⟩)
 (.leaf ⟨(30, 30792038752512), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 30792038817792), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record002_result⟩)
 (.branch 4
 (.leaf ⟨(30, 30792274157696), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record003_result⟩)
 (.leaf ⟨(30, 30792277303328), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(30, 30792310853664), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record005_result⟩)
 (.branch 7
 (.leaf ⟨(30, 30793347375232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record006_result⟩)
 (.leaf ⟨(30, 30805155913760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(30, 30805189464096), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record008_result⟩)
 (.branch 10
 (.leaf ⟨(30, 30824009335040), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record009_result⟩)
 (.leaf ⟨(30, 30825274417408), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(30, 30825274482688), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record011_result⟩)
 (.leaf ⟨(30, 30825290997760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record012_result⟩))
 (.branch 14
 (.leaf ⟨(30, 30825542852736), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record013_result⟩)
 (.branch 15
 (.leaf ⟨(30, 30826398024192), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record014_result⟩)
 (.leaf ⟨(30, 30826402217984), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(30, 30826670587905), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record016_result⟩)
 (.branch 18
 (.leaf ⟨(30, 30826871922688), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record017_result⟩)
 (.leaf ⟨(30, 30830965571584), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(30, 30831032672256), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record019_result⟩)
 (.branch 21
 (.leaf ⟨(30, 30839549198337), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record020_result⟩)
 (.leaf ⟨(30, 30840617189504), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(30, 30857758773280), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record022_result⟩)
 (.leaf ⟨(30, 30864197558304), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record023_result⟩))
 (.branch 25
 (.leaf ⟨(30, 30864198078496), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record024_result⟩)
 (.branch 26
 (.leaf ⟨(30, 30865053777920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record025_result⟩)
 (.leaf ⟨(30, 30865254129696), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(30, 30865322147841), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record027_result⟩)
 (.branch 29
 (.leaf ⟨(30, 30865325301760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record028_result⟩)
 (.leaf ⟨(30, 30865515094272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(30, 30866327867424), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record030_result⟩)
 (.branch 32
 (.leaf ⟨(30, 30866362335233), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record031_result⟩)
 (.leaf ⟨(30, 30866588311808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record032_result⟩)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf ⟨(30, 30873639518208), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record033_result⟩)
 (.branch 35
 (.leaf ⟨(30, 30881620697120), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record034_result⟩)
 (.leaf ⟨(30, 30896656809984), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record035_result⟩)))
 (.branch 37
 (.leaf ⟨(30, 30896665133056), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record036_result⟩)
 (.branch 38
 (.leaf ⟨(30, 30898560966656), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record037_result⟩)
 (.leaf ⟨(30, 30900687601665), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record038_result⟩))))
 (.branch 42
 (.branch 40
 (.leaf ⟨(30, 30900825882624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record039_result⟩)
 (.branch 41
 (.leaf ⟨(30, 30900947518208), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record040_result⟩)
 (.leaf ⟨(30, 30915979903520), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record041_result⟩)))
 (.branch 43
 (.leaf ⟨(30, 30931012821248), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record042_result⟩)
 (.branch 44
 (.leaf ⟨(30, 30934041640960), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record043_result⟩)
 (.leaf ⟨(30, 30942363140096), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00051.record044_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25157 + i))) 0 45 :=
  interval_of_check _ 0 45 (by decide +kernel)

public theorem complete : Block 25157 25202 :=
  block_of_table results 25157 45 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0779
