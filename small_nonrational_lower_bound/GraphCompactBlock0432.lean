module
prelude
import GraphInputsRow28Part00012Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0432
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 29
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(28, 32804960337920), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record000_result⟩)
 (.branch 2
 (.leaf ⟨(28, 32805027315712), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record001_result⟩)
 (.leaf ⟨(28, 32822676946944), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(28, 32839319945216), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record003_result⟩)
 (.leaf ⟨(28, 32919313711104), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record004_result⟩))
 (.branch 6
 (.leaf ⟨(28, 32935956709376), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record005_result⟩)
 (.leaf ⟨(28, 32991020646400), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(28, 32991289049088), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record007_result⟩)
 (.branch 9
 (.leaf ⟨(28, 33023068274688), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record008_result⟩)
 (.leaf ⟨(28, 33039071608832), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(28, 33072322060416), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record010_result⟩)
 (.leaf ⟨(28, 33132520734720), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record011_result⟩))
 (.branch 13
 (.leaf ⟨(28, 33133123600384), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record012_result⟩)
 (.leaf ⟨(28, 33168027549696), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(28, 33204467662848), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record014_result⟩)
 (.branch 16
 (.leaf ⟨(28, 33264807452672), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record015_result⟩)
 (.leaf ⟨(28, 33273111777312), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(28, 33297946116096), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record017_result⟩)
 (.leaf ⟨(28, 33298210357248), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record018_result⟩))
 (.branch 20
 (.leaf ⟨(28, 33720325111808), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record019_result⟩)
 (.leaf ⟨(28, 34086003441920), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record020_result⟩))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf ⟨(28, 34120432418816), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record021_result⟩)
 (.leaf ⟨(28, 34124865732608), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record022_result⟩))
 (.branch 24
 (.leaf ⟨(28, 34125394214912), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record023_result⟩)
 (.leaf ⟨(28, 34129026482176), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record024_result⟩)))
 (.branch 27
 (.branch 26
 (.leaf ⟨(28, 34129554964480), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record025_result⟩)
 (.leaf ⟨(28, 34132147044352), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record026_result⟩))
 (.branch 28
 (.leaf ⟨(28, 34145025654784), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record027_result⟩)
 (.leaf ⟨(28, 34187960713216), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record028_result⟩))))))
 (.branch 44
 (.branch 36
 (.branch 32
 (.branch 30
 (.leaf ⟨(28, 34213709611008), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record029_result⟩)
 (.branch 31
 (.leaf ⟨(28, 34223442427904), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record030_result⟩)
 (.leaf ⟨(28, 34228783808512), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record031_result⟩)))
 (.branch 34
 (.branch 33
 (.leaf ⟨(28, 34240622231552), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record032_result⟩)
 (.leaf ⟨(28, 34240754352128), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record033_result⟩))
 (.branch 35
 (.leaf ⟨(28, 34241662418944), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record034_result⟩)
 (.leaf ⟨(28, 34256678092800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record035_result⟩))))
 (.branch 40
 (.branch 38
 (.branch 37
 (.leaf ⟨(28, 34278134120448), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record036_result⟩)
 (.leaf ⟨(28, 34497195163648), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record037_result⟩))
 (.branch 39
 (.leaf ⟨(28, 34498320269312), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record038_result⟩)
 (.leaf ⟨(28, 34500532764672), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record039_result⟩)))
 (.branch 42
 (.branch 41
 (.leaf ⟨(28, 34531555934208), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record040_result⟩)
 (.leaf ⟨(28, 34535848804352), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record041_result⟩))
 (.branch 43
 (.leaf ⟨(28, 34634666872832), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record042_result⟩)
 (.leaf ⟨(28, 34634667393024), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record043_result⟩)))))
 (.branch 51
 (.branch 47
 (.branch 45
 (.leaf ⟨(28, 34635707383808), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record044_result⟩)
 (.branch 46
 (.leaf ⟨(28, 34635727831040), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record045_result⟩)
 (.leaf ⟨(28, 34635740348928), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record046_result⟩)))
 (.branch 49
 (.branch 48
 (.leaf ⟨(28, 34635748737024), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record047_result⟩)
 (.leaf ⟨(28, 34635828494336), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record048_result⟩))
 (.branch 50
 (.leaf ⟨(28, 34636244189184), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record049_result⟩)
 (.leaf ⟨(28, 34644321894400), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record050_result⟩))))
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf ⟨(28, 34644850376704), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record051_result⟩)
 (.leaf ⟨(28, 34651813449728), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record052_result⟩))
 (.branch 54
 (.leaf ⟨(28, 34652870021120), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record053_result⟩)
 (.leaf ⟨(28, 34660420157440), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record054_result⟩)))
 (.branch 57
 (.branch 56
 (.leaf ⟨(28, 34673547804672), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record055_result⟩)
 (.leaf ⟨(28, 34704686317568), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record056_result⟩))
 (.branch 58
 (.leaf ⟨(28, 34713536299008), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record057_result⟩)
 (.leaf ⟨(28, 34729139109888), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record058_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20377 + i))) 0 59 :=
  interval_of_check _ 0 59 (by decide +kernel)

public theorem complete : Block 20377 20436 :=
  block_of_table results 20377 59 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0432
