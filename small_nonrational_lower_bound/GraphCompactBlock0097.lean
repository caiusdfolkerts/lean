module
prelude
import GraphInputsRow23Part00019Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0097
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 37
 (.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(23, 25980811411456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record000_result⟩)
 (.leaf ⟨(23, 25993159393536), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record001_result⟩))
 (.branch 3
 (.leaf ⟨(23, 25993696264192), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record002_result⟩)
 (.leaf ⟨(23, 25993813430272), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(23, 25994886906368), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record004_result⟩)
 (.leaf ⟨(23, 26117981929472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record005_result⟩))
 (.branch 7
 (.leaf ⟨(23, 26122545283072), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 26130983948288), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record007_result⟩)
 (.leaf ⟨(23, 26132057424384), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(23, 26319576694784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record009_result⟩)
 (.leaf ⟨(23, 26320113500160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record010_result⟩))
 (.branch 12
 (.leaf ⟨(23, 26336739592192), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record011_result⟩)
 (.leaf ⟨(23, 26398254243904), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(23, 26398287274048), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record013_result⟩)
 (.leaf ⟨(23, 26428221521920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record014_result⟩))
 (.branch 16
 (.leaf ⟨(23, 26428353577216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 26428353642496), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record016_result⟩)
 (.leaf ⟨(23, 26428617883648), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record017_result⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨(23, 26428622012544), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record018_result⟩)
 (.leaf ⟨(23, 26428624093312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record019_result⟩))
 (.branch 21
 (.leaf ⟨(23, 26431539454016), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record020_result⟩)
 (.leaf ⟨(23, 26441305563264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(23, 26462712332288), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record022_result⟩)
 (.leaf ⟨(23, 26463785549824), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record023_result⟩))
 (.branch 25
 (.leaf ⟨(23, 26464020889728), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record024_result⟩)
 (.branch 26
 (.leaf ⟨(23, 26464024010880), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record025_result⟩)
 (.leaf ⟨(23, 26466873016576), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record026_result⟩)))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf ⟨(23, 26466873081856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record027_result⟩)
 (.leaf ⟨(23, 26467275653248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record028_result⟩))
 (.branch 30
 (.leaf ⟨(23, 26467275685888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record029_result⟩)
 (.branch 31
 (.leaf ⟨(23, 26467276693632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record030_result⟩)
 (.leaf ⟨(23, 26468315840640), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record031_result⟩))))
 (.branch 34
 (.branch 33
 (.leaf ⟨(23, 26468315873280), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record032_result⟩)
 (.leaf ⟨(23, 26468316881024), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record033_result⟩))
 (.branch 35
 (.leaf ⟨(23, 26475667398688), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record034_result⟩)
 (.branch 36
 (.leaf ⟨(23, 26498346156160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record035_result⟩)
 (.leaf ⟨(23, 26532370743552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record036_result⟩)))))))
 (.branch 55
 (.branch 46
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf ⟨(23, 26532370808832), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record037_result⟩)
 (.leaf ⟨(23, 26532741390464), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record038_result⟩))
 (.branch 40
 (.leaf ⟨(23, 26544312434944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record039_result⟩)
 (.leaf ⟨(23, 26571228381184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record040_result⟩)))
 (.branch 43
 (.branch 42
 (.leaf ⟨(23, 26571622596864), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record041_result⟩)
 (.leaf ⟨(23, 26648730697728), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record042_result⟩))
 (.branch 44
 (.leaf ⟨(23, 26670014664736), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record043_result⟩)
 (.branch 45
 (.leaf ⟨(23, 26777579716608), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record044_result⟩)
 (.leaf ⟨(23, 26943986606208), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record045_result⟩)))))
 (.branch 50
 (.branch 48
 (.branch 47
 (.leaf ⟨(23, 26948279476352), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record046_result⟩)
 (.leaf ⟨(23, 26956865216640), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record047_result⟩))
 (.branch 49
 (.leaf ⟨(23, 26990985904384), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record048_result⟩)
 (.leaf ⟨(23, 26991254339712), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record049_result⟩)))
 (.branch 52
 (.branch 51
 (.leaf ⟨(23, 26992527818880), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record050_result⟩)
 (.leaf ⟨(23, 27015638491136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record051_result⟩))
 (.branch 53
 (.leaf ⟨(23, 27015906861184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record052_result⟩)
 (.branch 54
 (.leaf ⟨(23, 27016757838080), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record053_result⟩)
 (.leaf ⟨(23, 27016762032640), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record054_result⟩))))))
 (.branch 64
 (.branch 59
 (.branch 57
 (.branch 56
 (.leaf ⟨(23, 27016766226432), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record055_result⟩)
 (.leaf ⟨(23, 27016963432576), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record056_result⟩))
 (.branch 58
 (.leaf ⟨(23, 27080063000576), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record057_result⟩)
 (.leaf ⟨(23, 27085483606016), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record058_result⟩)))
 (.branch 61
 (.branch 60
 (.leaf ⟨(23, 27094069346304), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record059_result⟩)
 (.leaf ⟨(23, 27110997557248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record060_result⟩))
 (.branch 62
 (.leaf ⟨(23, 27120709468416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record061_result⟩)
 (.branch 63
 (.leaf ⟨(23, 27121378459648), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record062_result⟩)
 (.leaf ⟨(23, 27128693293056), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record063_result⟩)))))
 (.branch 69
 (.branch 66
 (.branch 65
 (.leaf ⟨(23, 27130373144576), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record064_result⟩)
 (.leaf ⟨(23, 27130645708800), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record065_result⟩))
 (.branch 67
 (.leaf ⟨(23, 27130909949952), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record066_result⟩)
 (.branch 68
 (.leaf ⟨(23, 27217505554464), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record067_result⟩)
 (.leaf ⟨(23, 27222062665760), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record068_result⟩))))
 (.branch 71
 (.branch 70
 (.leaf ⟨(23, 27224254726272), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record069_result⟩)
 (.leaf ⟨(23, 27250632196352), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record070_result⟩))
 (.branch 72
 (.leaf ⟨(23, 27251301187584), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record071_result⟩)
 (.branch 73
 (.leaf ⟨(23, 27257542311936), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record072_result⟩)
 (.leaf ⟨(23, 27258582499328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record073_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7198 + i))) 0 74 :=
  interval_of_check _ 0 74 (by decide +kernel)

public theorem complete : Block 7198 7272 :=
  block_of_table results 7198 74 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0097
