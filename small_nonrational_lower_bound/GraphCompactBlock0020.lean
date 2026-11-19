module
prelude
import GraphInputsRow16Part00020Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0020
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 22864975626240), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_result⟩)
 (.leaf ⟨(16, 22872116494336), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 22879459639552), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record002_result⟩)
 (.leaf ⟨(16, 22887417282816), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(16, 22887417348096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record004_result⟩)
 (.leaf ⟨(16, 22889299542016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record005_result⟩))
 (.branch 7
 (.leaf ⟨(16, 22893460226304), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record006_result⟩)
 (.leaf ⟨(16, 22893460291584), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(16, 22893594492928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record008_result⟩)
 (.leaf ⟨(16, 22893859709184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record009_result⟩))
 (.branch 11
 (.leaf ⟨(16, 22893862895616), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record010_result⟩)
 (.leaf ⟨(16, 22898929631232), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(16, 22902184394752), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record012_result⟩)
 (.leaf ⟨(16, 22907515371520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record013_result⟩))
 (.branch 15
 (.leaf ⟨(16, 22913961959424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record014_result⟩)
 (.branch 16
 (.leaf ⟨(16, 22920388706560), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record015_result⟩)
 (.leaf ⟨(16, 22920388771840), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record016_result⟩))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(16, 22922530980096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record017_result⟩)
 (.leaf ⟨(16, 22922535141632), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record018_result⟩))
 (.branch 20
 (.leaf ⟨(16, 22922535206912), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record019_result⟩)
 (.leaf ⟨(16, 22922799382784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(16, 22922799448064), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record021_result⟩)
 (.leaf ⟨(16, 22926830157824), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record022_result⟩))
 (.branch 24
 (.leaf ⟨(16, 22926881458432), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record023_result⟩)
 (.leaf ⟨(16, 22927094398976), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record024_result⟩))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf ⟨(16, 22927098560512), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record025_result⟩)
 (.leaf ⟨(16, 22929289019648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record026_result⟩))
 (.branch 28
 (.leaf ⟨(16, 22945997160704), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record027_result⟩)
 (.leaf ⟨(16, 22948081762304), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record028_result⟩)))
 (.branch 31
 (.branch 30
 (.leaf ⟨(16, 22948287225856), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record029_result⟩)
 (.leaf ⟨(16, 22948288136192), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record030_result⟩))
 (.branch 32
 (.leaf ⟨(16, 22948552377344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record031_result⟩)
 (.branch 33
 (.leaf ⟨(16, 22976096403712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record032_result⟩)
 (.leaf ⟨(16, 22988973965568), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record033_result⟩)))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf ⟨(16, 23147492425984), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record034_result⟩)
 (.leaf ⟨(16, 23147494572032), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record035_result⟩))
 (.branch 37
 (.leaf ⟨(16, 23147500814336), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036_result⟩)
 (.leaf ⟨(16, 23179713069056), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record037_result⟩)))
 (.branch 40
 (.branch 39
 (.leaf ⟨(16, 23199880347904), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record038_result⟩)
 (.leaf ⟨(16, 23211902304256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record039_result⟩))
 (.branch 41
 (.leaf ⟨(16, 23211908546560), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record040_result⟩)
 (.leaf ⟨(16, 23215577563392), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record041_result⟩))))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf ⟨(16, 23216044146944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record042_result⟩)
 (.leaf ⟨(16, 23219742654464), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record043_result⟩))
 (.branch 45
 (.leaf ⟨(16, 23247695397120), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record044_result⟩)
 (.leaf ⟨(16, 23247755215104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(16, 23247761457408), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record046_result⟩)
 (.leaf ⟨(16, 23247761522688), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record047_result⟩))
 (.branch 49
 (.leaf ⟨(16, 23248164110400), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record048_result⟩)
 (.branch 50
 (.leaf ⟨(16, 23248165150784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record049_result⟩)
 (.leaf ⟨(16, 23248223879424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record050_result⟩))))))
 (.branch 60
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf ⟨(16, 23248289939712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record051_result⟩)
 (.leaf ⟨(16, 23248292085760), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record052_result⟩))
 (.branch 54
 (.leaf ⟨(16, 23248298328064), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record053_result⟩)
 (.leaf ⟨(16, 23248300408832), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record054_result⟩)))
 (.branch 57
 (.branch 56
 (.leaf ⟨(16, 23249841832192), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record055_result⟩)
 (.leaf ⟨(16, 23251384803392), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record056_result⟩))
 (.branch 58
 (.leaf ⟨(16, 23280427745280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record057_result⟩)
 (.branch 59
 (.leaf ⟨(16, 23280495886336), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record058_result⟩)
 (.leaf ⟨(16, 23283077562368), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record059_result⟩)))))
 (.branch 64
 (.branch 62
 (.branch 61
 (.leaf ⟨(16, 23283715538944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record060_result⟩)
 (.leaf ⟨(16, 23284167163904), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record061_result⟩))
 (.branch 63
 (.leaf ⟨(16, 23284838040064), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record062_result⟩)
 (.leaf ⟨(16, 23316379418624), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record063_result⟩)))
 (.branch 66
 (.branch 65
 (.leaf ⟨(16, 23348073725952), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_result⟩)
 (.leaf ⟨(16, 23372249465088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record065_result⟩))
 (.branch 67
 (.leaf ⟨(16, 23372249530368), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record066_result⟩)
 (.branch 68
 (.leaf ⟨(16, 23372449726720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record067_result⟩)
 (.leaf ⟨(16, 23372449792000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1252 + i))) 0 69 :=
  interval_of_check _ 0 69 (by decide +kernel)

public theorem complete : Block 1252 1321 :=
  block_of_table results 1252 69 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0020
