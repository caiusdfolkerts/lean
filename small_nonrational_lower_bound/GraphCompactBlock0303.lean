module
prelude
import GraphInputsRow25Part00013Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0303
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 37
 (.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(25, 17532610150400), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record000_result⟩)
 (.leaf ⟨(25, 17549236502528), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record001_result⟩))
 (.branch 3
 (.leaf ⟨(25, 17566953111552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record002_result⟩)
 (.leaf ⟨(25, 17595714584896), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(25, 17595718746432), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record004_result⟩)
 (.leaf ⟨(25, 17631130755392), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record005_result⟩))
 (.branch 7
 (.leaf ⟨(25, 17636824023104), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record006_result⟩)
 (.branch 8
 (.leaf ⟨(25, 17640010645568), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record007_result⟩)
 (.leaf ⟨(25, 17672222900288), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(25, 17706686447616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record009_result⟩)
 (.leaf ⟨(25, 17721852960832), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record010_result⟩))
 (.branch 12
 (.leaf ⟨(25, 17775403827200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record011_result⟩)
 (.leaf ⟨(25, 17783725326336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(25, 17784129994816), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record013_result⟩)
 (.leaf ⟨(25, 17786277470272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record014_result⟩))
 (.branch 16
 (.leaf ⟨(25, 17856532119552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record015_result⟩)
 (.branch 17
 (.leaf ⟨(25, 18143305605440), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record016_result⟩)
 (.leaf ⟨(25, 18181884313600), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record017_result⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨(25, 18248657600512), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record018_result⟩)
 (.leaf ⟨(25, 18253355155456), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record019_result⟩))
 (.branch 21
 (.leaf ⟨(25, 18271933858048), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record020_result⟩)
 (.leaf ⟨(25, 18272070205440), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(25, 18272078528512), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record022_result⟩)
 (.leaf ⟨(25, 18336033275905), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record023_result⟩))
 (.branch 25
 (.leaf ⟨(25, 18336503037952), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record024_result⟩)
 (.branch 26
 (.leaf ⟨(25, 18370393022464), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record025_result⟩)
 (.leaf ⟨(25, 18384771153920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record026_result⟩)))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf ⟨(25, 18406082511104), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record027_result⟩)
 (.leaf ⟨(25, 18406350979072), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record028_result⟩))
 (.branch 30
 (.leaf ⟨(25, 18406359302144), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record029_result⟩)
 (.branch 31
 (.leaf ⟨(25, 18406887653888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record030_result⟩)
 (.leaf ⟨(25, 18406896041984), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record031_result⟩))))
 (.branch 34
 (.branch 33
 (.leaf ⟨(25, 18522338033664), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record032_result⟩)
 (.leaf ⟨(25, 18527159320576), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record033_result⟩))
 (.branch 35
 (.leaf ⟨(25, 18531039052544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record034_result⟩)
 (.branch 36
 (.leaf ⟨(25, 18531320070144), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record035_result⟩)
 (.leaf ⟨(25, 18540033769472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record036_result⟩)))))))
 (.branch 56
 (.branch 46
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf ⟨(25, 18544330801152), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record037_result⟩)
 (.leaf ⟨(25, 18548491550720), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record038_result⟩))
 (.branch 40
 (.leaf ⟨(25, 18593115046144), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record039_result⟩)
 (.leaf ⟨(25, 18778875265280), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record040_result⟩)))
 (.branch 43
 (.branch 42
 (.leaf ⟨(25, 18817531052032), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record041_result⟩)
 (.leaf ⟨(25, 18920014618624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record042_result⟩))
 (.branch 44
 (.leaf ⟨(25, 19093952397312), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record043_result⟩)
 (.branch 45
 (.leaf ⟨(25, 19294748442624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record044_result⟩)
 (.leaf ⟨(25, 19366825426944), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record045_result⟩)))))
 (.branch 51
 (.branch 48
 (.branch 47
 (.leaf ⟨(25, 19435410685952), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record046_result⟩)
 (.leaf ⟨(25, 19504260186112), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record047_result⟩))
 (.branch 49
 (.leaf ⟨(25, 19512581685248), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record048_result⟩)
 (.branch 50
 (.leaf ⟨(25, 19564259704832), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record049_result⟩)
 (.leaf ⟨(25, 19573914992640), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record050_result⟩))))
 (.branch 53
 (.branch 52
 (.leaf ⟨(25, 19586326233344), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record051_result⟩)
 (.leaf ⟨(25, 19588947443712), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record052_result⟩))
 (.branch 54
 (.leaf ⟨(25, 19611625980480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record053_result⟩)
 (.branch 55
 (.leaf ⟨(25, 19611627044864), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record054_result⟩)
 (.leaf ⟨(25, 19619574188032), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record055_result⟩))))))
 (.branch 65
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf ⟨(25, 19623982532608), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record056_result⟩)
 (.leaf ⟨(25, 19624510882312), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record057_result⟩))
 (.branch 59
 (.leaf ⟨(25, 19633109204992), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record058_result⟩)
 (.leaf ⟨(25, 19637261860864), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record059_result⟩)))
 (.branch 62
 (.branch 61
 (.leaf ⟨(25, 19645987815424), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record060_result⟩)
 (.leaf ⟨(25, 19649752203264), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record061_result⟩))
 (.branch 63
 (.leaf ⟨(25, 19650280685568), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record062_result⟩)
 (.branch 64
 (.leaf ⟨(25, 19701694464000), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record063_result⟩)
 (.leaf ⟨(25, 19710412324864), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record064_result⟩)))))
 (.branch 70
 (.branch 67
 (.branch 66
 (.leaf ⟨(25, 19718337462272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record065_result⟩)
 (.leaf ⟨(25, 19718865944576), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record066_result⟩))
 (.branch 68
 (.leaf ⟨(25, 19729745969152), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record067_result⟩)
 (.branch 69
 (.leaf ⟨(25, 19733906718720), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record068_result⟩)
 (.leaf ⟨(25, 19742228217856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record069_result⟩))))
 (.branch 72
 (.branch 71
 (.leaf ⟨(25, 19742624579584), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record070_result⟩)
 (.leaf ⟨(25, 19748328898560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record071_result⟩))
 (.branch 73
 (.leaf ⟨(25, 19901414670336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record072_result⟩)
 (.branch 74
 (.leaf ⟨(25, 20193195589632), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record073_result⟩)
 (.leaf ⟨(25, 20199436713984), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00013.record074_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (13172 + i))) 0 75 :=
  interval_of_check _ 0 75 (by decide +kernel)

public theorem complete : Block 13172 13247 :=
  block_of_table results 13172 75 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0303
