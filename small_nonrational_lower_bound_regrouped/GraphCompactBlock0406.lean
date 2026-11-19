module
prelude
import GraphInputsRow27Part00003Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0406
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(27, 6727061962752), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record000_result⟩)
 (.branch 2
 (.leaf ⟨(27, 6727206436865), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record001_result⟩)
 (.leaf ⟨(27, 6790396870656), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(27, 6791486472192), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record003_result⟩)
 (.branch 5
 (.leaf ⟨(27, 6791630946305), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record004_result⟩)
 (.leaf ⟨(27, 6823698661632), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(27, 6823702693120), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record006_result⟩)
 (.branch 8
 (.leaf ⟨(27, 6837682405384), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record007_result⟩)
 (.leaf ⟨(27, 6838144827400), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(27, 6838147948552), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record009_result⟩)
 (.branch 11
 (.leaf ⟨(27, 6839878254600), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record010_result⟩)
 (.leaf ⟨(27, 6854837239816), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(27, 6857598959617), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record012_result⟩)
 (.branch 14
 (.leaf ⟨(27, 6866188894208), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record013_result⟩)
 (.leaf ⟨(27, 6866453135360), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(27, 6877489438976), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record015_result⟩)
 (.branch 17
 (.leaf ⟨(27, 6907471380736), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record016_result⟩)
 (.leaf ⟨(27, 6907537441024), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(27, 6920335491072), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record018_result⟩)
 (.branch 20
 (.leaf ⟨(27, 6927654322176), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record019_result⟩)
 (.leaf ⟨(27, 6929734696960), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(27, 6936483364864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record021_result⟩)
 (.leaf ⟨(27, 6936545263616), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record022_result⟩))
 (.branch 24
 (.leaf ⟨(27, 6936549425152), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record023_result⟩)
 (.leaf ⟨(27, 6968889638912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(27, 6975115280640), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record025_result⟩)
 (.branch 27
 (.leaf ⟨(27, 6975316582656), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record026_result⟩)
 (.leaf ⟨(27, 6977338048512), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(27, 6977470169088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record028_result⟩)
 (.branch 30
 (.leaf ⟨(27, 6979880845312), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record029_result⟩)
 (.leaf ⟨(27, 6982287228929), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(27, 6984173715456), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record031_result⟩)
 (.branch 33
 (.leaf ⟨(27, 6986447978497), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record032_result⟩)
 (.leaf ⟨(27, 6988528353281), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(27, 6998930228224), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record034_result⟩)
 (.branch 36
 (.leaf ⟨(27, 6999454515840), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record035_result⟩)
 (.leaf ⟨(27, 7003078557952), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(27, 7003082784768), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record037_result⟩)
 (.branch 39
 (.leaf ⟨(27, 7003086946304), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record038_result⟩)
 (.leaf ⟨(27, 7003090977792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(27, 7003346830080), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record040_result⟩)
 (.branch 42
 (.leaf ⟨(27, 7003615265408), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record041_result⟩)
 (.leaf ⟨(27, 7033120129024), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(27, 7072076791808), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record043_result⟩)
 (.branch 45
 (.leaf ⟨(27, 7072605274112), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record044_result⟩)
 (.leaf ⟨(27, 7074016722944), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(27, 7074025046016), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record046_result⟩)
 (.leaf ⟨(27, 7074148843520), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record047_result⟩))
 (.branch 49
 (.leaf ⟨(27, 7074157166592), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record048_result⟩)
 (.leaf ⟨(27, 7074617507840), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(27, 7147985928576), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record050_result⟩)
 (.branch 52
 (.leaf ⟨(27, 7149128847744), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record051_result⟩)
 (.leaf ⟨(27, 7149260968320), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(27, 7155970756992), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record053_result⟩)
 (.branch 55
 (.leaf ⟨(27, 7186046615568), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record054_result⟩)
 (.leaf ⟨(27, 7186826724100), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(27, 7302571720704), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record056_result⟩)
 (.branch 58
 (.leaf ⟨(27, 7448724275200), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record057_result⟩)
 (.leaf ⟨(27, 7518138925568), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(27, 7525076664320), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record059_result⟩)
 (.branch 61
 (.leaf ⟨(27, 7533938868225), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record060_result⟩)
 (.leaf ⟨(27, 7551374590464), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(27, 7559194132736), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record062_result⟩)
 (.branch 64
 (.leaf ⟨(27, 7559196016648), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record063_result⟩)
 (.leaf ⟨(27, 7560285554944), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(27, 7560285618184), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record065_result⟩)
 (.branch 67
 (.leaf ⟨(27, 7560302199552), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record066_result⟩)
 (.leaf ⟨(27, 7560310652928), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(27, 7560830650496), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record068_result⟩)
 (.branch 70
 (.leaf ⟨(27, 7563731607552), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record069_result⟩)
 (.leaf ⟨(27, 7564017272960), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(27, 7572607205377), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record071_result⟩)
 (.leaf ⟨(27, 7586199896064), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record072_result⟩))
 (.branch 74
 (.leaf ⟨(27, 7586332016640), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record073_result⟩)
 (.leaf ⟨(27, 7586792357888), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(27, 7586860498944), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record075_result⟩)
 (.branch 77
 (.leaf ⟨(27, 7593521219840), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record076_result⟩)
 (.leaf ⟨(27, 7593644951560), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(27, 7593661923328), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record078_result⟩)
 (.branch 80
 (.leaf ⟨(27, 7597801538568), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record079_result⟩)
 (.leaf ⟨(27, 7598074169344), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(27, 7598363377665), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record081_result⟩)
 (.branch 83
 (.leaf ⟨(27, 7602775787520), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record082_result⟩)
 (.leaf ⟨(27, 7607070752768), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(27, 7611241988097), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record084_result⟩)
 (.branch 86
 (.leaf ⟨(27, 7623843905536), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record085_result⟩)
 (.leaf ⟨(27, 7623977992192), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(27, 7635122257920), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record087_result⟩)
 (.branch 89
 (.leaf ⟨(27, 7647604506624), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record088_result⟩)
 (.leaf ⟨(27, 7658733043712), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(27, 7741286481920), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record090_result⟩)
 (.branch 92
 (.leaf ⟨(27, 7930197835776), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record091_result⟩)
 (.leaf ⟨(27, 7994185121792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(27, 8041321892096), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record093_result⟩)
 (.branch 95
 (.leaf ⟨(27, 8041321955336), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record094_result⟩)
 (.leaf ⟨(27, 8041413050368), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(27, 8041809412096), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record096_result⟩)
 (.leaf ⟨(27, 8045032185856), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record097_result⟩))
 (.branch 99
 (.leaf ⟨(27, 8067236233216), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record098_result⟩)
 (.leaf ⟨(27, 8067368353792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00003.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17973 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 17973 18073 :=
  block_of_table results 17973 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0406
