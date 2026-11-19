module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public meta import IntegerTables
public import RootedSixBase02
public import RawKindedFacePlacement
public import RootedSixBase02OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T0
open ConcreteGrowth
abbrev blockCount : Nat := 144
noncomputable def template : Cell := ⟨2, 31, [3, 5, 6, 9, 10, 12, 17, 18, 24], [7, 13, 14, 19, 25, 26]⟩
cert_root_5 02
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 72
 (.branch 36
 (.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨1, 4, 274960, 274960, 361617786720, 288326448720⟩, 510))
 (.leaf (⟨1, 4, 274960, 274960, 361616738145, 288326448645⟩, 863)))
 (.branch 3
 (.leaf (⟨1, 4, 274960, 274960, 361599960930, 288326447205⟩, 972))
 (.leaf (⟨1, 4, 274960, 274960, 361331525475, 288326420325⟩, 1237))))
 (.branch 6
 (.branch 5
 (.leaf (⟨1, 4, 274960, 274960, 357036558180, 288325928805⟩, 1346))
 (.leaf (⟨1, 4, 274960, 274960, 288317081445, 288317081445⟩, 1371)))
 (.branch 7
 (.leaf (⟨1, 4, 274945, 274945, 361617786720, 288326448720⟩, 510))
 (.branch 8
 (.leaf (⟨1, 4, 274945, 274945, 361616738145, 288326448645⟩, 863))
 (.leaf (⟨1, 4, 274945, 274945, 361599960930, 288326447205⟩, 972))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (⟨1, 4, 274945, 274945, 361331525475, 288326420325⟩, 1237))
 (.leaf (⟨1, 4, 274945, 274945, 357036558180, 288325928805⟩, 1346)))
 (.branch 12
 (.leaf (⟨1, 4, 274945, 274945, 288317081445, 288317081445⟩, 1371))
 (.leaf (⟨2, 4, 274960, 274960, 361626105360, 361626105360⟩, 16580861))))
 (.branch 15
 (.branch 14
 (.leaf (⟨2, 4, 274960, 274960, 361609328160, 361626104160⟩, 22348117))
 (.leaf (⟨2, 4, 274960, 274960, 361592550945, 361626104070⟩, 35258906)))
 (.branch 16
 (.leaf (⟨2, 4, 274960, 274960, 361340892720, 361626081120⟩, 27853225))
 (.branch 17
 (.leaf (⟨2, 4, 274960, 274960, 361324115505, 361626081030⟩, 45482678))
 (.leaf (⟨2, 4, 274960, 274960, 356760712770, 361625649270⟩, 58131319)))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf (⟨2, 4, 274960, 274960, 352465745475, 361625618550⟩, 69993516))
 (.leaf (⟨2, 4, 274960, 274960, 288309671505, 361617786630⟩, 50987786)))
 (.branch 21
 (.leaf (⟨2, 4, 274960, 274960, 283746268755, 361617754230⟩, 75498624))
 (.leaf (⟨2, 4, 274960, 274960, 215026792020, 361617201270⟩, 82642157))))
 (.branch 24
 (.branch 23
 (.leaf (⟨1, 4, 274690, 274465, 361617786720, 288326448720⟩, 505))
 (.leaf (⟨1, 4, 274690, 274465, 361616738145, 288326448645⟩, 858)))
 (.branch 25
 (.leaf (⟨1, 4, 274690, 274465, 361599960930, 288326447205⟩, 967))
 (.branch 26
 (.leaf (⟨1, 4, 274690, 274465, 361331525475, 288326420325⟩, 1232))
 (.leaf (⟨1, 4, 274690, 274465, 357036558180, 288325928805⟩, 1341))))))
 (.branch 31
 (.branch 29
 (.branch 28
 (.leaf (⟨1, 4, 274690, 274465, 288317081445, 288317081445⟩, 1366))
 (.leaf (⟨2, 4, 274720, 274720, 361626105360, 361626105360⟩, 16253179)))
 (.branch 30
 (.leaf (⟨2, 4, 274720, 274720, 361609328160, 361626104160⟩, 22020435))
 (.leaf (⟨2, 4, 274720, 274720, 361592550945, 361626104070⟩, 34931224))))
 (.branch 33
 (.branch 32
 (.leaf (⟨2, 4, 274720, 274720, 361340892720, 361626081120⟩, 27525543))
 (.leaf (⟨2, 4, 274720, 274720, 361324115505, 361626081030⟩, 45154996)))
 (.branch 34
 (.leaf (⟨2, 4, 274720, 274720, 356760712770, 361625649270⟩, 57803637))
 (.branch 35
 (.leaf (⟨2, 4, 274720, 274720, 352465745475, 361625618550⟩, 69665834))
 (.leaf (⟨2, 4, 274720, 274720, 288309671505, 361617786630⟩, 50660104))))))))
 (.branch 54
 (.branch 45
 (.branch 40
 (.branch 38
 (.branch 37
 (.leaf (⟨2, 4, 274720, 274720, 283746268755, 361617754230⟩, 75170942))
 (.leaf (⟨2, 4, 274720, 274720, 215026792020, 361617201270⟩, 82314475)))
 (.branch 39
 (.leaf (⟨2, 4, 274465, 274690, 361626105360, 361626105360⟩, 16253179))
 (.leaf (⟨2, 4, 274465, 274690, 361609328160, 361626104160⟩, 22020435))))
 (.branch 42
 (.branch 41
 (.leaf (⟨2, 4, 274465, 274690, 361592550945, 361626104070⟩, 34931224))
 (.leaf (⟨2, 4, 274465, 274690, 361340892720, 361626081120⟩, 27525543)))
 (.branch 43
 (.leaf (⟨2, 4, 274465, 274690, 361324115505, 361626081030⟩, 45154996))
 (.branch 44
 (.leaf (⟨2, 4, 274465, 274690, 356760712770, 361625649270⟩, 57803637))
 (.leaf (⟨2, 4, 274465, 274690, 352465745475, 361625618550⟩, 69665834))))))
 (.branch 49
 (.branch 47
 (.branch 46
 (.leaf (⟨2, 4, 274465, 274690, 288309671505, 361617786630⟩, 50660104))
 (.leaf (⟨2, 4, 274465, 274690, 283746268755, 361617754230⟩, 75170942)))
 (.branch 48
 (.leaf (⟨2, 4, 274465, 274690, 215026792020, 361617201270⟩, 82314475))
 (.leaf (⟨3, 4, 274960, 274960, 361742426640, 434925761040⟩, 124521259464501720611749995))))
 (.branch 51
 (.branch 50
 (.leaf (⟨3, 4, 274960, 274960, 361473991440, 434925741840⟩, 211565246662594835843842227))
 (.leaf (⟨3, 4, 274960, 274960, 283627709745, 434918463495⟩, 744709668250915166640407148)))
 (.branch 52
 (.leaf (⟨3, 4, 274960, 274960, 141893788995, 434917935495⟩, 1196854823974343292984886242))
 (.branch 53
 (.leaf (⟨1, 4, 270595, 262945, 361617786720, 288326448720⟩, 511))
 (.leaf (⟨1, 4, 270595, 262945, 361616738145, 288326448645⟩, 864)))))))
 (.branch 63
 (.branch 58
 (.branch 56
 (.branch 55
 (.leaf (⟨1, 4, 270595, 262945, 361599960930, 288326447205⟩, 973))
 (.leaf (⟨1, 4, 270595, 262945, 361331525475, 288326420325⟩, 1238)))
 (.branch 57
 (.leaf (⟨1, 4, 270595, 262945, 357036558180, 288325928805⟩, 1347))
 (.leaf (⟨1, 4, 270595, 262945, 288317081445, 288317081445⟩, 1372))))
 (.branch 60
 (.branch 59
 (.leaf (⟨2, 4, 270640, 267040, 361626105360, 361626105360⟩, 16646398))
 (.leaf (⟨2, 4, 270640, 267040, 361609328160, 361626104160⟩, 22413654)))
 (.branch 61
 (.leaf (⟨2, 4, 270640, 267040, 361592550945, 361626104070⟩, 35324443))
 (.branch 62
 (.leaf (⟨2, 4, 270640, 267040, 361340892720, 361626081120⟩, 27918762))
 (.leaf (⟨2, 4, 270640, 267040, 361324115505, 361626081030⟩, 45548215))))))
 (.branch 67
 (.branch 65
 (.branch 64
 (.leaf (⟨2, 4, 270640, 267040, 356760712770, 361625649270⟩, 58196856))
 (.leaf (⟨2, 4, 270640, 267040, 352465745475, 361625618550⟩, 70059053)))
 (.branch 66
 (.leaf (⟨2, 4, 270640, 267040, 288309671505, 361617786630⟩, 51053323))
 (.leaf (⟨2, 4, 270640, 267040, 283746268755, 361617754230⟩, 75564161))))
 (.branch 69
 (.branch 68
 (.leaf (⟨2, 4, 270640, 267040, 215026792020, 361617201270⟩, 82707694))
 (.leaf (⟨2, 4, 270385, 267010, 361626105360, 361626105360⟩, 16646398)))
 (.branch 70
 (.leaf (⟨2, 4, 270385, 267010, 361609328160, 361626104160⟩, 22413654))
 (.branch 71
 (.leaf (⟨2, 4, 270385, 267010, 361592550945, 361626104070⟩, 35324443))
 (.leaf (⟨2, 4, 270385, 267010, 361340892720, 361626081120⟩, 27918762)))))))))
 (.branch 108
 (.branch 90
 (.branch 81
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf (⟨2, 4, 270385, 267010, 361324115505, 361626081030⟩, 45548215))
 (.leaf (⟨2, 4, 270385, 267010, 356760712770, 361625649270⟩, 58196856)))
 (.branch 75
 (.leaf (⟨2, 4, 270385, 267010, 352465745475, 361625618550⟩, 70059053))
 (.leaf (⟨2, 4, 270385, 267010, 288309671505, 361617786630⟩, 51053323))))
 (.branch 78
 (.branch 77
 (.leaf (⟨2, 4, 270385, 267010, 283746268755, 361617754230⟩, 75564161))
 (.leaf (⟨2, 4, 270385, 267010, 215026792020, 361617201270⟩, 82707694)))
 (.branch 79
 (.leaf (⟨2, 4, 266290, 266290, 361626105360, 361626105360⟩, 16449784))
 (.branch 80
 (.leaf (⟨2, 4, 266290, 266290, 361609328160, 361626104160⟩, 22217040))
 (.leaf (⟨2, 4, 266290, 266290, 361592550945, 361626104070⟩, 35127829))))))
 (.branch 85
 (.branch 83
 (.branch 82
 (.leaf (⟨2, 4, 266290, 266290, 361340892720, 361626081120⟩, 27722148))
 (.leaf (⟨2, 4, 266290, 266290, 361324115505, 361626081030⟩, 45351601)))
 (.branch 84
 (.leaf (⟨2, 4, 266290, 266290, 356760712770, 361625649270⟩, 58000242))
 (.leaf (⟨2, 4, 266290, 266290, 352465745475, 361625618550⟩, 69862439))))
 (.branch 87
 (.branch 86
 (.leaf (⟨2, 4, 266290, 266290, 288309671505, 361617786630⟩, 50856709))
 (.leaf (⟨2, 4, 266290, 266290, 283746268755, 361617754230⟩, 75367547)))
 (.branch 88
 (.leaf (⟨2, 4, 266290, 266290, 215026792020, 361617201270⟩, 82511080))
 (.branch 89
 (.leaf (⟨3, 4, 267040, 270640, 361742426640, 434925761040⟩, 126939184891270215162593385))
 (.leaf (⟨3, 4, 267040, 270640, 361473991440, 434925741840⟩, 213983172089363330394685617)))))))
 (.branch 99
 (.branch 94
 (.branch 92
 (.branch 91
 (.leaf (⟨3, 4, 267040, 270640, 283627709745, 434918463495⟩, 747127593677683661191250538))
 (.leaf (⟨3, 4, 267040, 270640, 141893788995, 434917935495⟩, 1199272749401111787535729632)))
 (.branch 93
 (.leaf (⟨3, 4, 262945, 270595, 361742426640, 434925761040⟩, 126939184891270215162593385))
 (.leaf (⟨3, 4, 262945, 270595, 361473991440, 434925741840⟩, 213983172089363330394685617))))
 (.branch 96
 (.branch 95
 (.leaf (⟨3, 4, 262945, 270595, 283627709745, 434918463495⟩, 747127593677683661191250538))
 (.leaf (⟨3, 4, 262945, 270595, 141893788995, 434917935495⟩, 1199272749401111787535729632)))
 (.branch 97
 (.leaf (⟨1, 4, 205060, 17185, 361617786720, 288326448720⟩, 504))
 (.branch 98
 (.leaf (⟨1, 4, 205060, 17185, 361616738145, 288326448645⟩, 857))
 (.leaf (⟨1, 4, 205060, 17185, 361599960930, 288326447205⟩, 966))))))
 (.branch 103
 (.branch 101
 (.branch 100
 (.leaf (⟨1, 4, 205060, 17185, 361331525475, 288326420325⟩, 1231))
 (.leaf (⟨1, 4, 205060, 17185, 357036558180, 288325928805⟩, 1340)))
 (.branch 102
 (.leaf (⟨1, 4, 205060, 17185, 288317081445, 288317081445⟩, 1365))
 (.leaf (⟨2, 4, 205120, 82720, 361626105360, 361626105360⟩, 16187642))))
 (.branch 105
 (.branch 104
 (.leaf (⟨2, 4, 205120, 82720, 361609328160, 361626104160⟩, 21954898))
 (.leaf (⟨2, 4, 205120, 82720, 361592550945, 361626104070⟩, 34865687)))
 (.branch 106
 (.leaf (⟨2, 4, 205120, 82720, 361340892720, 361626081120⟩, 27460006))
 (.branch 107
 (.leaf (⟨2, 4, 205120, 82720, 361324115505, 361626081030⟩, 45089459))
 (.leaf (⟨2, 4, 205120, 82720, 356760712770, 361625649270⟩, 57738100))))))))
 (.branch 126
 (.branch 117
 (.branch 112
 (.branch 110
 (.branch 109
 (.leaf (⟨2, 4, 205120, 82720, 352465745475, 361625618550⟩, 69600297))
 (.leaf (⟨2, 4, 205120, 82720, 288309671505, 361617786630⟩, 50594567)))
 (.branch 111
 (.leaf (⟨2, 4, 205120, 82720, 283746268755, 361617754230⟩, 75105405))
 (.leaf (⟨2, 4, 205120, 82720, 215026792020, 361617201270⟩, 82248938))))
 (.branch 114
 (.branch 113
 (.leaf (⟨2, 4, 204865, 82690, 361626105360, 361626105360⟩, 16187642))
 (.leaf (⟨2, 4, 204865, 82690, 361609328160, 361626104160⟩, 21954898)))
 (.branch 115
 (.leaf (⟨2, 4, 204865, 82690, 361592550945, 361626104070⟩, 34865687))
 (.branch 116
 (.leaf (⟨2, 4, 204865, 82690, 361340892720, 361626081120⟩, 27460006))
 (.leaf (⟨2, 4, 204865, 82690, 361324115505, 361626081030⟩, 45089459))))))
 (.branch 121
 (.branch 119
 (.branch 118
 (.leaf (⟨2, 4, 204865, 82690, 356760712770, 361625649270⟩, 57738100))
 (.leaf (⟨2, 4, 204865, 82690, 352465745475, 361625618550⟩, 69600297)))
 (.branch 120
 (.leaf (⟨2, 4, 204865, 82690, 288309671505, 361617786630⟩, 50594567))
 (.leaf (⟨2, 4, 204865, 82690, 283746268755, 361617754230⟩, 75105405))))
 (.branch 123
 (.branch 122
 (.leaf (⟨2, 4, 204865, 82690, 215026792020, 361617201270⟩, 82248938))
 (.leaf (⟨3, 4, 205840, 148240, 361742426640, 434925761040⟩, 123312315197861538455748714)))
 (.branch 124
 (.leaf (⟨3, 4, 205840, 148240, 361473991440, 434925741840⟩, 210356302395954653687840946))
 (.branch 125
 (.leaf (⟨3, 4, 205840, 148240, 283627709745, 434918463495⟩, 743500723984274984484405867))
 (.leaf (⟨3, 4, 205840, 148240, 141893788995, 434917935495⟩, 1195645879707703110828884961)))))))
 (.branch 135
 (.branch 130
 (.branch 128
 (.branch 127
 (.leaf (⟨2, 4, 135235, 66610, 361626105360, 361626105360⟩, 16253179))
 (.leaf (⟨2, 4, 135235, 66610, 361609328160, 361626104160⟩, 22020435)))
 (.branch 129
 (.leaf (⟨2, 4, 135235, 66610, 361592550945, 361626104070⟩, 34931224))
 (.leaf (⟨2, 4, 135235, 66610, 361340892720, 361626081120⟩, 27525543))))
 (.branch 132
 (.branch 131
 (.leaf (⟨2, 4, 135235, 66610, 361324115505, 361626081030⟩, 45154996))
 (.leaf (⟨2, 4, 135235, 66610, 356760712770, 361625649270⟩, 57803637)))
 (.branch 133
 (.leaf (⟨2, 4, 135235, 66610, 352465745475, 361625618550⟩, 69665834))
 (.branch 134
 (.leaf (⟨2, 4, 135235, 66610, 288309671505, 361617786630⟩, 50660104))
 (.leaf (⟨2, 4, 135235, 66610, 283746268755, 361617754230⟩, 75170942))))))
 (.branch 139
 (.branch 137
 (.branch 136
 (.leaf (⟨2, 4, 135235, 66610, 215026792020, 361617201270⟩, 82314475))
 (.leaf (⟨3, 4, 136240, 136240, 361742426640, 434925761040⟩, 124521259464501720611749995)))
 (.branch 138
 (.leaf (⟨3, 4, 136240, 136240, 361473991440, 434925741840⟩, 211565246662594835843842227))
 (.leaf (⟨3, 4, 136240, 136240, 283627709745, 434918463495⟩, 744709668250915166640407148))))
 (.branch 141
 (.branch 140
 (.leaf (⟨3, 4, 136240, 136240, 141893788995, 434917935495⟩, 1196854823974343292984886242))
 (.leaf (⟨3, 4, 132145, 136195, 361742426640, 434925761040⟩, 124521259464501720611749995)))
 (.branch 142
 (.leaf (⟨3, 4, 132145, 136195, 361473991440, 434925741840⟩, 211565246662594835843842227))
 (.branch 143
 (.leaf (⟨3, 4, 132145, 136195, 283627709745, 434918463495⟩, 744709668250915166640407148))
 (.leaf (⟨3, 4, 132145, 136195, 141893788995, 434917935495⟩, 1196854823974343292984886242))))))))))
cert_raw_3
cert_witness_3 8084
cert_faceTable_3 287
cert_faceWitness_3
cert_validity_3 5
cert_placement_3 5 02
cert_test_9
cert_symmetry_3 02
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T0
cert_check_3 0000 0000 0 0 1 1
cert_block_6 0000 0 1
cert_check_3 0001 0000 1 0 1 1
cert_block_6 0001 1 1
cert_check_3 0002 0000 2 0 1 1
cert_block_6 0002 2 1
cert_check_3 0003 0000 3 0 1 1
cert_block_6 0003 3 1
cert_check_3 0004 0000 4 0 1 1
cert_block_6 0004 4 1
cert_check_3 0005 0000 5 0 1 1
cert_block_6 0005 5 1
cert_check_3 0006 0000 6 0 1 1
cert_block_6 0006 6 1
cert_check_3 0007 0000 7 0 1 1
cert_block_6 0007 7 1
cert_check_3 0008 0000 8 0 1 1
cert_block_6 0008 8 1
cert_check_3 0009 0000 9 0 1 1
cert_block_6 0009 9 1
cert_check_3 0010 0000 10 0 1 1
cert_block_6 0010 10 1
cert_check_3 0011 0000 11 0 1 1
cert_block_6 0011 11 1
cert_check_3 0012 0000 12 0 2 2
cert_block_6 0012 12 2
cert_check_3 0013 0000 13 0 2 2
cert_block_6 0013 13 2
cert_check_3 0014 0000 14 0 2 2
cert_block_6 0014 14 2
cert_check_3 0015 0000 15 0 2 2
cert_block_6 0015 15 2
cert_check_3 0016 0000 16 0 2 2
cert_block_6 0016 16 2
cert_check_3 0017 0000 17 0 2 2
cert_block_6 0017 17 2
cert_check_3 0018 0000 18 0 2 2
cert_block_6 0018 18 2
cert_check_3 0019 0000 19 0 2 2
cert_block_6 0019 19 2
cert_check_3 0020 0000 20 0 2 2
cert_block_6 0020 20 2
cert_check_3 0021 0000 21 0 2 2
cert_block_6 0021 21 2
cert_check_3 0022 0000 22 0 1 1
cert_block_6 0022 22 1
cert_check_3 0023 0000 23 0 1 1
cert_block_6 0023 23 1
cert_check_3 0024 0000 24 0 1 1
cert_block_6 0024 24 1
cert_check_3 0025 0000 25 0 1 1
cert_block_6 0025 25 1
cert_check_3 0026 0000 26 0 1 1
cert_block_6 0026 26 1
cert_check_3 0027 0000 27 0 1 1
cert_block_6 0027 27 1
cert_check_3 0028 0000 28 0 2 2
cert_block_6 0028 28 2
cert_check_3 0029 0000 29 0 2 2
cert_block_6 0029 29 2
cert_check_3 0030 0000 30 0 2 2
cert_block_6 0030 30 2
cert_check_3 0031 0000 31 0 2 2
cert_block_6 0031 31 2
cert_check_3 0032 0000 32 0 2 2
cert_block_6 0032 32 2
cert_check_3 0033 0000 33 0 2 2
cert_block_6 0033 33 2
cert_check_3 0034 0000 34 0 2 2
cert_block_6 0034 34 2
cert_check_3 0035 0000 35 0 2 2
cert_block_6 0035 35 2
cert_check_3 0036 0000 36 0 2 2
cert_block_6 0036 36 2
cert_check_3 0037 0000 37 0 2 2
cert_block_6 0037 37 2
cert_check_3 0038 0000 38 0 2 2
cert_block_6 0038 38 2
cert_check_3 0039 0000 39 0 2 2
cert_block_6 0039 39 2
cert_check_3 0040 0000 40 0 2 2
cert_block_6 0040 40 2
cert_check_3 0041 0000 41 0 2 2
cert_block_6 0041 41 2
cert_check_3 0042 0000 42 0 2 2
cert_block_6 0042 42 2
cert_check_3 0043 0000 43 0 2 2
cert_block_6 0043 43 2
cert_check_3 0044 0000 44 0 2 2
cert_block_6 0044 44 2
cert_check_3 0045 0000 45 0 2 2
cert_block_6 0045 45 2
cert_check_3 0046 0000 46 0 2 2
cert_block_6 0046 46 2
cert_check_3 0047 0000 47 0 2 2
cert_block_6 0047 47 2
cert_check_3 0048 0000 48 0 6 6
cert_block_6 0048 48 6
cert_check_3 0049 0000 49 0 6 6
cert_block_6 0049 49 6
cert_check_3 0050 0000 50 0 6 6
cert_block_6 0050 50 6
cert_check_3 0051 0000 51 0 6 6
cert_block_6 0051 51 6
cert_check_3 0052 0000 52 0 1 1
cert_block_6 0052 52 1
cert_check_3 0053 0000 53 0 1 1
cert_block_6 0053 53 1
cert_check_3 0054 0000 54 0 1 1
cert_block_6 0054 54 1
cert_check_3 0055 0000 55 0 1 1
cert_block_6 0055 55 1
cert_check_3 0056 0000 56 0 1 1
cert_block_6 0056 56 1
cert_check_3 0057 0000 57 0 1 1
cert_block_6 0057 57 1
cert_check_3 0058 0000 58 0 2 2
cert_block_6 0058 58 2
cert_check_3 0059 0000 59 0 2 2
cert_block_6 0059 59 2
cert_check_3 0060 0000 60 0 2 2
cert_block_6 0060 60 2
cert_check_3 0061 0000 61 0 2 2
cert_block_6 0061 61 2
cert_check_3 0062 0000 62 0 2 2
cert_block_6 0062 62 2
cert_check_3 0063 0000 63 0 2 2
cert_block_6 0063 63 2
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T0
cert_check_3 0064 0000 64 0 2 2
cert_block_6 0064 64 2
cert_check_3 0065 0000 65 0 2 2
cert_block_6 0065 65 2
cert_check_3 0066 0000 66 0 2 2
cert_block_6 0066 66 2
cert_check_3 0067 0000 67 0 2 2
cert_block_6 0067 67 2
cert_check_3 0068 0000 68 0 2 2
cert_block_6 0068 68 2
cert_check_3 0069 0000 69 0 2 2
cert_block_6 0069 69 2
cert_check_3 0070 0000 70 0 2 2
cert_block_6 0070 70 2
cert_check_3 0071 0000 71 0 2 2
cert_block_6 0071 71 2
cert_check_3 0072 0000 72 0 2 2
cert_block_6 0072 72 2
cert_check_3 0073 0000 73 0 2 2
cert_block_6 0073 73 2
cert_check_3 0074 0000 74 0 2 2
cert_block_6 0074 74 2
cert_check_3 0075 0000 75 0 2 2
cert_block_6 0075 75 2
cert_check_3 0076 0000 76 0 2 2
cert_block_6 0076 76 2
cert_check_3 0077 0000 77 0 2 2
cert_block_6 0077 77 2
cert_check_3 0078 0000 78 0 2 2
cert_block_6 0078 78 2
cert_check_3 0079 0000 79 0 2 2
cert_block_6 0079 79 2
cert_check_3 0080 0000 80 0 2 2
cert_block_6 0080 80 2
cert_check_3 0081 0000 81 0 2 2
cert_block_6 0081 81 2
cert_check_3 0082 0000 82 0 2 2
cert_block_6 0082 82 2
cert_check_3 0083 0000 83 0 2 2
cert_block_6 0083 83 2
cert_check_3 0084 0000 84 0 2 2
cert_block_6 0084 84 2
cert_check_3 0085 0000 85 0 2 2
cert_block_6 0085 85 2
cert_check_3 0086 0000 86 0 2 2
cert_block_6 0086 86 2
cert_check_3 0087 0000 87 0 2 2
cert_block_6 0087 87 2
cert_check_3 0088 0000 88 0 6 6
cert_block_6 0088 88 6
cert_check_3 0089 0000 89 0 6 6
cert_block_6 0089 89 6
cert_check_3 0090 0000 90 0 6 6
cert_block_6 0090 90 6
cert_check_3 0091 0000 91 0 6 6
cert_block_6 0091 91 6
cert_check_3 0092 0000 92 0 6 6
cert_block_6 0092 92 6
cert_check_3 0093 0000 93 0 6 6
cert_block_6 0093 93 6
cert_check_3 0094 0000 94 0 6 6
cert_block_6 0094 94 6
cert_check_3 0095 0000 95 0 6 6
cert_block_6 0095 95 6
cert_check_3 0096 0000 96 0 1 1
cert_block_6 0096 96 1
cert_check_3 0097 0000 97 0 1 1
cert_block_6 0097 97 1
cert_check_3 0098 0000 98 0 1 1
cert_block_6 0098 98 1
cert_check_3 0099 0000 99 0 1 1
cert_block_6 0099 99 1
cert_check_3 0100 0000 100 0 1 1
cert_block_6 0100 100 1
cert_check_3 0101 0000 101 0 1 1
cert_block_6 0101 101 1
cert_check_3 0102 0000 102 0 2 2
cert_block_6 0102 102 2
cert_check_3 0103 0000 103 0 2 2
cert_block_6 0103 103 2
cert_check_3 0104 0000 104 0 2 2
cert_block_6 0104 104 2
cert_check_3 0105 0000 105 0 2 2
cert_block_6 0105 105 2
cert_check_3 0106 0000 106 0 2 2
cert_block_6 0106 106 2
cert_check_3 0107 0000 107 0 2 2
cert_block_6 0107 107 2
cert_check_3 0108 0000 108 0 2 2
cert_block_6 0108 108 2
cert_check_3 0109 0000 109 0 2 2
cert_block_6 0109 109 2
cert_check_3 0110 0000 110 0 2 2
cert_block_6 0110 110 2
cert_check_3 0111 0000 111 0 2 2
cert_block_6 0111 111 2
cert_check_3 0112 0000 112 0 2 2
cert_block_6 0112 112 2
cert_check_3 0113 0000 113 0 2 2
cert_block_6 0113 113 2
cert_check_3 0114 0000 114 0 2 2
cert_block_6 0114 114 2
cert_check_3 0115 0000 115 0 2 2
cert_block_6 0115 115 2
cert_check_3 0116 0000 116 0 2 2
cert_block_6 0116 116 2
cert_check_3 0117 0000 117 0 2 2
cert_block_6 0117 117 2
cert_check_3 0118 0000 118 0 2 2
cert_block_6 0118 118 2
cert_check_3 0119 0000 119 0 2 2
cert_block_6 0119 119 2
cert_check_3 0120 0000 120 0 2 2
cert_block_6 0120 120 2
cert_check_3 0121 0000 121 0 2 2
cert_block_6 0121 121 2
cert_check_3 0122 0000 122 0 6 6
cert_block_6 0122 122 6
cert_check_3 0123 0000 123 0 6 6
cert_block_6 0123 123 6
cert_check_3 0124 0000 124 0 6 6
cert_block_6 0124 124 6
cert_check_3 0125 0000 125 0 6 6
cert_block_6 0125 125 6
cert_check_3 0126 0000 126 0 2 2
cert_block_6 0126 126 2
cert_check_3 0127 0000 127 0 2 2
cert_block_6 0127 127 2
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T0
cert_check_3 0128 0000 128 0 2 2
cert_block_6 0128 128 2
cert_check_3 0129 0000 129 0 2 2
cert_block_6 0129 129 2
cert_check_3 0130 0000 130 0 2 2
cert_block_6 0130 130 2
cert_check_3 0131 0000 131 0 2 2
cert_block_6 0131 131 2
cert_check_3 0132 0000 132 0 2 2
cert_block_6 0132 132 2
cert_check_3 0133 0000 133 0 2 2
cert_block_6 0133 133 2
cert_check_3 0134 0000 134 0 2 2
cert_block_6 0134 134 2
cert_check_3 0135 0000 135 0 2 2
cert_block_6 0135 135 2
cert_check_3 0136 0000 136 0 6 6
cert_block_6 0136 136 6
cert_check_3 0137 0000 137 0 6 6
cert_block_6 0137 137 6
cert_check_3 0138 0000 138 0 6 6
cert_block_6 0138 138 6
cert_check_3 0139 0000 139 0 6 6
cert_block_6 0139 139 6
cert_check_3 0140 0000 140 0 6 6
cert_block_6 0140 140 6
cert_check_3 0141 0000 141 0 6 6
cert_block_6 0141 141 6
cert_check_3 0142 0000 142 0 6 6
cert_block_6 0142 142 6
cert_check_3 0143 0000 143 0 6 6
cert_block_6 0143 143 6
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T0
cert_metadata_validity_11 0000 0 16 16
cert_metadata_validity_11 0016 16 32 16
cert_metadata_validity_11 0032 32 48 16
cert_metadata_validity_11 0048 48 64 16
cert_metadata_validity_11 0064 64 80 16
cert_metadata_validity_11 0080 80 96 16
cert_metadata_validity_11 0096 96 112 16
cert_metadata_validity_11 0112 112 128 16
cert_metadata_validity_11 0128 128 144 16
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 64 144
  (FiniteChecks.interval_append (validity) 0 32 64
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 64
  metadata_validity_0032
  metadata_validity_0048))
  (FiniteChecks.interval_append (validity) 64 96 144
  (FiniteChecks.interval_append (validity) 64 80 96
  metadata_validity_0064
  metadata_validity_0080)
  (FiniteChecks.interval_append (validity) 96 112 144
  metadata_validity_0096
  (FiniteChecks.interval_append (validity) 112 128 144
  metadata_validity_0112
  metadata_validity_0128))))
cert_metadata_symmetry_11 0000 0 16 16
cert_metadata_symmetry_11 0016 16 32 16
cert_metadata_symmetry_11 0032 32 48 16
cert_metadata_symmetry_11 0048 48 64 16
cert_metadata_symmetry_11 0064 64 80 16
cert_metadata_symmetry_11 0080 80 96 16
cert_metadata_symmetry_11 0096 96 112 16
cert_metadata_symmetry_11 0112 112 128 16
cert_metadata_symmetry_11 0128 128 144 16
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 64 144
  (FiniteChecks.interval_append (symmetry) 0 32 64
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 64
  metadata_symmetry_0032
  metadata_symmetry_0048))
  (FiniteChecks.interval_append (symmetry) 64 96 144
  (FiniteChecks.interval_append (symmetry) 64 80 96
  metadata_symmetry_0064
  metadata_symmetry_0080)
  (FiniteChecks.interval_append (symmetry) 96 112 144
  metadata_symmetry_0096
  (FiniteChecks.interval_append (symmetry) 112 128 144
  metadata_symmetry_0112
  metadata_symmetry_0128))))
cert_metadata_normalizers_3 5
cert_metadata_root_3
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.S5T0
