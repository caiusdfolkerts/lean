module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public meta import CertificateNumbers
public import HexNatLiteral
public import RootedSevenPure032GrowthCacheData
public import IdentityRawMaps
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0066
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 461
abbrev nodeCount : Nat := 4700
abbrev leafCount : Nat := 162
cert_widths_2 9 13 8
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))
 (.branch 3
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩)
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩))
 (.branch 7
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩)
 (.branch 8
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩))
 (.branch 12
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩)
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩))
 (.branch 16
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)
 (.branch 17
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩)
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩)
 (.leaf ⟨(certNat% 38),(certNat% 39)⟩))
 (.branch 21
 (.leaf ⟨(certNat% 40),(certNat% 41)⟩)
 (.leaf ⟨(certNat% 42),(certNat% 43)⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(certNat% 44),(certNat% 45)⟩)
 (.leaf ⟨(certNat% 46),(certNat% 47)⟩))
 (.branch 25
 (.leaf ⟨(certNat% 48),(certNat% 49)⟩)
 (.branch 26
 (.leaf ⟨(certNat% 50),(certNat% 51)⟩)
 (.leaf ⟨(certNat% 52),(certNat% 53)⟩)))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf ⟨(certNat% 54),(certNat% 55)⟩)
 (.leaf ⟨(certNat% 56),(certNat% 57)⟩))
 (.branch 30
 (.leaf ⟨(certNat% 58),(certNat% 59)⟩)
 (.branch 31
 (.leaf ⟨(certNat% 60),(certNat% 61)⟩)
 (.leaf ⟨(certNat% 62),(certNat% 63)⟩))))
 (.branch 34
 (.branch 33
 (.leaf ⟨(certNat% 64),(certNat% 65)⟩)
 (.leaf ⟨(certNat% 66),(certNat% 67)⟩))
 (.branch 35
 (.leaf ⟨(certNat% 68),(certNat% 69)⟩)
 (.branch 36
 (.leaf ⟨(certNat% 70),(certNat% 71)⟩)
 (.leaf ⟨(certNat% 72),(certNat% 73)⟩)))))))
def counterTable : Table Nat :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 74))
 (.leaf (certNat% 75)))
 (.branch 3
 (.leaf (certNat% 76))
 (.leaf (certNat% 77))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 78))
 (.leaf (certNat% 79)))
 (.branch 7
 (.leaf (certNat% 80))
 (.branch 8
 (.leaf (certNat% 81))
 (.leaf (certNat% 82))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (certNat% 83))
 (.leaf (certNat% 84)))
 (.branch 12
 (.leaf (certNat% 85))
 (.leaf (certNat% 86))))
 (.branch 15
 (.branch 14
 (.leaf (certNat% 87))
 (.leaf (certNat% 88)))
 (.branch 16
 (.leaf (certNat% 89))
 (.branch 17
 (.leaf (certNat% 90))
 (.leaf (certNat% 91)))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf (certNat% 92))
 (.leaf (certNat% 93)))
 (.branch 21
 (.leaf (certNat% 94))
 (.leaf (certNat% 95))))
 (.branch 24
 (.branch 23
 (.leaf (certNat% 96))
 (.leaf (certNat% 97)))
 (.branch 25
 (.leaf (certNat% 98))
 (.branch 26
 (.leaf (certNat% 99))
 (.leaf (certNat% 100))))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf (certNat% 101))
 (.leaf (certNat% 102)))
 (.branch 30
 (.leaf (certNat% 103))
 (.branch 31
 (.leaf (certNat% 104))
 (.leaf (certNat% 105)))))
 (.branch 34
 (.branch 33
 (.leaf (certNat% 106))
 (.leaf (certNat% 107)))
 (.branch 35
 (.leaf (certNat% 108))
 (.branch 36
 (.leaf (certNat% 109))
 (.leaf (certNat% 110))))))))
cert_codes_2
cert_counters_2
cert_rawNodes_2
def leafTable : Table Nat :=
(.branch 81
 (.branch 40
 (.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (certNat% 111))
 (.leaf (certNat% 112)))
 (.branch 3
 (.leaf (certNat% 113))
 (.branch 4
 (.leaf (certNat% 114))
 (.leaf (certNat% 115)))))
 (.branch 7
 (.branch 6
 (.leaf (certNat% 116))
 (.leaf (certNat% 117)))
 (.branch 8
 (.leaf (certNat% 118))
 (.branch 9
 (.leaf (certNat% 119))
 (.leaf (certNat% 120))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (certNat% 121))
 (.leaf (certNat% 122)))
 (.branch 13
 (.leaf (certNat% 123))
 (.branch 14
 (.leaf (certNat% 124))
 (.leaf (certNat% 125)))))
 (.branch 17
 (.branch 16
 (.leaf (certNat% 126))
 (.leaf (certNat% 127)))
 (.branch 18
 (.leaf (certNat% 128))
 (.branch 19
 (.leaf (certNat% 129))
 (.leaf (certNat% 130)))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf (certNat% 131))
 (.leaf (certNat% 132)))
 (.branch 23
 (.leaf (certNat% 133))
 (.branch 24
 (.leaf (certNat% 134))
 (.leaf (certNat% 135)))))
 (.branch 27
 (.branch 26
 (.leaf (certNat% 136))
 (.leaf (certNat% 137)))
 (.branch 28
 (.leaf (certNat% 138))
 (.branch 29
 (.leaf (certNat% 139))
 (.leaf (certNat% 140))))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf (certNat% 141))
 (.leaf (certNat% 142)))
 (.branch 33
 (.leaf (certNat% 143))
 (.branch 34
 (.leaf (certNat% 144))
 (.leaf (certNat% 145)))))
 (.branch 37
 (.branch 36
 (.leaf (certNat% 146))
 (.leaf (certNat% 147)))
 (.branch 38
 (.leaf (certNat% 148))
 (.branch 39
 (.leaf (certNat% 149))
 (.leaf (certNat% 150))))))))
 (.branch 60
 (.branch 50
 (.branch 45
 (.branch 42
 (.branch 41
 (.leaf (certNat% 151))
 (.leaf (certNat% 152)))
 (.branch 43
 (.leaf (certNat% 153))
 (.branch 44
 (.leaf (certNat% 154))
 (.leaf (certNat% 155)))))
 (.branch 47
 (.branch 46
 (.leaf (certNat% 156))
 (.leaf (certNat% 157)))
 (.branch 48
 (.leaf (certNat% 158))
 (.branch 49
 (.leaf (certNat% 159))
 (.leaf (certNat% 160))))))
 (.branch 55
 (.branch 52
 (.branch 51
 (.leaf (certNat% 161))
 (.leaf (certNat% 162)))
 (.branch 53
 (.leaf (certNat% 163))
 (.branch 54
 (.leaf (certNat% 164))
 (.leaf (certNat% 165)))))
 (.branch 57
 (.branch 56
 (.leaf (certNat% 166))
 (.leaf (certNat% 167)))
 (.branch 58
 (.leaf (certNat% 168))
 (.branch 59
 (.leaf (certNat% 169))
 (.leaf (certNat% 170)))))))
 (.branch 70
 (.branch 65
 (.branch 62
 (.branch 61
 (.leaf (certNat% 171))
 (.leaf (certNat% 172)))
 (.branch 63
 (.leaf (certNat% 173))
 (.branch 64
 (.leaf (certNat% 174))
 (.leaf (certNat% 175)))))
 (.branch 67
 (.branch 66
 (.leaf (certNat% 176))
 (.leaf (certNat% 177)))
 (.branch 68
 (.leaf (certNat% 178))
 (.branch 69
 (.leaf (certNat% 179))
 (.leaf (certNat% 180))))))
 (.branch 75
 (.branch 72
 (.branch 71
 (.leaf (certNat% 181))
 (.leaf (certNat% 182)))
 (.branch 73
 (.leaf (certNat% 183))
 (.branch 74
 (.leaf (certNat% 184))
 (.leaf (certNat% 185)))))
 (.branch 78
 (.branch 76
 (.leaf (certNat% 186))
 (.branch 77
 (.leaf (certNat% 187))
 (.leaf (certNat% 188))))
 (.branch 79
 (.leaf (certNat% 189))
 (.branch 80
 (.leaf (certNat% 190))
 (.leaf (certNat% 191)))))))))
 (.branch 121
 (.branch 101
 (.branch 91
 (.branch 86
 (.branch 83
 (.branch 82
 (.leaf (certNat% 192))
 (.leaf (certNat% 193)))
 (.branch 84
 (.leaf (certNat% 194))
 (.branch 85
 (.leaf (certNat% 195))
 (.leaf (certNat% 196)))))
 (.branch 88
 (.branch 87
 (.leaf (certNat% 197))
 (.leaf (certNat% 198)))
 (.branch 89
 (.leaf (certNat% 199))
 (.branch 90
 (.leaf (certNat% 200))
 (.leaf (certNat% 201))))))
 (.branch 96
 (.branch 93
 (.branch 92
 (.leaf (certNat% 202))
 (.leaf (certNat% 203)))
 (.branch 94
 (.leaf (certNat% 204))
 (.branch 95
 (.leaf (certNat% 205))
 (.leaf (certNat% 206)))))
 (.branch 98
 (.branch 97
 (.leaf (certNat% 207))
 (.leaf (certNat% 208)))
 (.branch 99
 (.leaf (certNat% 209))
 (.branch 100
 (.leaf (certNat% 210))
 (.leaf (certNat% 211)))))))
 (.branch 111
 (.branch 106
 (.branch 103
 (.branch 102
 (.leaf (certNat% 212))
 (.leaf (certNat% 213)))
 (.branch 104
 (.leaf (certNat% 214))
 (.branch 105
 (.leaf (certNat% 215))
 (.leaf (certNat% 216)))))
 (.branch 108
 (.branch 107
 (.leaf (certNat% 217))
 (.leaf (certNat% 218)))
 (.branch 109
 (.leaf (certNat% 219))
 (.branch 110
 (.leaf (certNat% 220))
 (.leaf (certNat% 221))))))
 (.branch 116
 (.branch 113
 (.branch 112
 (.leaf (certNat% 222))
 (.leaf (certNat% 223)))
 (.branch 114
 (.leaf (certNat% 224))
 (.branch 115
 (.leaf (certNat% 225))
 (.leaf (certNat% 226)))))
 (.branch 118
 (.branch 117
 (.leaf (certNat% 227))
 (.leaf (certNat% 228)))
 (.branch 119
 (.leaf (certNat% 229))
 (.branch 120
 (.leaf (certNat% 230))
 (.leaf (certNat% 231))))))))
 (.branch 141
 (.branch 131
 (.branch 126
 (.branch 123
 (.branch 122
 (.leaf (certNat% 232))
 (.leaf (certNat% 233)))
 (.branch 124
 (.leaf (certNat% 234))
 (.branch 125
 (.leaf (certNat% 235))
 (.leaf (certNat% 236)))))
 (.branch 128
 (.branch 127
 (.leaf (certNat% 237))
 (.leaf (certNat% 238)))
 (.branch 129
 (.leaf (certNat% 239))
 (.branch 130
 (.leaf (certNat% 240))
 (.leaf (certNat% 241))))))
 (.branch 136
 (.branch 133
 (.branch 132
 (.leaf (certNat% 242))
 (.leaf (certNat% 243)))
 (.branch 134
 (.leaf (certNat% 244))
 (.branch 135
 (.leaf (certNat% 245))
 (.leaf (certNat% 246)))))
 (.branch 138
 (.branch 137
 (.leaf (certNat% 247))
 (.leaf (certNat% 248)))
 (.branch 139
 (.leaf (certNat% 249))
 (.branch 140
 (.leaf (certNat% 250))
 (.leaf (certNat% 251)))))))
 (.branch 151
 (.branch 146
 (.branch 143
 (.branch 142
 (.leaf (certNat% 252))
 (.leaf (certNat% 253)))
 (.branch 144
 (.leaf (certNat% 254))
 (.branch 145
 (.leaf (certNat% 255))
 (.leaf (certNat% 256)))))
 (.branch 148
 (.branch 147
 (.leaf (certNat% 257))
 (.leaf (certNat% 258)))
 (.branch 149
 (.leaf (certNat% 259))
 (.branch 150
 (.leaf (certNat% 260))
 (.leaf (certNat% 261))))))
 (.branch 156
 (.branch 153
 (.branch 152
 (.leaf (certNat% 262))
 (.leaf (certNat% 263)))
 (.branch 154
 (.leaf (certNat% 264))
 (.branch 155
 (.leaf (certNat% 265))
 (.leaf (certNat% 266)))))
 (.branch 159
 (.branch 157
 (.leaf (certNat% 267))
 (.branch 158
 (.leaf (certNat% 268))
 (.leaf (certNat% 269))))
 (.branch 160
 (.leaf (certNat% 270))
 (.branch 161
 (.leaf (certNat% 271))
 (.leaf (certNat% 272))))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 9 (PackedRawNatGrowth.take 5 code)
    (PackedRawNatGrowth.drop 5 code)).1

cert_leaves_2
cert_quota_2 2 0 4 5
cert_nodeTest_2 032
cert_nodeTest_sound_2 032
cert_leafTest_2 032
end Papers.RationalityTen.RootedForests.RootedRawForest0066
