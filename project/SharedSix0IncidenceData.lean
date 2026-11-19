module
prelude
public meta import CertificateNumbers
public import SharedPoolIncidence
public import SharedSix0CellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
def vertexTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 0) (Nat.shiftLeft (certNat% 1) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 2) (Nat.shiftLeft (Nat.lor (certNat% 3) (Nat.shiftLeft (certNat% 4) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 5) (Nat.shiftLeft (Nat.lor (certNat% 6) (Nat.shiftLeft (certNat% 7) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 8) (Nat.shiftLeft (Nat.lor (certNat% 9) (Nat.shiftLeft (certNat% 10) 4096)) 4096)) 12288)) 20480)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 11) (Nat.shiftLeft (certNat% 12) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 13) (Nat.shiftLeft (Nat.lor (certNat% 14) (Nat.shiftLeft (certNat% 15) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 16) (Nat.shiftLeft (Nat.lor (certNat% 17) (Nat.shiftLeft (certNat% 18) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 19) (Nat.shiftLeft (Nat.lor (certNat% 20) (Nat.shiftLeft (certNat% 21) 4096)) 4096)) 12288)) 20480))))
 (.branch 3
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 22) (Nat.shiftLeft (certNat% 23) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 24) (Nat.shiftLeft (Nat.lor (certNat% 25) (Nat.shiftLeft (certNat% 26) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 27) (Nat.shiftLeft (Nat.lor (certNat% 28) (Nat.shiftLeft (certNat% 29) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 30) (Nat.shiftLeft (Nat.lor (certNat% 31) (Nat.shiftLeft (certNat% 32) 4096)) 4096)) 12288)) 20480)))
 (.branch 4
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 33) (Nat.shiftLeft (certNat% 34) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 35) (Nat.shiftLeft (Nat.lor (certNat% 36) (Nat.shiftLeft (certNat% 37) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 38) (Nat.shiftLeft (Nat.lor (certNat% 39) (Nat.shiftLeft (certNat% 40) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 41) (Nat.shiftLeft (Nat.lor (certNat% 42) (Nat.shiftLeft (certNat% 43) 4096)) 4096)) 12288)) 20480)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 44) (Nat.shiftLeft (certNat% 45) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 46) (Nat.shiftLeft (Nat.lor (certNat% 47) (Nat.shiftLeft (certNat% 48) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 49) (Nat.shiftLeft (Nat.lor (certNat% 50) (Nat.shiftLeft (certNat% 51) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 52) (Nat.shiftLeft (Nat.lor (certNat% 53) (Nat.shiftLeft (certNat% 54) 4096)) 4096)) 12288)) 20480))))))
 (.branch 7
 (.branch 6
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 55) (Nat.shiftLeft (certNat% 56) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 57) (Nat.shiftLeft (Nat.lor (certNat% 58) (Nat.shiftLeft (certNat% 59) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 60) (Nat.shiftLeft (Nat.lor (certNat% 61) (Nat.shiftLeft (certNat% 62) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 63) (Nat.shiftLeft (Nat.lor (certNat% 64) (Nat.shiftLeft (certNat% 65) 4096)) 4096)) 12288)) 20480)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 66) (Nat.shiftLeft (certNat% 67) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 68) (Nat.shiftLeft (Nat.lor (certNat% 69) (Nat.shiftLeft (certNat% 70) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 71) (Nat.shiftLeft (Nat.lor (certNat% 72) (Nat.shiftLeft (certNat% 73) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 74) (Nat.shiftLeft (Nat.lor (certNat% 75) (Nat.shiftLeft (certNat% 76) 4096)) 4096)) 12288)) 20480))))
 (.branch 8
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 77) (Nat.shiftLeft (certNat% 78) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 79) (Nat.shiftLeft (Nat.lor (certNat% 80) (Nat.shiftLeft (certNat% 81) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 82) (Nat.shiftLeft (certNat% 83) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 73) (Nat.shiftLeft (Nat.lor (certNat% 84) (Nat.shiftLeft (certNat% 85) 4096)) 8192)) 8192)) 20480)))
 (.branch 9
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 86) (Nat.shiftLeft (certNat% 87) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 88) (Nat.shiftLeft (Nat.lor (certNat% 81) (Nat.shiftLeft (certNat% 81) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 82) (Nat.shiftLeft (certNat% 89) 8192)) (Nat.shiftLeft (Nat.lor (certNat% 81) (Nat.shiftLeft (Nat.lor (certNat% 81) (Nat.shiftLeft (certNat% 85) 4096)) 4096)) 12288)) 20480)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 90) (Nat.shiftLeft (certNat% 91) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 92) (Nat.shiftLeft (certNat% 81) 4096)) 20480)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 81) (Nat.shiftLeft (certNat% 81) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 81) (Nat.shiftLeft (certNat% 85) 4096)) 8192)) 28672)))))))
def edgeTable : Table Nat :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 93) (Nat.shiftLeft (certNat% 94) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 95) (Nat.shiftLeft (Nat.lor (certNat% 96) (Nat.shiftLeft (certNat% 97) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 98) (Nat.shiftLeft (Nat.lor (certNat% 99) (Nat.shiftLeft (certNat% 100) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 101) (Nat.shiftLeft (Nat.lor (certNat% 102) (Nat.shiftLeft (certNat% 103) 4096)) 4096)) 12288)) 20480)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 104) (Nat.shiftLeft (certNat% 105) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 106) (Nat.shiftLeft (Nat.lor (certNat% 107) (Nat.shiftLeft (certNat% 108) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 109) (Nat.shiftLeft (Nat.lor (certNat% 110) (Nat.shiftLeft (certNat% 111) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 112) (Nat.shiftLeft (Nat.lor (certNat% 113) (Nat.shiftLeft (certNat% 114) 4096)) 4096)) 12288)) 20480))))
 (.branch 3
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 115) (Nat.shiftLeft (certNat% 116) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 117) (Nat.shiftLeft (Nat.lor (certNat% 118) (Nat.shiftLeft (certNat% 119) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 120) (Nat.shiftLeft (Nat.lor (certNat% 121) (Nat.shiftLeft (certNat% 122) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 123) (Nat.shiftLeft (Nat.lor (certNat% 124) (Nat.shiftLeft (certNat% 125) 4096)) 4096)) 12288)) 20480)))
 (.branch 4
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 126) (Nat.shiftLeft (certNat% 127) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 128) (Nat.shiftLeft (Nat.lor (certNat% 129) (Nat.shiftLeft (certNat% 130) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 131) (Nat.shiftLeft (Nat.lor (certNat% 132) (Nat.shiftLeft (certNat% 133) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 134) (Nat.shiftLeft (Nat.lor (certNat% 135) (Nat.shiftLeft (certNat% 136) 4096)) 4096)) 12288)) 20480)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 137) (Nat.shiftLeft (certNat% 138) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 139) (Nat.shiftLeft (Nat.lor (certNat% 140) (Nat.shiftLeft (certNat% 141) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 142) (Nat.shiftLeft (Nat.lor (certNat% 143) (Nat.shiftLeft (certNat% 144) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 145) (Nat.shiftLeft (Nat.lor (certNat% 146) (Nat.shiftLeft (certNat% 147) 4096)) 4096)) 12288)) 20480))))))
 (.branch 8
 (.branch 6
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 148) (Nat.shiftLeft (certNat% 149) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 150) (Nat.shiftLeft (Nat.lor (certNat% 151) (Nat.shiftLeft (certNat% 152) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 153) (Nat.shiftLeft (Nat.lor (certNat% 154) (Nat.shiftLeft (certNat% 155) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 156) (Nat.shiftLeft (Nat.lor (certNat% 157) (Nat.shiftLeft (certNat% 158) 4096)) 4096)) 12288)) 20480)))
 (.branch 7
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 159) (Nat.shiftLeft (certNat% 160) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 161) (Nat.shiftLeft (Nat.lor (certNat% 162) (Nat.shiftLeft (certNat% 163) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 164) (Nat.shiftLeft (certNat% 165) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 166) (Nat.shiftLeft (Nat.lor (certNat% 167) (Nat.shiftLeft (certNat% 168) 4096)) 8192)) 8192)) 20480)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 169) (Nat.shiftLeft (certNat% 170) 8192)) (Nat.shiftLeft (Nat.lor (certNat% 171) (Nat.shiftLeft (certNat% 172) 4096)) 12288)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 173) (Nat.shiftLeft (certNat% 174) 8192)) (Nat.shiftLeft (Nat.lor (certNat% 175) (Nat.shiftLeft (Nat.lor (certNat% 176) (Nat.shiftLeft (certNat% 177) 4096)) 4096)) 12288)) 20480)))))
 (.branch 9
 (.leaf (Nat.lor (Nat.lor (certNat% 178) (Nat.shiftLeft (Nat.lor (certNat% 179) (Nat.shiftLeft (certNat% 180) 4096)) 20480)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 181) (Nat.shiftLeft (certNat% 182) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 183) (Nat.shiftLeft (certNat% 184) 4096)) 8192)) 28672)))
 (.branch 10
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 185) (Nat.shiftLeft (certNat% 186) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 187) (Nat.shiftLeft (Nat.lor (certNat% 188) (Nat.shiftLeft (certNat% 189) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 190) (Nat.shiftLeft (Nat.lor (certNat% 191) (Nat.shiftLeft (certNat% 192) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 193) (Nat.shiftLeft (Nat.lor (certNat% 194) (Nat.shiftLeft (certNat% 195) 4096)) 4096)) 12288)) 20480)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 196) (Nat.shiftLeft (certNat% 197) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 198) (Nat.shiftLeft (Nat.lor (certNat% 199) (Nat.shiftLeft (certNat% 200) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 201) (Nat.shiftLeft (Nat.lor (certNat% 202) (Nat.shiftLeft (certNat% 203) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 204) (Nat.shiftLeft (Nat.lor (certNat% 205) (Nat.shiftLeft (certNat% 206) 4096)) 4096)) 12288)) 20480)))))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 207) (Nat.shiftLeft (certNat% 208) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 209) (Nat.shiftLeft (Nat.lor (certNat% 210) (Nat.shiftLeft (certNat% 211) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 212) (Nat.shiftLeft (Nat.lor (certNat% 213) (Nat.shiftLeft (certNat% 214) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 215) (Nat.shiftLeft (Nat.lor (certNat% 216) (Nat.shiftLeft (certNat% 217) 4096)) 4096)) 12288)) 20480)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 218) (Nat.shiftLeft (certNat% 219) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 220) (Nat.shiftLeft (Nat.lor (certNat% 221) (Nat.shiftLeft (certNat% 222) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 223) (Nat.shiftLeft (Nat.lor (certNat% 224) (Nat.shiftLeft (certNat% 225) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 226) (Nat.shiftLeft (Nat.lor (certNat% 227) (Nat.shiftLeft (certNat% 228) 4096)) 4096)) 12288)) 20480))))
 (.branch 14
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 229) (Nat.shiftLeft (certNat% 230) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 231) (Nat.shiftLeft (Nat.lor (certNat% 232) (Nat.shiftLeft (certNat% 233) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 234) (Nat.shiftLeft (Nat.lor (certNat% 235) (Nat.shiftLeft (certNat% 236) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 237) (Nat.shiftLeft (Nat.lor (certNat% 238) (Nat.shiftLeft (certNat% 239) 4096)) 4096)) 12288)) 20480)))
 (.branch 15
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 240) (Nat.shiftLeft (certNat% 241) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 242) (Nat.shiftLeft (Nat.lor (certNat% 243) (Nat.shiftLeft (certNat% 244) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 245) (Nat.shiftLeft (certNat% 246) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 247) (Nat.shiftLeft (Nat.lor (certNat% 248) (Nat.shiftLeft (certNat% 249) 4096)) 8192)) 8192)) 20480)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 250) (Nat.shiftLeft (certNat% 251) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 252) (Nat.shiftLeft (Nat.lor (certNat% 253) (Nat.shiftLeft (certNat% 254) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 255) (Nat.shiftLeft (certNat% 256) 8192)) (Nat.shiftLeft (Nat.lor (certNat% 257) (Nat.shiftLeft (Nat.lor (certNat% 258) (Nat.shiftLeft (certNat% 259) 4096)) 4096)) 12288)) 20480))))))
 (.branch 19
 (.branch 17
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 260) (Nat.shiftLeft (certNat% 261) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 262) (Nat.shiftLeft (certNat% 263) 4096)) 20480)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 264) (Nat.shiftLeft (certNat% 265) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 266) (Nat.shiftLeft (certNat% 267) 4096)) 8192)) 28672)))
 (.branch 18
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 268) (Nat.shiftLeft (certNat% 269) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 270) (Nat.shiftLeft (Nat.lor (certNat% 271) (Nat.shiftLeft (certNat% 272) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 273) (Nat.shiftLeft (Nat.lor (certNat% 274) (Nat.shiftLeft (certNat% 275) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 276) (Nat.shiftLeft (Nat.lor (certNat% 277) (Nat.shiftLeft (certNat% 278) 4096)) 4096)) 12288)) 20480)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 279) (Nat.shiftLeft (certNat% 280) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 281) (Nat.shiftLeft (Nat.lor (certNat% 282) (Nat.shiftLeft (certNat% 283) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 284) (Nat.shiftLeft (Nat.lor (certNat% 285) (Nat.shiftLeft (certNat% 286) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 287) (Nat.shiftLeft (Nat.lor (certNat% 288) (Nat.shiftLeft (certNat% 289) 4096)) 4096)) 12288)) 20480)))))
 (.branch 20
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 290) (Nat.shiftLeft (certNat% 291) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 292) (Nat.shiftLeft (Nat.lor (certNat% 293) (Nat.shiftLeft (certNat% 294) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 295) (Nat.shiftLeft (Nat.lor (certNat% 296) (Nat.shiftLeft (certNat% 297) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 298) (Nat.shiftLeft (Nat.lor (certNat% 299) (Nat.shiftLeft (certNat% 300) 4096)) 4096)) 12288)) 20480)))
 (.branch 21
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 301) (Nat.shiftLeft (certNat% 302) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 303) (Nat.shiftLeft (Nat.lor (certNat% 304) (Nat.shiftLeft (certNat% 305) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 306) (Nat.shiftLeft (Nat.lor (certNat% 307) (Nat.shiftLeft (certNat% 308) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 309) (Nat.shiftLeft (Nat.lor (certNat% 310) (Nat.shiftLeft (certNat% 311) 4096)) 4096)) 12288)) 20480)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 312) (Nat.shiftLeft (certNat% 313) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 314) (Nat.shiftLeft (Nat.lor (certNat% 315) (Nat.shiftLeft (certNat% 316) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 317) (Nat.shiftLeft (certNat% 318) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 319) (Nat.shiftLeft (Nat.lor (certNat% 320) (Nat.shiftLeft (certNat% 321) 4096)) 8192)) 8192)) 20480))))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 322) (Nat.shiftLeft (certNat% 323) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 324) (Nat.shiftLeft (Nat.lor (certNat% 325) (Nat.shiftLeft (certNat% 326) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 327) (Nat.shiftLeft (certNat% 328) 8192)) (Nat.shiftLeft (Nat.lor (certNat% 329) (Nat.shiftLeft (Nat.lor (certNat% 330) (Nat.shiftLeft (certNat% 331) 4096)) 4096)) 12288)) 20480)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 332) (Nat.shiftLeft (certNat% 333) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 334) (Nat.shiftLeft (certNat% 335) 4096)) 20480)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 336) (Nat.shiftLeft (certNat% 337) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 338) (Nat.shiftLeft (certNat% 339) 4096)) 8192)) 28672))))
 (.branch 25
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 340) (Nat.shiftLeft (certNat% 341) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 342) (Nat.shiftLeft (Nat.lor (certNat% 343) (Nat.shiftLeft (certNat% 344) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 345) (Nat.shiftLeft (Nat.lor (certNat% 346) (Nat.shiftLeft (certNat% 347) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 348) (Nat.shiftLeft (Nat.lor (certNat% 349) (Nat.shiftLeft (certNat% 350) 4096)) 4096)) 12288)) 20480)))
 (.branch 26
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 351) (Nat.shiftLeft (certNat% 352) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 353) (Nat.shiftLeft (Nat.lor (certNat% 354) (Nat.shiftLeft (certNat% 355) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 356) (Nat.shiftLeft (Nat.lor (certNat% 357) (Nat.shiftLeft (certNat% 358) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 359) (Nat.shiftLeft (Nat.lor (certNat% 360) (Nat.shiftLeft (certNat% 361) 4096)) 4096)) 12288)) 20480)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 362) (Nat.shiftLeft (certNat% 363) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 364) (Nat.shiftLeft (Nat.lor (certNat% 365) (Nat.shiftLeft (certNat% 366) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 367) (Nat.shiftLeft (Nat.lor (certNat% 368) (Nat.shiftLeft (certNat% 369) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 370) (Nat.shiftLeft (Nat.lor (certNat% 371) (Nat.shiftLeft (certNat% 372) 4096)) 4096)) 12288)) 20480))))))
 (.branch 30
 (.branch 28
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 373) (Nat.shiftLeft (certNat% 374) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 375) (Nat.shiftLeft (Nat.lor (certNat% 376) (Nat.shiftLeft (certNat% 377) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 378) (Nat.shiftLeft (certNat% 379) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 380) (Nat.shiftLeft (Nat.lor (certNat% 381) (Nat.shiftLeft (certNat% 382) 4096)) 8192)) 8192)) 20480)))
 (.branch 29
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 383) (Nat.shiftLeft (certNat% 384) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 385) (Nat.shiftLeft (Nat.lor (certNat% 386) (Nat.shiftLeft (certNat% 387) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 388) (Nat.shiftLeft (certNat% 389) 8192)) (Nat.shiftLeft (Nat.lor (certNat% 390) (Nat.shiftLeft (Nat.lor (certNat% 391) (Nat.shiftLeft (certNat% 392) 4096)) 4096)) 12288)) 20480)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 393) (Nat.shiftLeft (certNat% 394) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 395) (Nat.shiftLeft (certNat% 396) 4096)) 20480)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 397) (Nat.shiftLeft (certNat% 398) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 399) (Nat.shiftLeft (certNat% 400) 4096)) 8192)) 28672)))))
 (.branch 31
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 401) (Nat.shiftLeft (certNat% 402) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 403) (Nat.shiftLeft (Nat.lor (certNat% 404) (Nat.shiftLeft (certNat% 405) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 406) (Nat.shiftLeft (Nat.lor (certNat% 407) (Nat.shiftLeft (certNat% 408) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 409) (Nat.shiftLeft (Nat.lor (certNat% 410) (Nat.shiftLeft (certNat% 411) 4096)) 4096)) 12288)) 20480)))
 (.branch 32
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 412) (Nat.shiftLeft (certNat% 413) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 414) (Nat.shiftLeft (Nat.lor (certNat% 415) (Nat.shiftLeft (certNat% 416) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 417) (Nat.shiftLeft (Nat.lor (certNat% 418) (Nat.shiftLeft (certNat% 419) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 420) (Nat.shiftLeft (Nat.lor (certNat% 421) (Nat.shiftLeft (certNat% 422) 4096)) 4096)) 12288)) 20480)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 423) (Nat.shiftLeft (certNat% 424) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 425) (Nat.shiftLeft (Nat.lor (certNat% 426) (Nat.shiftLeft (certNat% 427) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 428) (Nat.shiftLeft (certNat% 429) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 430) (Nat.shiftLeft (Nat.lor (certNat% 431) (Nat.shiftLeft (certNat% 432) 4096)) 8192)) 8192)) 20480)))))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 433) (Nat.shiftLeft (certNat% 434) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 435) (Nat.shiftLeft (Nat.lor (certNat% 436) (Nat.shiftLeft (certNat% 437) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 438) (Nat.shiftLeft (certNat% 439) 8192)) (Nat.shiftLeft (Nat.lor (certNat% 440) (Nat.shiftLeft (Nat.lor (certNat% 441) (Nat.shiftLeft (certNat% 442) 4096)) 4096)) 12288)) 20480)))
 (.branch 35
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 443) (Nat.shiftLeft (certNat% 444) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 445) (Nat.shiftLeft (certNat% 446) 4096)) 20480)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 447) (Nat.shiftLeft (certNat% 448) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 449) (Nat.shiftLeft (certNat% 450) 4096)) 8192)) 28672)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 451) (Nat.shiftLeft (certNat% 452) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 453) (Nat.shiftLeft (Nat.lor (certNat% 454) (Nat.shiftLeft (certNat% 455) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 456) (Nat.shiftLeft (Nat.lor (certNat% 457) (Nat.shiftLeft (certNat% 458) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 459) (Nat.shiftLeft (Nat.lor (certNat% 460) (Nat.shiftLeft (certNat% 461) 4096)) 4096)) 12288)) 20480)))))
 (.branch 37
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 462) (Nat.shiftLeft (certNat% 463) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 464) (Nat.shiftLeft (Nat.lor (certNat% 465) (Nat.shiftLeft (certNat% 466) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 467) (Nat.shiftLeft (certNat% 468) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 469) (Nat.shiftLeft (Nat.lor (certNat% 470) (Nat.shiftLeft (certNat% 471) 4096)) 8192)) 8192)) 20480)))
 (.branch 38
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 472) (Nat.shiftLeft (certNat% 473) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 474) (Nat.shiftLeft (Nat.lor (certNat% 475) (Nat.shiftLeft (certNat% 476) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 477) (Nat.shiftLeft (certNat% 478) 8192)) (Nat.shiftLeft (Nat.lor (certNat% 479) (Nat.shiftLeft (Nat.lor (certNat% 480) (Nat.shiftLeft (certNat% 481) 4096)) 4096)) 12288)) 20480)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 482) (Nat.shiftLeft (certNat% 483) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 484) (Nat.shiftLeft (certNat% 485) 4096)) 20480)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 486) (Nat.shiftLeft (certNat% 487) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 488) (Nat.shiftLeft (certNat% 489) 4096)) 8192)) 28672))))))
 (.branch 42
 (.branch 40
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 490) (Nat.shiftLeft (certNat% 491) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 492) (Nat.shiftLeft (certNat% 493) 8192)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 494) (Nat.shiftLeft (certNat% 495) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 496) (Nat.shiftLeft (certNat% 497) 12288)) 8192)) 20480)))
 (.branch 41
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 498) (Nat.shiftLeft (certNat% 499) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 500) (Nat.shiftLeft (certNat% 501) 4096)) 12288)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 502) (Nat.shiftLeft (certNat% 503) 12288)) (Nat.shiftLeft (Nat.lor (certNat% 504) (Nat.shiftLeft (certNat% 505) 4096)) 16384)) 20480)))
 (.leaf (Nat.lor (Nat.lor (Nat.lor (certNat% 506) (Nat.shiftLeft (certNat% 507) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 508) (Nat.shiftLeft (certNat% 509) 4096)) 20480)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 510) (Nat.shiftLeft (certNat% 511) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 512) (Nat.shiftLeft (certNat% 513) 4096)) 8192)) 28672)))))
 (.branch 43
 (.leaf (Nat.lor (Nat.lor (certNat% 514) (Nat.shiftLeft (Nat.lor (certNat% 515) (Nat.shiftLeft (certNat% 516) 8192)) 4096)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 517) (Nat.shiftLeft (certNat% 518) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 519) (Nat.shiftLeft (certNat% 520) 4096)) 20480)) 16384)))
 (.branch 44
 (.leaf (Nat.lor (Nat.lor (certNat% 521) (Nat.shiftLeft (Nat.lor (certNat% 522) (Nat.shiftLeft (certNat% 523) 20480)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 524) (Nat.shiftLeft (Nat.lor (certNat% 525) (Nat.shiftLeft (certNat% 526) 4096)) 8192)) 28672)))
 (.leaf (Nat.lor (Nat.lor (certNat% 527) (Nat.shiftLeft (Nat.lor (certNat% 528) (Nat.shiftLeft (certNat% 529) 24576)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 530) (Nat.shiftLeft (Nat.lor (certNat% 531) (Nat.shiftLeft (certNat% 532) 4096)) 4096)) 32768)))))))))
def kindTable : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf 0)
 (.leaf (certNat% 533)))
 (.branch 3
 (.leaf (Nat.lor (certNat% 534) (Nat.shiftLeft (certNat% 535) 4096)))
 (.branch 4
 (.leaf (Nat.lor (certNat% 536) (Nat.shiftLeft (certNat% 537) 4096)))
 (.leaf (Nat.shiftLeft (Nat.lor (Nat.lor (Nat.lor (certNat% 538) (Nat.shiftLeft (certNat% 81) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 81) (Nat.shiftLeft (Nat.lor (certNat% 81) (Nat.shiftLeft (certNat% 81) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 81) (Nat.shiftLeft (certNat% 81) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 81) (Nat.shiftLeft (Nat.lor (certNat% 81) (Nat.shiftLeft (certNat% 85) 4096)) 4096)) 8192)) 20480)) 4096)))))
def rows : Rows 44310 :=
  ⟨fun a => vertexTable.get a.val, fun q => edgeTable.get q.val,
    fun j => kindTable.get j.val⟩
def test (i : Nat) : Bool := cellTest SharedSix0CellPool.entry rows i
end Papers.RationalityTen.SharedSix0Incidence
