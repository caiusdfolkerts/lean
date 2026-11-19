module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public meta import CertificateNumbers
public import SharedGraphFramePairs
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs
cert_group_3 0510 590095798560 589873692960 0 1 2 124 3
cert_group_4 0511 590112506625 589876634625 4 5 6 129 7 1584729923396900350
cert_group_4 0512 590112506640 589876634640 8 5 9 129 10 1584729923396900350
cert_group_7 0513 590112559170 589876510770 11 5 12 154 13 14
cert_group_3 0514 590112571425 589876642050 15 5 16 86 17
cert_group_7 0515 590112571920 589876642320 18 5 19 152 20 21
cert_group_3 0516 590112625440 589876699440 22 5 23 91 24
cert_group_3 0517 590112632865 589876703490 25 5 26 86 27
cert_group_7 0518 590112633360 589876703760 28 5 29 152 30 31
cert_group_5 0519 590140884225 590140884225 32 33 34 563 37 35 36 38 39
cert_group 0520 590140884240 590140884240 40 33 41 464 42 43 44 45
cert_group_2 0521 590140888065 590141867265 46 33 47 383 48 49 50
def group0522 : Group where
  vertexCode := 590140888080
  inverseVertexCode := 590141867280
  lowTable := (certNat% 51)
  highTable := (certNat% 33)
  edgeTable := (certNat% 52)
  pairPred := 257
  pairs := { width := 32, code := (Nat.lor (certNat% 53) (Nat.shiftLeft (Nat.lor (certNat% 54) (Nat.shiftLeft 1433855410199597990 4096)) 4096)) }
cert_group_7 0523 590141867265 590140888065 55 56 57 238 58 59
cert_group_2 0524 590141867280 590140888080 60 56 61 360 62 63 64
def group0525 : Group where
  vertexCode := 590141871105
  inverseVertexCode := 590141871105
  lowTable := (certNat% 65)
  highTable := (certNat% 56)
  edgeTable := (certNat% 66)
  pairPred := 681
  pairs := { width := 32, code := (Nat.lor (Nat.lor (certNat% 67) (Nat.shiftLeft (Nat.lor (certNat% 68) (Nat.shiftLeft (certNat% 69) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 70) (Nat.shiftLeft (Nat.lor (certNat% 71) (Nat.shiftLeft (certNat% 72) 4096)) 4096)) 12288)) }
end Papers.RationalityTen.SharedFrameCatalogue
