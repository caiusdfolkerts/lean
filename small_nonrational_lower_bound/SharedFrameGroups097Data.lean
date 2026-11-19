module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public meta import CertificateNumbers
public import SharedGraphFramePairs
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs
def group1031 : Group where
  vertexCode := 654802563600
  inverseVertexCode := 654787818000
  lowTable := (certNat% 0)
  highTable := (certNat% 1)
  edgeTable := (certNat% 2)
  pairPred := 924
  pairs := { width := 32, code := (Nat.lor (Nat.lor (Nat.lor (certNat% 3) (Nat.shiftLeft (certNat% 4) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 5) (Nat.shiftLeft (certNat% 6) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 7) (Nat.shiftLeft (certNat% 8) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 9) (Nat.shiftLeft (certNat% 10) 4096)) 8192)) 16384)) }
cert_group 1032 654804390960 654804390960 11 12 13 411 14 15 16 17
cert_group_7 1033 654804402480 654804456480 18 12 19 131 20 21
def group1034 : Group where
  vertexCode := 654804402960
  inverseVertexCode := 654804460560
  lowTable := (certNat% 22)
  highTable := (certNat% 12)
  edgeTable := (certNat% 23)
  pairPred := 257
  pairs := { width := 32, code := (Nat.lor (certNat% 24) (Nat.shiftLeft (Nat.lor (certNat% 25) (Nat.shiftLeft 7409671172740378256 4096)) 4096)) }
cert_group_7 1035 654804456480 654804402480 26 12 27 131 28 29
cert_group_7 1036 654804467730 654804467730 30 12 31 140 32 33
cert_group_7 1037 654804467745 654804467970 34 12 35 138 36 37
cert_group_2 1038 654804467970 654804467745 38 12 39 332 40 41 42
end Papers.RationalityTen.SharedFrameCatalogue
