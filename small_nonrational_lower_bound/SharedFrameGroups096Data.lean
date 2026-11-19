module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public meta import CertificateNumbers
public import SharedGraphFramePairs
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs
cert_group_5 1024 654787814160 654802559760 0 1 2 551 5 3 4 6 7
cert_group 1025 654787817985 654802563585 8 1 9 393 10 11 12 13
cert_group_6 1026 654787818000 654802563600 14 1 15 1226 16 17 18 19 20 21 22 23 24 25
cert_group_3 1027 654802555680 654787813680 26 27 28 117 29
cert_group_7 1028 654802559760 654787814160 30 27 31 219 32 33
def group1029 : Group where
  vertexCode := 654802563360
  inverseVertexCode := 654787817760
  lowTable := (certNat% 34)
  highTable := (certNat% 27)
  edgeTable := (certNat% 35)
  pairPred := 256
  pairs := { width := 32, code := (Nat.lor (certNat% 36) (Nat.shiftLeft (Nat.lor (certNat% 37) (Nat.shiftLeft 319297314 4096)) 4096)) }
cert_group 1030 654802563585 654787817985 38 27 39 468 40 41 42 43
end Papers.RationalityTen.SharedFrameCatalogue
