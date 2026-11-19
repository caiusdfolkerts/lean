module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public meta import CertificateNumbers
public import SharedGraphFramePairs
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs
def group1111 : Group where
  vertexCode := 654820257810
  inverseVertexCode := 654820257810
  lowTable := (certNat% 0)
  highTable := (certNat% 1)
  edgeTable := (certNat% 2)
  pairPred := 697
  pairs := { width := 32, code := (Nat.lor (Nat.lor (certNat% 3) (Nat.shiftLeft (Nat.lor (certNat% 4) (Nat.shiftLeft (certNat% 5) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 6) (Nat.shiftLeft (Nat.lor (certNat% 7) (Nat.shiftLeft (certNat% 8) 4096)) 4096)) 12288)) }
def group1112 : Group where
  vertexCode := 654820257825
  inverseVertexCode := 654820258050
  lowTable := (certNat% 9)
  highTable := (certNat% 1)
  edgeTable := (certNat% 10)
  pairPred := 1078
  pairs := { width := 32, code := (Nat.lor (Nat.lor (Nat.lor (certNat% 11) (Nat.shiftLeft (certNat% 12) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 13) (Nat.shiftLeft (certNat% 14) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 15) (Nat.shiftLeft (certNat% 16) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 17) (Nat.shiftLeft (Nat.lor (certNat% 18) (Nat.shiftLeft (certNat% 19) 4096)) 4096)) 8192)) 16384)) }
cert_group_6 1113 654820258050 654820257825 20 1 21 1257 22 23 24 25 26 27 28 29 30 31
end Papers.RationalityTen.SharedFrameCatalogue
