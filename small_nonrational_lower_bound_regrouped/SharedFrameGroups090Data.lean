module
prelude
public meta import CertificateNumbers
public import SharedGraphFramePairs
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs
def group1000 : Group where
  vertexCode := 654568596225
  inverseVertexCode := 654568596225
  lowTable := (certNat% 0)
  highTable := (certNat% 1)
  edgeTable := (certNat% 2)
  pairPred := 1340
  pairs := { width := 32, code := (Nat.lor (Nat.lor (Nat.lor (certNat% 3) (Nat.shiftLeft (certNat% 4) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 5) (Nat.shiftLeft (Nat.lor (certNat% 6) (Nat.shiftLeft (certNat% 7) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% 8) (Nat.shiftLeft (Nat.lor (certNat% 9) (Nat.shiftLeft (certNat% 10) 4096)) 4096)) (Nat.shiftLeft (Nat.lor (certNat% 11) (Nat.shiftLeft (Nat.lor (certNat% 12) (Nat.shiftLeft (certNat% 13) 4096)) 4096)) 12288)) 20480)) }
end Papers.RationalityTen.SharedFrameCatalogue
