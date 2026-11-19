module
prelude
public import RawFaceNormalizers
public import TenGraphEdges

@[expose] public section

/-! Small record checks connect each common-face block to the already
verified outside-label generators. They inspect only ten vertex values,
independently of the size of the candidate-cell universe. -/

namespace Papers.RationalityTen.RawOutsidePlacement

def swapValue (first second vertex : Nat) : Nat :=
  if vertex = first then second else if vertex = second then first else vertex

def blockCheck {g : Nat} [NeZero g] (vertexCode : Fin g → Nat)
    (rootVertices : Nat) (B : RawFacePlacement.Block) : Bool :=
  ((List.range B.outside).all fun j =>
    !(rootVertices.testBit (RawFacePlacement.digit B.targetForward (B.shared + j)))) &&
  ((List.range (B.outside - 1)).all fun j =>
    (List.finRange 10).all fun v =>
      decide ((TenGraphEdges.vertexMap (vertexCode (Fin.ofNat g j)) v).val =
        swapValue (RawFacePlacement.digit B.targetForward (B.shared + j))
          (RawFacePlacement.digit B.targetForward (B.shared + (j + 1))) v.val))

end Papers.RationalityTen.RawOutsidePlacement
