module
prelude
public import PackedGraphCertificate
public import RawGraphSemanticCertificate

@[expose] public section

/-! The geometric meaning of a raw forward map, independent of any catalogue. -/

namespace Papers.RationalityTen.RawFrameSupport

open PackedGraphCertificate RawGraphSemanticCertificate

def Supported (D : RawData) (f : Fin D.g) : Prop :=
  (∀ c, D.maps f c = c) ∨
    ∃ (vertexForward vertexInverse : Nat) (inverse : Fin D.n → Fin D.n),
      FrameFacts D.data.cells D.data.requiredEdges vertexForward vertexInverse
        (D.maps f) inverse

theorem of_identity (D : RawData) (f : Fin D.g)
    (h : ∀ c, D.maps f c = c) : Supported D f := Or.inl h

end Papers.RationalityTen.RawFrameSupport
