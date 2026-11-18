module
prelude
public import ResidualBatch.Graph

public section
namespace Papers.RationalityTen.ResidualBatch
open RawGraphSemanticCertificate

/-- Reassemble the original side predicate from literal geometry, separately
checked frames, an empty root and all original terminal dispositions. -/
theorem sideOfFrames (p : Packet)
    (lit : allFin (literalCellTest p.data.data) = true)
    (frames : ∀ f, frameCheck p.data f (p.frame f) = true)
    (root : decide ((p.data.nodes p.data.rootNode).cells = []) = true)
    (leaves : allFin (fun j => RawLeafCertificate.check p.data.data.quota
      ((p.data.leaf j).map p.data.data.cells) (p.leaf j)) = true) :
    sideCheck p = true := by
  have hf : allFin (fun f => frameCheck p.data f (p.frame f)) = true :=
    List.all_eq_true.mpr fun f _ => frames f
  exact Bool.and_eq_true_iff.mpr ⟨lit, Bool.and_eq_true_iff.mpr
    ⟨hf, Bool.and_eq_true_iff.mpr ⟨root, leaves⟩⟩⟩

end Papers.RationalityTen.ResidualBatch
