module
prelude
public import RawFrameSupportCore
public import PackedGraphInputs
public import RawLeafCertificate

@[expose] public section

/-!
The complete local proof obligations for a packed graph certificate. This
interface imports no graph catalogue, global cell universe or row table.
-/

namespace Papers.RationalityTen.GraphCaseCertificate

open PackedGraphCertificate

structure Core (D : RawData) : Prop where
  matrix : MatrixGraphProblem.Checked D.data
  valid : GraphGrowthInputs.Valid D.inputs
  literal : RawGraphSemanticCertificate.LiteralFacts D.data
  nodes : ∀ i, RawGraphConditionedGrowth.nodeCheck (D.inputs.problem valid)
    D.maps D.leaf D.nodes i = true
  leaf_nodup : ∀ j, (D.leaf j).Nodup
  frames : ∀ f, RawFrameSupport.Supported D f
  root_empty : (D.nodes D.rootNode).cells = []
  leaves_checked : ∃ certificates : Fin D.l → RawLeafCertificate.Certificate,
    ∀ j, RawLeafCertificate.check D.data.quota
      ((D.leaf j).map D.data.cells) (certificates j) = true

end Papers.RationalityTen.GraphCaseCertificate
