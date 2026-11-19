module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00146Data
public import GraphInputsRow24Part00146Frames
public import GraphInputsRow24Part00146Leaves
public import GraphInputsRow24Part00146Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00146.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008
def vertexColumn : Fields := ⟨10, hexnat% "3d0ec670bc9c8f29a8eac6a3a4e8ba39a56358b61da4e338ae1ba1e4789e0fad19c4f1b26693a719a65998e5392e4e565655354b51d58d934cd2b46d8751d2743d98ce3c4e5334e334ccb31cf0b92ccb8ad2b2ac6b86d1b26c3b91d4731ca719e1725c570de0f23c4f0bc1f4590e384b12a4c5454954348d90c6384d130ce0b42c2b41c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db6db6db6d36da6d36db49349a69369349269249349249a493492492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000800f7ef98dc800000", hexnat% "244200000020000000", hexnat% "20c02000000000000000", hexnat% "2000000400004400400000", 8640266240, hexnat% "10000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2d666782067bc00000", hexnat% "200080000000d000000000", hexnat% "120400000000000000000", 40567617525645312, 84662462447616]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200040f7ef98ed800000", hexnat% "480200000200000000", hexnat% "12000000002000000", hexnat% "100840000000000000000", hexnat% "2000000400004400400000", hexnat% "200000000010000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000810610efdc77c00000", 10977524225933312, 54043206265864192, hexnat% "2c4000000000000000", hexnat% "120402000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2d6641cf063fc00000", hexnat% "200080000000d000000000", hexnat% "120400000000000000000", 40567617525645312, 10696050188746752]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200040b6ed88ffc00000", hexnat% "210600000000000000", hexnat% "2000000000004400000000", 18298081099382784, hexnat% "1004c2000000000000000", hexnat% "800000001000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000000400a14426400000", hexnat% "294200000000000000", 85830634831872, hexnat% "120800041000000000000", 36028842401333248, 15200199706148864, hexnat% "442000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00146.record008
