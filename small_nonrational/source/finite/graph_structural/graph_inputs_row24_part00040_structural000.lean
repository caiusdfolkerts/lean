module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00040Data
public import GraphInputsRow24Part00040Frames
public import GraphInputsRow24Part00040Leaves
public import GraphInputsRow24Part00040Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002
def vertexColumn : Fields := ⟨10, hexnat% "31c9723c1f31a5693a1eb162d876c38ce1ba1e4785e0fb19965598e5391e715956352d475c368d934cd8b46d8751d1743dc4d534ccb31cf0b62d4b32d2b1ae1b46c5b0ef0731c6785d1725e0f43c1f2b0aa298560d88e1382ec47092a4a5854550d60d2344d0b4a344c530cd0b22c4b0ac8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6d26936926db6924924924d2492492493493492492249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2070080b7beedb00000000", hexnat% "600000000000400000000", 37154834364760064, hexnat% "3f000000000000000", hexnat% "740000000000000000", hexnat% "1000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "70000bffee7700000000", hexnat% "400004000008000000000", hexnat% "3200000000000000000000", hexnat% "3b000000000000000", hexnat% "740000000000000000", hexnat% "80000000800000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "32703dfb182efd00000000", hexnat% "400000000800200000000", hexnat% "420000000000000000", 63050394783186944, 2040693581152256]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3260041278267900000000", hexnat% "400004000808600000000", hexnat% "380100000000000000", 2049489674174464, hexnat% "10400080000000000000", hexnat% "3a800000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "32007c1b18267900000000", 63059190876209152, hexnat% "70000000000000000000", hexnat% "400004000808600000000", hexnat% "3a000000000000000", 2040693581152256]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "14707ffb008eff00000000", hexnat% "2200000000000000000000", 2075877953241088, 65302194596872192, 4503599627370496]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "366004430086ff00000000", 2084674046263296, hexnat% "3b800000000000000", hexnat% "380000000000000000", 33776997205278720, hexnat% "10400080000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30000c001006c800000000", hexnat% "660000000000100000000", 2225420124553216, hexnat% "10400080000000000000", 29273603736338432, hexnat% "3f800000400000000", hexnat% "300300000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006
def vertexColumn : Fields := ⟨10, hexnat% "c725c8f0bc1f31a2e87ac58b61db0e6394e3392e2b86e8791e2785e0fb19966392e479c56558d4b51d70da358d9354d3362d4b4ad1b61d4749d1743dc4cb31cf0b62d4b32d2b1ae1b46c9bc1d8751cc749c6785d1725e0f43c8f13c2f07caa1683a298560db092a61916439c14a5854550d4a314c3342c8b12c2b06d0721c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6d26936db4db69249249249b6db69a6d26924924924924924d2491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨87, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "87ffc053606033e0000000", hexnat% "600000000000004800000000", hexnat% "3000000000000900000000000", 17042430230528, 8725724278030336]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "87dec053206033e0000000", hexnat% "1200000000000804000000000", 17076789968896, 8743316464074752, hexnat% "2400021000040000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24001f1404351d00840000000", hexnat% "e801000002000000000", hexnat% "86000000000003a0000000", hexnat% "1200000000020004000000000", 3975834046038016, 17111149707264]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10087f840533ff013e0000000", hexnat% "7800000002800000000", hexnat% "2400000000040000000000000", 17317308137472, hexnat% "200000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4086214053412ffbe0000000", hexnat% "e800000000000000000", hexnat% "3000000000000900000000000", 8514618045497344, hexnat% "1d0000000000000000000", hexnat% "200000000020000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20001f000135ff083e0000000", hexnat% "8600404000000000000000", hexnat% "400001000000004800000000", 16698832846848, hexnat% "1200000800020000000000000", hexnat% "e000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000031ffffbe0000000", hexnat% "e801000000000000000", hexnat% "8600404000000000000000", hexnat% "1d0000000000000000000", hexnat% "2400001000040000000000000", hexnat% "1200000000020000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3600631800361f4f8e0000000", hexnat% "1c0001000000000000000", 12103217840128, 8444249301319680, hexnat% "e000000000000000000", hexnat% "8000404000000100000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "240862040537ff483e0000000", hexnat% "1d0000000000000000000", 12610023981056, hexnat% "7800000000000000000", hexnat% "8000000000000000000", hexnat% "1200000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "802000033ffffbe0000000", hexnat% "600405000000000000000", hexnat% "e800000000000000000", hexnat% "2400001000040000000000000", hexnat% "1d0000000000000000000", hexnat% "1200000000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3608231800361affbe0000000", hexnat% "400405000000000000000", hexnat% "e000000000000000000", 8532210231541760, hexnat% "1c0000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "240862140536136cbe0000000", 10101763080192, 8655355533852672, hexnat% "1d0000000000000000000", hexnat% "e800000000000000000", hexnat% "1200000000000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81f000532166c000000000", hexnat% "2400001000040100840000000", hexnat% "8400000080000000000", 564065034305536, hexnat% "6800000003000000000", hexnat% "1200600000000000000000000", 8022036836253696]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c15 c8
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c16 c7
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c17 c6
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c18 c5
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c19 c4
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c20 c3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c21 c2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c23 c0
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record006
