module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow31Part00093Data
public import GraphInputsRow31Part00093Frames
public import GraphInputsRow31Part00093Leaves
public import GraphInputsRow31Part00093Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00093.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093.record000
def vertexColumn : Fields := ⟨10, hexnat% "f81f0bae1b46a99a699966a5996959562d876a398e9394e2b86e2785ef06e1786d1744f1b25c93a4d9e1745a95a599565a5595955551d68d6364d5346d17783d0ea368e6358e9364e5354cb3a2d8b92d4b2ac9bc1e8761e4751e2749ca719e1745c9715e0f43c8f13cb81e0b42b09c0f0721a85a0e8360b81e2c4712a469264590e685614a5254352342d0764350c6314c3312c2b06e0741c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "249b6db6db49b6d249b6da6d24d26d26d24da4d36936926d2492492492492491249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨96, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100000013800020003fffe0000000000", hexnat% "663000000000000000", hexnat% "33180000000000000000000", hexnat% "4008280000000010c00000000000000", hexnat% "8004140000218000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100000013200004003fffe0000000000", hexnat% "2263000000000000000", hexnat% "93180000000000000000000", hexnat% "4008280000000010c00000000000000", hexnat% "8004140000218000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c00c3c1300218000272220000000000", hexnat% "2663000000000000000", hexnat% "10d84440000000000", 2700400557817856, hexnat% "b3180000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180000013100002003fffe0000000000", hexnat% "2463000000000000000", hexnat% "a3180000000000000000000", hexnat% "4140000218000000000000000000", hexnat% "4008280000000010c00000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c00c3c1300000010f9c440000000000", hexnat% "b3180000000000000000000", hexnat% "218000062220000000000", 448600744132608, hexnat% "2663000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c000001300000000218000000000000", hexnat% "2663062220000000000", hexnat% "b3180000184440000000000", hexnat% "c0000008000400000000000000", hexnat% "300000010000800000000000000", hexnat% "c000000200010000000000000000", 448600744132608]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨122, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨123, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00093.record000
