module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00212Data
public import GraphInputsRow29Part00212Frames
public import GraphInputsRow29Part00212Leaves
public import GraphInputsRow29Part00212Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00212.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002
def vertexColumn : Fields := ⟨10, hexnat% "1f06e178791d46d1743d1ac5b19c5713c2f07c748f26695a8e8ba1e9c6a9a6639996558d62d876c398e53a2e2b86e4789e1783e744f1665598e4b91e5c5a966539595554d52d4756354d2b46d4749d1743d70ea398ce364d5334e332cc7362d4b8acab1ae1b46c9b16c3ba1d8791d4731e2729c6745c9715c3743c8f13c2f07e2c649524698651a0e438b11c6290e625294658342d24c5382c1b81c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db6db4d26da6da4db4926d36da6d24d24db49b49b69b6d24d26d369249249249a4d2491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨104, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨111, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "b118e211880c03b07d61ba000000", hexnat% "200004002000004000000", hexnat% "100000000000001c00000000", 2748779069440, hexnat% "30c00000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81007010388c03b27ffdbe000000", hexnat% "380004000000000000000", hexnat% "820000000000000000000000", hexnat% "3018000000000000000000000000", hexnat% "400000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81005010080003b27c3d86000000", hexnat% "380004000000000000000", hexnat% "a20000000000000020000000", hexnat% "3018000000000000000000000000", 4123571257344, hexnat% "30cc0000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2018d213b8cc40b257fdbe000000", hexnat% "100200000000000000000000000", hexnat% "9000000000000300200000000000", 8796093022208]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180213b8cc40827c0196000000", hexnat% "900000000000000020000000", hexnat% "b000000000000300000000000000", 13510919141195776, hexnat% "100600000000000014000000000", 2886352240640]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "189213b8cc40b27fbdbe000000", 216173056991690752, hexnat% "100600000000000000000000000", hexnat% "b000000000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1002388c40b247bd1e000000", hexnat% "100e20000000000000020000000", hexnat% "1180400000000000000000", hexnat% "8000000000100004080000000", 144176760727011328, hexnat% "b010000000000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "189213b8cc40b27efdbe000000", 216173881625411584, hexnat% "100600000000000000000000000", hexnat% "b000000000000000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1002384c40b246fc9e000000", hexnat% "100e20000000000000020000000", hexnat% "1180800000000000000000", hexnat% "10000000000200010100000000", 72119166689083392, hexnat% "b008000000000000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a118f211080843b27d7db6000000", hexnat% "1000000080040000000008000000", hexnat% "200000000000000000000", 2748779069440, hexnat% "30c00000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "21005013b80c43b27ebd9e000000", hexnat% "a20000000000000020000000", 1374389534720, hexnat% "9018000000000000000000000000", hexnat% "c00000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "21005001000843b27c1d96000000", hexnat% "1280000000000000000000", hexnat% "a20000000000000020000000", hexnat% "38c40000000000000000", hexnat% "9018000000000000000000000000", 4260741775360]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨104, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "b118620280c443b27d0d8e000000", hexnat% "1100000000000000000000", hexnat% "900000000000000020000000", 3161364365312, hexnat% "38080000001000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "b118620000c04380394da2000000", hexnat% "900000000000000004000000", hexnat% "380c0000001000000000", hexnat% "200000002440000000000", hexnat% "1180000030000000000000", 2886620676096]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18920000c040b27ebdbe000000", hexnat% "380c0000000000000000", hexnat% "1380000000000000000000", 216174156503318528, hexnat% "100600000000000000000000000", hexnat% "b000000000000000000000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9118f210880443b27d7dae000000", hexnat% "2000000100080000000010000000", hexnat% "200000000000000000000", 2748779069440, hexnat% "30c00000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11103013b80c43b27ebd9e000000", hexnat% "400000000000014020000000", hexnat% "820000000000000000000000", hexnat% "a008000000000000000000000000", hexnat% "c00000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11103000800443b27c1d8e000000", hexnat% "1300000000000000000000", hexnat% "c20000000000000020000000", hexnat% "a008000000000000000000000000", 4260875993088, hexnat% "38c80000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨104, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "101002380c40b25ebc1e000000", hexnat% "100e20000000000000020000000", hexnat% "8000000c00000000180000000", hexnat% "1180000000000000000000", 216209340875407360, hexnat% "b000000000000000000000000000"]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "110f000000043803bfd3e000000", hexnat% "200000002440000000000", hexnat% "8020000c00000000080000000", hexnat% "b000000000000000000000000000", hexnat% "380c0000000000000000", hexnat% "1180000030000000000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "118f000000043803bfcbe000000", hexnat% "20000c00000000100000000", hexnat% "200000002440000000000", hexnat% "b000000000000000000000000000", hexnat% "380c0000000000000000", hexnat% "1180000030000000000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "b118620000c04380395da2000000", hexnat% "900000000000000004000000", hexnat% "380c0000000000000000", 2886620676096, hexnat% "200000002440000000000", hexnat% "1180000030000000000000"]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "181000000040b21d5c06000000", 105553653137408, hexnat% "b000000000000300000000000000", hexnat% "38cc0000000000000000", 2893063127040, hexnat% "1380000000000000000000", hexnat% "100e20000000000000000000000"]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c33 c30
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c34 c29
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c35 c28
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c36 c27
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c37 c22
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c38 c21
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c39 c18
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c40 c13
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c41 c10
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c42 c7
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c43 c4
  c44
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00212.record002
