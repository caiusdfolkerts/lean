module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00055Data
public import GraphInputsRow29Part00055Frames
public import GraphInputsRow29Part00055Leaves
public import GraphInputsRow29Part00055Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨71, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨95, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 72057628397666304, (certNat% 4), 144115256795332608]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), 69256347648, (certNat% 10)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨101, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), (certNat% 13), 35218731827200]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), 2287293423419392, (certNat% 17)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), 144255994283687936, (certNat% 19), (certNat% 20), 74344612583440384, (certNat% 21)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), (certNat% 24), (certNat% 9), 33554432]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 23), (certNat% 26), (certNat% 27), (certNat% 28)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 85899345920, 252342316621103104, (certNat% 30), (certNat% 13)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 27), (certNat% 32), (certNat% 33), (certNat% 34)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), (certNat% 27), 252412685365280768, (certNat% 36), 9511602415153971200, (certNat% 37)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c18 c11
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 39), (certNat% 13), (certNat% 40), (certNat% 41)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 10), 216313519602139136, (certNat% 43), 35184372088832]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), 17985175552, (certNat% 45), (certNat% 46), (certNat% 47)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 4), (certNat% 24), 144185625539510272, (certNat% 46)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), (certNat% 50), (certNat% 33), (certNat% 51), (certNat% 47)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 24), 216260743044005888, (certNat% 53), (certNat% 10), (certNat% 33)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c27 c23
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c28 c22
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c29 c21
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c30 c20
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), 72057628397666304, (certNat% 41), (certNat% 39), (certNat% 55)]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), (certNat% 57), (certNat% 58), (certNat% 59), (certNat% 60), (certNat% 61)]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c33 c32
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), 88046829568, 216190374299828224, 2251834173423616, (certNat% 47)]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), (certNat% 64), 85899345920, 17626545782784]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), (certNat% 66), (certNat% 67), 17179869184, (certNat% 68)]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), (certNat% 66), (certNat% 70), 72075186223972352, (certNat% 71)]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), (certNat% 73), 19327352832, 34359738368]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), (certNat% 70), 19327352832, 34359738368, (certNat% 10)]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c41 c40
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 75), 88046829568, 162727720910848, (certNat% 5)]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), (certNat% 77), (certNat% 68), (certNat% 47), 72075220583710720]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 78), (certNat% 10), 51539607552, 72057594037927936, (certNat% 68)]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), (certNat% 80), 19327352832, (certNat% 68), 72075220583710720, (certNat% 47)]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c47 c44
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c48 c43
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c49 c42
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c50 c39
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c51 c38
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c52 c35
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 81), (certNat% 82), (certNat% 83), (certNat% 84), (certNat% 85), (certNat% 23)]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 86), (certNat% 23), (certNat% 24), (certNat% 87)]
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 88), (certNat% 23), 144273517750255616, 2181038080, 9259400833873739776]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 89), (certNat% 23), (certNat% 26), (certNat% 27), (certNat% 90)]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 91), 158329674399744, (certNat% 30), 85899345920]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 92), (certNat% 3), 85899345920, (certNat% 30)]
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 93), (certNat% 23), 9223376434901286912, (certNat% 94), 144115256795332608]
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c60 c59
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨106, by decide⟩ c61 c58
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 95), (certNat% 27), 144277915796766720, (certNat% 96), (certNat% 20), 70900514816]
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c63 c62
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c64 c57
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c65 c56
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c66 c55
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 97), (certNat% 98), 88617254912, (certNat% 30), (certNat% 83), (certNat% 99)]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 100), (certNat% 82), (certNat% 60), (certNat% 83), 72110404955799552, 17179869184]
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 101), 72110404955799552, (certNat% 60), (certNat% 102), (certNat% 103), (certNat% 104)]
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 105), (certNat% 60), (certNat% 106), 9223372037391646720, 35235911696384, 72215923712327680]
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 107), (certNat% 108), (certNat% 109), 51573161984, 189291921837916160, 72110370596061184]
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 110), (certNat% 58), 72233515898372096, (certNat% 80), 9268412431174991872, 144115188075855872]
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 111), (certNat% 112), 35235911696384, 216331111788183552, (certNat% 83)]
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 113), (certNat% 60), (certNat% 80), (certNat% 114), 19864223744, 72110404955799552, 189296319884427264]
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c75 c74
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c76 c73
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c77 c72
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c78 c71
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c79 c70
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨101, by decide⟩ c80 c69
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c81 c68
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c82 c67
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c83 c54
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c84 c53
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c85 c34
  let c87 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c86 c31
  let c88 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c87 c19
  let c89 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c88 c10
  c89
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001
def vertexColumn : Fields := ⟨10, (certNat% 115)⟩
def kindColumn : Fields := ⟨3, (certNat% 116)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨33, by decide⟩, ⟨40, by decide⟩, ⟨46, by decide⟩, ⟨55, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨95, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨100, by decide⟩, ⟨103, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨112, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 117), (certNat% 118), (certNat% 119), (certNat% 120)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 121), (certNat% 122), (certNat% 123), (certNat% 124)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 125), (certNat% 126), (certNat% 127), (certNat% 128), (certNat% 129)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨103, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 130), (certNat% 131), (certNat% 132), (certNat% 133), (certNat% 134)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 135), (certNat% 136), (certNat% 137), (certNat% 138), (certNat% 139)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 140), (certNat% 141), (certNat% 142), (certNat% 143), (certNat% 144)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 145), (certNat% 146), (certNat% 132), (certNat% 147)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 148), (certNat% 123), (certNat% 120), (certNat% 142), (certNat% 119)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 149), (certNat% 128), (certNat% 150), (certNat% 151), (certNat% 147), (certNat% 136)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨103, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨107, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 152), (certNat% 153), (certNat% 154), (certNat% 155), (certNat% 156), (certNat% 157)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 158), (certNat% 159), (certNat% 119), (certNat% 160), (certNat% 161)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 158), (certNat% 159), (certNat% 119), (certNat% 123), (certNat% 162)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 163), (certNat% 147), (certNat% 123), (certNat% 164), (certNat% 162)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 165), (certNat% 160), 36029896564146176, (certNat% 159), (certNat% 161)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 166), (certNat% 160), (certNat% 132), (certNat% 164), (certNat% 167), (certNat% 146)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c23 c20
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c24 c19
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c25 c18
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 168), (certNat% 119), (certNat% 169), (certNat% 170), (certNat% 159)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 171), (certNat% 150), (certNat% 119), (certNat% 172), (certNat% 159)]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 173), (certNat% 132), (certNat% 174), (certNat% 175), (certNat% 176), (certNat% 177)]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c29 c28
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨107, by decide⟩ c30 c27
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 178), (certNat% 141), (certNat% 179), (certNat% 180)]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 181), (certNat% 150), (certNat% 160), (certNat% 128), (certNat% 129)]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨103, by decide⟩ c33 c32
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 182), (certNat% 179), (certNat% 183), (certNat% 184), (certNat% 185), (certNat% 159)]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 186), (certNat% 187), (certNat% 188), (certNat% 184), (certNat% 129), (certNat% 189)]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 190), (certNat% 131), (certNat% 191), (certNat% 138), (certNat% 192), (certNat% 187)]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 193), (certNat% 194), (certNat% 195), (certNat% 196), (certNat% 197)]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 198), (certNat% 199), (certNat% 200), (certNat% 184), (certNat% 188), (certNat% 201)]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c40 c39
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 202), (certNat% 122), (certNat% 119), (certNat% 203), (certNat% 162)]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 204), (certNat% 205), (certNat% 206), (certNat% 207)]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 208), (certNat% 209), (certNat% 210), (certNat% 129), (certNat% 211), (certNat% 134)]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c45 c42
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c46 c42
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 212), (certNat% 131), (certNat% 164), (certNat% 138), (certNat% 199), (certNat% 213)]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 214), (certNat% 215), (certNat% 216), (certNat% 217), (certNat% 154)]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 218), (certNat% 128), (certNat% 219), (certNat% 220), (certNat% 132), (certNat% 221)]
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 222), (certNat% 223), (certNat% 224), (certNat% 225)]
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 226), (certNat% 179), (certNat% 227), (certNat% 228), (certNat% 220), (certNat% 221)]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c52 c51
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 229), (certNat% 230), (certNat% 224), (certNat% 184), (certNat% 231), (certNat% 199), (certNat% 189)]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c54 c53
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c55 c50
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c56 c49
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c57 c48
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c58 c47
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨108, by decide⟩ c59 c41
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c60 c38
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c61 c37
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c62 c36
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c63 c31
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c64 c26
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c65 c17
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c66 c16
  c67
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record001
