module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_graph_certificateTable " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def record⟪0⟫_certificateTable : Table Certificate :=
(.leaf (.matching Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪2⟫))"### args

elab "cert_graph_certificateTable_10 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def record⟪0⟫_certificateTable : Table Certificate :=
(.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪3⟫))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪2⟫.r⟪4⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪2⟫.r⟪5⟫))))"### args

elab "cert_graph_certificateTable_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def record⟪0⟫_certificateTable : Table Certificate :=
(.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪5⟫))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪6⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪2⟫.r⟪7⟫))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪3⟫.r⟪8⟫))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪4⟫.r⟪9⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪4⟫.r⟪10⟫)))))"### args

elab "cert_graph_certificateTable_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def record⟪0⟫_certificateTable : Table Certificate :=
(.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪3⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪2⟫.r⟪4⟫)))"### args

elab "cert_graph_certificateTable_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def record⟪0⟫_certificateTable : Table Certificate :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪4⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪5⟫)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪2⟫.r⟪6⟫))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪2⟫.r⟪7⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪2⟫.r⟪8⟫)))))
 (.branch 7
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪2⟫.r⟪9⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪2⟫.r⟪10⟫)))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪2⟫.r⟪11⟫))
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪3⟫.r⟪12⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪3⟫.r⟪13⟫))))))"### args

elab "cert_graph_certificateTable_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def record⟪0⟫_certificateTable : Table Certificate :=
(.leaf (.quota 1))"### args

elab "cert_graph_certificateTable_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def record⟪0⟫_certificateTable : Table Certificate :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪5⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪2⟫.r⟪6⟫)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪3⟫.r⟪7⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪3⟫.r⟪8⟫))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪4⟫.r⟪9⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪4⟫.r⟪10⟫)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪4⟫.r⟪11⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪4⟫.r⟪12⟫)))))"### args

elab "cert_graph_certificateTable_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def record⟪0⟫_certificateTable : Table Certificate :=
(.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪2⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪3⟫)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪4⟫))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪5⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪6⟫)))))"### args

elab "cert_graph_certificateTable_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def record⟪0⟫_certificateTable : Table Certificate :=
(.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪4⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪2⟫.r⟪5⟫)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪2⟫.r⟪6⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪3⟫.r⟪7⟫))))"### args

elab "cert_graph_certificateTable_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def record⟪0⟫_certificateTable : Table Certificate :=
(.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪4⟫))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪5⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪6⟫))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪2⟫.r⟪7⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪3⟫.r⟪8⟫)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪3⟫.r⟪9⟫))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M⟪3⟫.r⟪10⟫)))))"### args

elab "cert_graph_certificates " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def record⟪0⟫_certificates (j : Fin record⟪0⟫.l) : Certificate :=
  record⟪0⟫_certificateTable.get j.val"### args

elab "cert_graph_leaf_certificates_checked " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_leaf_certificates_checked : ∀ j : Fin record⟪0⟫.l,
    RawLeafCertificate.check record⟪0⟫.data.quota (record⟪0⟫_rawLeaves j)
      (record⟪0⟫_certificates j) = true :=
  (Fin.cases record⟪0⟫_leaf_checked_0 (Fin.cases record⟪0⟫_leaf_checked_1 (Fin.cases record⟪0⟫_leaf_checked_2 (Fin.cases record⟪0⟫_leaf_checked_3 (Fin.cases record⟪0⟫_leaf_checked_4 (Fin.cases record⟪0⟫_leaf_checked_5 (Fin.cases record⟪0⟫_leaf_checked_6 (Fin.cases record⟪0⟫_leaf_checked_7 (Fin.cases record⟪0⟫_leaf_checked_8 (Fin.cases record⟪0⟫_leaf_checked_9 (fun j => Fin.elim0 j)))))))))))"### args

elab "cert_graph_leaf_certificates_checked_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_leaf_certificates_checked : ∀ j : Fin record⟪0⟫.l,
    RawLeafCertificate.check record⟪0⟫.data.quota (record⟪0⟫_rawLeaves j)
      (record⟪0⟫_certificates j) = true :=
  (Fin.cases record⟪0⟫_leaf_checked_0 (Fin.cases record⟪0⟫_leaf_checked_1 (Fin.cases record⟪0⟫_leaf_checked_2 (Fin.cases record⟪0⟫_leaf_checked_3 (Fin.cases record⟪0⟫_leaf_checked_4 (Fin.cases record⟪0⟫_leaf_checked_5 (Fin.cases record⟪0⟫_leaf_checked_6 (fun j => Fin.elim0 j))))))))"### args

elab "cert_graph_leaf_certificates_checked_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_leaf_certificates_checked : ∀ j : Fin record⟪0⟫.l,
    RawLeafCertificate.check record⟪0⟫.data.quota (record⟪0⟫_rawLeaves j)
      (record⟪0⟫_certificates j) = true :=
  (Fin.cases record⟪0⟫_leaf_checked_0 (Fin.cases record⟪0⟫_leaf_checked_1 (Fin.cases record⟪0⟫_leaf_checked_2 (Fin.cases record⟪0⟫_leaf_checked_3 (Fin.cases record⟪0⟫_leaf_checked_4 (fun j => Fin.elim0 j))))))"### args

elab "cert_graph_leaf_certificates_checked_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_leaf_certificates_checked : ∀ j : Fin record⟪0⟫.l,
    RawLeafCertificate.check record⟪0⟫.data.quota (record⟪0⟫_rawLeaves j)
      (record⟪0⟫_certificates j) = true :=
  (Fin.cases record⟪0⟫_leaf_checked_0 (Fin.cases record⟪0⟫_leaf_checked_1 (Fin.cases record⟪0⟫_leaf_checked_2 (Fin.cases record⟪0⟫_leaf_checked_3 (fun j => Fin.elim0 j)))))"### args

elab "cert_graph_leaf_certificates_checked_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_leaf_certificates_checked : ∀ j : Fin record⟪0⟫.l,
    RawLeafCertificate.check record⟪0⟫.data.quota (record⟪0⟫_rawLeaves j)
      (record⟪0⟫_certificates j) = true :=
  (Fin.cases record⟪0⟫_leaf_checked_0 (Fin.cases record⟪0⟫_leaf_checked_1 (Fin.cases record⟪0⟫_leaf_checked_2 (fun j => Fin.elim0 j))))"### args

elab "cert_graph_leaf_certificates_checked_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_leaf_certificates_checked : ∀ j : Fin record⟪0⟫.l,
    RawLeafCertificate.check record⟪0⟫.data.quota (record⟪0⟫_rawLeaves j)
      (record⟪0⟫_certificates j) = true :=
  (Fin.cases record⟪0⟫_leaf_checked_0 (Fin.cases record⟪0⟫_leaf_checked_1 (Fin.cases record⟪0⟫_leaf_checked_2 (Fin.cases record⟪0⟫_leaf_checked_3 (Fin.cases record⟪0⟫_leaf_checked_4 (Fin.cases record⟪0⟫_leaf_checked_5 (fun j => Fin.elim0 j)))))))"### args

elab "cert_graph_leaf_certificates_checked_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_leaf_certificates_checked : ∀ j : Fin record⟪0⟫.l,
    RawLeafCertificate.check record⟪0⟫.data.quota (record⟪0⟫_rawLeaves j)
      (record⟪0⟫_certificates j) = true :=
  (Fin.cases record⟪0⟫_leaf_checked_0 (fun j => Fin.elim0 j))"### args

elab "cert_graph_leaf_certificates_checked_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_leaf_certificates_checked : ∀ j : Fin record⟪0⟫.l,
    RawLeafCertificate.check record⟪0⟫.data.quota (record⟪0⟫_rawLeaves j)
      (record⟪0⟫_certificates j) = true :=
  (Fin.cases record⟪0⟫_leaf_checked_0 (Fin.cases record⟪0⟫_leaf_checked_1 (Fin.cases record⟪0⟫_leaf_checked_2 (Fin.cases record⟪0⟫_leaf_checked_3 (Fin.cases record⟪0⟫_leaf_checked_4 (Fin.cases record⟪0⟫_leaf_checked_5 (Fin.cases record⟪0⟫_leaf_checked_6 (Fin.cases record⟪0⟫_leaf_checked_7 (fun j => Fin.elim0 j)))))))))"### args

elab "cert_graph_leaf_certificates_checked_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_leaf_certificates_checked : ∀ j : Fin record⟪0⟫.l,
    RawLeafCertificate.check record⟪0⟫.data.quota (record⟪0⟫_rawLeaves j)
      (record⟪0⟫_certificates j) = true :=
  (Fin.cases record⟪0⟫_leaf_checked_0 (Fin.cases record⟪0⟫_leaf_checked_1 (fun j => Fin.elim0 j)))"### args

elab "cert_graph_leaf_checked_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_leaf_checked_⟪1⟫ :
    RawLeafCertificate.check record⟪0⟫.data.quota (record⟪0⟫_rawLeaves ⟪1⟫)
      (record⟪0⟫_certificates ⟪1⟫) = true := by
  change RawLeafCertificate.check record⟪0⟫.data.quota (record⟪0⟫_rawLeaves ⟪1⟫)
    (.matching Nonrational.InducedTerminalMatches.M⟪2⟫.r⟪3⟫) = true
  exact matching_checked record⟪0⟫.data.quota (record⟪0⟫_rawLeaves ⟪1⟫) Nonrational.InducedTerminalMatches.M⟪2⟫.r⟪3⟫
    Nonrational.InducedTerminalMatches.M⟪2⟫.r⟪3⟫_checked (by decide +kernel)"### args

elab "cert_graph_leaf_checked_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_leaf_checked_0 :
    RawLeafCertificate.check record⟪0⟫.data.quota (record⟪0⟫_rawLeaves 0)
      (record⟪0⟫_certificates 0) = true := by
  change RawLeafCertificate.check record⟪0⟫.data.quota [] (.quota 1) = true
  exact empty_checked record⟪0⟫.data.quota 1 (by decide +kernel)"### args

elab "cert_graph_rawLeaves " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def record⟪0⟫_rawLeaves (j : Fin record⟪0⟫.l) : List Cell :=
  (record⟪0⟫.leaf j).map record⟪0⟫.data.cells"### args

elab "cert_graph_raw_exact " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_raw_exact (j : Fin record⟪0⟫.l) :
    (record⟪0⟫.leaf j).map record⟪0⟫.data.cells = record⟪0⟫_rawLeaves j := rfl"### args

