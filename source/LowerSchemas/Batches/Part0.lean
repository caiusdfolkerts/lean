module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_certificate " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def certificate : ReconstructionCertificate boundary ⟪0⟫ where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin ⟪1⟫, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j"### args

elab "cert_cover " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def cover⟪0⟫ : FacetCoverage heightProof coverFacet⟪0⟫ :=
  .fromLargerFacet ![⟪3⟫, ⟪4⟫, ⟪1⟫, ⟪7⟫] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_⟪9⟫, (by decide +kernel)⟩ ⟨vertices_⟪10⟫, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_⟪11⟫, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_⟪13⟫, by decide +kernel⟩ ![⟪6⟫, ⟪2⟫, ⟪8⟫, ⟪14⟫]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_⟪12⟫, (by decide +kernel)⟩ ⟨vertices_⟪13⟫, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) ⟪5⟫ (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)"### args

elab "cert_coverFacet " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def coverFacet⟪0⟫ : boundary.facets := ⟨vertices_⟪1⟫, by decide +kernel⟩"### args

elab "cert_cover_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def cover⟪0⟫ : FacetCoverage heightProof coverFacet⟪0⟫ :=
  .fundamental ![⟪2⟫, ⟪1⟫, ⟪3⟫, ⟪4⟫] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_⟪5⟫, (by decide +kernel)⟩ ⟨vertices_⟪6⟫, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) ⟪7⟫ (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)"### args

elab "cert_cover_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def cover⟪0⟫ : FacetCoverage heightProof coverFacet⟪0⟫ :=
  .oneRow ![⟪1⟫, ⟪3⟫, ⟪4⟫, ⟪5⟫] (frameCertificate_of_valid boundary _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) ⟪2⟫ (by decide +kernel)"### args

elab "cert_cover_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def cover⟪0⟫ : FacetCoverage heightProof coverFacet⟪0⟫ :=
  .fundamental ![⟪1⟫, ⟪2⟫, ⟪3⟫, ⟪4⟫] (frameCertificate_of_valid boundary _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)"### args

elab "cert_cover_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def cover⟪0⟫ : FacetCoverage heightProof coverFacet⟪0⟫ :=
  .oneRow ![⟪2⟫, ⟪3⟫, ⟪4⟫, ⟪5⟫] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_⟪6⟫, (by decide +kernel)⟩ ⟨vertices_⟪7⟫, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) ⟪8⟫ (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) ⟪1⟫ (by decide +kernel)"### args

elab "cert_coveringFacets " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def coveringFacets : Fin 6 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5]"### args

elab "cert_coveringFacets_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]"### args

elab "cert_coveringFacets_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def coveringFacets : Fin 5 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4]"### args

elab "cert_coveringFacets_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def coveringFacets : Fin 7 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6]"### args

elab "cert_coveringFacets_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def coveringFacets : Fin 10 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8, coverFacet9]"### args

elab "cert_coveringFacets_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def coveringFacets : Fin 11 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8, coverFacet9, coverFacet10]"### args

elab "cert_coveringFacets_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def coveringFacets : Fin 8 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7]"### args

elab "cert_coveringProof " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def coveringProof (j : Fin 10) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (Fin.cases cover9 (fun i => Fin.elim0 i))))))))))) j"### args

elab "cert_coveringProof_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def coveringProof (j : Fin 8) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (fun i => Fin.elim0 i))))))))) j"### args

elab "cert_coveringProof_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def coveringProof (j : Fin 11) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (Fin.cases cover9 (Fin.cases cover10 (fun i => Fin.elim0 i)))))))))))) j"### args

elab "cert_coveringProof_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j"### args

elab "cert_coveringProof_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def coveringProof (j : Fin 7) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (fun i => Fin.elim0 i)))))))) j"### args

elab "cert_coveringProof_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def coveringProof (j : Fin 6) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (fun i => Fin.elim0 i))))))) j"### args

elab "cert_coveringProof_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def coveringProof (j : Fin 5) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (fun i => Fin.elim0 i)))))) j"### args

elab "cert_heightProof " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def heightProof : HeightCertificate boundary ⟪0⟫ :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)"### args

elab "cert_incidenceProof " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)"### args

elab "cert_nodeAtPriority " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 13 => Sum.inl ⟪0⟫
  | 14 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 15 => Sum.inl ⟪2⟫
  | 16 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 19 => Sum.inl ⟪4⟫
  | 20 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_10 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inl ⟪0⟫
  | 13 => Sum.inr ⟨(false, vertices_⟪14⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 15 => Sum.inl ⟪2⟫
  | 16 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_11 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_⟪13⟫), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_⟪14⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_12 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 15 => Sum.inl ⟪1⟫
  | 16 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 18 => Sum.inl ⟪3⟫
  | 19 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_13 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_14 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_⟪18⟫), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_15 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 14 => Sum.inl ⟪0⟫
  | 15 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 17 => Sum.inl ⟪2⟫
  | 18 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_16 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_17 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_⟪13⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_18 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_⟪11⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_⟪12⟫), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_⟪13⟫), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_⟪14⟫), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_19 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 15 => Sum.inl ⟪0⟫
  | 16 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_⟪18⟫), by decide +kernel⟩
  | 18 => Sum.inl ⟪2⟫
  | 19 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 13 => Sum.inl ⟪0⟫
  | 14 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 15 => Sum.inl ⟪2⟫
  | 16 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_⟪19⟫), by decide +kernel⟩
  | 18 => Sum.inl ⟪4⟫
  | 19 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 21 => Sum.inl ⟪6⟫
  | 22 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_20 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inl ⟪0⟫
  | 13 => Sum.inr ⟨(false, vertices_⟪14⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 15 => Sum.inl ⟪2⟫
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_21 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 16 => Sum.inl ⟪0⟫
  | 17 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_⟪19⟫), by decide +kernel⟩
  | 19 => Sum.inl ⟪2⟫
  | 20 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_⟪23⟫), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_22 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_23 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_⟪14⟫), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_24 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 16 => Sum.inl ⟪2⟫
  | 17 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_⟪19⟫), by decide +kernel⟩
  | 19 => Sum.inl ⟪0⟫
  | 20 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_⟪23⟫), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_25 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 14 => Sum.inl ⟪0⟫
  | 15 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 17 => Sum.inl ⟪2⟫
  | 18 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_26 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_⟪12⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_⟪13⟫), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_⟪14⟫), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_27 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 14 => Sum.inl ⟪0⟫
  | 15 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 17 => Sum.inl ⟪2⟫
  | 18 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_28 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inl ⟪0⟫
  | 14 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 16 => Sum.inl ⟪2⟫
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_⟪18⟫), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_29 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_⟪13⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_⟪14⟫), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_⟪9⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_⟪11⟫), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_⟪12⟫), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_⟪13⟫), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_30 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inl ⟪0⟫
  | 14 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 16 => Sum.inl ⟪2⟫
  | 17 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_31 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_32 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_33 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_⟪18⟫), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_34 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_35 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_⟪11⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_⟪12⟫), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_⟪13⟫), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_⟪14⟫), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_36 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 15 => Sum.inl ⟪0⟫
  | 16 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 17 => Sum.inl ⟪2⟫
  | 18 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 21 => Sum.inl ⟪4⟫
  | 22 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_⟪23⟫), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_37 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_⟪13⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_38 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_⟪11⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_⟪12⟫), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_⟪13⟫), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_39 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 16 => Sum.inl ⟪0⟫
  | 17 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_⟪19⟫), by decide +kernel⟩
  | 19 => Sum.inl ⟪2⟫
  | 20 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_⟪23⟫), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 14 => Sum.inl ⟪0⟫
  | 15 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 17 => Sum.inl ⟪2⟫
  | 18 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_40 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_41 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inl ⟪2⟫
  | 11 => Sum.inr ⟨(false, vertices_⟪12⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_⟪13⟫), by decide +kernel⟩
  | 13 => Sum.inl ⟪0⟫
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_⟪14⟫), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_42 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 17 => Sum.inl ⟪3⟫
  | 18 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 20 => Sum.inl ⟪1⟫
  | 21 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_43 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 17 => Sum.inl ⟪3⟫
  | 18 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_⟪19⟫), by decide +kernel⟩
  | 20 => Sum.inl ⟪1⟫
  | 21 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_44 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_⟪14⟫), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_45 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_⟪18⟫), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_46 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_⟪14⟫), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_47 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_⟪14⟫), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_48 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 14 => Sum.inl ⟪0⟫
  | 15 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 16 => Sum.inl ⟪4⟫
  | 17 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 19 => Sum.inl ⟪2⟫
  | 20 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_49 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_⟪13⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 16 => Sum.inl ⟪0⟫
  | 17 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_⟪19⟫), by decide +kernel⟩
  | 19 => Sum.inl ⟪2⟫
  | 20 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_⟪23⟫), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_50 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 16 => Sum.inl ⟪2⟫
  | 17 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_⟪19⟫), by decide +kernel⟩
  | 19 => Sum.inl ⟪0⟫
  | 20 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_⟪23⟫), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_51 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_52 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 17 => Sum.inl ⟪1⟫
  | 18 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 20 => Sum.inl ⟪3⟫
  | 21 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_53 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 14 => Sum.inl ⟪0⟫
  | 15 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 17 => Sum.inl ⟪2⟫
  | 18 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_54 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_⟪14⟫), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_55 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_⟪11⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_⟪12⟫), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_⟪13⟫), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_56 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_⟪13⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_57 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_⟪13⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_58 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inl ⟪2⟫
  | 12 => Sum.inr ⟨(false, vertices_⟪13⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_⟪14⟫), by decide +kernel⟩
  | 14 => Sum.inl ⟪0⟫
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_59 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 11 => Sum.inl ⟪0⟫
  | 12 => Sum.inr ⟨(false, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inl ⟪2⟫
  | 14 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 16 => Sum.inl ⟪4⟫
  | 17 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_⟪21⟫), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_60 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_⟪20⟫), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_61 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 16 => Sum.inl ⟪0⟫
  | 17 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 19 => Sum.inl ⟪2⟫
  | 20 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_⟪21⟫), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_⟪23⟫), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_62 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_63 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_⟪18⟫), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_64 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_65 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪17⟫), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 17 => Sum.inl ⟪3⟫
  | 18 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_⟪20⟫), by decide +kernel⟩
  | 20 => Sum.inl ⟪1⟫
  | 21 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 23 => Sum.inl ⟪5⟫
  | 24 => Sum.inr ⟨(false, vertices_⟪23⟫), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_66 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪0⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪2⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_⟪18⟫), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_67 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inl ⟪0⟫
  | 13 => Sum.inr ⟨(false, vertices_⟪14⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 15 => Sum.inl ⟪2⟫
  | 16 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_68 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 15 => Sum.inl ⟪0⟫
  | 16 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 17 => Sum.inl ⟪2⟫
  | 18 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_⟪13⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_⟪14⟫), by decide +kernel⟩
  | 12 => Sum.inl ⟪0⟫
  | 13 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 15 => Sum.inl ⟪2⟫
  | 16 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 18 => Sum.inl ⟪4⟫
  | 19 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inl ⟪2⟫
  | 13 => Sum.inr ⟨(false, vertices_⟪14⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_⟪15⟫), by decide +kernel⟩
  | 15 => Sum.inl ⟪0⟫
  | 16 => Sum.inr ⟨(false, vertices_⟪16⟫), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_⟪19⟫), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_nodeAtPriority_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_⟪1⟫), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_⟪3⟫), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_⟪4⟫), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_⟪5⟫), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_⟪6⟫), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_⟪7⟫), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_⟪8⟫), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_⟪9⟫), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_⟪10⟫), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_⟪11⟫), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_⟪12⟫), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_⟪13⟫), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_⟪14⟫), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_⟪15⟫), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_⟪16⟫), by decide +kernel⟩
  | 15 => Sum.inl ⟪0⟫
  | 16 => Sum.inr ⟨(false, vertices_⟪17⟫), by decide +kernel⟩
  | 17 => Sum.inl ⟪2⟫
  | 18 => Sum.inr ⟨(false, vertices_⟪18⟫), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_⟪19⟫), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_⟪20⟫), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_⟪21⟫), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_⟪22⟫), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0"### args

elab "cert_pivot " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def pivot : Fin 5 → Fin 9 := ![⟪0⟫, ⟪1⟫, ⟪2⟫, ⟪3⟫, ⟪4⟫]"### args

elab "cert_pivot_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def pivot : Fin 4 → Fin 9 := ![⟪0⟫, ⟪1⟫, ⟪2⟫, ⟪3⟫]"### args

elab "cert_pivot_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def pivot : Fin 3 → Fin 9 := ![⟪1⟫, ⟪0⟫, ⟪2⟫]"### args

elab "cert_pointPriority " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def pointPriority : Fin 9 → ℕ := ![⟪0⟫, ⟪1⟫, ⟪2⟫, ⟪3⟫, ⟪4⟫, ⟪5⟫, ⟪6⟫, ⟪7⟫, ⟪8⟫]"### args

elab "cert_priority " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority"### args

elab "cert_priority_injective " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)"### args

elab "cert_row " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def row⟪0⟫ : HeightRow boundary where
  frameSize := 4
  frame := ![⟪2⟫, ⟪3⟫, ⟪4⟫, ⟪5⟫]
  vertex := ⟪1⟫
  face := Sum.inl ⟨vertices_⟪6⟫, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := frameCertificate_of_valid boundary _ (by decide +kernel)
  spanning_certificate := by decide +kernel"### args

elab "cert_row_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def row⟪0⟫ : HeightRow boundary where
  frameSize := 3
  frame := ![⟪1⟫, ⟪2⟫, ⟪3⟫]
  vertex := ⟪4⟫
  face := Sum.inr ⟨vertices_⟪5⟫, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_⟪5⟫, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel"### args

elab "cert_row_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def row⟪0⟫ : HeightRow boundary where
  frameSize := 3
  frame := ![⟪2⟫, ⟪1⟫, ⟪3⟫]
  vertex := ⟪4⟫
  face := Sum.inr ⟨vertices_⟪5⟫, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := frameCertificate_of_valid boundary _ (by decide +kernel)
  spanning_certificate := by decide +kernel"### args

elab "cert_row_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def row⟪0⟫ : HeightRow boundary where
  frameSize := 4
  frame := ![⟪1⟫, ⟪2⟫, ⟪3⟫, ⟪4⟫]
  vertex := ⟪5⟫
  face := Sum.inl ⟨vertices_⟪6⟫, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_⟪7⟫, (by decide +kernel)⟩ ⟨vertices_⟪6⟫, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) ⟪8⟫ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel"### args

elab "cert_rows " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]"### args

elab "cert_rows_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def rows : Fin 5 → HeightRow boundary := ![row0, row1, row2, row3, row4]"### args

elab "cert_rows_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def rows : Fin 3 → HeightRow boundary := ![row0, row1, row2]"### args

