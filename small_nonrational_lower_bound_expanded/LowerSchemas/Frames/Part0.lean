module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_graph_frame_graph " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frame⟪1⟫_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group⟪2⟫.graphBitCheck record⟪0⟫.data.requiredEdges q = true := by decide +kernel"### args

elab "cert_graph_frame_indices " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def record⟪0⟫_frame⟪1⟫_indices (c : Fin record⟪0⟫.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group⟪2⟫.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group⟪2⟫.count (({ width := ⟪3⟫, code := (certNat% ⟪4⟫) } : Fields).get c.val)"### args

elab "cert_graph_frame_links " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frame⟪1⟫_links_⟪2⟫ : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group⟪3⟫.localPairCheck (embedding (N := 44310) record⟪0⟫) (record⟪0⟫.maps ⟪4⟫) (record⟪0⟫.inverseMaps ⟪4⟫) record⟪0⟫_frame⟪1⟫_indices (Fin.ofNat record⟪0⟫.n i)) ⟪5⟫ ⟪6⟫ :=
  interval_of_check _ ⟪5⟫ ⟪7⟫ (by decide +kernel)"### args

elab "cert_graph_frame_links_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frame⟪1⟫_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group⟪2⟫.localPairCheck (embedding (N := 44310) record⟪0⟫) (record⟪0⟫.maps ⟪3⟫)
      (record⟪0⟫.inverseMaps ⟪3⟫) record⟪0⟫_frame⟪1⟫_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 ⟪4⟫ record⟪0⟫_frame⟪1⟫_links_0000 (interval_append _ 64 128 ⟪4⟫ record⟪0⟫_frame⟪1⟫_links_0064 record⟪0⟫_frame⟪1⟫_links_0128))"### args

elab "cert_graph_frame_links_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frame⟪1⟫_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group⟪2⟫.localPairCheck (smallEmbedding record⟪0⟫) (record⟪0⟫.maps ⟪3⟫)
      (record⟪0⟫.inverseMaps ⟪3⟫) record⟪0⟫_frame⟪1⟫_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 ⟪4⟫ record⟪0⟫_frame⟪1⟫_links_0000 record⟪0⟫_frame⟪1⟫_links_0064)"### args

elab "cert_graph_frame_links_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frame⟪1⟫_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group⟪2⟫.localPairCheck (smallEmbedding record⟪0⟫) (record⟪0⟫.maps ⟪3⟫)
      (record⟪0⟫.inverseMaps ⟪3⟫) record⟪0⟫_frame⟪1⟫_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 ⟪4⟫ record⟪0⟫_frame⟪1⟫_links_0000 (interval_append _ 64 128 ⟪4⟫ record⟪0⟫_frame⟪1⟫_links_0064 record⟪0⟫_frame⟪1⟫_links_0128))"### args

elab "cert_graph_frame_links_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frame⟪1⟫_links_⟪2⟫ : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group⟪3⟫.localPairCheck (smallEmbedding record⟪0⟫) (record⟪0⟫.maps ⟪4⟫) (record⟪0⟫.inverseMaps ⟪4⟫) record⟪0⟫_frame⟪1⟫_indices (Fin.ofNat record⟪0⟫.n i)) ⟪5⟫ ⟪6⟫ :=
  interval_of_check _ ⟪5⟫ ⟪7⟫ (by decide +kernel)"### args

elab "cert_graph_frame_links_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frame⟪1⟫_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group⟪2⟫.localPairCheck (smallEmbedding record⟪0⟫) (record⟪0⟫.maps ⟪3⟫)
      (record⟪0⟫.inverseMaps ⟪3⟫) record⟪0⟫_frame⟪1⟫_indices c = true :=
  fin_of_interval _ record⟪0⟫_frame⟪1⟫_links_0000"### args

elab "cert_graph_frame_links_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frame⟪1⟫_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group⟪2⟫.localPairCheck (embedding (N := 44310) record⟪0⟫) (record⟪0⟫.maps ⟪3⟫)
      (record⟪0⟫.inverseMaps ⟪3⟫) record⟪0⟫_frame⟪1⟫_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 ⟪4⟫ record⟪0⟫_frame⟪1⟫_links_0000 record⟪0⟫_frame⟪1⟫_links_0064)"### args

elab "cert_graph_frame_supported " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frame⟪1⟫_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c)) : Supported record⟪0⟫ ⟪2⟫ :=
  of_group record⟪0⟫ ⟪2⟫ (smallEmbedding record⟪0⟫) (small_cells_exact record⟪0⟫ hcells) Papers.RationalityTen.SharedFrameCatalogue.group⟪3⟫
    Papers.RationalityTen.SharedFrameCatalogue.group⟪3⟫_facts record⟪0⟫_frame⟪1⟫_indices record⟪0⟫_frame⟪1⟫_graph record⟪0⟫_frame⟪1⟫_links"### args

elab "cert_graph_frame_supported_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frame000_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c)) :
    Supported record⟪0⟫ 0 :=
  of_identity record⟪0⟫ 0 (by decide +kernel)"### args

elab "cert_graph_frame_supported_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frame⟪1⟫_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSix0.cells (embedding record⟪0⟫ c)) : Supported record⟪0⟫ ⟪2⟫ :=
  of_group record⟪0⟫ ⟪2⟫ (embedding record⟪0⟫) hcells Papers.RationalityTen.SharedFrameCatalogue.group⟪3⟫
    Papers.RationalityTen.SharedFrameCatalogue.group⟪3⟫_facts record⟪0⟫_frame⟪1⟫_indices record⟪0⟫_frame⟪1⟫_graph record⟪0⟫_frame⟪1⟫_links"### args

elab "cert_graph_frame_supported_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frame000_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSix0.cells (embedding record⟪0⟫ c)) :
    Supported record⟪0⟫ 0 :=
  of_identity record⟪0⟫ 0 (by decide +kernel)"### args

elab "cert_graph_frames_supported " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSix0.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (Fin.cases (record⟪0⟫_frame003_supported hcells) (Fin.cases (record⟪0⟫_frame004_supported hcells) (Fin.cases (record⟪0⟫_frame005_supported hcells) (fun j => Fin.elim0 j)))))))"### args

elab "cert_graph_frames_supported_10 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSix0.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (Fin.cases (record⟪0⟫_frame003_supported hcells) (Fin.cases (record⟪0⟫_frame004_supported hcells) (Fin.cases (record⟪0⟫_frame005_supported hcells) (Fin.cases (record⟪0⟫_frame006_supported hcells) (fun j => Fin.elim0 j))))))))"### args

elab "cert_graph_frames_supported_11 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSix0.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (fun j => Fin.elim0 j)))"### args

elab "cert_graph_frames_supported_12 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSix0.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (Fin.cases (record⟪0⟫_frame003_supported hcells) (Fin.cases (record⟪0⟫_frame004_supported hcells) (Fin.cases (record⟪0⟫_frame005_supported hcells) (Fin.cases (record⟪0⟫_frame006_supported hcells) (Fin.cases (record⟪0⟫_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))"### args

elab "cert_graph_frames_supported_13 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSix0.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (Fin.cases (record⟪0⟫_frame003_supported hcells) (fun j => Fin.elim0 j)))))"### args

elab "cert_graph_frames_supported_14 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (Fin.cases (record⟪0⟫_frame003_supported hcells) (Fin.cases (record⟪0⟫_frame004_supported hcells) (Fin.cases (record⟪0⟫_frame005_supported hcells) (Fin.cases (record⟪0⟫_frame006_supported hcells) (Fin.cases (record⟪0⟫_frame007_supported hcells) (Fin.cases (record⟪0⟫_frame008_supported hcells) (Fin.cases (record⟪0⟫_frame009_supported hcells) (Fin.cases (record⟪0⟫_frame010_supported hcells) (Fin.cases (record⟪0⟫_frame011_supported hcells) (Fin.cases (record⟪0⟫_frame012_supported hcells) (Fin.cases (record⟪0⟫_frame013_supported hcells) (Fin.cases (record⟪0⟫_frame014_supported hcells) (fun j => Fin.elim0 j))))))))))))))))"### args

elab "cert_graph_frames_supported_15 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (Fin.cases (record⟪0⟫_frame003_supported hcells) (Fin.cases (record⟪0⟫_frame004_supported hcells) (Fin.cases (record⟪0⟫_frame005_supported hcells) (Fin.cases (record⟪0⟫_frame006_supported hcells) (Fin.cases (record⟪0⟫_frame007_supported hcells) (Fin.cases (record⟪0⟫_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))"### args

elab "cert_graph_frames_supported_16 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (fun j => Fin.elim0 j))))"### args

elab "cert_graph_frames_supported_17 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSix0.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (fun j => Fin.elim0 j))))"### args

elab "cert_graph_frames_supported_18 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (fun j => Fin.elim0 j))"### args

elab "cert_graph_frames_supported_19 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (Fin.cases (record⟪0⟫_frame003_supported hcells) (Fin.cases (record⟪0⟫_frame004_supported hcells) (Fin.cases (record⟪0⟫_frame005_supported hcells) (Fin.cases (record⟪0⟫_frame006_supported hcells) (fun j => Fin.elim0 j))))))))"### args

elab "cert_graph_frames_supported_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSix0.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (fun j => Fin.elim0 j))"### args

elab "cert_graph_frames_supported_20 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (fun j => Fin.elim0 j)))"### args

elab "cert_graph_frames_supported_21 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (Fin.cases (record⟪0⟫_frame003_supported hcells) (Fin.cases (record⟪0⟫_frame004_supported hcells) (Fin.cases (record⟪0⟫_frame005_supported hcells) (Fin.cases (record⟪0⟫_frame006_supported hcells) (Fin.cases (record⟪0⟫_frame007_supported hcells) (Fin.cases (record⟪0⟫_frame008_supported hcells) (Fin.cases (record⟪0⟫_frame009_supported hcells) (Fin.cases (record⟪0⟫_frame010_supported hcells) (Fin.cases (record⟪0⟫_frame011_supported hcells) (Fin.cases (record⟪0⟫_frame012_supported hcells) (Fin.cases (record⟪0⟫_frame013_supported hcells) (Fin.cases (record⟪0⟫_frame014_supported hcells) (Fin.cases (record⟪0⟫_frame015_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))"### args

elab "cert_graph_frames_supported_22 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (Fin.cases (record⟪0⟫_frame003_supported hcells) (Fin.cases (record⟪0⟫_frame004_supported hcells) (Fin.cases (record⟪0⟫_frame005_supported hcells) (Fin.cases (record⟪0⟫_frame006_supported hcells) (Fin.cases (record⟪0⟫_frame007_supported hcells) (Fin.cases (record⟪0⟫_frame008_supported hcells) (Fin.cases (record⟪0⟫_frame009_supported hcells) (Fin.cases (record⟪0⟫_frame010_supported hcells) (Fin.cases (record⟪0⟫_frame011_supported hcells) (fun j => Fin.elim0 j)))))))))))))"### args

elab "cert_graph_frames_supported_23 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (Fin.cases (record⟪0⟫_frame003_supported hcells) (Fin.cases (record⟪0⟫_frame004_supported hcells) (Fin.cases (record⟪0⟫_frame005_supported hcells) (Fin.cases (record⟪0⟫_frame006_supported hcells) (Fin.cases (record⟪0⟫_frame007_supported hcells) (Fin.cases (record⟪0⟫_frame008_supported hcells) (Fin.cases (record⟪0⟫_frame009_supported hcells) (fun j => Fin.elim0 j)))))))))))"### args

elab "cert_graph_frames_supported_24 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (Fin.cases (record⟪0⟫_frame003_supported hcells) (Fin.cases (record⟪0⟫_frame004_supported hcells) (Fin.cases (record⟪0⟫_frame005_supported hcells) (Fin.cases (record⟪0⟫_frame006_supported hcells) (Fin.cases (record⟪0⟫_frame007_supported hcells) (Fin.cases (record⟪0⟫_frame008_supported hcells) (Fin.cases (record⟪0⟫_frame009_supported hcells) (Fin.cases (record⟪0⟫_frame010_supported hcells) (fun j => Fin.elim0 j))))))))))))"### args

elab "cert_graph_frames_supported_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (Fin.cases (record⟪0⟫_frame003_supported hcells) (Fin.cases (record⟪0⟫_frame004_supported hcells) (Fin.cases (record⟪0⟫_frame005_supported hcells) (Fin.cases (record⟪0⟫_frame006_supported hcells) (Fin.cases (record⟪0⟫_frame007_supported hcells) (Fin.cases (record⟪0⟫_frame008_supported hcells) (Fin.cases (record⟪0⟫_frame009_supported hcells) (Fin.cases (record⟪0⟫_frame010_supported hcells) (Fin.cases (record⟪0⟫_frame011_supported hcells) (Fin.cases (record⟪0⟫_frame012_supported hcells) (Fin.cases (record⟪0⟫_frame013_supported hcells) (fun j => Fin.elim0 j)))))))))))))))"### args

elab "cert_graph_frames_supported_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (Fin.cases (record⟪0⟫_frame003_supported hcells) (Fin.cases (record⟪0⟫_frame004_supported hcells) (Fin.cases (record⟪0⟫_frame005_supported hcells) (Fin.cases (record⟪0⟫_frame006_supported hcells) (Fin.cases (record⟪0⟫_frame007_supported hcells) (Fin.cases (record⟪0⟫_frame008_supported hcells) (Fin.cases (record⟪0⟫_frame009_supported hcells) (Fin.cases (record⟪0⟫_frame010_supported hcells) (Fin.cases (record⟪0⟫_frame011_supported hcells) (Fin.cases (record⟪0⟫_frame012_supported hcells) (fun j => Fin.elim0 j))))))))))))))"### args

elab "cert_graph_frames_supported_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSix0.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (Fin.cases (record⟪0⟫_frame003_supported hcells) (Fin.cases (record⟪0⟫_frame004_supported hcells) (fun j => Fin.elim0 j))))))"### args

elab "cert_graph_frames_supported_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (Fin.cases (record⟪0⟫_frame003_supported hcells) (fun j => Fin.elim0 j)))))"### args

elab "cert_graph_frames_supported_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (Fin.cases (record⟪0⟫_frame003_supported hcells) (Fin.cases (record⟪0⟫_frame004_supported hcells) (fun j => Fin.elim0 j))))))"### args

elab "cert_graph_frames_supported_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (Fin.cases (record⟪0⟫_frame003_supported hcells) (Fin.cases (record⟪0⟫_frame004_supported hcells) (Fin.cases (record⟪0⟫_frame005_supported hcells) (Fin.cases (record⟪0⟫_frame006_supported hcells) (Fin.cases (record⟪0⟫_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))"### args

elab "cert_graph_frames_supported_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record⟪0⟫_frames_supported (hcells : ∀ c, record⟪0⟫.data.cells c = FacetUniverses.FullSmall.cells (embedding record⟪0⟫ c)) :
    ∀ f : Fin record⟪0⟫.g, Supported record⟪0⟫ f :=
  (Fin.cases (record⟪0⟫_frame000_supported hcells) (Fin.cases (record⟪0⟫_frame001_supported hcells) (Fin.cases (record⟪0⟫_frame002_supported hcells) (Fin.cases (record⟪0⟫_frame003_supported hcells) (Fin.cases (record⟪0⟫_frame004_supported hcells) (Fin.cases (record⟪0⟫_frame005_supported hcells) (fun j => Fin.elim0 j)))))))"### args

