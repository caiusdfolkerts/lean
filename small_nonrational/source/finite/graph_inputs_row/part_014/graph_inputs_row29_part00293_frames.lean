module
prelude
public import GraphInputsRow29Part00293Data
public import RawFrameSupport
public import SharedFrameGroups006Checked
public import SharedFrameGroups011Checked
public import SharedFrameGroups012Checked
public import SharedFrameGroups013Checked
public import SharedFrameGroups018Checked
public import SharedFrameGroups019Checked
public import SharedFrameGroups020Checked
public import SharedFrameGroups021Checked
public import SharedFrameGroups022Checked
public import SharedFrameGroups023Checked
public import SharedFrameGroups024Checked
public import SharedFrameGroups025Checked
public import SharedFrameGroups026Checked
public import SharedFrameGroups027Checked
public import SharedFrameGroups028Checked
public import SharedFrameGroups029Checked
public import SharedFrameGroups033Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups043Checked
public import SharedFrameGroups044Checked
public import SharedFrameGroups045Checked
public import SharedFrameGroups046Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups058Checked
public import SharedFrameGroups059Checked
public import SharedFrameGroups061Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups064Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups072Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups081Checked
public import SharedFrameGroups082Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups097Checked
public import SharedFrameGroups098Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups110Checked
public import SharedFrameGroups111Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00293
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1c6ae287113661aead6567fb371998bc65d12e39648b005762b6d5aaace563ab01572aad5532a7d4129db4e1a6b53369894bca59d2ac937492a4491f48e846b23191688a344221c90be76a3a21cc4d8069a34399f0cea66f3341984cb4653325190cc7a5c32ce9624af856f2b11550a8c538294944ca0a4f727793889aa4c725c92ac93848623c11a87863981c08db46be34f19f8cc063e2fa1750b645982be1570a7851e27e12c8924470231115088c43821610307c83c01cc0db86882f01660a9851827412f09184642120fd07903981b8042020810007003701b00a4050027008804001e00e006002c0140090030014008003 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record000_frame001_links_0000 (interval_append _ 64 128 150 record000_frame001_links_0064 record000_frame001_links_0128))
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1ce8e52720b6d1b24d816a4b4eda68c115f4af556b8b3c5942c49600aee56dab1d566a95541a9c13e09d04de26993289824b7a56d28e92948ba4111de8e8470a3691a68cc46022e51647b03c61de8e0e6e736b9b1cd6e6a634a1a10cea66232398d0c465b22c91608ae45622a894fca5e52028693c89be4ce26413049744b3256929893e49624792207ac3ab1cb0dfc6d43571a08cb06322ec16b0b0c5722a914c8a284f426b12408e045221b10607f83e01e60eb071836c1a70cb86202ca1550a304e025211b086840c1ee0f007483881b8042020810007003701b00a4050027008804001e00e006002c0140090030014008003 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record000_frame002_links_0000 (interval_append _ 64 128 150 record000_frame002_links_0064 record000_frame002_links_0128))
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1091.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1091.count (({ width := 10, code := 0xa067f9f6789da749be6d9ae5894a5192a4490e418f63a8de348c22a89e238661384a108320981a037fdf97d9f27b5e9799e3781dc759d373dbf6e5b86c1aa6a5a6691a06759a65d926398b621805e9795d9745c16d5a9675895e56d585555353d4c525465053d4e9374ad2849d244811c45912435023f8fb3e0f43c0ea398e1358d233cca318c3300bc2e0b42c0aa298a12589223c8a218832007c1d8721bc6c1a0370d8350c02f0b82408c220441003c0e0300b028090180501003 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record000_frame003_links_0000 (interval_append _ 64 128 150 record000_frame003_links_0064 record000_frame003_links_0128))
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1091
    Papers.RationalityTen.SharedFrameCatalogue.group1091_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1094.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1094.count (({ width := 9, code := 0x3037fbf5eef378badcee569b3596c15dae56eb358ab556a950a752e8b42a0d027d3d9dcea733599cc25d2c95ca6512791c863d1689c4a1d0b854220f068240e04ff7ebedf2f5793c5deee76badd4e973391c4e06f375b8da6cb61aad368b3d90c76331180be5d2dd68ac54aa14aa14fa6d309546a29128541a04fc7b3c1d0e46e359a0c05d2e160ac542893894482310c802713094462210874381b088401e0e0602c1409030140803 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1094.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record000_frame004_links_0000 (interval_append _ 64 128 150 record000_frame004_links_0064 record000_frame004_links_0128))
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1094
    Papers.RationalityTen.SharedFrameCatalogue.group1094_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
def record000_frame005_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xc01bf0be9bb1b99b91b67b4bb3fa65a4ca42a109f49e89d79c89c19b59a399497796895a90b8e98d98c68b48a989b8898798598458318138037f87ed7d77c37a278d7786aa69568b65864063662b61d61360b5fe5f35e55d05c45b457755d55054353352851f5115044f44dc4ce4bf4b64a749c49348547a46c4544454383a538b37e36b35834d34133131f2f62e62d42c72b72ad2a12932862612512422322232132011f41e21d51cd1c41b51a81831741671551431331231161020f50e80da0cf04204104003803703602902802701101000f00e00c00b00a009006005004003 } : Fields).get c.val)
theorem record000_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record000_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record000) (record000.maps 5)
      (record000.inverseMaps 5) record000_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record000_frame005_links_0000 (interval_append _ 64 128 150 record000_frame005_links_0064 record000_frame005_links_0128))
theorem record000_frame005_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 5 :=
  of_group record000 5 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record000_frame005_indices record000_frame005_graph record000_frame005_links
def record000_frame006_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x76675f75d73572671a6fe6f16ea67c66765a63862461e61260e60b6055ff5fb5f25ed5e85b159a58c58157556e56455754d53852a52050e5054fa4f04e64dc4c44ba4ac44d43942f40f3fd3f63ee3ea3e73e13dc3d83d43cc3c73c238c37836d36635e35935334a34133932831e31631230b3042fe2f52ef2e42d32ca2c127225c25024523e23923022621b2051fa1f01ea1e41de1d51c91c41a81a119518f18a18618117b17216715f15514613a11c1101030fa0f20e90e20d90cc0c30bd0b40ab04003f03e03803703602902802701101000f00e00c00b00a009006005004003 } : Fields).get c.val)
theorem record000_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record000_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record000) (record000.maps 6)
      (record000.inverseMaps 6) record000_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record000_frame006_links_0000 (interval_append _ 64 128 150 record000_frame006_links_0064 record000_frame006_links_0128))
theorem record000_frame006_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 6 :=
  of_group record000 6 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record000_frame006_indices record000_frame006_graph record000_frame006_links
def record000_frame007_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1a2ad07680b2f9956ca262fb115874b3858fac55592ab05542a6d516a7f53a29a14c0a44516286537099b4c825fd2dc95c4a5a4e525a90e47ba38518a8b3450a2410fc87242aa0fd0547423961c94daa6bb3591a9cd3268833e19accc265631e18a8c325cf2dc16c4b5259a2c695f8ae25662ad9500a6252328e142c9f84ed26f134c98e4ac24e923c7c63c71df0eb473638c1bd8db06c43391928c4c60c2f41718b4c5842b814809f44d625912388d04442120fe87b83c01d10e186e43281830b9859029e140098048c21e0ff07903941b2042020810007003701b00a4050027008804001e00e006002c0140090030014008003 } : Fields).get c.val)
theorem record000_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record000_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 7)
      (record000.inverseMaps 7) record000_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record000_frame007_links_0000 (interval_append _ 64 128 150 record000_frame007_links_0064 record000_frame007_links_0128))
theorem record000_frame007_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 7 :=
  of_group record000 7 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record000_frame007_indices record000_frame007_graph record000_frame007_links
def record000_frame008_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x81580a8067d57c87c17a27977927127006fa6c46b36ab6a169768b68167867265e65064460b5f95f05e65dd5d45cc5c05b75a359558a57c57556e56756055b5505495424c04ab4a546545344e44643a4304244194104063ee3e23d739b38938137936f36435934f34333932131530a3073002f92f22eb2e62e02d72cf2c826725024823c23222421a20c2041e61dc1d21cb1c31bc1b51ae1a819318c18317a16e16715e15914b14313c13512e12811310a1040fa0ee0e50e00d90ce0c90c30c00be04204104003803703602902802701101000f00e00c00b00a009006005004003 } : Fields).get c.val)
theorem record000_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record000) (record000.maps 8) (record000.inverseMaps 8) record000_frame008_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record000) (record000.maps 8) (record000.inverseMaps 8) record000_frame008_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record000) (record000.maps 8) (record000.inverseMaps 8) record000_frame008_indices (Fin.ofNat record000.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record000_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record000) (record000.maps 8)
      (record000.inverseMaps 8) record000_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record000_frame008_links_0000 (interval_append _ 64 128 150 record000_frame008_links_0064 record000_frame008_links_0128))
theorem record000_frame008_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 8 :=
  of_group record000 8 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record000_frame008_indices record000_frame008_graph record000_frame008_links
def record000_frame009_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0988.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0988.count (({ width := 9, code := 0x225118843e1d0d8642e14ff7f3f5f8fb7d3e5eef579bc5deec753a1cce57238dc2df6eb6db2d66a349a0ce6632990c661b057ebd5e2ed74b95c2dd6ab358abd5aab5429948a351285409e4e26930964a2451e8d46229108642209007d3d9e4f0773b1d4e873391c4e06d359a4d06733194c86330178b85b2d164b0572b154a853291449c4c25124904723114884321104802a148a04e261287c3c1d088401e0e0602c1409030140803 } : Fields).get c.val)
theorem record000_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0988.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0988.localPairCheck (smallEmbedding record000) (record000.maps 9) (record000.inverseMaps 9) record000_frame009_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0988.localPairCheck (smallEmbedding record000) (record000.maps 9) (record000.inverseMaps 9) record000_frame009_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0988.localPairCheck (smallEmbedding record000) (record000.maps 9) (record000.inverseMaps 9) record000_frame009_indices (Fin.ofNat record000.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record000_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0988.localPairCheck (smallEmbedding record000) (record000.maps 9)
      (record000.inverseMaps 9) record000_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record000_frame009_links_0000 (interval_append _ 64 128 150 record000_frame009_links_0064 record000_frame009_links_0128))
theorem record000_frame009_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 9 :=
  of_group record000 9 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0988
    Papers.RationalityTen.SharedFrameCatalogue.group0988_facts record000_frame009_indices record000_frame009_graph record000_frame009_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (Fin.cases (record000_frame005_supported hcells) (Fin.cases (record000_frame006_supported hcells) (Fin.cases (record000_frame007_supported hcells) (Fin.cases (record000_frame008_supported hcells) (Fin.cases (record000_frame009_supported hcells) (fun j => Fin.elim0 j)))))))))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1a5ad2668fb461a22d0a681b3f19eacea58aac0d5e2ade5652ad9546a8f53f29793529974c2a5c92bc94a49ba48d2248f2477a3a11c28da469a33118a8be45ba2b91568a444ea25911e6c435a1a8cd22681339197cc986392b7957ca9c53c2961474a144f727213209824ba25992b494c49f24c124491048123d91d48de4691c10db46b43441978c7060e2f316e8b085722a914c8a284f426b12d893047821910507f03dc1e00eb071836c1a70cb86202f01690ac84d824e11908583f41ee0f007483881b60d5057826c0dc05f02000d806a03401980c80620270130094048023011004801800b00500240100060028010006002 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame001_links_0000 (interval_append _ 64 128 150 record001_frame001_links_0064 record001_frame001_links_0128))
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x2bc574add5a6b2d61ab554ea75449a333663cc297d2ea59cac94f2763245d8ab13e24c438790d616c2483f0620840a808ff9fbbf07d0f7dee3d87a8f41e635d6b0d4da7349688cf99c3315b0b4164ac357caed59aa9544a4945a834f69d938a694bc9512323e4708cd172283b0744e49c13786dcd79a4334630c297d2ec5c0b59682c0558a793e2704cc971282464708a90f2124087e0f51dc3806c8d219c320610bb1682c0550a712c2183285607e0d81a8340660c81882704c094120230440480600b0140240400600a01001802 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame002_links_0000 (interval_append _ 64 128 150 record001_frame002_links_0064 record001_frame002_links_0128))
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1092.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1092.count (({ width := 9, code := 0x2f578bb5d2e571b7db6d768ab552a550a75369749a3d1277399bcd66732984ba59299449a49229047e3b1b8cc5a2b1489c4a23007f3f1f4f87bbd5e6f071b85bedd6db69b0d669b3596c96331586c15f2ed6eb559ac560ae52289409d4e2693095492391a8b44a1d0a8441200fa773a9cce470379b4d66933998c8622f964ae552a148a04e2612c92481e8cc52200e86832180b8582a12088401e0e068281208038180a04018080200 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame003_links_0000 (interval_append _ 64 128 150 record001_frame003_links_0064 record001_frame003_links_0128))
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1092
    Papers.RationalityTen.SharedFrameCatalogue.group1092_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1089.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1089.count (({ width := 9, code := 0x2c761af56eb357aa5469f4aa1d067d3b9ccde693197caa4d2490c7a391a8bc52250d8642a0f0481401fafa7c3cde4f1783bddce974399cae471b85bede6cb61acd56a34da2cf6732d90c661b057cbb5cad962af572b156aa53a91449f4ea692e9549235188b44a210e8642209027d3e1e8f2783b9d8e873391c4de6d361a0ce653218cc2602f174b85b2a93c8839158a04e261289046200f8783a1c0d848180b050241006028100602 } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame004_links_0000 (interval_append _ 64 128 150 record001_frame004_links_0064 record001_frame004_links_0128))
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1089
    Papers.RationalityTen.SharedFrameCatalogue.group1089_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1086.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1086.count (({ width := 9, code := 0x35babd469747a1cf66f3394c3613037ebe5eaef74b95b6cd64b0d7ab95aabd52a54da652a8f44a15027b3a9c4ce6531984be5d218fc76391b8d4622d1483c1202ff7ebedf2f5793b1d2e772389bedc6cb559ecd6632992c8602f576b85b2cd60ad54a8d409d4d2612c944923916854220902803f9f4f67a3c9e0ec74391b0d6693419cca6431184c05f2b9448c39158a04e261289046200f8783a1c0d848180b050241006028100602 } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame005_links_0000 (interval_append _ 64 128 150 record001_frame005_links_0064 record001_frame005_links_0128))
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1086
    Papers.RationalityTen.SharedFrameCatalogue.group1086_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
def record001_frame006_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1083.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1083.count (({ width := 9, code := 0x2f578bb5d2e571b7db6d768ab552a550a75369749a3d1277399bcd66732984ba59299449a49229047e3b1b8cc5a2b1489c4a23007f3f1f4f87bbd5e6f071b85bedd6db69b0d669b3596c96331586c15f2ed6eb559ac560ae52289409d4e2693095492391a8b44a1d0a8441200fa773a9cce470379b4d66933998c8622f964ae552a148a04e2612c92481e8cc52200e86832180b8582a12088401e0e068281208038180a04018080200 } : Fields).get c.val)
theorem record001_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record001) (record001.maps 6)
      (record001.inverseMaps 6) record001_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame006_links_0000 (interval_append _ 64 128 150 record001_frame006_links_0064 record001_frame006_links_0128))
theorem record001_frame006_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 6 :=
  of_group record001 6 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1083
    Papers.RationalityTen.SharedFrameCatalogue.group1083_facts record001_frame006_indices record001_frame006_graph record001_frame006_links
def record001_frame007_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1082.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1082.count (({ width := 9, code := 0x2773a9c4da6b34994c25d2b8f47637198c45e2b1388c3a0f068240a03007f3f1f4f77b3d5e6f1783bddaeb74b99cae471b89c2d66ab4da2d067b3596c85f2f576b95c2dd6ab3582ad52a75329546a14f26d30964a249228f44a1d0a8441a04fe7c3c9d8ea74391c0de6e361a8ce612f974b85a2c960ac5429948a04e259148641200f8783a1c0dc6a34168983e180b8582a14098482210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record001_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1082.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1082.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1082.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1082.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1082.localPairCheck (smallEmbedding record001) (record001.maps 7)
      (record001.inverseMaps 7) record001_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame007_links_0000 (interval_append _ 64 128 150 record001_frame007_links_0064 record001_frame007_links_0128))
theorem record001_frame007_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 7 :=
  of_group record001 7 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1082
    Papers.RationalityTen.SharedFrameCatalogue.group1082_facts record001_frame007_indices record001_frame007_graph record001_frame007_links
def record001_frame008_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa89a82a7aa70a63a55a43a36a28a0393f93792e9239169098f88eb8dc8bc84783c82f82180e7fc7e67d57c47a079c79378377276375373e72a7166fb6f66e46d26bf6ab5d85cf5c65bc5ae59d58d5805704fa4ef4e44da4cc4bd4ac49e4904764704634554474394284184073f03e13d33c23b33a332e3233163082f82ea2dc2d02c12a72a029628627526725a2492392282051f61e51d71c91c21ba1ae1a01911831731651561331271181070fa0f10e60d90cc0be0b509f09506c05d04003603503403303203102702602502402302201200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record001_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record001) (record001.maps 8)
      (record001.inverseMaps 8) record001_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame008_links_0000 (interval_append _ 64 128 150 record001_frame008_links_0064 record001_frame008_links_0128))
theorem record001_frame008_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 8 :=
  of_group record001 8 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record001_frame008_indices record001_frame008_graph record001_frame008_links
def record001_frame009_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x2564a994928a4ec999272324447d8710d21942e8570960ec1a829025ee3d77a2f31e2bbf772ec5d4b9c730e4dc7b88708dedbab6f6cad61ab350692d15a0ade5b4b59692ce594b15602bb4f69d93826c4cc9852ea5449c8f91c23345c8a10f219424824fb1f23d879cf09db344670cb992316608be1742da568ac1532a0528a313e2704cc95916226438841021fc3e87a8ef1d23906f0d71a231c610be1702c4560a91482784b893114200320560780d0198320620c01782604a090118220420480600b0140240400600a01001802 } : Fields).get c.val)
theorem record001_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record001) (record001.maps 9) (record001.inverseMaps 9) record001_frame009_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record001) (record001.maps 9) (record001.inverseMaps 9) record001_frame009_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record001) (record001.maps 9) (record001.inverseMaps 9) record001_frame009_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record001) (record001.maps 9)
      (record001.inverseMaps 9) record001_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame009_links_0000 (interval_append _ 64 128 150 record001_frame009_links_0064 record001_frame009_links_0128))
theorem record001_frame009_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 9 :=
  of_group record001 9 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record001_frame009_indices record001_frame009_graph record001_frame009_links
def record001_frame010_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0640.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0640.count (({ width := 8, code := 0xc6c5c4c3c2c1bfbebdbab7b6b5b4b3b2b0afaeaba9a8a7a6a5a4a2a1a09d9c9b9a999897959493908f8e8d8c8b88878685848381807f7b7a797877767473726f6e6d6c6b696867656362615f5e5d5b5a595857555453514f4e4d4c4b4a4947464542413f3e3d3c3b3a393837353433302f2d2c2b2a2927262524211e1b1817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record001_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0640.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0640.localPairCheck (smallEmbedding record001) (record001.maps 10) (record001.inverseMaps 10) record001_frame010_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0640.localPairCheck (smallEmbedding record001) (record001.maps 10) (record001.inverseMaps 10) record001_frame010_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0640.localPairCheck (smallEmbedding record001) (record001.maps 10) (record001.inverseMaps 10) record001_frame010_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0640.localPairCheck (smallEmbedding record001) (record001.maps 10)
      (record001.inverseMaps 10) record001_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame010_links_0000 (interval_append _ 64 128 150 record001_frame010_links_0064 record001_frame010_links_0128))
theorem record001_frame010_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 10 :=
  of_group record001 10 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0640
    Papers.RationalityTen.SharedFrameCatalogue.group0640_facts record001_frame010_indices record001_frame010_graph record001_frame010_links
def record001_frame011_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb33b29b22b19b0baffaf1adbaccaab9da9cb9c29b89a59969889729639468c88b68aa89e88c87c86a85183d81c8138037f87ed7d77c37af79978476976374f73872170962861a6126085fb5f05e25d45c854053052751c50e5014f14e14d34b64a749c49348547a46c45c44d43842641840a3f93eb36e35b34e34433432230f2fd2ed2d32c72b72ad2a12932862752652552302212111ff1ee1e21d51cd1c41b51a81981871781531411311211111020f50e80da0cb0c00a809906e05f04003603503403303203102702602502402302201200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record001_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record001) (record001.maps 11) (record001.inverseMaps 11) record001_frame011_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record001) (record001.maps 11) (record001.inverseMaps 11) record001_frame011_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record001) (record001.maps 11) (record001.inverseMaps 11) record001_frame011_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record001) (record001.maps 11)
      (record001.inverseMaps 11) record001_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame011_links_0000 (interval_append _ 64 128 150 record001_frame011_links_0064 record001_frame011_links_0128))
theorem record001_frame011_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 11 :=
  of_group record001 11 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record001_frame011_indices record001_frame011_graph record001_frame011_links
def record001_frame012_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x73973473072a72472071b71470e70466a65d65664d64163862e6236156015bf5b75ab5a259759058357757055655354c54754153c53753152a52451c51951350c5054fe44d43e43942e42241940e4013f739338a38037536a36335534934032a32331e31831230d3083012fb2f32ec2e52df2da2d426725b25224b23f23422821c20f1f81f21e91e21d81d01c71bd1b41a918d18417b17116515e15514e14413b13512911f1170f90f00e80dd0d10cc0c50c00bc0b60b109c09106c05d03e03503403303203103002702602502402302201200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record001_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record001) (record001.maps 12) (record001.inverseMaps 12) record001_frame012_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record001) (record001.maps 12) (record001.inverseMaps 12) record001_frame012_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record001) (record001.maps 12) (record001.inverseMaps 12) record001_frame012_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record001) (record001.maps 12)
      (record001.inverseMaps 12) record001_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame012_links_0000 (interval_append _ 64 128 150 record001_frame012_links_0064 record001_frame012_links_0128))
theorem record001_frame012_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 12 :=
  of_group record001 12 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record001_frame012_indices record001_frame012_graph record001_frame012_links
def record001_frame013_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x2bdd73adf5a2b155daaf546a5d4098d30e5e4b595f2ae5249d9332362cc4f89110a1e4368610a20f41481d021ff3f87e2fb5f33dd7aef29e3bc3778ed5d8b3c66ccc596b28646c798c31257eadd5a2ad554a894da9651a9f93aa6f4cc9812d25048e8fd16a2544286d0ba103846e8da1ab34c67cca98c3045c8b59672c6570ab1542945049f12a2464808e115220424818ff1f23d0770e81c234c670c81882f45b0b015629c5009c11a2083485d0800d81a8340660c81882704c094120230440480600b0140240400600a01001802 } : Fields).get c.val)
theorem record001_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record001) (record001.maps 13) (record001.inverseMaps 13) record001_frame013_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record001) (record001.maps 13) (record001.inverseMaps 13) record001_frame013_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record001) (record001.maps 13) (record001.inverseMaps 13) record001_frame013_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record001) (record001.maps 13)
      (record001.inverseMaps 13) record001_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame013_links_0000 (interval_append _ 64 128 150 record001_frame013_links_0064 record001_frame013_links_0128))
theorem record001_frame013_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 13 :=
  of_group record001 13 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record001_frame013_indices record001_frame013_graph record001_frame013_links
def record001_frame014_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0854.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0854.count (({ width := 8, code := 0xaaa9a8a7a6a5a4a2a1a09d9c9b9a99989795949391908f8e8d8c8b898887868584838281807e7d7c7b7a797877767574737271706e6d6c6b6a6968676664636261605f5e5d5b5a5958565554535251504f4e4d4c4a494847464544434241403e3d3b3a393837363534333231302e2d2b2a2928272524232221201e1c1a1817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record001_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0854.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0854.localPairCheck (smallEmbedding record001) (record001.maps 14) (record001.inverseMaps 14) record001_frame014_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0854.localPairCheck (smallEmbedding record001) (record001.maps 14) (record001.inverseMaps 14) record001_frame014_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0854.localPairCheck (smallEmbedding record001) (record001.maps 14) (record001.inverseMaps 14) record001_frame014_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0854.localPairCheck (smallEmbedding record001) (record001.maps 14)
      (record001.inverseMaps 14) record001_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame014_links_0000 (interval_append _ 64 128 150 record001_frame014_links_0064 record001_frame014_links_0128))
theorem record001_frame014_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 14 :=
  of_group record001 14 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0854
    Papers.RationalityTen.SharedFrameCatalogue.group0854_facts record001_frame014_indices record001_frame014_graph record001_frame014_links
def record001_frame015_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0850.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0850.count (({ width := 8, code := 0x9594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record001_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0850.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0850.localPairCheck (smallEmbedding record001) (record001.maps 15) (record001.inverseMaps 15) record001_frame015_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0850.localPairCheck (smallEmbedding record001) (record001.maps 15) (record001.inverseMaps 15) record001_frame015_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0850.localPairCheck (smallEmbedding record001) (record001.maps 15) (record001.inverseMaps 15) record001_frame015_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0850.localPairCheck (smallEmbedding record001) (record001.maps 15)
      (record001.inverseMaps 15) record001_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame015_links_0000 (interval_append _ 64 128 150 record001_frame015_links_0064 record001_frame015_links_0128))
theorem record001_frame015_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 15 :=
  of_group record001 15 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0850
    Papers.RationalityTen.SharedFrameCatalogue.group0850_facts record001_frame015_indices record001_frame015_graph record001_frame015_links
def record001_frame016_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0848.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0848.count (({ width := 9, code := 0x237198bc5225108742e130681c05fefc7d3e1ecf378bb9d8ea74395c6e16fb71b4d76b351a4cf66b2d92c66230580bf5f2f578bb5d2e570b75b2d566b2582bd5cad562ad54a853a9546a14f27134974aa4d208e46a31168a44a1d0a82401f8f6793b9d0e672389c0de6e369acd46733194c86331184c05f2f174b85a2c958aa5429948a04f27134984b241147a35140984a2411888421f0f074381b0d048180b050241006028100602 } : Fields).get c.val)
theorem record001_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0848.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0848.localPairCheck (smallEmbedding record001) (record001.maps 16) (record001.inverseMaps 16) record001_frame016_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0848.localPairCheck (smallEmbedding record001) (record001.maps 16) (record001.inverseMaps 16) record001_frame016_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0848.localPairCheck (smallEmbedding record001) (record001.maps 16) (record001.inverseMaps 16) record001_frame016_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0848.localPairCheck (smallEmbedding record001) (record001.maps 16)
      (record001.inverseMaps 16) record001_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame016_links_0000 (interval_append _ 64 128 150 record001_frame016_links_0064 record001_frame016_links_0128))
theorem record001_frame016_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 16 :=
  of_group record001 16 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0848
    Papers.RationalityTen.SharedFrameCatalogue.group0848_facts record001_frame016_indices record001_frame016_graph record001_frame016_links
def record001_frame017_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0xe5792e3f8ce2786e0b7edeb72cfb3bce335ccb2fcaf26c8718beaf6bcaeeba6e4b76d4b2ebeaeeb7aceafaaea7a8a9ba528ca22819ea739be3c8e6368ce308b62888a1c7f5fa7ddf37bdeb795db745c5709bf6edb76cdae69da065d8e61d805f579561555494f52d4750d3b4cd27491214791a4591243908408f43bcea39ce337cdb35cd333ccb31cbf2dca627c9824c8b21c821f4781c46e1a868140470dc330c8310c02f0b8270982509023088120300b02809020060140400c02 } : Fields).get c.val)
theorem record001_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record001) (record001.maps 17) (record001.inverseMaps 17) record001_frame017_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record001) (record001.maps 17) (record001.inverseMaps 17) record001_frame017_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record001) (record001.maps 17) (record001.inverseMaps 17) record001_frame017_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record001) (record001.maps 17)
      (record001.inverseMaps 17) record001_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame017_links_0000 (interval_append _ 64 128 150 record001_frame017_links_0064 record001_frame017_links_0128))
theorem record001_frame017_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 17 :=
  of_group record001 17 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record001_frame017_indices record001_frame017_graph record001_frame017_links
def record001_frame018_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0377.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0377.count (({ width := 9, code := 0x35bacd5eab53a8d369345a0c6e2f1387c2e0f037ebdddad367b2d8ec35faed6aaf52a8d3e9b4ba4d1e8b429fcee75389b4d2671e8dc622b1287c2e0f0378bb9d6e872b89bcda6b349a0ce6632990c5612fd76b85aac960ae50a7d3a9b4ca5d2a9247a2d14894421d0c8542204fc76399c0dc6b351a4d06733194c8612f158a6502712c94492411c8a442190870331409c4c251208c44211007c3c1d0e048180b050241006028100602 } : Fields).get c.val)
theorem record001_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0377.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0377.localPairCheck (smallEmbedding record001) (record001.maps 18) (record001.inverseMaps 18) record001_frame018_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0377.localPairCheck (smallEmbedding record001) (record001.maps 18) (record001.inverseMaps 18) record001_frame018_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0377.localPairCheck (smallEmbedding record001) (record001.maps 18) (record001.inverseMaps 18) record001_frame018_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0377.localPairCheck (smallEmbedding record001) (record001.maps 18)
      (record001.inverseMaps 18) record001_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame018_links_0000 (interval_append _ 64 128 150 record001_frame018_links_0064 record001_frame018_links_0128))
theorem record001_frame018_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 18 :=
  of_group record001 18 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0377
    Papers.RationalityTen.SharedFrameCatalogue.group0377_facts record001_frame018_indices record001_frame018_graph record001_frame018_links
def record001_frame019_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0373.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0373.count (({ width := 9, code := 0x2130782c0e02ff7ebedf2f57a3c9e0ee763a9d0e672381bedd6db65aed569b459ecc65b258ec561b057ebd5dae16eb559ac55eac552a14ca4512813c9c4ca612e964aa51269248a3d1a8b44a1d0a83409fcf87a3c1d8e872389bcda6b3499cca6330978ba5c2d968b2582b958aa5228138984a249208e46229108642208fc7c3d1e0ec74391c0dc6c35198c85e2e1188842200f8783a1c0d86832180b844160a048200e06028100602 } : Fields).get c.val)
theorem record001_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0373.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record001) (record001.maps 19) (record001.inverseMaps 19) record001_frame019_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record001) (record001.maps 19) (record001.inverseMaps 19) record001_frame019_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record001) (record001.maps 19) (record001.inverseMaps 19) record001_frame019_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record001) (record001.maps 19)
      (record001.inverseMaps 19) record001_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame019_links_0000 (interval_append _ 64 128 150 record001_frame019_links_0064 record001_frame019_links_0128))
theorem record001_frame019_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 19 :=
  of_group record001 19 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0373
    Papers.RationalityTen.SharedFrameCatalogue.group0373_facts record001_frame019_indices record001_frame019_graph record001_frame019_links
def record001_frame020_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0369.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0369.count (({ width := 8, code := 0x9594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record001_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0369.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0369.localPairCheck (smallEmbedding record001) (record001.maps 20) (record001.inverseMaps 20) record001_frame020_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0369.localPairCheck (smallEmbedding record001) (record001.maps 20) (record001.inverseMaps 20) record001_frame020_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0369.localPairCheck (smallEmbedding record001) (record001.maps 20) (record001.inverseMaps 20) record001_frame020_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0369.localPairCheck (smallEmbedding record001) (record001.maps 20)
      (record001.inverseMaps 20) record001_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame020_links_0000 (interval_append _ 64 128 150 record001_frame020_links_0064 record001_frame020_links_0128))
theorem record001_frame020_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 20 :=
  of_group record001 20 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0369
    Papers.RationalityTen.SharedFrameCatalogue.group0369_facts record001_frame020_indices record001_frame020_graph record001_frame020_links
def record001_frame021_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0365.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0365.count (({ width := 8, code := 0x9594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record001_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0365.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0365.localPairCheck (smallEmbedding record001) (record001.maps 21) (record001.inverseMaps 21) record001_frame021_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0365.localPairCheck (smallEmbedding record001) (record001.maps 21) (record001.inverseMaps 21) record001_frame021_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0365.localPairCheck (smallEmbedding record001) (record001.maps 21) (record001.inverseMaps 21) record001_frame021_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0365.localPairCheck (smallEmbedding record001) (record001.maps 21)
      (record001.inverseMaps 21) record001_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame021_links_0000 (interval_append _ 64 128 150 record001_frame021_links_0064 record001_frame021_links_0128))
theorem record001_frame021_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 21 :=
  of_group record001 21 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0365
    Papers.RationalityTen.SharedFrameCatalogue.group0365_facts record001_frame021_indices record001_frame021_graph record001_frame021_links
def record001_frame022_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0364.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0364.count (({ width := 8, code := 0x9594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record001_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0364.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0364.localPairCheck (smallEmbedding record001) (record001.maps 22) (record001.inverseMaps 22) record001_frame022_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0364.localPairCheck (smallEmbedding record001) (record001.maps 22) (record001.inverseMaps 22) record001_frame022_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame022_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0364.localPairCheck (smallEmbedding record001) (record001.maps 22) (record001.inverseMaps 22) record001_frame022_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0364.localPairCheck (smallEmbedding record001) (record001.maps 22)
      (record001.inverseMaps 22) record001_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame022_links_0000 (interval_append _ 64 128 150 record001_frame022_links_0064 record001_frame022_links_0128))
theorem record001_frame022_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 22 :=
  of_group record001 22 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0364
    Papers.RationalityTen.SharedFrameCatalogue.group0364_facts record001_frame022_indices record001_frame022_graph record001_frame022_links
def record001_frame023_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x17dabdb5e22ed1748b915c02dc16bab4b52828f5448a1450227cd3c89d44e1a6c926a91e482a3c51c08cc45d22a512a88343c2181092835411a0490027ef3ef1f44f9a7b73d01e20eec6443179868c165fc2f61778b9e5bf29d949ca2450227a139c9ae4c925e12a092c48423a119c8b444c21f90c884a4142020fc87ca3d91a98cf464e3171840be45d42db1660af856229d14509e04da260129091c47422010787f43e21e40eb071836a1a80ce064030a1790b6854c28012d090845420e0f907483781a80c9055826c0dc05f02000d806a03401980c80620270130094048023011004801800b00500240100060028010006002 } : Fields).get c.val)
theorem record001_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record001) (record001.maps 23) (record001.inverseMaps 23) record001_frame023_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record001) (record001.maps 23) (record001.inverseMaps 23) record001_frame023_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame023_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record001) (record001.maps 23) (record001.inverseMaps 23) record001_frame023_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record001) (record001.maps 23)
      (record001.inverseMaps 23) record001_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame023_links_0000 (interval_append _ 64 128 150 record001_frame023_links_0064 record001_frame023_links_0128))
theorem record001_frame023_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 23 :=
  of_group record001 23 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record001_frame023_indices record001_frame023_graph record001_frame023_links
def record001_frame024_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1039.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1039.count (({ width := 11, code := 0x257caa94927e4c49491921e40c7583505607c08806ff5fc3f17daf81dabb0750e89cd393712e0dbeb726deda9b135a6a8d39a4340672cb195326644c798babb570ad5582ab54aa814da954ba96529a504989212023b4688b51422243484d062063fe7e0f69e73c276ceb9d133c664c998b3085f4bb16f2d0578ad9572a2528a293e2784e09a1282444708a91221e428830ff1f23c8758e51bc348668c61842f45b8b21562985109f1202103385807c0d81a8340660c81882704c094120230440480600b0140240400600a01001802 } : Fields).get c.val)
theorem record001_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record001) (record001.maps 24) (record001.inverseMaps 24) record001_frame024_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record001) (record001.maps 24) (record001.inverseMaps 24) record001_frame024_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame024_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record001) (record001.maps 24) (record001.inverseMaps 24) record001_frame024_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record001) (record001.maps 24)
      (record001.inverseMaps 24) record001_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame024_links_0000 (interval_append _ 64 128 150 record001_frame024_links_0064 record001_frame024_links_0128))
theorem record001_frame024_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 24 :=
  of_group record001 24 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1039
    Papers.RationalityTen.SharedFrameCatalogue.group1039_facts record001_frame024_indices record001_frame024_graph record001_frame024_links
def record001_frame025_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1032.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1032.count (({ width := 9, code := 0x2dd6db5daacf65b1586c15da7d3a994ba4d1e8742a0cfa773a9c4de6d3599cc25d2a94ca24d259248e431f8ec622f168ac5227058240600fd7d3ddecf5763add2e772b89bedd6d359a8d36833994c863b0d7ebc5cadd68b3562a952a652a853c9c4c255289348a3d1c8b43a19067d3d1dce873391c4dc6d361acd26631974b4582b150a44f261289047208f46e30118803e1e0e87036180b8582a1409838180b050241006028100602 } : Fields).get c.val)
theorem record001_frame025_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1032.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame025_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1032.localPairCheck (smallEmbedding record001) (record001.maps 25) (record001.inverseMaps 25) record001_frame025_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame025_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1032.localPairCheck (smallEmbedding record001) (record001.maps 25) (record001.inverseMaps 25) record001_frame025_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame025_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1032.localPairCheck (smallEmbedding record001) (record001.maps 25) (record001.inverseMaps 25) record001_frame025_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame025_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1032.localPairCheck (smallEmbedding record001) (record001.maps 25)
      (record001.inverseMaps 25) record001_frame025_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame025_links_0000 (interval_append _ 64 128 150 record001_frame025_links_0064 record001_frame025_links_0128))
theorem record001_frame025_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 25 :=
  of_group record001 25 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1032
    Papers.RationalityTen.SharedFrameCatalogue.group1032_facts record001_frame025_indices record001_frame025_graph record001_frame025_links
def record001_frame026_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0429.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0429.count (({ width := 8, code := 0x9594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record001_frame026_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0429.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame026_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0429.localPairCheck (smallEmbedding record001) (record001.maps 26) (record001.inverseMaps 26) record001_frame026_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame026_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0429.localPairCheck (smallEmbedding record001) (record001.maps 26) (record001.inverseMaps 26) record001_frame026_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame026_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0429.localPairCheck (smallEmbedding record001) (record001.maps 26) (record001.inverseMaps 26) record001_frame026_indices (Fin.ofNat record001.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record001_frame026_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0429.localPairCheck (smallEmbedding record001) (record001.maps 26)
      (record001.inverseMaps 26) record001_frame026_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record001_frame026_links_0000 (interval_append _ 64 128 150 record001_frame026_links_0064 record001_frame026_links_0128))
theorem record001_frame026_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 26 :=
  of_group record001 26 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0429
    Papers.RationalityTen.SharedFrameCatalogue.group0429_facts record001_frame026_indices record001_frame026_graph record001_frame026_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (Fin.cases (record001_frame005_supported hcells) (Fin.cases (record001_frame006_supported hcells) (Fin.cases (record001_frame007_supported hcells) (Fin.cases (record001_frame008_supported hcells) (Fin.cases (record001_frame009_supported hcells) (Fin.cases (record001_frame010_supported hcells) (Fin.cases (record001_frame011_supported hcells) (Fin.cases (record001_frame012_supported hcells) (Fin.cases (record001_frame013_supported hcells) (Fin.cases (record001_frame014_supported hcells) (Fin.cases (record001_frame015_supported hcells) (Fin.cases (record001_frame016_supported hcells) (Fin.cases (record001_frame017_supported hcells) (Fin.cases (record001_frame018_supported hcells) (Fin.cases (record001_frame019_supported hcells) (Fin.cases (record001_frame020_supported hcells) (Fin.cases (record001_frame021_supported hcells) (Fin.cases (record001_frame022_supported hcells) (Fin.cases (record001_frame023_supported hcells) (Fin.cases (record001_frame024_supported hcells) (Fin.cases (record001_frame025_supported hcells) (Fin.cases (record001_frame026_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))))))))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x93e93592c9209139068f58e88d98bf84683a82d81f80c7f97e37d27c27a379b79078076f76075073b7277135d95d25c95bf5b15a059058357355d4fb4f24e74dd4cf4c04af4a149347b47546d46045244443642541540432d3203133052f52e72d92cd2be2a029628627526725a2492392282071f81e71d91cb1c21ba1ae1a019118317316515613512911a1090fc08b07606c05d05705605505405304003602702102001f01e01d01201101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame001_links_0000 (interval_append _ 64 128 129 record002_frame001_links_0064 record002_frame001_links_0128))
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0x9d79c89c19b59a399498596f9609498c68b48a989b88987986784e83a81f8108007f77ea7d47c07ac79678162b61d61360b5fe5f35e55d75cb5b454353352851f5115044f44e44d64bf4b34a449b49048247746945944a36b35834d34133131f30c2fa2ea2c72b72ad2a12932862752652552322232132011f01e21d51cd1c41b51a819818717815514313312311309107806e05f05905805705605504003602702102001f01e01d01201101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame002_links_0000 (interval_append _ 64 128 129 record002_frame002_links_0064 record002_frame002_links_0128))
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0x33dceb37cd331cbb2ac9720c66f9bd6f1bb6e8b8edbb4ac9afebaadab2ab6a9a96a0a66928f63a8de348c62e8aa2487a177f9fb7e1f57c5ed7a1de751c7711c16f9b96d5b16b1a567957551515394a519414e531491214791a4591243908408f53c0eb3a0e437cdb35cd333ccb31cbf2dca7280992508d1845714047104400fc3e0f4370cc270842007c1e074120441003c0e0340c02c0a02408018050100300800 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame003_links_0000 (interval_append _ 64 128 129 record002_frame003_links_0064 record002_frame003_links_0128))
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
def record002_frame004_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0452.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0452.count (({ width := 9, code := 0x1419fcf677399bcd667319749a47208ec6a2f1488c3a13068240a00fe7e3e9f0f66e369b0d66a349a0ce6632182bf5eaed72b75aacd62ad55aa54ea551a853e9d4da190882401f8f87a3c1d8e471381bcdc6d361a8d06431180bc5c2d164b0572b154a8522813094482311074361a8d05c2d160ac54261287c32180b8582a110803c1c0d0602c14090401c0c050200c0400 } : Fields).get c.val)
theorem record002_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record002) (record002.maps 4)
      (record002.inverseMaps 4) record002_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame004_links_0000 (interval_append _ 64 128 129 record002_frame004_links_0064 record002_frame004_links_0128))
theorem record002_frame004_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 4 :=
  of_group record002 4 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0452
    Papers.RationalityTen.SharedFrameCatalogue.group0452_facts record002_frame004_indices record002_frame004_graph record002_frame004_links
def record002_frame005_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xa4d51d2885424a024f8a7893a49c14d9a4c9236902477a3791948b8453a24d10887542ea1190648204079ff8fd87db32398c8c3a60e2ff97bcbc25d22e116d0a7c52a28a94149ee4ea26d133097e4b1252924c902471232115c89243c2178d4067432418a8c185ee2e816c8b2856229d14509e04da260129091c47422210887fc3e41e50eb071836a1a80ce064030a1790b6855428412f0910458122078037017c0b205802b81580aa04001b009c04202000f807803a012008804001e00e006803001600a004802000c005002000c004000 } : Fields).get c.val)
theorem record002_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 5)
      (record002.inverseMaps 5) record002_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame005_links_0000 (interval_append _ 64 128 129 record002_frame005_links_0064 record002_frame005_links_0128))
theorem record002_frame005_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 5 :=
  of_group record002 5 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record002_frame005_indices record002_frame005_graph record002_frame005_links
def record002_frame006_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0x520a33452875059f93e279ceb9c127247c878ff1d2354638bb14e23c3a85909a0ec1180f001fcbf06aad35a3340676cc595b27644c55712d5594b155f2b5560aa952a9a524a1d402784e0999302584a8780ea1cb38c700dc1b335c6a4cc98e30c600be1742dc5a0b29572965009c13024e46c8990f20e4047e8f61e43946d8d11923043b8680c014c2684c0961282483c06809c1082003e0780e8120220400780e01a0300580a0120200300500800c01000 } : Fields).get c.val)
theorem record002_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record002) (record002.maps 6)
      (record002.inverseMaps 6) record002_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame006_links_0000 (interval_append _ 64 128 129 record002_frame006_links_0064 record002_frame006_links_0128))
theorem record002_frame006_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 6 :=
  of_group record002 6 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record002_frame006_indices record002_frame006_graph record002_frame006_links
def record002_frame007_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0351.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0351.count (({ width := 9, code := 0x18ac461b0982c05faf97abbdc6dd6bb4592c15cac5529d4ba4d1e89419f4ee71358a4461d0b8441604ff7e3e1e4ef763a5cae16eb65aad066b2d92c661b017aba5ba5d2a9348a39168842a08fc7d3e1ecf2773a9cce26e361a8d0663218cc4612f974b6592b94ca04d2511c6e361a8d05c2d160ac542914088381b0d06430110803c1c0d0602c14090401c0c050200c0400 } : Fields).get c.val)
theorem record002_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record002) (record002.maps 7)
      (record002.inverseMaps 7) record002_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame007_links_0000 (interval_append _ 64 128 129 record002_frame007_links_0064 record002_frame007_links_0128))
theorem record002_frame007_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 7 :=
  of_group record002 7 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0351
    Papers.RationalityTen.SharedFrameCatalogue.group0351_facts record002_frame007_indices record002_frame007_graph record002_frame007_links
def record002_frame008_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xac855a2a81518a775312941476a27505a52526a921487a3f51d48d746222c112a88843b21910a4842418207d01a7fb2ca1600ad85582a194b8a38507279935c82a4011f68f6c7923b61d18e406f83611aa0d0866031e1870bf05d62d9163883c4102010fd07cc3d81e50ef075c3921c20dd86d035a1a60cf86603221810bd05cc2d81650b005642a414b0a204f426c12f094046022210a08183f0122078037017c0b205802b81580aa04001b009c04202000f807803a012008804001e00e006803001600a004802000c005002000c004000 } : Fields).get c.val)
theorem record002_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 8) (record002.inverseMaps 8) record002_frame008_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 8) (record002.inverseMaps 8) record002_frame008_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 8) (record002.inverseMaps 8) record002_frame008_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 8)
      (record002.inverseMaps 8) record002_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame008_links_0000 (interval_append _ 64 128 129 record002_frame008_links_0064 record002_frame008_links_0128))
theorem record002_frame008_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 8 :=
  of_group record002 8 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame008_indices record002_frame008_graph record002_frame008_links
def record002_frame009_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x5a159c59158b57e57956f56155a5474f34ef4e54e14d54ce4c24b44ad49949548f48347846c46545944a43c36836135c35034a34033332b32130e2ba2b42af2a529f29528827d27426025c25324a23d23522c21e21120318b18718117c17717116c16616115715414f14914313d13813212d12311d11611110e10c10a1051000fb0f60f00ea0e50d80d20cd0c70c308307006705805205105004f04e03f03602702102001f01e01d01201101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record002_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record002) (record002.maps 9) (record002.inverseMaps 9) record002_frame009_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record002) (record002.maps 9) (record002.inverseMaps 9) record002_frame009_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record002) (record002.maps 9) (record002.inverseMaps 9) record002_frame009_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record002) (record002.maps 9)
      (record002.inverseMaps 9) record002_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame009_links_0000 (interval_append _ 64 128 129 record002_frame009_links_0064 record002_frame009_links_0128))
theorem record002_frame009_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 9 :=
  of_group record002 9 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record002_frame009_indices record002_frame009_graph record002_frame009_links
def record002_frame010_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x59058858257b57356655f5555485394f04e84e04d94d04c54ba4ae4a349248c48548047847046645c45544838938137a37336836235734a3413312e92e02d82d12c62be2b22a429a28a28427d27827026625f25424a2401cb1c51bf1bc1b71b01aa1a419d18f18918418017a17316c16615e15114b14313d13913312c12712311d11610f1070ff0f10e90e10dc0d708506f06805905305205105004f03d03602702102001f01e01d01201101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record002_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record002) (record002.maps 10) (record002.inverseMaps 10) record002_frame010_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record002) (record002.maps 10) (record002.inverseMaps 10) record002_frame010_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record002) (record002.maps 10) (record002.inverseMaps 10) record002_frame010_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record002) (record002.maps 10)
      (record002.inverseMaps 10) record002_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame010_links_0000 (interval_append _ 64 128 129 record002_frame010_links_0064 record002_frame010_links_0128))
theorem record002_frame010_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 10 :=
  of_group record002 10 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record002_frame010_indices record002_frame010_graph record002_frame010_links
def record002_frame011_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0381.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0381.count (({ width := 9, code := 0x11389446210f87436190b84c0a00fe7e3e9f0f67a3c9dced763add4e97439dcce569345a0cf6733598cb6532182bf5eaed72b75aacd62ad562ad54a95429d4ca5522411c8c452210c8541a04f87a3c1d8e872381b4d46431180bc5d2d964ae55299449e4c2490c823f1e8f06a31180bc5228138984a211007c32180b8582a110803c1c0d0602c14090401c0c050200c0400 } : Fields).get c.val)
theorem record002_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0381.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record002) (record002.maps 11) (record002.inverseMaps 11) record002_frame011_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record002) (record002.maps 11) (record002.inverseMaps 11) record002_frame011_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record002) (record002.maps 11) (record002.inverseMaps 11) record002_frame011_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record002) (record002.maps 11)
      (record002.inverseMaps 11) record002_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame011_links_0000 (interval_append _ 64 128 129 record002_frame011_links_0064 record002_frame011_links_0128))
theorem record002_frame011_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 11 :=
  of_group record002 11 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0381
    Papers.RationalityTen.SharedFrameCatalogue.group0381_facts record002_frame011_indices record002_frame011_graph record002_frame011_links
def record002_frame012_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x5d25ce5c45bb5b25a859d59258657b52e52351650a4ff4f54e84db4ce4c24bc4b34aa49f49949248847f47539639238837e37336735d35434a33f2f22e72da2cc2bf2b22a729c29228628027726e26225924f2462402391c11bb1b41ae1a619e19618e18617d17917216b16515d15514f14713c13813312e12712311e11a11410d1071000f90f30e90e40de0d90d308f07706d05e05805705605505404003602702102001f01e01d01201101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record002_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record002) (record002.maps 12) (record002.inverseMaps 12) record002_frame012_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record002) (record002.maps 12) (record002.inverseMaps 12) record002_frame012_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record002) (record002.maps 12) (record002.inverseMaps 12) record002_frame012_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record002) (record002.maps 12)
      (record002.inverseMaps 12) record002_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame012_links_0000 (interval_append _ 64 128 129 record002_frame012_links_0064 record002_frame012_links_0128))
theorem record002_frame012_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 12 :=
  of_group record002 12 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record002_frame012_indices record002_frame012_graph record002_frame012_links
def record002_frame013_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0605.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0605.count (({ width := 10, code := 0x317c570fc3707c1700beaf5bbed3b42c8b16beaf2b5abaa8a829ca628ea2e849fe7a9ca6a87e1c86a1082e0981a047f9f776dd674dc8709bf6e9b86c5a86919d6658d61d825f57a5c5304b92948d1e46d184510e42106408fd3e0f63c4ee3a4e036cd8354d1338cc320c32fcbd2e4b52c4a828c9f26c961b45f1644c1184511043108380c82507c1e0741c06c120441003c0e0340c02c0a02408018050100300800 } : Fields).get c.val)
theorem record002_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0605.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0605.localPairCheck (smallEmbedding record002) (record002.maps 13) (record002.inverseMaps 13) record002_frame013_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0605.localPairCheck (smallEmbedding record002) (record002.maps 13) (record002.inverseMaps 13) record002_frame013_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0605.localPairCheck (smallEmbedding record002) (record002.maps 13) (record002.inverseMaps 13) record002_frame013_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0605.localPairCheck (smallEmbedding record002) (record002.maps 13)
      (record002.inverseMaps 13) record002_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame013_links_0000 (interval_append _ 64 128 129 record002_frame013_links_0064 record002_frame013_links_0128))
theorem record002_frame013_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 13 :=
  of_group record002 13 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0605
    Papers.RationalityTen.SharedFrameCatalogue.group0605_facts record002_frame013_indices record002_frame013_graph record002_frame013_links
def record002_frame014_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xb125802bb95b6ac7559aa81518a7b530a6993289824b7a56d28e934490243d1ea8ee473a3811b28d2465a31117a8b63639adcd4c69434219d4cc464f31e188cae45622a894fca5e52028693e89ce4ce26393009724b2256129493c4972480dfc6d43571a08cb06323041780b685722a914c8a284f426b12d893047821b10607f83e01e20eb071836c1a70cb86202f01690ac84e025211b08683fc122078037017c0b205802b81580aa04001b009c04202000f807803a012008804001e00e006803001600a004802000c005002000c004000 } : Fields).get c.val)
theorem record002_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 14) (record002.inverseMaps 14) record002_frame014_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 14) (record002.inverseMaps 14) record002_frame014_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 14) (record002.inverseMaps 14) record002_frame014_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 14)
      (record002.inverseMaps 14) record002_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame014_links_0000 (interval_append _ 64 128 129 record002_frame014_links_0064 record002_frame014_links_0128))
theorem record002_frame014_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 14 :=
  of_group record002 14 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record002_frame014_indices record002_frame014_graph record002_frame014_links
def record002_frame015_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x66765b65564a63f63762c6206136035bd5b45aa59f59658e58157556d55855254b54554053b53653052952345044143a43142441b4114043fa3e939638d38137836c36535834c34333032932231c31731130c3073002fa26525925124923d23222621920c1f21e91e21d81d01c71bd1b41a918f18617c17316715e15514e14413b13512911f1170fb0f10ea0df0d308b07606c05d05705605505405303e03502702102001f01e01d01201101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record002_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record002) (record002.maps 15) (record002.inverseMaps 15) record002_frame015_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record002) (record002.maps 15) (record002.inverseMaps 15) record002_frame015_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record002) (record002.maps 15) (record002.inverseMaps 15) record002_frame015_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record002) (record002.maps 15)
      (record002.inverseMaps 15) record002_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame015_links_0000 (interval_append _ 64 128 129 record002_frame015_links_0064 record002_frame015_links_0128))
theorem record002_frame015_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 15 :=
  of_group record002 15 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record002_frame015_indices record002_frame015_graph record002_frame015_links
def record002_frame016_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0377.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0377.count (({ width := 9, code := 0x18cc56230d84c1602fb7abbda2cd64b1582bd5cacd5aa750a75329548a3512833e8fc72331689c421b0982c05e4ef763a5cce370371b0d468b3d9acb64b1d88c15f2813c9c4d2612c9448a3914894421d0c8542204fc773a1c4de6c351a4d06733194c8612f15ca85127930823c1c0cc6230178b85a2813884361a0c8602e12088401e0e06830160a048200c050200c0400 } : Fields).get c.val)
theorem record002_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0377.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0377.localPairCheck (smallEmbedding record002) (record002.maps 16) (record002.inverseMaps 16) record002_frame016_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0377.localPairCheck (smallEmbedding record002) (record002.maps 16) (record002.inverseMaps 16) record002_frame016_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0377.localPairCheck (smallEmbedding record002) (record002.maps 16) (record002.inverseMaps 16) record002_frame016_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0377.localPairCheck (smallEmbedding record002) (record002.maps 16)
      (record002.inverseMaps 16) record002_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame016_links_0000 (interval_append _ 64 128 129 record002_frame016_links_0064 record002_frame016_links_0128))
theorem record002_frame016_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 16 :=
  of_group record002 16 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0377
    Papers.RationalityTen.SharedFrameCatalogue.group0377_facts record002_frame016_indices record002_frame016_graph record002_frame016_links
def record002_frame017_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x5b25ab59d59358a57e57456955d5535105094fb4f14e64da4d24c94bd4b14ac4a64a049a49348c48647f4783a439a38e37f37636c36035734f3412f52eb2df2d02c72bf2b12a829e29228d28728127a27426d26726125a1e81dc1d21c81c01b61ad1a519b18f18717c17617216e16816315d15214813e13913212d12511a11210d1071020fe0fa0f00e60dc0d40d108d07606c05d05705605505405303e03502702102001f01e01d01201101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record002_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record002) (record002.maps 17) (record002.inverseMaps 17) record002_frame017_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record002) (record002.maps 17) (record002.inverseMaps 17) record002_frame017_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record002) (record002.maps 17) (record002.inverseMaps 17) record002_frame017_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record002) (record002.maps 17)
      (record002.inverseMaps 17) record002_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame017_links_0000 (interval_append _ 64 128 129 record002_frame017_links_0064 record002_frame017_links_0128))
theorem record002_frame017_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 17 :=
  of_group record002 17 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record002_frame017_indices record002_frame017_graph record002_frame017_links
def record002_frame018_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0600.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0600.count (({ width := 11, code := 0x39f734e51c6b836fede5b9b6e6ccd0da033a668cb994b23638c4985306604bf57c2f15d8b9d712db4e09b1322604ae95126a474828e10a210418810fe9f83e47b8f31dc3b275ce99ce38e710df1ba36a5c8b79692c0560aa14e28e5009b1332544989091e232448869011f63d4788ea1ca3806d8d219a31c620c21782cc558a413e264398680c21582885009e1382683c06809c1082003e0780e8120220400780e01a0300580a0120200300500800c01000 } : Fields).get c.val)
theorem record002_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0600.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record002) (record002.maps 18) (record002.inverseMaps 18) record002_frame018_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record002) (record002.maps 18) (record002.inverseMaps 18) record002_frame018_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record002) (record002.maps 18) (record002.inverseMaps 18) record002_frame018_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record002) (record002.maps 18)
      (record002.inverseMaps 18) record002_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame018_links_0000 (interval_append _ 64 128 129 record002_frame018_links_0064 record002_frame018_links_0128))
theorem record002_frame018_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 18 :=
  of_group record002 18 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0600
    Papers.RationalityTen.SharedFrameCatalogue.group0600_facts record002_frame018_indices record002_frame018_graph record002_frame018_links
def record002_frame019_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x71a7117076fa6f06e66d66ca6bf6aa62261960e6005f45e85d55c75b95a059758e58657e57656e56655e55542841f4144063fa3ee3db3cd3bf3a632c32331930c3022f82e82dc2d12bc2b42ab2a329b29328b28327b2721fa1f31ec1e61df1d81d11ca1c31b71b01a81a119919018818117916716015915114a14513e13612f12711e11610f1070f50ee0e70df0d809107806e05f05905805705605504003602702102001f01e01d01201101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record002_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record002) (record002.maps 19) (record002.inverseMaps 19) record002_frame019_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record002) (record002.maps 19) (record002.inverseMaps 19) record002_frame019_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record002) (record002.maps 19) (record002.inverseMaps 19) record002_frame019_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record002) (record002.maps 19)
      (record002.inverseMaps 19) record002_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame019_links_0000 (interval_append _ 64 128 129 record002_frame019_links_0064 record002_frame019_links_0128))
theorem record002_frame019_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 19 :=
  of_group record002 19 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record002_frame019_indices record002_frame019_graph record002_frame019_links
def record002_frame020_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0864.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0864.count (({ width := 11, code := 0x42f85309a0fc1982303202bfc7e4f31e43c0772ecdd5ba673ae51c3b816f8dddb836a6c8d7dad3535c0b696a2cd58ab055d2b154ea6d3c2754de9a13025c4aa9312323b46c8c51622543c8690a20e4106b0d299f338658c898c3085f0b816a2ca57cac15129851ca013325c4908e917222430831001f03c8768e71c2350668c617c2e03f86b0c61582804f09c1342603c06809c1082003e0780e8120220400780e01a0300580a0120200300500800c01000 } : Fields).get c.val)
theorem record002_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record002) (record002.maps 20) (record002.inverseMaps 20) record002_frame020_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record002) (record002.maps 20) (record002.inverseMaps 20) record002_frame020_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record002) (record002.maps 20) (record002.inverseMaps 20) record002_frame020_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record002) (record002.maps 20)
      (record002.inverseMaps 20) record002_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame020_links_0000 (interval_append _ 64 128 129 record002_frame020_links_0064 record002_frame020_links_0128))
theorem record002_frame020_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 20 :=
  of_group record002 20 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0864
    Papers.RationalityTen.SharedFrameCatalogue.group0864_facts record002_frame020_indices record002_frame020_graph record002_frame020_links
def record002_frame021_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0376.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0376.count (({ width := 9, code := 0x1108743215088341202fe7dbd5e6f177bb5d6e97338dc0dd6db65aed569b459ecd5f2f174b85b2d164af562a546a14fa7536994ba51228e45a250e8541a04fe7d3d9b4d86b351a4d0673298cc05f2f174b85b2d160ac52281389a4b251249047231148842200f074381b8d45a2b150a04c251208c44200f874361a0c8602e12088401e0e06830160a048200c050200c0400 } : Fields).get c.val)
theorem record002_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0376.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0376.localPairCheck (smallEmbedding record002) (record002.maps 21) (record002.inverseMaps 21) record002_frame021_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0376.localPairCheck (smallEmbedding record002) (record002.maps 21) (record002.inverseMaps 21) record002_frame021_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0376.localPairCheck (smallEmbedding record002) (record002.maps 21) (record002.inverseMaps 21) record002_frame021_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0376.localPairCheck (smallEmbedding record002) (record002.maps 21)
      (record002.inverseMaps 21) record002_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame021_links_0000 (interval_append _ 64 128 129 record002_frame021_links_0064 record002_frame021_links_0128))
theorem record002_frame021_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 21 :=
  of_group record002 21 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0376
    Papers.RationalityTen.SharedFrameCatalogue.group0376_facts record002_frame021_indices record002_frame021_graph record002_frame021_links
def record002_frame022_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1045.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1045.count (({ width := 11, code := 0x36a6ccd7dac352698d199fb39664c3d853035f8bd577ae95c2b6568acb592b0d5dab7560aad5329e47a8e118a2a4448690aa0e4107fcee1d83a2728e19bd3706c8d61a433e674cb98f314608bf17a2e64e89c1352664bc959282484808d118226438859062023f87c8ee1d4398710dc1b0358688cc1923105f8bc16e2b0540a413e268378610b41382404708c1142203a06609c1082003e0780e8120220400780e01a0300580a0120200300500800c01000 } : Fields).get c.val)
theorem record002_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1045.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record002) (record002.maps 22) (record002.inverseMaps 22) record002_frame022_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record002) (record002.maps 22) (record002.inverseMaps 22) record002_frame022_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame022_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record002) (record002.maps 22) (record002.inverseMaps 22) record002_frame022_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record002) (record002.maps 22)
      (record002.inverseMaps 22) record002_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame022_links_0000 (interval_append _ 64 128 129 record002_frame022_links_0064 record002_frame022_links_0128))
theorem record002_frame022_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 22 :=
  of_group record002 22 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1045
    Papers.RationalityTen.SharedFrameCatalogue.group1045_facts record002_frame022_indices record002_frame022_graph record002_frame022_links
def record002_frame023_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0348.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0348.count (({ width := 8, code := 0x807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record002_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0348.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0348.localPairCheck (smallEmbedding record002) (record002.maps 23) (record002.inverseMaps 23) record002_frame023_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0348.localPairCheck (smallEmbedding record002) (record002.maps 23) (record002.inverseMaps 23) record002_frame023_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame023_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0348.localPairCheck (smallEmbedding record002) (record002.maps 23) (record002.inverseMaps 23) record002_frame023_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0348.localPairCheck (smallEmbedding record002) (record002.maps 23)
      (record002.inverseMaps 23) record002_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame023_links_0000 (interval_append _ 64 128 129 record002_frame023_links_0064 record002_frame023_links_0128))
theorem record002_frame023_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 23 :=
  of_group record002 23 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0348
    Papers.RationalityTen.SharedFrameCatalogue.group0348_facts record002_frame023_indices record002_frame023_graph record002_frame023_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (Fin.cases (record002_frame004_supported hcells) (Fin.cases (record002_frame005_supported hcells) (Fin.cases (record002_frame006_supported hcells) (Fin.cases (record002_frame007_supported hcells) (Fin.cases (record002_frame008_supported hcells) (Fin.cases (record002_frame009_supported hcells) (Fin.cases (record002_frame010_supported hcells) (Fin.cases (record002_frame011_supported hcells) (Fin.cases (record002_frame012_supported hcells) (Fin.cases (record002_frame013_supported hcells) (Fin.cases (record002_frame014_supported hcells) (Fin.cases (record002_frame015_supported hcells) (Fin.cases (record002_frame016_supported hcells) (Fin.cases (record002_frame017_supported hcells) (Fin.cases (record002_frame018_supported hcells) (Fin.cases (record002_frame019_supported hcells) (Fin.cases (record002_frame020_supported hcells) (Fin.cases (record002_frame021_supported hcells) (Fin.cases (record002_frame022_supported hcells) (Fin.cases (record002_frame023_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))))))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa87a80a78a6ca5fa51a3fa32a22a0f93e93592c9209139068f58e88d98c684583782a81c8097f77e07cf7bf7a879b79078076f76075073b7277137006eb6d96c66b36a05d95d25c95bf5b15a05905835735644fa4ef4e44da4cc4bd4ac49e49048047546d4604524444364254154043f53e43d63c53b63a632d3203133052f52e72d92cd2be2ac2a029628627526725a24923922821a2071f81e71d91cb1c21ba1ae1a01911831731651561460b405c05b05a05905805705605505405302602502402302202102001f01e01d01101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame001_links_0000 (interval_append _ 64 128 153 record003_frame001_links_0064 record003_frame001_links_0128))
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb31b27b20b14b06afaaecad6ac7ab79d79c89c19b59a399498596f9609518c38b18a889888687686484b8378248108007f77ea7d47c07ac79678176e7567407297126fc62b61d61360b5fe5f35e55d75cb5bc54053052751c50e5014f14e14d34c44b34a449b49048247746945944a43d42941b40d3fc3ee36b35834d34133131f30c2fa2ea2d82c72b72ad2a12932862752652552462322232132011f01e21d51cd1c41b51a819818717816b0bf05e05d05c05b05a05905805705605502602502402302202102001f01e01d01101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame002_links_0000 (interval_append _ 64 128 153 record003_frame002_links_0064 record003_frame002_links_0128))
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0x394e478ee2f88e1781df779dd73dceb37cd331cbb2ac9720c6ef8bd2f0baee6b86d8b3ec6b02baadab2ab6a9a96a0a6692a36839f2759ca6e8f63a8de348c62e8aa2487a197f5fa7ddf37bdeb795db745ca711c16f9b96d5b16b1a56799963d886057e5e957551515394a519414e5314a9244851e469164490e421023f4f53c0eb3a0e437cdb35cd333ccb31cbf2dcb01b4461144410c42104400fc3e0f4260942408c220842007c1e074110400f0380d0300b02809020060140400c0200400 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame003_links_0000 (interval_append _ 64 128 153 record003_frame003_links_0064 record003_frame003_links_0128))
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
def record003_frame004_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0452.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0452.count (({ width := 9, code := 0x162b057ab95aac55aa952a85067f3d9dce66f3599cc65f259147e39198b44e210d8541a0902803f9f8fa7c3d9e8f177bb5d6e96e369b0d66a349a0ce6632980be5e2e970b65a2c960ae55aa54ea551a853e9d4da652e9549a451e8642209007e3e1e8f0763a1c8e270379b8da6c351a0cc6431180bc5c2d164b0572b154a852281387833190c4602f170b4582b150783a1c0d86832180b8582a10078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record003_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record003) (record003.maps 4)
      (record003.inverseMaps 4) record003_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame004_links_0000 (interval_append _ 64 128 153 record003_frame004_links_0064 record003_frame004_links_0128))
theorem record003_frame004_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 4 :=
  of_group record003 4 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0452
    Papers.RationalityTen.SharedFrameCatalogue.group0452_facts record003_frame004_indices record003_frame004_graph record003_frame004_links
def record003_frame005_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0310.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0310.count (({ width := 8, code := 0xbdbcbbbab9b8b7b6b5b4b2b1b0afaeadacabaaa9a6a4a2a09e9c9a989695939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b78767472706e6c6a68676564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a3938373635342e2827262524232221201f1b1a1918171615141312100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0310.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0310.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0310.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0310.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0310.localPairCheck (smallEmbedding record003) (record003.maps 5)
      (record003.inverseMaps 5) record003_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame005_links_0000 (interval_append _ 64 128 153 record003_frame005_links_0064 record003_frame005_links_0128))
theorem record003_frame005_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 5 :=
  of_group record003 5 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0310
    Papers.RationalityTen.SharedFrameCatalogue.group0310_facts record003_frame005_indices record003_frame005_graph record003_frame005_links
def record003_frame006_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc2a60eb03d806bf55f72f89796bb45cf2a6d516a7f53a29a14c0a5051d289142297c4b5a56529093649624652028ea46a230916089e446a1ed0e285f424a0d103e8073f91f70f8c7af3539a64d1067c3359984cac6443191884b4c5972c515ecadc5652ac1514a6c52828c94209f24ea26d93489884b1251125090446f22f91408803ad1cd8e306f636c1b10d4867a32918b8c185e82e31698b085702a814a0a044de25912388d044420e0fe87b83c01d10e186e43561980c305d819205e02e81700b605a02c81600ae05602a809804a024011808804202000f807803a011008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record003_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 6)
      (record003.inverseMaps 6) record003_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame006_links_0000 (interval_append _ 64 128 153 record003_frame006_links_0064 record003_frame006_links_0128))
theorem record003_frame006_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 6 :=
  of_group record003 6 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record003_frame006_indices record003_frame006_graph record003_frame006_links
def record003_frame007_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x353d434dd2b47d133dcdb31cb2f3bc2edbaae7b92e0b66d5b46aeaaaa6a8a9ea6a93a26829ee789da739c66e9ae6397254932418f6388ce307fdfd7edf97ddf57c5eb799e1711c2701be6f1ba6cdac699a066d9965d9564d916217f5e17159d645855e569384d1304b5294991f45d1142d0640d003f8fb3e4f33ace6384d8350d0330c9314c12f4ba2d8b32b4a527c991743f0f83d0f03b0e8390e0370d823088210801f0781d0701b068110400f0380d0300b02809020060140400c0200400 } : Fields).get c.val)
theorem record003_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record003) (record003.maps 7)
      (record003.inverseMaps 7) record003_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame007_links_0000 (interval_append _ 64 128 153 record003_frame007_links_0064 record003_frame007_links_0128))
theorem record003_frame007_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 7 :=
  of_group record003 7 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record003_frame007_indices record003_frame007_graph record003_frame007_links
def record003_frame008_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0200.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0200.count (({ width := 10, code := 0x2288962287e1c866158460d825e8795e277ddc765d674dd0735b76d1b16b9ab6a1a367999651926418e6318a6218660d805f57a5e1765d17256557555535454f53149519434b92c4a928499244891f4711945914449104390c42505404fd3ecf93dcf53ccd7350d1338cb320c5300bb2d8b22c0ae2b0aa2a0a62889e2689624c902348b22086210822007e1f0771c86d13c380dc360d4340cc320c4300bc2007c1e0741c06c1a0641805c110400f0380d0300b02809020060140400c0200400 } : Fields).get c.val)
theorem record003_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record003) (record003.maps 8)
      (record003.inverseMaps 8) record003_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame008_links_0000 (interval_append _ 64 128 153 record003_frame008_links_0064 record003_frame008_links_0128))
theorem record003_frame008_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 8 :=
  of_group record003 8 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0200
    Papers.RationalityTen.SharedFrameCatalogue.group0200_facts record003_frame008_indices record003_frame008_graph record003_frame008_links
def record003_frame009_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0785.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0785.count (({ width := 10, code := 0x257956539464f9364991a439021484a108360b8220680e017fdea79de4785de76dd8749ce729c8719c4709c06f9bb6d9b16b1a6691a16799b5d9745c9705b96c5a5655855d51d4550d414fd3d4f1384d5324b92c4a928499244851b4550f4250741503400e4384de36cd8354d3330c6300bb2e4b72d4b32c4af2a4a427c99258932408e22c8921c8520c811fc791d06f1303a0e4380dc360d4340cc320c41f0781d0701b0681906017058110400f0380d0300b02809020060140400c0200400 } : Fields).get c.val)
theorem record003_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record003) (record003.maps 9)
      (record003.inverseMaps 9) record003_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame009_links_0000 (interval_append _ 64 128 153 record003_frame009_links_0064 record003_frame009_links_0128))
theorem record003_frame009_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 9 :=
  of_group record003 9 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0785
    Papers.RationalityTen.SharedFrameCatalogue.group0785_facts record003_frame009_indices record003_frame009_graph record003_frame009_links
def record003_frame010_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0336.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0336.count (({ width := 10, code := 0x1dc769d8759d4749d0739cc729aa6a1a6691a26819f6799d67187611815f97b5e1755c96f5b16a5a166591625815f5755b56556551525414f4d9344c9304b92c4a5274952343d0d42d0941d0541102400fe3ecf93dcf53ccf13bcec3a4e6390e2380de370c12f8bb2e0b52c8b02b0a8290a02789c26898258942408c220842047e1ec791dc751cc711bc6d1ac661845c104340cc320c4300bc2e0b42c0ac1e0741c06c1a0641805c160541003c0e0340c02c0a0240801c060140400c0200400 } : Fields).get c.val)
theorem record003_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0336.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record003) (record003.maps 10) (record003.inverseMaps 10) record003_frame010_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record003) (record003.maps 10) (record003.inverseMaps 10) record003_frame010_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record003) (record003.maps 10) (record003.inverseMaps 10) record003_frame010_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record003) (record003.maps 10)
      (record003.inverseMaps 10) record003_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame010_links_0000 (interval_append _ 64 128 153 record003_frame010_links_0064 record003_frame010_links_0128))
theorem record003_frame010_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 10 :=
  of_group record003 10 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0336
    Papers.RationalityTen.SharedFrameCatalogue.group0336_facts record003_frame010_indices record003_frame010_graph record003_frame010_links
def record003_frame011_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xbe85eaaefd762ba05c6adf56d8b595a7a935474a2150928093e29e24e9270536a92f48c23fd1d88db463a2d5148890442a1d50ba846419208101e7fe3f61f6cfa47be3d49e40efa76b32398c8c3a60e2ff97bcbc25d22e116d8a7652728914089e84e726b93249784b2252924c902471232115c89243c217909882e4071fa8f9c7b635019d0c9062a30617b8ba05b22ca15f8ac453a28a13c09b44c025212388e846222210887fc3e41e50eb071836a1a80ce064030a1790b6859019005e02e81700b605a02c81600ae05602a809804a024011808804202000f807803a011008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record003_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 11) (record003.inverseMaps 11) record003_frame011_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 11) (record003.inverseMaps 11) record003_frame011_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 11) (record003.inverseMaps 11) record003_frame011_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 11)
      (record003.inverseMaps 11) record003_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame011_links_0000 (interval_append _ 64 128 153 record003_frame011_links_0064 record003_frame011_links_0128))
theorem record003_frame011_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 11 :=
  of_group record003 11 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record003_frame011_indices record003_frame011_graph record003_frame011_links
def record003_frame012_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0x5a2b39662cad8ab07602bdd73ad74828cd14a1d4167e4f89e73ae7149991921a3ec728d11862dc518910ea1642683b04603c007f2fc1f33df79cefdd9ba56aad35a3340676cc595b27644c5d6fad2592b0d5e2b355caa151a9b524a1d402784e0999302584a892d222364548810a9e03a872ce31c03706ccd71a9342664c71863005f0ba16e2d0594ae9572965009c13024e46c8990f20e4047e8f61e43b0488520a21402784e09a1302584a092098128240460881082003e0780e81102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record003_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record003) (record003.maps 12) (record003.inverseMaps 12) record003_frame012_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record003) (record003.maps 12) (record003.inverseMaps 12) record003_frame012_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record003) (record003.maps 12) (record003.inverseMaps 12) record003_frame012_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record003) (record003.maps 12)
      (record003.inverseMaps 12) record003_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame012_links_0000 (interval_append _ 64 128 153 record003_frame012_links_0064 record003_frame012_links_0128))
theorem record003_frame012_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 12 :=
  of_group record003 12 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record003_frame012_indices record003_frame012_graph record003_frame012_links
def record003_frame013_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0351.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0351.count (({ width := 9, code := 0x1afd6eaf53a7d2e8f439fcee2b1186c260b017ebe5eaf170b6daacd62af56aad52a7d2e9347a25067d3b9c4d6672f964a64f258a4461d0b8441604ff7e3e9e2ee75b9dc6df6db5da6d166b2d92c661b017aba5bad562ad54a9946974aa4d228e45a210a823f9f8fa7c3d9e4ee75399c4de6e361a8d0663218cc4612f974b6592b9547433190c4602f170b4582b15084401f0f074381b0d0643010078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record003_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record003) (record003.maps 13) (record003.inverseMaps 13) record003_frame013_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record003) (record003.maps 13) (record003.inverseMaps 13) record003_frame013_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record003) (record003.maps 13) (record003.inverseMaps 13) record003_frame013_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record003) (record003.maps 13)
      (record003.inverseMaps 13) record003_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame013_links_0000 (interval_append _ 64 128 153 record003_frame013_links_0064 record003_frame013_links_0128))
theorem record003_frame013_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 13 :=
  of_group record003 13 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0351
    Papers.RationalityTen.SharedFrameCatalogue.group0351_facts record003_frame013_indices record003_frame013_graph record003_frame013_links
def record003_frame014_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0432.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0432.count (({ width := 8, code := 0xbdbcbbbab9b8b7b6b5b4b2b1b0afaeadacabaaa9a6a4a2a09e9c9a989695939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b78767472706e6c6a68676564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a3938373635342e2827262524232221201f1b1a1918171615141312100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0432.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0432.localPairCheck (smallEmbedding record003) (record003.maps 14) (record003.inverseMaps 14) record003_frame014_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0432.localPairCheck (smallEmbedding record003) (record003.maps 14) (record003.inverseMaps 14) record003_frame014_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0432.localPairCheck (smallEmbedding record003) (record003.maps 14) (record003.inverseMaps 14) record003_frame014_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0432.localPairCheck (smallEmbedding record003) (record003.maps 14)
      (record003.inverseMaps 14) record003_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame014_links_0000 (interval_append _ 64 128 153 record003_frame014_links_0064 record003_frame014_links_0128))
theorem record003_frame014_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 14 :=
  of_group record003 14 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0432
    Papers.RationalityTen.SharedFrameCatalogue.group0432_facts record003_frame014_indices record003_frame014_graph record003_frame014_links
def record003_frame015_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x43c8710ce1842b8510920fc1c830f41e5bc7784ef9dd3b5762eb5d4b87700de1b8b696c8d79ab35169ad25a0b3c668cbd93b2363cc59893065febe978ae8534a5547a895069f53ca734da9a524a4347a8d91822a44c8810d217428831032003f47d0f89eb3ca788ec9d239e724e19903105fcbb16d2ca580ab94f296528a093d26a4c4949252424648a90d21040c7e0f51de39c708da1a8334650c417a2e83904808e118228440861082084007e08c1102104007c0f01d03806c0d01102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record003_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record003) (record003.maps 15) (record003.inverseMaps 15) record003_frame015_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record003) (record003.maps 15) (record003.inverseMaps 15) record003_frame015_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record003) (record003.maps 15) (record003.inverseMaps 15) record003_frame015_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record003) (record003.maps 15)
      (record003.inverseMaps 15) record003_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame015_links_0000 (interval_append _ 64 128 153 record003_frame015_links_0064 record003_frame015_links_0128))
theorem record003_frame015_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 15 :=
  of_group record003 15 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record003_frame015_indices record003_frame015_graph record003_frame015_links
def record003_frame016_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0699.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0699.count (({ width := 8, code := 0xebeae9e8e7e6e5e4e3e2d5d4d3d2d1d0cfcecdccc4c2c0bebcbab8b6b4b2b1b0afaeadacabaaa9a8a7a6a5a4a3969594939291908f8e8d8583817f7d7b797775737271706f6e6d6c6b6a6968676665645d5b59585655545251504f4d4b4a48474644434241403f3e3d3c3a383735343331302f292827262524232221201f1e1d1c1b1a1918171615100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0699.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0699.localPairCheck (smallEmbedding record003) (record003.maps 16) (record003.inverseMaps 16) record003_frame016_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0699.localPairCheck (smallEmbedding record003) (record003.maps 16) (record003.inverseMaps 16) record003_frame016_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0699.localPairCheck (smallEmbedding record003) (record003.maps 16) (record003.inverseMaps 16) record003_frame016_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0699.localPairCheck (smallEmbedding record003) (record003.maps 16)
      (record003.inverseMaps 16) record003_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame016_links_0000 (interval_append _ 64 128 153 record003_frame016_links_0064 record003_frame016_links_0128))
theorem record003_frame016_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 16 :=
  of_group record003 16 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0699
    Papers.RationalityTen.SharedFrameCatalogue.group0699_facts record003_frame016_indices record003_frame016_graph record003_frame016_links
def record003_frame017_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0088.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0088.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0088.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0088.localPairCheck (smallEmbedding record003) (record003.maps 17) (record003.inverseMaps 17) record003_frame017_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0088.localPairCheck (smallEmbedding record003) (record003.maps 17) (record003.inverseMaps 17) record003_frame017_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0088.localPairCheck (smallEmbedding record003) (record003.maps 17) (record003.inverseMaps 17) record003_frame017_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0088.localPairCheck (smallEmbedding record003) (record003.maps 17)
      (record003.inverseMaps 17) record003_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame017_links_0000 (interval_append _ 64 128 153 record003_frame017_links_0064 record003_frame017_links_0128))
theorem record003_frame017_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 17 :=
  of_group record003 17 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0088
    Papers.RationalityTen.SharedFrameCatalogue.group0088_facts record003_frame017_indices record003_frame017_graph record003_frame017_links
def record003_frame018_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0962.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0962.count (({ width := 10, code := 0x2c2afebbae2b4ac6aeaaaa7a92649865e96e589565293e4c926328ba2a89e238821d8661684e108320a81a04801fe7f1f87d9f17b9ec7a9e86b9ab6a1a668da167d9c669986097e5f1795dd745c9705b56b5a5645855d56956551515354b5214550d414fd1243105400f93d0f13a8e5388e1370d934cd0328c8314bf2f4ba2e0b52c4ad2a4a52889d2689524c9022c891944511043108411003f0f83d0f023088210801f0781d0701b068110400f0380d0300b02809020060140400c0200400 } : Fields).get c.val)
theorem record003_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record003) (record003.maps 18) (record003.inverseMaps 18) record003_frame018_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record003) (record003.maps 18) (record003.inverseMaps 18) record003_frame018_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record003) (record003.maps 18) (record003.inverseMaps 18) record003_frame018_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record003) (record003.maps 18)
      (record003.inverseMaps 18) record003_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame018_links_0000 (interval_append _ 64 128 153 record003_frame018_links_0064 record003_frame018_links_0128))
theorem record003_frame018_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 18 :=
  of_group record003 18 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0962
    Papers.RationalityTen.SharedFrameCatalogue.group0962_facts record003_frame018_indices record003_frame018_graph record003_frame018_links
def record003_frame019_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0518.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0518.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0518.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0518.localPairCheck (smallEmbedding record003) (record003.maps 19) (record003.inverseMaps 19) record003_frame019_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0518.localPairCheck (smallEmbedding record003) (record003.maps 19) (record003.inverseMaps 19) record003_frame019_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0518.localPairCheck (smallEmbedding record003) (record003.maps 19) (record003.inverseMaps 19) record003_frame019_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0518.localPairCheck (smallEmbedding record003) (record003.maps 19)
      (record003.inverseMaps 19) record003_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame019_links_0000 (interval_append _ 64 128 153 record003_frame019_links_0064 record003_frame019_links_0128))
theorem record003_frame019_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 19 :=
  of_group record003 19 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0518
    Papers.RationalityTen.SharedFrameCatalogue.group0518_facts record003_frame019_indices record003_frame019_graph record003_frame019_links
def record003_frame020_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0731.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0731.count (({ width := 8, code := 0xd2d1d0cfcecdcccbcac9bcbbbab9b8b7b6b5b4b3acabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a99989796959487868584838281807f7e77767574737271706f6e6d6c6b6a696867666564636261605f5856545351504f4d4c4b4a4846454342413f3e3d3c3b3a393837353332302f2e2c2b2a292827262524232221201f1e1d1c1b1a1918171615100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0731.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0731.localPairCheck (smallEmbedding record003) (record003.maps 20) (record003.inverseMaps 20) record003_frame020_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0731.localPairCheck (smallEmbedding record003) (record003.maps 20) (record003.inverseMaps 20) record003_frame020_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0731.localPairCheck (smallEmbedding record003) (record003.maps 20) (record003.inverseMaps 20) record003_frame020_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0731.localPairCheck (smallEmbedding record003) (record003.maps 20)
      (record003.inverseMaps 20) record003_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame020_links_0000 (interval_append _ 64 128 153 record003_frame020_links_0064 record003_frame020_links_0128))
theorem record003_frame020_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 20 :=
  of_group record003 20 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0731
    Papers.RationalityTen.SharedFrameCatalogue.group0731_facts record003_frame020_indices record003_frame020_graph record003_frame020_links
def record003_frame021_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0183.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0183.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0183.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0183.localPairCheck (smallEmbedding record003) (record003.maps 21) (record003.inverseMaps 21) record003_frame021_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0183.localPairCheck (smallEmbedding record003) (record003.maps 21) (record003.inverseMaps 21) record003_frame021_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0183.localPairCheck (smallEmbedding record003) (record003.maps 21) (record003.inverseMaps 21) record003_frame021_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0183.localPairCheck (smallEmbedding record003) (record003.maps 21)
      (record003.inverseMaps 21) record003_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame021_links_0000 (interval_append _ 64 128 153 record003_frame021_links_0064 record003_frame021_links_0128))
theorem record003_frame021_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 21 :=
  of_group record003 21 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0183
    Papers.RationalityTen.SharedFrameCatalogue.group0183_facts record003_frame021_indices record003_frame021_graph record003_frame021_links
def record003_frame022_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0917.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0917.count (({ width := 9, code := 0x14aa4d228f46a250a833f9e4a24f2692c9247219047e3b0f86c2e130782c0e02ff7ebf1f6fa7cbe1eef67abd1e6f1783bddaeb6a34da4d16833d9acc65b2574b85bad166b0572b554a853a994aa3512813e9e4e26d32984ba552682409fcf87a3b9d8e871381bcdc6c351a0cc6531984c05e2e970b65a2c95caa5228134984a239187e371b0d46833190c4602f1708842200f8783a1c0d86832110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record003_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0917.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0917.localPairCheck (smallEmbedding record003) (record003.maps 22) (record003.inverseMaps 22) record003_frame022_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0917.localPairCheck (smallEmbedding record003) (record003.maps 22) (record003.inverseMaps 22) record003_frame022_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame022_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0917.localPairCheck (smallEmbedding record003) (record003.maps 22) (record003.inverseMaps 22) record003_frame022_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0917.localPairCheck (smallEmbedding record003) (record003.maps 22)
      (record003.inverseMaps 22) record003_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame022_links_0000 (interval_append _ 64 128 153 record003_frame022_links_0064 record003_frame022_links_0128))
theorem record003_frame022_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 22 :=
  of_group record003 22 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0917
    Papers.RationalityTen.SharedFrameCatalogue.group0917_facts record003_frame022_indices record003_frame022_graph record003_frame022_links
def record003_frame023_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0695.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0695.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0695.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0695.localPairCheck (smallEmbedding record003) (record003.maps 23) (record003.inverseMaps 23) record003_frame023_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0695.localPairCheck (smallEmbedding record003) (record003.maps 23) (record003.inverseMaps 23) record003_frame023_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame023_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0695.localPairCheck (smallEmbedding record003) (record003.maps 23) (record003.inverseMaps 23) record003_frame023_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0695.localPairCheck (smallEmbedding record003) (record003.maps 23)
      (record003.inverseMaps 23) record003_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame023_links_0000 (interval_append _ 64 128 153 record003_frame023_links_0064 record003_frame023_links_0128))
theorem record003_frame023_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 23 :=
  of_group record003 23 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0695
    Papers.RationalityTen.SharedFrameCatalogue.group0695_facts record003_frame023_indices record003_frame023_graph record003_frame023_links
def record003_frame024_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0390.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0390.count (({ width := 8, code := 0xc8c6c4c2c0bebcbab8b6b4b2b0aeacaaa8a6a4a2a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a8988878583817f7d7b797775737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a3938372c2b2a292827262524231c1b1a1918171615141311100f0e0d0c0b0a090806050403020100 } : Fields).get c.val)
theorem record003_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0390.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0390.localPairCheck (smallEmbedding record003) (record003.maps 24) (record003.inverseMaps 24) record003_frame024_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0390.localPairCheck (smallEmbedding record003) (record003.maps 24) (record003.inverseMaps 24) record003_frame024_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame024_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0390.localPairCheck (smallEmbedding record003) (record003.maps 24) (record003.inverseMaps 24) record003_frame024_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0390.localPairCheck (smallEmbedding record003) (record003.maps 24)
      (record003.inverseMaps 24) record003_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame024_links_0000 (interval_append _ 64 128 153 record003_frame024_links_0064 record003_frame024_links_0128))
theorem record003_frame024_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 24 :=
  of_group record003 24 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0390
    Papers.RationalityTen.SharedFrameCatalogue.group0390_facts record003_frame024_indices record003_frame024_graph record003_frame024_links
def record003_frame025_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0692.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0692.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame025_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0692.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame025_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0692.localPairCheck (smallEmbedding record003) (record003.maps 25) (record003.inverseMaps 25) record003_frame025_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame025_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0692.localPairCheck (smallEmbedding record003) (record003.maps 25) (record003.inverseMaps 25) record003_frame025_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame025_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0692.localPairCheck (smallEmbedding record003) (record003.maps 25) (record003.inverseMaps 25) record003_frame025_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame025_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0692.localPairCheck (smallEmbedding record003) (record003.maps 25)
      (record003.inverseMaps 25) record003_frame025_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame025_links_0000 (interval_append _ 64 128 153 record003_frame025_links_0064 record003_frame025_links_0128))
theorem record003_frame025_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 25 :=
  of_group record003 25 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0692
    Papers.RationalityTen.SharedFrameCatalogue.group0692_facts record003_frame025_indices record003_frame025_graph record003_frame025_links
def record003_frame026_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0414.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0414.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame026_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0414.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame026_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0414.localPairCheck (smallEmbedding record003) (record003.maps 26) (record003.inverseMaps 26) record003_frame026_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame026_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0414.localPairCheck (smallEmbedding record003) (record003.maps 26) (record003.inverseMaps 26) record003_frame026_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame026_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0414.localPairCheck (smallEmbedding record003) (record003.maps 26) (record003.inverseMaps 26) record003_frame026_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame026_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0414.localPairCheck (smallEmbedding record003) (record003.maps 26)
      (record003.inverseMaps 26) record003_frame026_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame026_links_0000 (interval_append _ 64 128 153 record003_frame026_links_0064 record003_frame026_links_0128))
theorem record003_frame026_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 26 :=
  of_group record003 26 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0414
    Papers.RationalityTen.SharedFrameCatalogue.group0414_facts record003_frame026_indices record003_frame026_graph record003_frame026_links
def record003_frame027_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0277.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0277.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame027_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0277.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame027_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0277.localPairCheck (smallEmbedding record003) (record003.maps 27) (record003.inverseMaps 27) record003_frame027_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame027_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0277.localPairCheck (smallEmbedding record003) (record003.maps 27) (record003.inverseMaps 27) record003_frame027_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame027_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0277.localPairCheck (smallEmbedding record003) (record003.maps 27) (record003.inverseMaps 27) record003_frame027_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame027_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0277.localPairCheck (smallEmbedding record003) (record003.maps 27)
      (record003.inverseMaps 27) record003_frame027_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame027_links_0000 (interval_append _ 64 128 153 record003_frame027_links_0064 record003_frame027_links_0128))
theorem record003_frame027_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 27 :=
  of_group record003 27 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0277
    Papers.RationalityTen.SharedFrameCatalogue.group0277_facts record003_frame027_indices record003_frame027_graph record003_frame027_links
def record003_frame028_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xcef66f3331976ca664831f58d2c5361faa294f2a6752b2905456a1850227b93b49844bea5d92de9684b0a5692a694c4a2a4f926e930494a489236914486a4191fe8f6477a3a11c28da37e1b9cdac6c33579a64d0866f32c9910ae85612a794f4a5651828293d09c24d125f12b093448823b919c8aa443219108c8204001f78f7c79e3051790b8059c2bc1548a5850a272131093c47a22b10c88203f01e60ea070c3681a10c886002e01600ab053c29014109d04cc25812508f045c1a205e02e81700b605a02c81600ae05602a809804a024011808804202000f807803a011008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record003_frame028_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame028_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 28) (record003.inverseMaps 28) record003_frame028_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame028_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 28) (record003.inverseMaps 28) record003_frame028_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame028_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 28) (record003.inverseMaps 28) record003_frame028_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame028_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 28)
      (record003.inverseMaps 28) record003_frame028_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame028_links_0000 (interval_append _ 64 128 153 record003_frame028_links_0064 record003_frame028_links_0128))
theorem record003_frame028_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 28 :=
  of_group record003 28 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record003_frame028_indices record003_frame028_graph record003_frame028_links
def record003_frame029_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x592b1961ac1577ae55a2ae557aa13ae73ce29b535265cc09772c254c718d919e31c5d8ad13e244428770d617c2884506e0a40d80cffdfc3ee7caf75ebbd16c2d75abb4d686ced98b26638c4d67ac8586af95a2ad54aa794ba8d510a053ca724d49892ca514909051aa2c444865089d439e724e11bb3646a8d199c324634c397f2ee5c0b395f2ae534a313a26249c8f116222434841021fa3e0790ed1ce384530580ae1582a8540a61482885009e098128240460881082003e0780e81102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record003_frame029_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame029_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record003) (record003.maps 29) (record003.inverseMaps 29) record003_frame029_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame029_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record003) (record003.maps 29) (record003.inverseMaps 29) record003_frame029_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame029_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record003) (record003.maps 29) (record003.inverseMaps 29) record003_frame029_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame029_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record003) (record003.maps 29)
      (record003.inverseMaps 29) record003_frame029_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame029_links_0000 (interval_append _ 64 128 153 record003_frame029_links_0064 record003_frame029_links_0128))
theorem record003_frame029_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 29 :=
  of_group record003 29 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record003_frame029_indices record003_frame029_graph record003_frame029_links
def record003_frame030_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x6aa6a269b68e68868167966f6646555d25c85c25bb5b45a95a159758957d53d53753052a52351e51951250a5014fa4f34ec4e64df4da4d54ce4c64be4b54ae4a749f4984094043f73f13e43dd3d43cb3bd3b035434b34333832f32b32431a30e3042f92f12e92e22da2d42cc2bf2b42aa29d29128727c27021620b2021fc1f41ed1e61dc1cf1c51bb1b21aa1a519d19618e18117416b15f15314713d13212912211b11510e1091040fd0f70f10ae05c05b05a05905805705605505405302602502402302202102001f01e01d01101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record003_frame030_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame030_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record003) (record003.maps 30) (record003.inverseMaps 30) record003_frame030_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame030_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record003) (record003.maps 30) (record003.inverseMaps 30) record003_frame030_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame030_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record003) (record003.maps 30) (record003.inverseMaps 30) record003_frame030_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame030_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record003) (record003.maps 30)
      (record003.inverseMaps 30) record003_frame030_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame030_links_0000 (interval_append _ 64 128 153 record003_frame030_links_0064 record003_frame030_links_0128))
theorem record003_frame030_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 30 :=
  of_group record003 30 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record003_frame030_indices record003_frame030_graph record003_frame030_links
def record003_frame031_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0757.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0757.count (({ width := 8, code := 0xf6f5f4f3f2f1f0efeeede3e2e1e0dfdedddcdbdad2d0cecccac8c6c3c1bfbebdbbbab8b6b4b3b1afadaba9a7a6a2a1a09f9e9d9c9b9a999291908f8e8d8c8a8988878685848382807f7d7b79787776756e6d6c6b6a6968666564636261605f5e5c5b595755545352514f4d4b49474543413f3d3127262524232221201f1e1b1a1918171615141312100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame031_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0757.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame031_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0757.localPairCheck (smallEmbedding record003) (record003.maps 31) (record003.inverseMaps 31) record003_frame031_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame031_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0757.localPairCheck (smallEmbedding record003) (record003.maps 31) (record003.inverseMaps 31) record003_frame031_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame031_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0757.localPairCheck (smallEmbedding record003) (record003.maps 31) (record003.inverseMaps 31) record003_frame031_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame031_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0757.localPairCheck (smallEmbedding record003) (record003.maps 31)
      (record003.inverseMaps 31) record003_frame031_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame031_links_0000 (interval_append _ 64 128 153 record003_frame031_links_0064 record003_frame031_links_0128))
theorem record003_frame031_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 31 :=
  of_group record003 31 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0757
    Papers.RationalityTen.SharedFrameCatalogue.group0757_facts record003_frame031_indices record003_frame031_graph record003_frame031_links
def record003_frame032_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0198.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0198.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame032_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0198.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame032_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0198.localPairCheck (smallEmbedding record003) (record003.maps 32) (record003.inverseMaps 32) record003_frame032_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame032_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0198.localPairCheck (smallEmbedding record003) (record003.maps 32) (record003.inverseMaps 32) record003_frame032_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame032_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0198.localPairCheck (smallEmbedding record003) (record003.maps 32) (record003.inverseMaps 32) record003_frame032_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame032_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0198.localPairCheck (smallEmbedding record003) (record003.maps 32)
      (record003.inverseMaps 32) record003_frame032_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame032_links_0000 (interval_append _ 64 128 153 record003_frame032_links_0064 record003_frame032_links_0128))
theorem record003_frame032_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 32 :=
  of_group record003 32 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0198
    Papers.RationalityTen.SharedFrameCatalogue.group0198_facts record003_frame032_indices record003_frame032_graph record003_frame032_links
def record003_frame033_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x5b05ab5a75a059a59558a58457e5774fb4f64f24e94e34dd4d44ce4c94c248647f47847046846145845044944243d43743042942241c41540e4084023fb3f43ed3e73e036d36535f35a35334b34333c33432d2e62d92cf2c82c22bb2b02a829f29829028927e27627126c26525e25725224723d2342302291e11d41ca1c11b91b01a71a119a19318b18417916f16816115b15615114d14213812f12a12311c1161101091040fe0f80f30ed0e80b105b05a05905805705605505405305202602502402302202102001f01e01d01101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record003_frame033_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame033_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record003) (record003.maps 33) (record003.inverseMaps 33) record003_frame033_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame033_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record003) (record003.maps 33) (record003.inverseMaps 33) record003_frame033_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame033_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record003) (record003.maps 33) (record003.inverseMaps 33) record003_frame033_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame033_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record003) (record003.maps 33)
      (record003.inverseMaps 33) record003_frame033_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame033_links_0000 (interval_append _ 64 128 153 record003_frame033_links_0064 record003_frame033_links_0128))
theorem record003_frame033_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 33 :=
  of_group record003 33 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record003_frame033_indices record003_frame033_graph record003_frame033_links
def record003_frame034_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0824.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0824.count (({ width := 11, code := 0x4fe9ef3d278ceb9c93826ecd699f1fa3d4748e11a6324618b916227c1581d02601bfb7e2fb1f2bdf7aef45e4bc377aed5d5ba673ae61c8b8e70cdf9bbb6f624c2d82b005f4bd177aeb5ccb7d52a9a52aa3945a834f69d937a674c095527a4948a8f51aa2f4528810e212412810fd9be36e6c0d41a2332648c69893045e4b916a2c4574aa14d28c50c9d9372564908e91521c41c808fc1ee3c4750e41be3644c85a0b21602b8560aa150298520a2098128240460881082003e0780e81102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record003_frame034_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame034_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record003) (record003.maps 34) (record003.inverseMaps 34) record003_frame034_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame034_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record003) (record003.maps 34) (record003.inverseMaps 34) record003_frame034_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame034_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record003) (record003.maps 34) (record003.inverseMaps 34) record003_frame034_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame034_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record003) (record003.maps 34)
      (record003.inverseMaps 34) record003_frame034_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame034_links_0000 (interval_append _ 64 128 153 record003_frame034_links_0064 record003_frame034_links_0128))
theorem record003_frame034_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 34 :=
  of_group record003 34 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0824
    Papers.RationalityTen.SharedFrameCatalogue.group0824_facts record003_frame034_indices record003_frame034_graph record003_frame034_links
def record003_frame035_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0697.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0697.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame035_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0697.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame035_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0697.localPairCheck (smallEmbedding record003) (record003.maps 35) (record003.inverseMaps 35) record003_frame035_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame035_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0697.localPairCheck (smallEmbedding record003) (record003.maps 35) (record003.inverseMaps 35) record003_frame035_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame035_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0697.localPairCheck (smallEmbedding record003) (record003.maps 35) (record003.inverseMaps 35) record003_frame035_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame035_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0697.localPairCheck (smallEmbedding record003) (record003.maps 35)
      (record003.inverseMaps 35) record003_frame035_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame035_links_0000 (interval_append _ 64 128 153 record003_frame035_links_0064 record003_frame035_links_0128))
theorem record003_frame035_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 35 :=
  of_group record003 35 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0697
    Papers.RationalityTen.SharedFrameCatalogue.group0697_facts record003_frame035_indices record003_frame035_graph record003_frame035_links
def record003_frame036_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0086.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0086.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame036_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0086.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame036_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0086.localPairCheck (smallEmbedding record003) (record003.maps 36) (record003.inverseMaps 36) record003_frame036_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame036_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0086.localPairCheck (smallEmbedding record003) (record003.maps 36) (record003.inverseMaps 36) record003_frame036_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame036_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0086.localPairCheck (smallEmbedding record003) (record003.maps 36) (record003.inverseMaps 36) record003_frame036_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame036_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0086.localPairCheck (smallEmbedding record003) (record003.maps 36)
      (record003.inverseMaps 36) record003_frame036_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame036_links_0000 (interval_append _ 64 128 153 record003_frame036_links_0064 record003_frame036_links_0128))
theorem record003_frame036_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 36 :=
  of_group record003 36 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0086
    Papers.RationalityTen.SharedFrameCatalogue.group0086_facts record003_frame036_indices record003_frame036_graph record003_frame036_links
def record003_frame037_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0413.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0413.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame037_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0413.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame037_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0413.localPairCheck (smallEmbedding record003) (record003.maps 37) (record003.inverseMaps 37) record003_frame037_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame037_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0413.localPairCheck (smallEmbedding record003) (record003.maps 37) (record003.inverseMaps 37) record003_frame037_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame037_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0413.localPairCheck (smallEmbedding record003) (record003.maps 37) (record003.inverseMaps 37) record003_frame037_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame037_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0413.localPairCheck (smallEmbedding record003) (record003.maps 37)
      (record003.inverseMaps 37) record003_frame037_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame037_links_0000 (interval_append _ 64 128 153 record003_frame037_links_0064 record003_frame037_links_0128))
theorem record003_frame037_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 37 :=
  of_group record003 37 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0413
    Papers.RationalityTen.SharedFrameCatalogue.group0413_facts record003_frame037_indices record003_frame037_graph record003_frame037_links
def record003_frame038_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0410.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0410.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame038_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0410.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame038_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0410.localPairCheck (smallEmbedding record003) (record003.maps 38) (record003.inverseMaps 38) record003_frame038_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame038_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0410.localPairCheck (smallEmbedding record003) (record003.maps 38) (record003.inverseMaps 38) record003_frame038_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame038_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0410.localPairCheck (smallEmbedding record003) (record003.maps 38) (record003.inverseMaps 38) record003_frame038_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame038_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0410.localPairCheck (smallEmbedding record003) (record003.maps 38)
      (record003.inverseMaps 38) record003_frame038_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame038_links_0000 (interval_append _ 64 128 153 record003_frame038_links_0064 record003_frame038_links_0128))
theorem record003_frame038_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 38 :=
  of_group record003 38 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0410
    Papers.RationalityTen.SharedFrameCatalogue.group0410_facts record003_frame038_indices record003_frame038_graph record003_frame038_links
def record003_frame039_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd9f6c535cdab6d43695b4519f8ce4666ab21568aa054629dd4c4a5051da89d42694649924792188fa473a3511828ad44d22210ec864429210906081f4069fecfd27d73e31ed4f4a7932ca1600ad85582a194b8a38507279937c8243fe1f50f6078c3b31d00e346f23661aa0d0866031e1870bf05d62d91638ad454629214089c44be20f10408043f41f30f607943bc1d70e807243841bb0da06b434c19f0cc06443141810bd05cc2d81650b005642a414b0a204f426c12f09404841aa05e02e81700b605a02c81600ae05602a809804a024011808804202000f807803a011008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record003_frame039_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame039_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 39) (record003.inverseMaps 39) record003_frame039_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame039_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 39) (record003.inverseMaps 39) record003_frame039_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame039_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 39) (record003.inverseMaps 39) record003_frame039_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame039_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 39)
      (record003.inverseMaps 39) record003_frame039_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame039_links_0000 (interval_append _ 64 128 153 record003_frame039_links_0064 record003_frame039_links_0128))
theorem record003_frame039_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 39 :=
  of_group record003 39 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame039_indices record003_frame039_graph record003_frame039_links
def record003_frame040_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x69b69368d68367766c65f6526466375a159c59158b57e57956f56155a54f4f24ec4e24de4d24cb4bf4b14aa49e49548f48347846c46545944a43c43042441740e4053f936836135c35034a34033332b3213162b92b12ac2a229c29228527a27126525c25324a23d23522c21e2112031f71e81df1d51cc1c018b18718117c17717116c16616115d15715414f14914313d13813212d12912311d11611110e10c10a1051000fb0f60f00ea0e50e00a905705605505405305205105004f04e02602502402302202102001f01e01d01101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record003_frame040_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame040_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record003) (record003.maps 40) (record003.inverseMaps 40) record003_frame040_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame040_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record003) (record003.maps 40) (record003.inverseMaps 40) record003_frame040_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame040_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record003) (record003.maps 40) (record003.inverseMaps 40) record003_frame040_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame040_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record003) (record003.maps 40)
      (record003.inverseMaps 40) record003_frame040_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame040_links_0000 (interval_append _ 64 128 153 record003_frame040_links_0064 record003_frame040_links_0128))
theorem record003_frame040_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 40 :=
  of_group record003 40 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record003_frame040_indices record003_frame040_graph record003_frame040_links
def record003_frame041_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x66a66465f65964f64563d63462761959058858257b57356655f5555485404ed4e54df4d64cd4c24b74ab4a049748c48548047847046645c45544843e43142841e41540d38938137a37336836235734a3413382e62dd2d72ce2c32bb2af2a129728f28427d27827026625f25424a24023622921e21520d2051cb1c51bf1bc1b71b01aa1a419d19618f18918418017a17316c16615e15715114b14313d13913312c12712311d11610f1070ff0f90b205805705605505405305205105004f02602502402302202102001f01e01d01101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record003_frame041_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame041_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record003) (record003.maps 41) (record003.inverseMaps 41) record003_frame041_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame041_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record003) (record003.maps 41) (record003.inverseMaps 41) record003_frame041_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame041_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record003) (record003.maps 41) (record003.inverseMaps 41) record003_frame041_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame041_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record003) (record003.maps 41)
      (record003.inverseMaps 41) record003_frame041_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame041_links_0000 (interval_append _ 64 128 153 record003_frame041_links_0064 record003_frame041_links_0128))
theorem record003_frame041_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 41 :=
  of_group record003 41 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record003_frame041_indices record003_frame041_graph record003_frame041_links
def record003_frame042_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0381.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0381.count (({ width := 9, code := 0x12a94ca24f2692c92472290c4e25118843e1d0d8642e15017fbf5f6f97bbd5e6f177bb5d8eb753a5d0e773395c8e371385c0df69345a0cf6733598cb6532580be5e2e970b65a2c960ae562ad54a95429d4ca55228d44a15027d3c904723114884321506813f9f0f4783b1d0e470369a8ce6431180bc5d2d964ae55299449e4c249186e2e168b0562a148a04e26128783a1c0d86832180b8582a10078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record003_frame042_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0381.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame042_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record003) (record003.maps 42) (record003.inverseMaps 42) record003_frame042_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame042_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record003) (record003.maps 42) (record003.inverseMaps 42) record003_frame042_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame042_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record003) (record003.maps 42) (record003.inverseMaps 42) record003_frame042_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame042_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record003) (record003.maps 42)
      (record003.inverseMaps 42) record003_frame042_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame042_links_0000 (interval_append _ 64 128 153 record003_frame042_links_0064 record003_frame042_links_0128))
theorem record003_frame042_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 42 :=
  of_group record003 42 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0381
    Papers.RationalityTen.SharedFrameCatalogue.group0381_facts record003_frame042_indices record003_frame042_graph record003_frame042_links
def record003_frame043_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0451.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0451.count (({ width := 8, code := 0xa4a3a2a1a09f9e9d9c9b999897969594939291908e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2827262524232221201f1b1a1918171615141312100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame043_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0451.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame043_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0451.localPairCheck (smallEmbedding record003) (record003.maps 43) (record003.inverseMaps 43) record003_frame043_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame043_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0451.localPairCheck (smallEmbedding record003) (record003.maps 43) (record003.inverseMaps 43) record003_frame043_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame043_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0451.localPairCheck (smallEmbedding record003) (record003.maps 43) (record003.inverseMaps 43) record003_frame043_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame043_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0451.localPairCheck (smallEmbedding record003) (record003.maps 43)
      (record003.inverseMaps 43) record003_frame043_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame043_links_0000 (interval_append _ 64 128 153 record003_frame043_links_0064 record003_frame043_links_0128))
theorem record003_frame043_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 43 :=
  of_group record003 43 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0451
    Papers.RationalityTen.SharedFrameCatalogue.group0451_facts record003_frame043_indices record003_frame043_graph record003_frame043_links
def record003_frame044_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0309.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0309.count (({ width := 8, code := 0xf3f1efedebe9e7e5e3e2dfdddbd9d7d5d3d1cfcecbc9c7c5c3c1bfbdbbbab7b5b3b1afadaba9a7a6a3a19f9d9b99979593918f8d8b89888583817f7d7b79777574716f6d6b6967656361605d5b59575554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a39383736353433322c27262524232221201f1e1b1a1918171615141312100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame044_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0309.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame044_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0309.localPairCheck (smallEmbedding record003) (record003.maps 44) (record003.inverseMaps 44) record003_frame044_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame044_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0309.localPairCheck (smallEmbedding record003) (record003.maps 44) (record003.inverseMaps 44) record003_frame044_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame044_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0309.localPairCheck (smallEmbedding record003) (record003.maps 44) (record003.inverseMaps 44) record003_frame044_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame044_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0309.localPairCheck (smallEmbedding record003) (record003.maps 44)
      (record003.inverseMaps 44) record003_frame044_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame044_links_0000 (interval_append _ 64 128 153 record003_frame044_links_0064 record003_frame044_links_0128))
theorem record003_frame044_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 44 :=
  of_group record003 44 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0309
    Papers.RationalityTen.SharedFrameCatalogue.group0309_facts record003_frame044_indices record003_frame044_graph record003_frame044_links
def record003_frame045_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6ea6e76e06dc6d56cf6c56b76aa69e5f45eb5e45db5d35ce5c65ba5af5a254d54553d53252a52551c5105054f84ee4e84df4d94ce4c94c04b24a749a48d48347946d4623ba3b03a83a239b39438c3803723683133093012fa2f22eb2e22d62c82bf2b42ad2a229d29428f28627826a25f25324923c2322281e11d91d01c81bf1b91b61af1a81a019819018817f17717016c16615f15714d14814013713012d12812211c11611010d1081010f90b405c05b05a05905805705605505405302602502402302202102001f01e01d01101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record003_frame045_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame045_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record003) (record003.maps 45) (record003.inverseMaps 45) record003_frame045_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame045_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record003) (record003.maps 45) (record003.inverseMaps 45) record003_frame045_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame045_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record003) (record003.maps 45) (record003.inverseMaps 45) record003_frame045_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame045_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record003) (record003.maps 45)
      (record003.inverseMaps 45) record003_frame045_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame045_links_0000 (interval_append _ 64 128 153 record003_frame045_links_0064 record003_frame045_links_0128))
theorem record003_frame045_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 45 :=
  of_group record003 45 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record003_frame045_indices record003_frame045_graph record003_frame045_links
def record003_frame046_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0758.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0758.count (({ width := 9, code := 0x1389bcda6b3499cc6612f974622f168ac52271287c3616fd7dbe5eef579bc1d6e872b91c6e270b81bedd6d361acd369345a0cf5cae16eb65aad166b0572b13c9c4d2612c9448a31128642a11068240a00fc7b3c9dce873391c4e06933994c86230980bc5d2e16cb2572b150a6522813c9c4d2612c9449241188843209007e3d1e0ec642b150a45027130944823110783a1c0d86832180b8582a10078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record003_frame046_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0758.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame046_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record003) (record003.maps 46) (record003.inverseMaps 46) record003_frame046_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame046_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record003) (record003.maps 46) (record003.inverseMaps 46) record003_frame046_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame046_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record003) (record003.maps 46) (record003.inverseMaps 46) record003_frame046_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame046_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record003) (record003.maps 46)
      (record003.inverseMaps 46) record003_frame046_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame046_links_0000 (interval_append _ 64 128 153 record003_frame046_links_0064 record003_frame046_links_0128))
theorem record003_frame046_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 46 :=
  of_group record003 46 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0758
    Papers.RationalityTen.SharedFrameCatalogue.group0758_facts record003_frame046_indices record003_frame046_graph record003_frame046_links
def record003_frame047_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0199.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0199.count (({ width := 8, code := 0xb1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9c9a98969492908e8c8a898887868584838281807f7e7d7c7b7a7978777675747372716f6d6b69676563615f5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame047_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0199.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame047_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0199.localPairCheck (smallEmbedding record003) (record003.maps 47) (record003.inverseMaps 47) record003_frame047_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame047_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0199.localPairCheck (smallEmbedding record003) (record003.maps 47) (record003.inverseMaps 47) record003_frame047_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame047_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0199.localPairCheck (smallEmbedding record003) (record003.maps 47) (record003.inverseMaps 47) record003_frame047_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame047_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0199.localPairCheck (smallEmbedding record003) (record003.maps 47)
      (record003.inverseMaps 47) record003_frame047_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame047_links_0000 (interval_append _ 64 128 153 record003_frame047_links_0064 record003_frame047_links_0128))
theorem record003_frame047_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 47 :=
  of_group record003 47 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0199
    Papers.RationalityTen.SharedFrameCatalogue.group0199_facts record003_frame047_indices record003_frame047_graph record003_frame047_links
def record003_frame048_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x6bd6b76b26aa6a169869068767e6785d25ce5c45bb5b25a859d59258657d52b5205135074fd4f34e54d94cc4c34bc4b34aa49f49949248847f47546e46445944f44643b39639238837e37336735d35434a3412ef2e42d72c92bd2b02a429a29028728027726e26225924f24624023923222821d2132071fe1c11bb1b41ae1a619e19618e18617f17d17917216b16515d15514f14714013c13813312e12712311e11a11410d1071000f90f30ed0b305d05c05b05a05905805705605505402602502402302202102001f01e01d01101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record003_frame048_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame048_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record003) (record003.maps 48) (record003.inverseMaps 48) record003_frame048_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame048_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record003) (record003.maps 48) (record003.inverseMaps 48) record003_frame048_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame048_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record003) (record003.maps 48) (record003.inverseMaps 48) record003_frame048_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame048_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record003) (record003.maps 48)
      (record003.inverseMaps 48) record003_frame048_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame048_links_0000 (interval_append _ 64 128 153 record003_frame048_links_0064 record003_frame048_links_0128))
theorem record003_frame048_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 48 :=
  of_group record003 48 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record003_frame048_indices record003_frame048_graph record003_frame048_links
def record003_frame049_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x34367cce99ab30654c8d8eb17622ae159aaf554a954fa98524a314325f4b89652b2534a0935252474889051f23b4708d51922f4588a51322143c86d0c2153886fcdd9b63626acd219e330648b59682ca588af95c2b2558a995029a528a39442824f89d93826a4c89692a24e490909021fe3f07c8f61e63c0768ea1ce390708de1b63606a8d219e330648c41822f85d8b816e2d85a8b41662c8588b015e2b8518580ae1582a8540a61482885009e098128240460881082003e0780e81102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record003_frame049_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame049_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record003) (record003.maps 49) (record003.inverseMaps 49) record003_frame049_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame049_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record003) (record003.maps 49) (record003.inverseMaps 49) record003_frame049_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame049_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record003) (record003.maps 49) (record003.inverseMaps 49) record003_frame049_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame049_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record003) (record003.maps 49)
      (record003.inverseMaps 49) record003_frame049_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame049_links_0000 (interval_append _ 64 128 153 record003_frame049_links_0064 record003_frame049_links_0128))
theorem record003_frame049_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 49 :=
  of_group record003 49 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record003_frame049_indices record003_frame049_graph record003_frame049_links
def record003_frame050_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1003.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1003.count (({ width := 9, code := 0x14fa6d329549a3d1687419fcda693398cc25d2c954a24d1c8d4662f168a44e230f86c2e130782c0e03007ebedf2f5793c1dcec72389c2df6f371b4d86b35194c863b1588c260afd7abb5cadd6ab358abd5cab54a9d46a04f271349147a39188b44a210c8441200fc7c3d1e0ec75391c0dc6a33994c6613017cbc5d2e16cb4592c15c9e3d1e0ec74391c0dc6c351a094482311084401f0f07438110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record003_frame050_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1003.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame050_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (smallEmbedding record003) (record003.maps 50) (record003.inverseMaps 50) record003_frame050_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame050_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (smallEmbedding record003) (record003.maps 50) (record003.inverseMaps 50) record003_frame050_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame050_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (smallEmbedding record003) (record003.maps 50) (record003.inverseMaps 50) record003_frame050_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame050_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (smallEmbedding record003) (record003.maps 50)
      (record003.inverseMaps 50) record003_frame050_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame050_links_0000 (interval_append _ 64 128 153 record003_frame050_links_0064 record003_frame050_links_0128))
theorem record003_frame050_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 50 :=
  of_group record003 50 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1003
    Papers.RationalityTen.SharedFrameCatalogue.group1003_facts record003_frame050_indices record003_frame050_graph record003_frame050_links
def record003_frame051_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0755.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0755.count (({ width := 8, code := 0xa2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a8988868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a6968676665646261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a4847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2b27262524232221201f1e1b1a1918171615141312100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame051_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0755.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame051_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0755.localPairCheck (smallEmbedding record003) (record003.maps 51) (record003.inverseMaps 51) record003_frame051_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame051_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0755.localPairCheck (smallEmbedding record003) (record003.maps 51) (record003.inverseMaps 51) record003_frame051_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame051_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0755.localPairCheck (smallEmbedding record003) (record003.maps 51) (record003.inverseMaps 51) record003_frame051_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame051_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0755.localPairCheck (smallEmbedding record003) (record003.maps 51)
      (record003.inverseMaps 51) record003_frame051_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame051_links_0000 (interval_append _ 64 128 153 record003_frame051_links_0064 record003_frame051_links_0128))
theorem record003_frame051_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 51 :=
  of_group record003 51 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0755
    Papers.RationalityTen.SharedFrameCatalogue.group0755_facts record003_frame051_indices record003_frame051_graph record003_frame051_links
def record003_frame052_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0196.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0196.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame052_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0196.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame052_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0196.localPairCheck (smallEmbedding record003) (record003.maps 52) (record003.inverseMaps 52) record003_frame052_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame052_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0196.localPairCheck (smallEmbedding record003) (record003.maps 52) (record003.inverseMaps 52) record003_frame052_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame052_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0196.localPairCheck (smallEmbedding record003) (record003.maps 52) (record003.inverseMaps 52) record003_frame052_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame052_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0196.localPairCheck (smallEmbedding record003) (record003.maps 52)
      (record003.inverseMaps 52) record003_frame052_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame052_links_0000 (interval_append _ 64 128 153 record003_frame052_links_0064 record003_frame052_links_0128))
theorem record003_frame052_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 52 :=
  of_group record003 52 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0196
    Papers.RationalityTen.SharedFrameCatalogue.group0196_facts record003_frame052_indices record003_frame052_graph record003_frame052_links
def record003_frame053_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x3776e4db5b3b606b4d4da634667eb696aad0594b0d5eab655eaa55127b4f09d53926f4d89a5332634c09752d2574a89452724b4909152123d4748dd1a2313a873ce51c437a6dcd81a9346670ba9722de5b0b49662c6580ae95a2ae550a894e296520a294227e4f09b9342624b89590c212418819001fa3e87b8f41e23b8758e81ca3886f8dc1b2358698ce196320628c21823005f8be17a2f05d8ba1722e05685c0b61682c8580ae1582a8540a6098128240460881082003e0780e81102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record003_frame053_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame053_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record003) (record003.maps 53) (record003.inverseMaps 53) record003_frame053_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame053_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record003) (record003.maps 53) (record003.inverseMaps 53) record003_frame053_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame053_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record003) (record003.maps 53) (record003.inverseMaps 53) record003_frame053_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame053_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record003) (record003.maps 53)
      (record003.inverseMaps 53) record003_frame053_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame053_links_0000 (interval_append _ 64 128 153 record003_frame053_links_0064 record003_frame053_links_0128))
theorem record003_frame053_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 53 :=
  of_group record003 53 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record003_frame053_indices record003_frame053_graph record003_frame053_links
def record003_frame054_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1004.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1004.count (({ width := 9, code := 0x1369a4ce6531984ba592a93c7235198c45e2d14894421b0380c01fefe7ebf1f2f77a3c5deee76bb1d6ea73b95c6df6eb6db2d76733196ca64b218cc4612fd6ab3592c560af572ad52a651a85409f4f27538994ba55228f46a2d12813f9f8fa7c3d9e8ee75391bcda6c359a8d2683298cc25d2d964ae552a14ca4512813c9c4d2612c86351a0cc6431180bc5c2d16084401f0f074381b0d06430110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record003_frame054_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1004.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame054_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (smallEmbedding record003) (record003.maps 54) (record003.inverseMaps 54) record003_frame054_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame054_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (smallEmbedding record003) (record003.maps 54) (record003.inverseMaps 54) record003_frame054_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame054_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (smallEmbedding record003) (record003.maps 54) (record003.inverseMaps 54) record003_frame054_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame054_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (smallEmbedding record003) (record003.maps 54)
      (record003.inverseMaps 54) record003_frame054_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame054_links_0000 (interval_append _ 64 128 153 record003_frame054_links_0064 record003_frame054_links_0128))
theorem record003_frame054_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 54 :=
  of_group record003 54 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1004
    Papers.RationalityTen.SharedFrameCatalogue.group1004_facts record003_frame054_indices record003_frame054_graph record003_frame054_links
def record003_frame055_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0756.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0756.count (({ width := 9, code := 0x13398cc25b2b9449a49229044a230f8642e0f0581c05fefc7dbe9f0f77a3cde2ee763add4e973b99c6e270b79b8da6cb5daad46431988c15faf574b85b2d162b057ab556aa5429548a15027d3c9c4d2652e954a2451e8d462291287432110682401f8f6793c1d8ea73391c4de6d359a4d06531984c05f2f174b65a2c158aa54291408a32188c05e2e168b0562a148783a1c0d86832180b8582a110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record003_frame055_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0756.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame055_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0756.localPairCheck (smallEmbedding record003) (record003.maps 55) (record003.inverseMaps 55) record003_frame055_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame055_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0756.localPairCheck (smallEmbedding record003) (record003.maps 55) (record003.inverseMaps 55) record003_frame055_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame055_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0756.localPairCheck (smallEmbedding record003) (record003.maps 55) (record003.inverseMaps 55) record003_frame055_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame055_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0756.localPairCheck (smallEmbedding record003) (record003.maps 55)
      (record003.inverseMaps 55) record003_frame055_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame055_links_0000 (interval_append _ 64 128 153 record003_frame055_links_0064 record003_frame055_links_0128))
theorem record003_frame055_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 55 :=
  of_group record003 55 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0756
    Papers.RationalityTen.SharedFrameCatalogue.group0756_facts record003_frame055_indices record003_frame055_graph record003_frame055_links
def record003_frame056_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0197.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0197.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame056_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0197.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame056_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0197.localPairCheck (smallEmbedding record003) (record003.maps 56) (record003.inverseMaps 56) record003_frame056_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame056_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0197.localPairCheck (smallEmbedding record003) (record003.maps 56) (record003.inverseMaps 56) record003_frame056_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame056_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0197.localPairCheck (smallEmbedding record003) (record003.maps 56) (record003.inverseMaps 56) record003_frame056_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame056_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0197.localPairCheck (smallEmbedding record003) (record003.maps 56)
      (record003.inverseMaps 56) record003_frame056_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame056_links_0000 (interval_append _ 64 128 153 record003_frame056_links_0064 record003_frame056_links_0128))
theorem record003_frame056_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 56 :=
  of_group record003 56 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0197
    Papers.RationalityTen.SharedFrameCatalogue.group0197_facts record003_frame056_indices record003_frame056_graph record003_frame056_links
def record003_frame057_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xcb8658b2a9948c9d64b323d910c8163d2b6d5aaace563ab01572ab2555aa9153a9aa4cc26192ec9644a9a50125a91b48523dd1ca8d3461a2c514088d43d21a10ae84b42220f506c82f33e19d4cde6683309968ca664c32298fcaf256c2af9544a865352931460a144fc276137c9a44c425b12a093248b23e91bc8ca46022d91588a236d1af8d3c67e33018f8c385fc2ee16e8b3057c2ae14f0a3c4fc26d12e8934478231115088c43821510307c83c01cc0db868831c17c0b5055c1a405e02e81700b605a02c81600ae05602a809804a024011808804202000f807803a011008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record003_frame057_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame057_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 57) (record003.inverseMaps 57) record003_frame057_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame057_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 57) (record003.inverseMaps 57) record003_frame057_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame057_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 57) (record003.inverseMaps 57) record003_frame057_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame057_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 57)
      (record003.inverseMaps 57) record003_frame057_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame057_links_0000 (interval_append _ 64 128 153 record003_frame057_links_0064 record003_frame057_links_0128))
theorem record003_frame057_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 57 :=
  of_group record003 57 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record003_frame057_indices record003_frame057_graph record003_frame057_links
def record003_frame058_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x6de6db6d96d46ce6ca6c56be6b96b461260e60b6055ff5fb5f65f05eb5e657f57256d56255554a54053052351950b5034f94ee4e34da4cc4bd4b24a549a49248c4874803ee3ea3e73e13dc3d83d43cf3ca3c436435b35835134833e33632d32231b30f3093032fc2f22ed2e12d72cf2c62bc2b72b32af2aa24523e23923022621b2122091fd1f41ea1e41de1d51c91c41b71ab1a519918f18a18618117a17216715f15514613a12e11f1131070a205a05905805705605505405305205102602502402302202102001f01e01d01101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record003_frame058_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame058_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record003) (record003.maps 58) (record003.inverseMaps 58) record003_frame058_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame058_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record003) (record003.maps 58) (record003.inverseMaps 58) record003_frame058_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame058_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record003) (record003.maps 58) (record003.inverseMaps 58) record003_frame058_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame058_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record003) (record003.maps 58)
      (record003.inverseMaps 58) record003_frame058_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame058_links_0000 (interval_append _ 64 128 153 record003_frame058_links_0064 record003_frame058_links_0128))
theorem record003_frame058_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 58 :=
  of_group record003 58 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record003_frame058_indices record003_frame058_graph record003_frame058_links
def record003_frame059_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0374.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0374.count (({ width := 9, code := 0x173b8dbedb6bb4d9ecb63b0d4aa14ea652a9146a250a8135994be59299348e411d8dc5e29118742e1105813fdfafa7c3d9e8f373391c4e06f371b4d86b35194c86331184c05f2ed70b6592c15cac552a14ca350279369a4ca612e9047a391a8c45a2910864220902803f9f8fa7c3d1e0ec74399c8e270371b0d46833190c6612f9748c361a8d06632188c05e2e168803e1e0e870361a0c8602e110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record003_frame059_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0374.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame059_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0374.localPairCheck (smallEmbedding record003) (record003.maps 59) (record003.inverseMaps 59) record003_frame059_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame059_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0374.localPairCheck (smallEmbedding record003) (record003.maps 59) (record003.inverseMaps 59) record003_frame059_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame059_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0374.localPairCheck (smallEmbedding record003) (record003.maps 59) (record003.inverseMaps 59) record003_frame059_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame059_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0374.localPairCheck (smallEmbedding record003) (record003.maps 59)
      (record003.inverseMaps 59) record003_frame059_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame059_links_0000 (interval_append _ 64 128 153 record003_frame059_links_0064 record003_frame059_links_0128))
theorem record003_frame059_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 59 :=
  of_group record003 59 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0374
    Papers.RationalityTen.SharedFrameCatalogue.group0374_facts record003_frame059_indices record003_frame059_graph record003_frame059_links
def record003_frame060_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x68467e67a67767367266c66565f65b5d55ce5cb5c65c35c05ba5b45ad5a854f54653b53152c52951f5115095004f74ed4e84e34d84d14c74b94b24a94a149a49348f48b3c53c03bb3b73b23af3a93a339d39933933132832131b31830f3022fd2f62ea2e22dc2d82cf2c92c02b32ad2a72a029b29629329022c22521e21520d2091fe1ef1e81e01d51cc1c41c01b91b21a719819018a18217b17417016c16215914f14713d13712b12011610b0ae05c05b05a05905805705605505405302602502402302202102001f01e01d01101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record003_frame060_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame060_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record003) (record003.maps 60) (record003.inverseMaps 60) record003_frame060_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame060_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record003) (record003.maps 60) (record003.inverseMaps 60) record003_frame060_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame060_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record003) (record003.maps 60) (record003.inverseMaps 60) record003_frame060_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame060_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record003) (record003.maps 60)
      (record003.inverseMaps 60) record003_frame060_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame060_links_0000 (interval_append _ 64 128 153 record003_frame060_links_0064 record003_frame060_links_0128))
theorem record003_frame060_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 60 :=
  of_group record003 60 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record003_frame060_indices record003_frame060_graph record003_frame060_links
def record003_frame061_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0551.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0551.count (({ width := 11, code := 0x3d67a2f41e7bcc796f19e1bbf774dadb3b646c2d79ae3566a4d39a5327646c7d8e31a630c4583b035f4be17aaf25e0bb574ae25b8b4966ac6580aed5b2b14a89412624948c90d1ea3946a8c104a064027fcfe1fb3ea7acf41e03ba764eb9d53a673ce41c33746d4d79aa34a684ce95a2ac540a614828a5049b93225c4a09191f2364608990d2104047d8f61e23b0748e71c637c6d8d71a4338650c317a2dc430520a21402784e09a1302584a092098128240460881082003e0780e81102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record003_frame061_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame061_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record003) (record003.maps 61) (record003.inverseMaps 61) record003_frame061_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame061_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record003) (record003.maps 61) (record003.inverseMaps 61) record003_frame061_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame061_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record003) (record003.maps 61) (record003.inverseMaps 61) record003_frame061_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame061_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record003) (record003.maps 61)
      (record003.inverseMaps 61) record003_frame061_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame061_links_0000 (interval_append _ 64 128 153 record003_frame061_links_0064 record003_frame061_links_0128))
theorem record003_frame061_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 61 :=
  of_group record003 61 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0551
    Papers.RationalityTen.SharedFrameCatalogue.group0551_facts record003_frame061_indices record003_frame061_graph record003_frame061_links
def record003_frame062_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x69368c68567f67b67567066c6666635b35ac5a559e59a59558f58b58658253052651b5135094ff4f44ee4e74e24d94cf4c44bb4b54ae4a649c49248b48647f47847046b3a93a439f39939439038b38638237e32b32331931430c3062fd2f72f22ed2e72df2d52ce2c82c32bd2b52af2a92a52a029b29629322421920c2031fc1f31ea1e31dc1d61cc1c11b41ac1a519e19618f18617e17917216b16516115914e14513d13212711e1131081010b005c05b05a05905805705605505405302602502402302202102001f01e01d01101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record003_frame062_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame062_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record003) (record003.maps 62) (record003.inverseMaps 62) record003_frame062_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame062_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record003) (record003.maps 62) (record003.inverseMaps 62) record003_frame062_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame062_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record003) (record003.maps 62) (record003.inverseMaps 62) record003_frame062_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame062_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record003) (record003.maps 62)
      (record003.inverseMaps 62) record003_frame062_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame062_links_0000 (interval_append _ 64 128 153 record003_frame062_links_0064 record003_frame062_links_0128))
theorem record003_frame062_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 62 :=
  of_group record003 62 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record003_frame062_indices record003_frame062_graph record003_frame062_links
def record003_frame063_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0591.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0591.count (({ width := 11, code := 0x42a84f0961141e8310520840a80ef15e0bbe776eddd93ad752e91d03726d6d95b03596aad35a3b40676cd998b2b64ac818c31361ac197faf85e6bbd73ae1528a414628950aa013e2784e69bd22a3f4708d518a2e45088d0fa1a430851072074087fcfd1f63e47b4f49e53c2770ec997322624c39822fa5d8b916b2ca584ae95729e524a193e2764d49792a24c4848d115222428808f91e63b0730df1ae3444805a0b21602b8560aa150298520a2098128240460881082003e0780e81102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record003_frame063_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame063_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record003) (record003.maps 63) (record003.inverseMaps 63) record003_frame063_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame063_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record003) (record003.maps 63) (record003.inverseMaps 63) record003_frame063_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame063_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record003) (record003.maps 63) (record003.inverseMaps 63) record003_frame063_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame063_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record003) (record003.maps 63)
      (record003.inverseMaps 63) record003_frame063_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame063_links_0000 (interval_append _ 64 128 153 record003_frame063_links_0064 record003_frame063_links_0128))
theorem record003_frame063_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 63 :=
  of_group record003 63 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0591
    Papers.RationalityTen.SharedFrameCatalogue.group0591_facts record003_frame063_indices record003_frame063_graph record003_frame063_links
def record003_frame064_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0347.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0347.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame064_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0347.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame064_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0347.localPairCheck (smallEmbedding record003) (record003.maps 64) (record003.inverseMaps 64) record003_frame064_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame064_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0347.localPairCheck (smallEmbedding record003) (record003.maps 64) (record003.inverseMaps 64) record003_frame064_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame064_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0347.localPairCheck (smallEmbedding record003) (record003.maps 64) (record003.inverseMaps 64) record003_frame064_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame064_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0347.localPairCheck (smallEmbedding record003) (record003.maps 64)
      (record003.inverseMaps 64) record003_frame064_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame064_links_0000 (interval_append _ 64 128 153 record003_frame064_links_0064 record003_frame064_links_0128))
theorem record003_frame064_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 64 :=
  of_group record003 64 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0347
    Papers.RationalityTen.SharedFrameCatalogue.group0347_facts record003_frame064_indices record003_frame064_graph record003_frame064_links
def record003_frame065_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0954.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0954.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame065_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0954.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame065_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0954.localPairCheck (smallEmbedding record003) (record003.maps 65) (record003.inverseMaps 65) record003_frame065_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame065_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0954.localPairCheck (smallEmbedding record003) (record003.maps 65) (record003.inverseMaps 65) record003_frame065_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame065_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0954.localPairCheck (smallEmbedding record003) (record003.maps 65) (record003.inverseMaps 65) record003_frame065_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame065_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0954.localPairCheck (smallEmbedding record003) (record003.maps 65)
      (record003.inverseMaps 65) record003_frame065_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame065_links_0000 (interval_append _ 64 128 153 record003_frame065_links_0064 record003_frame065_links_0128))
theorem record003_frame065_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 65 :=
  of_group record003 65 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0954
    Papers.RationalityTen.SharedFrameCatalogue.group0954_facts record003_frame065_indices record003_frame065_graph record003_frame065_links
def record003_frame066_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0515.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0515.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame066_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0515.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame066_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0515.localPairCheck (smallEmbedding record003) (record003.maps 66) (record003.inverseMaps 66) record003_frame066_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame066_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0515.localPairCheck (smallEmbedding record003) (record003.maps 66) (record003.inverseMaps 66) record003_frame066_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame066_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0515.localPairCheck (smallEmbedding record003) (record003.maps 66) (record003.inverseMaps 66) record003_frame066_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame066_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0515.localPairCheck (smallEmbedding record003) (record003.maps 66)
      (record003.inverseMaps 66) record003_frame066_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame066_links_0000 (interval_append _ 64 128 153 record003_frame066_links_0064 record003_frame066_links_0128))
theorem record003_frame066_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 66 :=
  of_group record003 66 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0515
    Papers.RationalityTen.SharedFrameCatalogue.group0515_facts record003_frame066_indices record003_frame066_graph record003_frame066_links
def record003_frame067_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0914.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0914.count (({ width := 8, code := 0xabaaa9a8a7a6a5a4a3a2a09f9e9d9c9b9a9998979594939291908f8e8d8c8a8988878685848382817f7d7c7b7a7977767574737271706f6e6c6b6a6968676665646361605f5e5d5c5b5a59585655545352504f4e4d4c4b4a4948474544434241403f3e3d3b3a3938373534333231302f2e2d2c27262524232221201f1e1d1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame067_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0914.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame067_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0914.localPairCheck (smallEmbedding record003) (record003.maps 67) (record003.inverseMaps 67) record003_frame067_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame067_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0914.localPairCheck (smallEmbedding record003) (record003.maps 67) (record003.inverseMaps 67) record003_frame067_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame067_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0914.localPairCheck (smallEmbedding record003) (record003.maps 67) (record003.inverseMaps 67) record003_frame067_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame067_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0914.localPairCheck (smallEmbedding record003) (record003.maps 67)
      (record003.inverseMaps 67) record003_frame067_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame067_links_0000 (interval_append _ 64 128 153 record003_frame067_links_0064 record003_frame067_links_0128))
theorem record003_frame067_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 67 :=
  of_group record003 67 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0914
    Papers.RationalityTen.SharedFrameCatalogue.group0914_facts record003_frame067_indices record003_frame067_graph record003_frame067_links
def record003_frame068_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0389.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0389.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame068_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0389.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame068_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0389.localPairCheck (smallEmbedding record003) (record003.maps 68) (record003.inverseMaps 68) record003_frame068_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame068_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0389.localPairCheck (smallEmbedding record003) (record003.maps 68) (record003.inverseMaps 68) record003_frame068_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame068_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0389.localPairCheck (smallEmbedding record003) (record003.maps 68) (record003.inverseMaps 68) record003_frame068_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame068_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0389.localPairCheck (smallEmbedding record003) (record003.maps 68)
      (record003.inverseMaps 68) record003_frame068_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame068_links_0000 (interval_append _ 64 128 153 record003_frame068_links_0064 record003_frame068_links_0128))
theorem record003_frame068_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 68 :=
  of_group record003 68 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0389
    Papers.RationalityTen.SharedFrameCatalogue.group0389_facts record003_frame068_indices record003_frame068_graph record003_frame068_links
def record003_frame069_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0691.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0691.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame069_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0691.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame069_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0691.localPairCheck (smallEmbedding record003) (record003.maps 69) (record003.inverseMaps 69) record003_frame069_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame069_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0691.localPairCheck (smallEmbedding record003) (record003.maps 69) (record003.inverseMaps 69) record003_frame069_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame069_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0691.localPairCheck (smallEmbedding record003) (record003.maps 69) (record003.inverseMaps 69) record003_frame069_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame069_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0691.localPairCheck (smallEmbedding record003) (record003.maps 69)
      (record003.inverseMaps 69) record003_frame069_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame069_links_0000 (interval_append _ 64 128 153 record003_frame069_links_0064 record003_frame069_links_0128))
theorem record003_frame069_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 69 :=
  of_group record003 69 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0691
    Papers.RationalityTen.SharedFrameCatalogue.group0691_facts record003_frame069_indices record003_frame069_graph record003_frame069_links
def record003_frame070_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0412.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0412.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame070_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0412.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame070_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0412.localPairCheck (smallEmbedding record003) (record003.maps 70) (record003.inverseMaps 70) record003_frame070_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame070_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0412.localPairCheck (smallEmbedding record003) (record003.maps 70) (record003.inverseMaps 70) record003_frame070_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame070_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0412.localPairCheck (smallEmbedding record003) (record003.maps 70) (record003.inverseMaps 70) record003_frame070_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame070_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0412.localPairCheck (smallEmbedding record003) (record003.maps 70)
      (record003.inverseMaps 70) record003_frame070_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame070_links_0000 (interval_append _ 64 128 153 record003_frame070_links_0064 record003_frame070_links_0128))
theorem record003_frame070_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 70 :=
  of_group record003 70 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0412
    Papers.RationalityTen.SharedFrameCatalogue.group0412_facts record003_frame070_indices record003_frame070_graph record003_frame070_links
def record003_frame071_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0276.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0276.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame071_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0276.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame071_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0276.localPairCheck (smallEmbedding record003) (record003.maps 71) (record003.inverseMaps 71) record003_frame071_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame071_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0276.localPairCheck (smallEmbedding record003) (record003.maps 71) (record003.inverseMaps 71) record003_frame071_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame071_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0276.localPairCheck (smallEmbedding record003) (record003.maps 71) (record003.inverseMaps 71) record003_frame071_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame071_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0276.localPairCheck (smallEmbedding record003) (record003.maps 71)
      (record003.inverseMaps 71) record003_frame071_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame071_links_0000 (interval_append _ 64 128 153 record003_frame071_links_0064 record003_frame071_links_0128))
theorem record003_frame071_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 71 :=
  of_group record003 71 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0276
    Papers.RationalityTen.SharedFrameCatalogue.group0276_facts record003_frame071_indices record003_frame071_graph record003_frame071_links
def record003_frame072_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x577ae75b6b4564ac1566a954da8f342664c69832f65ccb295729a504638b9152274488850ee1a42c84b07a0bc0f81300dfebf67def9df03db7aef4de7bcb6bcd65aa34f694d159fb39664cad6c2d0592b0d5f2bb566aa55129b520a254127a4ea9c133a5c4a6925202394688bd149d639e720e01bb36c6b4d119931e614be9762e05acb41602ac53ca41402724d0979292464708a90f2124087e0f51dc39c530550a814c290510a013c2704d098098128240460881082003e0780e81102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record003_frame072_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame072_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record003) (record003.maps 72) (record003.inverseMaps 72) record003_frame072_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame072_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record003) (record003.maps 72) (record003.inverseMaps 72) record003_frame072_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame072_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record003) (record003.maps 72) (record003.inverseMaps 72) record003_frame072_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame072_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record003) (record003.maps 72)
      (record003.inverseMaps 72) record003_frame072_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame072_links_0000 (interval_append _ 64 128 153 record003_frame072_links_0064 record003_frame072_links_0128))
theorem record003_frame072_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 72 :=
  of_group record003 72 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record003_frame072_indices record003_frame072_graph record003_frame072_links
def record003_frame073_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0303.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0303.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame073_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0303.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame073_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0303.localPairCheck (smallEmbedding record003) (record003.maps 73) (record003.inverseMaps 73) record003_frame073_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame073_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0303.localPairCheck (smallEmbedding record003) (record003.maps 73) (record003.inverseMaps 73) record003_frame073_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame073_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0303.localPairCheck (smallEmbedding record003) (record003.maps 73) (record003.inverseMaps 73) record003_frame073_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame073_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0303.localPairCheck (smallEmbedding record003) (record003.maps 73)
      (record003.inverseMaps 73) record003_frame073_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame073_links_0000 (interval_append _ 64 128 153 record003_frame073_links_0064 record003_frame073_links_0128))
theorem record003_frame073_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 73 :=
  of_group record003 73 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0303
    Papers.RationalityTen.SharedFrameCatalogue.group0303_facts record003_frame073_indices record003_frame073_graph record003_frame073_links
def record003_frame074_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0x4d89a933a63cc297f2ea59cad94b1222243f8770d617c2a84706e0abe37b8f51e73cb78cf05dcbb3756e91cf39b72ae35c3b826f4dd1b6b666c4d71ab3525dcba5712dc5aab4565ac557eae93e27a4ec9bd35a684c09612aa4e48c9051da3345a8a10f21541e81cff1f83e67b8f41a9346674cb991316604bc1712d0580ad9572a8540a61442784d89992c24c47c8d916220424820fd1f03c8768e91c63745305a0b21602b8560aa150298520a2094120230440841001f03c0740e01102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record003_frame074_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame074_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record003) (record003.maps 74) (record003.inverseMaps 74) record003_frame074_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame074_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record003) (record003.maps 74) (record003.inverseMaps 74) record003_frame074_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame074_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record003) (record003.maps 74) (record003.inverseMaps 74) record003_frame074_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame074_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record003) (record003.maps 74)
      (record003.inverseMaps 74) record003_frame074_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame074_links_0000 (interval_append _ 64 128 153 record003_frame074_links_0064 record003_frame074_links_0128))
theorem record003_frame074_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 74 :=
  of_group record003 74 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record003_frame074_indices record003_frame074_graph record003_frame074_links
def record003_frame075_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1039.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1039.count (({ width := 11, code := 0x4ae95328e4ec9692522a42c7f8f50660a40e80f009fe3f67defadf2bb475ee9dd0398722e1dc0b7b6e8db9b4b616b2d4da6b4667ccdd9732964ac858d313578ae55b2b1558a9950a9c52ca4d2ea594a6941262484808ed1a2324588990fa18422829021fd3ec7c0f49e33ba760e999d32e640c49822f65d0b69662c256cab9512945149f13c2704d09812a2484788b91321e428830ff1f23c8758e51bc3604f0570ac1542a0530a41442804f09c098128240460881082003e0780e81102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record003_frame075_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame075_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record003) (record003.maps 75) (record003.inverseMaps 75) record003_frame075_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame075_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record003) (record003.maps 75) (record003.inverseMaps 75) record003_frame075_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame075_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record003) (record003.maps 75) (record003.inverseMaps 75) record003_frame075_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame075_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record003) (record003.maps 75)
      (record003.inverseMaps 75) record003_frame075_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame075_links_0000 (interval_append _ 64 128 153 record003_frame075_links_0064 record003_frame075_links_0128))
theorem record003_frame075_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 75 :=
  of_group record003 75 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1039
    Papers.RationalityTen.SharedFrameCatalogue.group1039_facts record003_frame075_indices record003_frame075_graph record003_frame075_links
def record003_frame076_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0589.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0589.count (({ width := 11, code := 0x3fc7f0fd5fa3ef7d6f99f03da7aae65cb39371ce2dc23806fcde1b9348684ce599b29646c658930b60abf57baf15d0b816cad359ab0d5d2b1554a994fa974c89852f25a4aa941262484848fd0d21441c835052074047f4fb1f53e27a8f21e13b6754e81ca3826f0db9b135869cd117d2ec5c0b61652ba55ca994c2905109f93b26a4c49512924c48c8f91922a440849052023f07b0f21d8398700dc1aa33c4b8570ac1542a0530a41442804f09c094120230440841001f03c0740e01102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record003_frame076_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0589.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame076_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record003) (record003.maps 76) (record003.inverseMaps 76) record003_frame076_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame076_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record003) (record003.maps 76) (record003.inverseMaps 76) record003_frame076_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame076_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record003) (record003.maps 76) (record003.inverseMaps 76) record003_frame076_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame076_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record003) (record003.maps 76)
      (record003.inverseMaps 76) record003_frame076_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame076_links_0000 (interval_append _ 64 128 153 record003_frame076_links_0064 record003_frame076_links_0128))
theorem record003_frame076_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 76 :=
  of_group record003 76 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0589
    Papers.RationalityTen.SharedFrameCatalogue.group0589_facts record003_frame076_indices record003_frame076_graph record003_frame076_links
def record003_frame077_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0929.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0929.count (({ width := 9, code := 0x11a8c45e2b14894421f0d85c1205017fbf9f8fa7cbddeaf177bb9d8eb74b9dcce471385bede6e36db2d76b351a4d067b3596c95e2ed72b75aacd62af56aad46a250a793a9a4ca612a9449a45208e46a2d1288432110681401f8f874391c4de6e361a8d26732990c6622f978b65a2c958aa54291449e4d259289248239188a44219087034198c86230178b85a2c15874381b0d06430170b0542810078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record003_frame077_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0929.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame077_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0929.localPairCheck (smallEmbedding record003) (record003.maps 77) (record003.inverseMaps 77) record003_frame077_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame077_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0929.localPairCheck (smallEmbedding record003) (record003.maps 77) (record003.inverseMaps 77) record003_frame077_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame077_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0929.localPairCheck (smallEmbedding record003) (record003.maps 77) (record003.inverseMaps 77) record003_frame077_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame077_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0929.localPairCheck (smallEmbedding record003) (record003.maps 77)
      (record003.inverseMaps 77) record003_frame077_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame077_links_0000 (interval_append _ 64 128 153 record003_frame077_links_0064 record003_frame077_links_0128))
theorem record003_frame077_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 77 :=
  of_group record003 77 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0929
    Papers.RationalityTen.SharedFrameCatalogue.group0929_facts record003_frame077_indices record003_frame077_graph record003_frame077_links
def record003_frame078_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0411.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0411.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame078_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0411.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame078_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0411.localPairCheck (smallEmbedding record003) (record003.maps 78) (record003.inverseMaps 78) record003_frame078_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame078_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0411.localPairCheck (smallEmbedding record003) (record003.maps 78) (record003.inverseMaps 78) record003_frame078_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame078_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0411.localPairCheck (smallEmbedding record003) (record003.maps 78) (record003.inverseMaps 78) record003_frame078_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame078_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0411.localPairCheck (smallEmbedding record003) (record003.maps 78)
      (record003.inverseMaps 78) record003_frame078_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame078_links_0000 (interval_append _ 64 128 153 record003_frame078_links_0064 record003_frame078_links_0128))
theorem record003_frame078_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 78 :=
  of_group record003 78 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0411
    Papers.RationalityTen.SharedFrameCatalogue.group0411_facts record003_frame078_indices record003_frame078_graph record003_frame078_links
def record003_frame079_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0275.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0275.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame079_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0275.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame079_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0275.localPairCheck (smallEmbedding record003) (record003.maps 79) (record003.inverseMaps 79) record003_frame079_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame079_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0275.localPairCheck (smallEmbedding record003) (record003.maps 79) (record003.inverseMaps 79) record003_frame079_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame079_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0275.localPairCheck (smallEmbedding record003) (record003.maps 79) (record003.inverseMaps 79) record003_frame079_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame079_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0275.localPairCheck (smallEmbedding record003) (record003.maps 79)
      (record003.inverseMaps 79) record003_frame079_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame079_links_0000 (interval_append _ 64 128 153 record003_frame079_links_0064 record003_frame079_links_0128))
theorem record003_frame079_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 79 :=
  of_group record003 79 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0275
    Papers.RationalityTen.SharedFrameCatalogue.group0275_facts record003_frame079_indices record003_frame079_graph record003_frame079_links
def record003_frame080_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0081.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame080_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0081.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame080_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0081.localPairCheck (smallEmbedding record003) (record003.maps 80) (record003.inverseMaps 80) record003_frame080_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame080_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0081.localPairCheck (smallEmbedding record003) (record003.maps 80) (record003.inverseMaps 80) record003_frame080_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame080_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0081.localPairCheck (smallEmbedding record003) (record003.maps 80) (record003.inverseMaps 80) record003_frame080_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame080_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0081.localPairCheck (smallEmbedding record003) (record003.maps 80)
      (record003.inverseMaps 80) record003_frame080_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame080_links_0000 (interval_append _ 64 128 153 record003_frame080_links_0064 record003_frame080_links_0128))
theorem record003_frame080_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 80 :=
  of_group record003 80 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0081
    Papers.RationalityTen.SharedFrameCatalogue.group0081_facts record003_frame080_indices record003_frame080_graph record003_frame080_links
def record003_frame081_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0701.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0701.count (({ width := 9, code := 0x10783416090380bfdfcfc7d3d1e6f278bc1dcec75ba5cee16fb75b8da6c35daad369345a0cf66b2d92c762b0d82c05eaed72b758ac15eae56aad52a8532913e9e4ea7136994ba59289248a411e8e46a2d12884321106813f9f4f6763a9d0e672381b8da6b349a0ce6632990c4602f974b65a2c158a85228138984a2491c8843208f8662f170b4582b150a45027130803e1e0e870361a0c8602e110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record003_frame081_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0701.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame081_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0701.localPairCheck (smallEmbedding record003) (record003.maps 81) (record003.inverseMaps 81) record003_frame081_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame081_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0701.localPairCheck (smallEmbedding record003) (record003.maps 81) (record003.inverseMaps 81) record003_frame081_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame081_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0701.localPairCheck (smallEmbedding record003) (record003.maps 81) (record003.inverseMaps 81) record003_frame081_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame081_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0701.localPairCheck (smallEmbedding record003) (record003.maps 81)
      (record003.inverseMaps 81) record003_frame081_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame081_links_0000 (interval_append _ 64 128 153 record003_frame081_links_0064 record003_frame081_links_0128))
theorem record003_frame081_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 81 :=
  of_group record003 81 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0701
    Papers.RationalityTen.SharedFrameCatalogue.group0701_facts record003_frame081_indices record003_frame081_graph record003_frame081_links
def record003_frame082_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0176.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0176.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame082_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0176.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame082_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0176.localPairCheck (smallEmbedding record003) (record003.maps 82) (record003.inverseMaps 82) record003_frame082_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame082_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0176.localPairCheck (smallEmbedding record003) (record003.maps 82) (record003.inverseMaps 82) record003_frame082_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame082_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0176.localPairCheck (smallEmbedding record003) (record003.maps 82) (record003.inverseMaps 82) record003_frame082_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame082_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0176.localPairCheck (smallEmbedding record003) (record003.maps 82)
      (record003.inverseMaps 82) record003_frame082_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame082_links_0000 (interval_append _ 64 128 153 record003_frame082_links_0064 record003_frame082_links_0128))
theorem record003_frame082_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 82 :=
  of_group record003 82 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0176
    Papers.RationalityTen.SharedFrameCatalogue.group0176_facts record003_frame082_indices record003_frame082_graph record003_frame082_links
def record003_frame083_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0391.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0391.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame083_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0391.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame083_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0391.localPairCheck (smallEmbedding record003) (record003.maps 83) (record003.inverseMaps 83) record003_frame083_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame083_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0391.localPairCheck (smallEmbedding record003) (record003.maps 83) (record003.inverseMaps 83) record003_frame083_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame083_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0391.localPairCheck (smallEmbedding record003) (record003.maps 83) (record003.inverseMaps 83) record003_frame083_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame083_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0391.localPairCheck (smallEmbedding record003) (record003.maps 83)
      (record003.inverseMaps 83) record003_frame083_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame083_links_0000 (interval_append _ 64 128 153 record003_frame083_links_0064 record003_frame083_links_0128))
theorem record003_frame083_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 83 :=
  of_group record003 83 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0391
    Papers.RationalityTen.SharedFrameCatalogue.group0391_facts record003_frame083_indices record003_frame083_graph record003_frame083_links
def record003_frame084_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0991.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0991.count (({ width := 8, code := 0xdcdbdad9d8d7d5d3d2d1cecdcccbcac9c7c5c4c3c0bfbebcbbbab8b7b5b4b3b2b1b0afadabaaa8a7a6a5a3a1a09d9c9b9a9998969493928f8e8d8b8a89878684838281807f7e7c7a797776757472706f6c6b6a686766646361605f5e5d5c5b595756545352514f4d4c4b4a49484746454443423d3231302f2e2d2c2b2a29201f1e1d1c1b1a19181711100f0e0d0c0b0a090806050403020100 } : Fields).get c.val)
theorem record003_frame084_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0991.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame084_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0991.localPairCheck (smallEmbedding record003) (record003.maps 84) (record003.inverseMaps 84) record003_frame084_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame084_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0991.localPairCheck (smallEmbedding record003) (record003.maps 84) (record003.inverseMaps 84) record003_frame084_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame084_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0991.localPairCheck (smallEmbedding record003) (record003.maps 84) (record003.inverseMaps 84) record003_frame084_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame084_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0991.localPairCheck (smallEmbedding record003) (record003.maps 84)
      (record003.inverseMaps 84) record003_frame084_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame084_links_0000 (interval_append _ 64 128 153 record003_frame084_links_0064 record003_frame084_links_0128))
theorem record003_frame084_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 84 :=
  of_group record003 84 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0991
    Papers.RationalityTen.SharedFrameCatalogue.group0991_facts record003_frame084_indices record003_frame084_graph record003_frame084_links
def record003_frame085_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1097.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1097.count (({ width := 9, code := 0x1168ac52271288c3e1d0d85c12070280c01fefd7e3edf2ee76badd2e772b91c4e06fb79badb6cb5daad4693419ece66b3196ca62b1186c260b017cbd5e2e95eae562a950a652a8d42a04fa79389a4c2592a9348a411e8e46a311682409fcfa7b3c9e0ec74399c8e26f369acd26833190c66230980be5e2e970b65a2c960ae562a9509e3c1d8e872381b8d86a34198904622108803e1e0e87036110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record003_frame085_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1097.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame085_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record003) (record003.maps 85) (record003.inverseMaps 85) record003_frame085_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame085_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record003) (record003.maps 85) (record003.inverseMaps 85) record003_frame085_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame085_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record003) (record003.maps 85) (record003.inverseMaps 85) record003_frame085_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame085_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record003) (record003.maps 85)
      (record003.inverseMaps 85) record003_frame085_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame085_links_0000 (interval_append _ 64 128 153 record003_frame085_links_0064 record003_frame085_links_0128))
theorem record003_frame085_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 85 :=
  of_group record003 85 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1097
    Papers.RationalityTen.SharedFrameCatalogue.group1097_facts record003_frame085_indices record003_frame085_graph record003_frame085_links
def record003_frame086_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1038.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1038.count (({ width := 9, code := 0x144a15027d3c9d4e26d349949e4b2390c7e3b1b8cc5e2b0b854220d0481405fefd7e3e9f2f77abcde2f0773b1d6e97439dcae36d361acd4693419ccc653217cbd5dae56eb55a2c960af56ab154a85329146a14fa79389b4d2612c8e46a2d128742a1104803f9f4f87a3c1d8e873389bcdc6c359a8d06632990c66230980be5e2e970aa3e1e8f0763a1c8e06e361a8904622108803e1e0e87036110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record003_frame086_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1038.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame086_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1038.localPairCheck (smallEmbedding record003) (record003.maps 86) (record003.inverseMaps 86) record003_frame086_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame086_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1038.localPairCheck (smallEmbedding record003) (record003.maps 86) (record003.inverseMaps 86) record003_frame086_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame086_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1038.localPairCheck (smallEmbedding record003) (record003.maps 86) (record003.inverseMaps 86) record003_frame086_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame086_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1038.localPairCheck (smallEmbedding record003) (record003.maps 86)
      (record003.inverseMaps 86) record003_frame086_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame086_links_0000 (interval_append _ 64 128 153 record003_frame086_links_0064 record003_frame086_links_0128))
theorem record003_frame086_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 86 :=
  of_group record003 86 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1038
    Papers.RationalityTen.SharedFrameCatalogue.group1038_facts record003_frame086_indices record003_frame086_graph record003_frame086_links
def record003_frame087_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1095.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1095.count (({ width := 8, code := 0xebeae9e8e7e6e4e3e2e0dbdad9d8d7d6d4d3d2d0c9c8c6c5c4c2c1c0bebdbcbbb9b8b7b5b4b3b1b0afaeadacaba8a7a6a5a4a3a1a09f9d96959392918f8e8d8b8a89888685848281807e7d7c7b7a79787372706f6e6c6b6a686766656362615f5e5d5b5a595857565554535251504f4e4d4c4b46363534333231302f2e2d21201f1e1d1c1b1a191811100f0e0d0c0b0a090806050403020100 } : Fields).get c.val)
theorem record003_frame087_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1095.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame087_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1095.localPairCheck (smallEmbedding record003) (record003.maps 87) (record003.inverseMaps 87) record003_frame087_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame087_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1095.localPairCheck (smallEmbedding record003) (record003.maps 87) (record003.inverseMaps 87) record003_frame087_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame087_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1095.localPairCheck (smallEmbedding record003) (record003.maps 87) (record003.inverseMaps 87) record003_frame087_indices (Fin.ofNat record003.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record003_frame087_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1095.localPairCheck (smallEmbedding record003) (record003.maps 87)
      (record003.inverseMaps 87) record003_frame087_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record003_frame087_links_0000 (interval_append _ 64 128 153 record003_frame087_links_0064 record003_frame087_links_0128))
theorem record003_frame087_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 87 :=
  of_group record003 87 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1095
    Papers.RationalityTen.SharedFrameCatalogue.group1095_facts record003_frame087_indices record003_frame087_graph record003_frame087_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (Fin.cases (record003_frame004_supported hcells) (Fin.cases (record003_frame005_supported hcells) (Fin.cases (record003_frame006_supported hcells) (Fin.cases (record003_frame007_supported hcells) (Fin.cases (record003_frame008_supported hcells) (Fin.cases (record003_frame009_supported hcells) (Fin.cases (record003_frame010_supported hcells) (Fin.cases (record003_frame011_supported hcells) (Fin.cases (record003_frame012_supported hcells) (Fin.cases (record003_frame013_supported hcells) (Fin.cases (record003_frame014_supported hcells) (Fin.cases (record003_frame015_supported hcells) (Fin.cases (record003_frame016_supported hcells) (Fin.cases (record003_frame017_supported hcells) (Fin.cases (record003_frame018_supported hcells) (Fin.cases (record003_frame019_supported hcells) (Fin.cases (record003_frame020_supported hcells) (Fin.cases (record003_frame021_supported hcells) (Fin.cases (record003_frame022_supported hcells) (Fin.cases (record003_frame023_supported hcells) (Fin.cases (record003_frame024_supported hcells) (Fin.cases (record003_frame025_supported hcells) (Fin.cases (record003_frame026_supported hcells) (Fin.cases (record003_frame027_supported hcells) (Fin.cases (record003_frame028_supported hcells) (Fin.cases (record003_frame029_supported hcells) (Fin.cases (record003_frame030_supported hcells) (Fin.cases (record003_frame031_supported hcells) (Fin.cases (record003_frame032_supported hcells) (Fin.cases (record003_frame033_supported hcells) (Fin.cases (record003_frame034_supported hcells) (Fin.cases (record003_frame035_supported hcells) (Fin.cases (record003_frame036_supported hcells) (Fin.cases (record003_frame037_supported hcells) (Fin.cases (record003_frame038_supported hcells) (Fin.cases (record003_frame039_supported hcells) (Fin.cases (record003_frame040_supported hcells) (Fin.cases (record003_frame041_supported hcells) (Fin.cases (record003_frame042_supported hcells) (Fin.cases (record003_frame043_supported hcells) (Fin.cases (record003_frame044_supported hcells) (Fin.cases (record003_frame045_supported hcells) (Fin.cases (record003_frame046_supported hcells) (Fin.cases (record003_frame047_supported hcells) (Fin.cases (record003_frame048_supported hcells) (Fin.cases (record003_frame049_supported hcells) (Fin.cases (record003_frame050_supported hcells) (Fin.cases (record003_frame051_supported hcells) (Fin.cases (record003_frame052_supported hcells) (Fin.cases (record003_frame053_supported hcells) (Fin.cases (record003_frame054_supported hcells) (Fin.cases (record003_frame055_supported hcells) (Fin.cases (record003_frame056_supported hcells) (Fin.cases (record003_frame057_supported hcells) (Fin.cases (record003_frame058_supported hcells) (Fin.cases (record003_frame059_supported hcells) (Fin.cases (record003_frame060_supported hcells) (Fin.cases (record003_frame061_supported hcells) (Fin.cases (record003_frame062_supported hcells) (Fin.cases (record003_frame063_supported hcells) (Fin.cases (record003_frame064_supported hcells) (Fin.cases (record003_frame065_supported hcells) (Fin.cases (record003_frame066_supported hcells) (Fin.cases (record003_frame067_supported hcells) (Fin.cases (record003_frame068_supported hcells) (Fin.cases (record003_frame069_supported hcells) (Fin.cases (record003_frame070_supported hcells) (Fin.cases (record003_frame071_supported hcells) (Fin.cases (record003_frame072_supported hcells) (Fin.cases (record003_frame073_supported hcells) (Fin.cases (record003_frame074_supported hcells) (Fin.cases (record003_frame075_supported hcells) (Fin.cases (record003_frame076_supported hcells) (Fin.cases (record003_frame077_supported hcells) (Fin.cases (record003_frame078_supported hcells) (Fin.cases (record003_frame079_supported hcells) (Fin.cases (record003_frame080_supported hcells) (Fin.cases (record003_frame081_supported hcells) (Fin.cases (record003_frame082_supported hcells) (Fin.cases (record003_frame083_supported hcells) (Fin.cases (record003_frame084_supported hcells) (Fin.cases (record003_frame085_supported hcells) (Fin.cases (record003_frame086_supported hcells) (Fin.cases (record003_frame087_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms record003_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00293
