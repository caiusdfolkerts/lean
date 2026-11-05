module
prelude
public import GraphInputsSix0Part00067Data
public import RawFrameSupport
public import SharedFrameGroups009Checked
public import SharedFrameGroups017Checked
public import SharedFrameGroups034Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups107Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups114Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x940c8f639f15f8ab44aa22b0ec871c2de14507979f3b5dcc8e4071637d9bc4dab5ffaf7d766b7f5a82b114c0a3f4da25152468ca449a2190c481f3f59f48f8e7933be1da8d8e659315982cbbc5b52a71488a0a4ea26d12fc966491238918c89243b21310547f03e61ed0d9c66e30517b8b605942bf14f89b048c23111088003861b50c805b42c8159097848822c10607d83ac18e06a03481900c205602a812006a03201880bc058029010807803a01700a003c01c00d004802000e005002000c004000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (embedding record000) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x66d720789dc32606702176abae5d12e6971db855aeed5d599abf55a283b40b9ffccca63330994ec9fa4e515089cc4b9b9ad8f578aab549a969497a30115a878420a030fd27d63db1e9cb7a57928c90d47f638c1bc8d1061a2d815a8a8850427310d87943ba1d70e006d035819f0cb86282e816e0ac054827a128090846422610507b03c01d208c04001b40d206403081700b405602a815009003501880b0052024011007803a01c00d005c0280110078034018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (embedding record001) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x5a1b31646c4581b015daba572ac957eaad52aa352ea5540a794de96d2ba534728dcee9c136664cc591b1f63bc728c5066083fb7e0ee1d3b8b708e01bbb6e6cacb58e30f610c0178ada5a4ab95029051c9c5342624a88f91ca324568950f21b3fa7a4f21e23a8748e69bf37867ccb1842f45c0b315d2a051ca093824e458880e71b8334600b115027c4b0880a4144238420820cc1902804e0901181d0380680b8130240300580800800c01000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (embedding record006) hcells Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0562.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0562.count (({ width := 11, code := 0x4a694527e4dc929232063ec798e91ce32c618bb16e2cc4a89310a20c3e8790a200bf47d4f95ce3956eedcdb0b5869ed19a2b41620c0d6cad6596b015ea814ea97528a434748c517a254387c4f11c336a6b8d39973045e0b71662bc538a493e2664648990e20e3f87b8f51e03a4700d91a6328620bf1722d8578a213824c460850d81ac318570aa144260430820f41882e0540940e01b0220400400700c01401000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0562.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (embedding (N := 44310) record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group0562
    Papers.RationalityTen.SharedFrameCatalogue.group0562_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x5b0ed5f57dab4d22e8e133298dcbe25c32b69504a1e4df2028f4c4e224b08683ac0ca03efc37d6b53d9aeca56292ba94e4a404f6a6a532898c4c2a5e92ee96b4a7a4e925492448aa4211f88f5479a3b11c88dd3759ab8cb05982c31570a9e52926f92c48ec43120690047e03e11e88ca462e2ed1700ae84e0242103870833c1920c085c82c41510a484e426812608e845822410908183f81ee0f107503901b80d6068028c12209004001b80da03601600a004e025012007803a01c00b804c0240100078024010007 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (embedding record020) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x5b4ed7f649b18d2fa96732e98bcbd25bb1948bf44e224b08683ac1ae0b2fc57d7b3fd9b0ca56272a694e6a404f4a6a532898c4c2a5e92ee96b4a7a4e524891c481a3f11f48f3473a3911ba6ea357196cbac5982ba156ca524e625811d88584112008fac7c23d11b38ca460a2ec15d09dc4822070de868832417c0b905882ae1520a104e425a126090045821e10908303f81ee0f007503941b80d6068028c12409104702000de06e03580d8058027013009403c01d00e005c0240110080024010007 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (embedding record021) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x55f6ad34d8a63d14a86f33298dcbf65cd2b695048fe4551f98f046162dedf66e0b4099b2ca5628b0f5722b5c54ea9d14809ec4ec26a532898c4c2a6012d695b4aa253928e934495249123890948123d51e68eb4722378fc87103749ab8cae6422cc1618acc52927a13809a04a623b119c86042120690047e23e11e80ca462e2f715d0a144e226111b881c3f01c10d906783241820b905842a214909c84d024c11d08b044821210507f03d41e20ea07103701b00d004c82400ec06d01600a004e025011007c03c01c00b804c0240100068028012007 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record023_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record023_frame001_links_0000 (interval_append _ 64 128 131 record023_frame001_links_0064 record023_frame001_links_0128))
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (embedding record023) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0550.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0550.count (({ width := 11, code := 0x4e79cd38e6f4c798b2e654ca79392564848d91720a3fc7a8e71be3545189f1161fc3987107e053f67caf6dec3b6712d65ac32962ac4d843055f4b95722ce598b154da724909050b21341e7f4f89ed3a8728de1b436262cbb9632aa5349d93625c470869041fa3b4738e21be360648b916429c5109d13425c4688a10c2103d0770d01942f8570a0138250490700dc1a02c04c08c1001e0220340580800c01400800 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (embedding (N := 44310) record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (embedding (N := 44310) record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (embedding (N := 44310) record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (embedding record027) hcells Papers.RationalityTen.SharedFrameCatalogue.group0550
    Papers.RationalityTen.SharedFrameCatalogue.group0550_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x2c7d626abad586a314fba5f52ce74338d97a4b763971b28c9c5f5ff8fe97e53ed1b60d1466c329189cc3e5a5aabd4e6a3f4f4a7653529944c625e92e096a4b1253d290939498a49521c903480a3e91e48e7472a374e466ea356996cc865d62cc156ca7a52a273133c96047522190b08444112010fac7c03d11b38ca45d82ce15d89dc4c0241103075037a1b30d1064c2f81710b1055c2a414209c84b424c12008b043c21610607e03dc1e00e807283781ac0d0051824811c08003781ac058027013008c04001d00e005c024011007002c010007 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record030_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record030_frame001_links_0000 (interval_append _ 64 128 130 record030_frame001_links_0064 record030_frame001_links_0128))
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (embedding record030) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x2af55669b5cd5e66931d8ca45fa1fb0e884341d5ff8fe97e53ed1b60d4d66d313987cb4b57429d53d29d94d4a65131897f4bba5952c494f4a424d122a903480a3e51e68e7472a374ec86e832d990cbac5982b2939899e4a522a90b08444122008fac7c03d11b38ca45ec27713008d83cc1bd0d9868c32417c0b885882ae1520a104e425a126090045822210908303f01ee0ee07503941bc0d6068028013209204701f40ec06f0358114058027012808c04201d00e005c0240100070030010007 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (embedding record031) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
def record032_frame001_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0xae9ae8ae5ad2acdac9a6ea64a5ea0da069f09de9d09cc9a798898396e95f94e9499149129049008ef8eb8758257ea7c47b57b17136f469569361f6005d75d55cc5c05b159759357b5775704b348d42e4223ab38536535935534c34232431b3093002fc2bf29126723921320d2041f41ce1bc1b31a71a018917f17616e15e13811610c1030fa0ee0e70e00ce0ca0c60c209909607907606f06705c05905805704003b03602c02302102001e00d00c00b008006005001000 } : Fields).get c.val)
theorem record032_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record032_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record032) (record032.maps 1)
      (record032.inverseMaps 1) record032_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record032_frame001_links_0000 record032_frame001_links_0064)
theorem record032_frame001_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) : Supported record032 1 :=
  of_group record032 1 (embedding record032) hcells Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record032_frame001_indices record032_frame001_graph record032_frame001_links
def record032_frame002_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0562.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0562.count (({ width := 11, code := 0x2524a39452764e49b92f24e484849051fe3d4758e51c2344668c917a2e45889712221c4287b0f215419804f91ebbd1762ea5bab74692cf590b1e62ac297e2e35c0b055e2b2526a2d2f24f45687d031fb3ee7a8f31ca378698cc1943045e0b5162294514a193925c4a0911192264087d8f31e03a4700ce1903045d8b215629c4988c112218388700be1702b851090114220430700d41882a04207c0f01c01a0300580800c01400800 } : Fields).get c.val)
theorem record032_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0562.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (embedding (N := 44310) record032) (record032.maps 2) (record032.inverseMaps 2) record032_frame002_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (embedding (N := 44310) record032) (record032.maps 2) (record032.inverseMaps 2) record032_frame002_indices (Fin.ofNat record032.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record032_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (embedding (N := 44310) record032) (record032.maps 2)
      (record032.inverseMaps 2) record032_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record032_frame002_links_0000 record032_frame002_links_0064)
theorem record032_frame002_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) : Supported record032 2 :=
  of_group record032 2 (embedding record032) hcells Papers.RationalityTen.SharedFrameCatalogue.group0562
    Papers.RationalityTen.SharedFrameCatalogue.group0562_facts record032_frame002_indices record032_frame002_graph record032_frame002_links
def record032_frame003_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0xb09b06b01ae4adfad7a88a74a65a0ba039f09e69d59cf9ab98798197795e94e9418f48f08d28c88b08ab8408057c37957807766f26e268b6896246045cf5c95bb5a558c56b56653f53752849a47941b4073b13a438737737135f34d31f3092f42e52de2a828526824821e21520f2031e31d41c91c21b819a18e18017916c14e12911b10e1070f90f30ea0d00c70c10b909109007507206c06405905605505403f03a03502c02302102001e00d00c00b008006005001000 } : Fields).get c.val)
theorem record032_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record032) (record032.maps 3) (record032.inverseMaps 3) record032_frame003_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record032) (record032.maps 3) (record032.inverseMaps 3) record032_frame003_indices (Fin.ofNat record032.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record032_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record032) (record032.maps 3)
      (record032.inverseMaps 3) record032_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record032_frame003_links_0000 record032_frame003_links_0064)
theorem record032_frame003_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) : Supported record032 3 :=
  of_group record032 3 (embedding record032) hcells Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record032_frame003_indices record032_frame003_graph record032_frame003_links
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (Fin.cases (record032_frame001_supported hcells) (Fin.cases (record032_frame002_supported hcells) (Fin.cases (record032_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0x4b595f2b252ca393920e2a45089111215c1982303202bd67a0f31e5aeb5c2b6166aba568ac554a99512a0d38a6b48088d041dd3a0718db99c336650c29752e6588b094a27c4d09290e2104007c0e41b8344650c31802c8560a914c28c4f89b12e24c43083104200390700c81882704d0981042003e0760bc140240440841001f02e0480700d01802c0480600a00800800 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (embedding record033) hcells Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
def record034_frame001_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19dece9e6ef25791ac7e5f7af2b5c1ada55dead54dda4a4f0276737a9b72e755bca624d1a5b12668fb455225d11087241f1ff4fd67b93d499a4b5452e23790e07fe3c71bb0d8c6a833e1850b2456e28513a88c443821610387c83d81c90dd86d034c18f0c405cc2d81600ab850826c12f093848023411308584101d00e106d83540f207803b01cc0b405902c010408003e01d808804202000d005c026012007803801a00c00580280120060028008002000 } : Fields).get c.val)
theorem record034_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record034_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record034) (record034.maps 1)
      (record034.inverseMaps 1) record034_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record034_frame001_links_0000 record034_frame001_links_0064)
theorem record034_frame001_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 1 :=
  of_group record034 1 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record034_frame001_indices record034_frame001_graph record034_frame001_links
def record034_frame002_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x59bb3565ac5d8ab0d606bf565ac5572acd4ba914f69d534a632723d45b85907a053f579af09df3b4746e35c336d6c8cb1862f0586acd522944e099d3225e4a09011da284427f4f49e43ac704dd99f324638c01652b84f89a92d24c454851021f23c0730db1a030c4f09512022c338660c818c2604b0940f41e03a0720881082003405c0981201e0380680c0160280480600a00800800 } : Fields).get c.val)
theorem record034_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record034) (record034.maps 2) (record034.inverseMaps 2) record034_frame002_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record034) (record034.maps 2) (record034.inverseMaps 2) record034_frame002_indices (Fin.ofNat record034.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record034_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record034) (record034.maps 2)
      (record034.inverseMaps 2) record034_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record034_frame002_links_0000 record034_frame002_links_0064)
theorem record034_frame002_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 2 :=
  of_group record034 2 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record034_frame002_indices record034_frame002_graph record034_frame002_links
def record034_frame003_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1413a064fba7293889b14a0e4b113e89043e61b708e831c005fc0fb37c92d8956ea574e026352b692847e23d51ca8ca44321090648023f91c58ce26102c79590a7450f27693a09be4c724791788a442f2118eb46fa36f1a68c7461e2e215c8a8c4f224b11e08444041ed0ec86883061770b5857c2a414609d04b81f00e806e834c0f207803b01cc0b405902c010408003e01d808804202000d005c026012007803801a00c00580280120060028008002000 } : Fields).get c.val)
theorem record034_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record034) (record034.maps 3) (record034.inverseMaps 3) record034_frame003_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record034) (record034.maps 3) (record034.inverseMaps 3) record034_frame003_indices (Fin.ofNat record034.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record034_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record034) (record034.maps 3)
      (record034.inverseMaps 3) record034_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record034_frame003_links_0000 record034_frame003_links_0064)
theorem record034_frame003_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 3 :=
  of_group record034 3 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record034_frame003_indices record034_frame003_graph record034_frame003_links
def record034_frame004_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x96095e95693f93b9338f68eb89c89488087885e85383582e81c8156666135d758356d54e53651450d5054f54d94bb4b349548b4163be3873303182f92e32c42bd2b52a528926525b24223a2051ed1e71d41bc1b619f19118a17d16215913f13612e12711710c1060fe0f80f20ec0e40de0c80c20bc0b507907807607305a05905804104003e03b02202102001a01701301200f00e00d00c00b00a009006005002001000 } : Fields).get c.val)
theorem record034_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record034) (record034.maps 4) (record034.inverseMaps 4) record034_frame004_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record034) (record034.maps 4) (record034.inverseMaps 4) record034_frame004_indices (Fin.ofNat record034.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record034_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record034) (record034.maps 4)
      (record034.inverseMaps 4) record034_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record034_frame004_links_0000 record034_frame004_links_0064)
theorem record034_frame004_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 4 :=
  of_group record034 4 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record034_frame004_indices record034_frame004_graph record034_frame004_links
def record034_frame005_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x567acd57aa5d4aa8549a90cf29d939a70ccf9892c255ca393b009f13ce74ee59c537c6c2d6dac34d668c5d86af65deb194ea884d69792b24c4728d519a2b42e800fc1e53c06d0d199f32a61cc096b2b2540a012c24442c838fd1ec38c6d0d419e324620bf1702cc4b88f114214348680cc1942804f09c0fc1f03c0720881082003405c0981201e0380680c0160280480600a00800800 } : Fields).get c.val)
theorem record034_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record034) (record034.maps 5) (record034.inverseMaps 5) record034_frame005_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record034) (record034.maps 5) (record034.inverseMaps 5) record034_frame005_indices (Fin.ofNat record034.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record034_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record034) (record034.maps 5)
      (record034.inverseMaps 5) record034_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record034_frame005_links_0000 record034_frame005_links_0064)
theorem record034_frame005_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 5 :=
  of_group record034 5 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record034_frame005_indices record034_frame005_graph record034_frame005_links
def record034_frame006_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0x6dfdbbb5b676ccd8ba9751680cf39d73765dca591f2063cc6b446724b690b1ca3344f8650aa1341d810fd1f63d3792e0da43295e2b7565abf544a714c28d4f497529a3f4727f0f19dc39c6dcd698b2f85d0b294e2864a4901172223f47a0ee1d23886e0d71a0328598ac14e288388700dc1b02a0530a40fc1f03c0740881082003405c0981201e0380680c0160280480600a00800800 } : Fields).get c.val)
theorem record034_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record034) (record034.maps 6) (record034.inverseMaps 6) record034_frame006_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record034) (record034.maps 6) (record034.inverseMaps 6) record034_frame006_indices (Fin.ofNat record034.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record034_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record034) (record034.maps 6)
      (record034.inverseMaps 6) record034_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record034_frame006_links_0000 record034_frame006_links_0064)
theorem record034_frame006_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 6 :=
  of_group record034 6 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record034_frame006_indices record034_frame006_graph record034_frame006_links
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (Fin.cases (record034_frame001_supported hcells) (Fin.cases (record034_frame002_supported hcells) (Fin.cases (record034_frame003_supported hcells) (Fin.cases (record034_frame004_supported hcells) (Fin.cases (record034_frame005_supported hcells) (Fin.cases (record034_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
def record035_frame001_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x7c5f85eefca791f1dd0b9cf28e43c6785700df3b0f6069dd2fa0337666c678a70fe17bed7b2f2dd2b996fede5b9b6d69ace5939a92ee53c6d85f07200bfe7eef91e3bb374ed619d3285d4a954a2774e89bd302494708b5009e63c2744dc1b13145f0b51622b453499924240460860db1ac340638ba1522884e0970ea1d03906d0c616c2c8580821001f03705808c1082003405c0981201e0380680c0160280400600a00c00800 } : Fields).get c.val)
theorem record035_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record035_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record035) (record035.maps 1)
      (record035.inverseMaps 1) record035_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record035_frame001_links_0000 record035_frame001_links_0064)
theorem record035_frame001_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) : Supported record035 1 :=
  of_group record035 1 (embedding record035) hcells Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record035_frame001_indices record035_frame001_graph record035_frame001_links
def record035_frame002_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19dece9e6ef255919c83df7af2b75fba5dceedf36dcb5b56f6b71528a8fd37692945a9bd4dba67f32695aca5a4f922c91248423f91e78e745b627111e5ceaca55e0a1f499a3e512c8884392100fd47b93cb99a4bea5bc2758ffc78a3621aa0cf86182b6142898c46221c10b081c3e41ec0e486ec35619f0cc06242e61650b0055c29611f08d044c2160fd07403881b40d503c81e00ec06f032016c0b2058020810007c037016008c04202000d005c026012007803801a00c0058028010006002800c002000 } : Fields).get c.val)
theorem record035_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record035) (record035.maps 2) (record035.inverseMaps 2) record035_frame002_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record035) (record035.maps 2) (record035.inverseMaps 2) record035_frame002_indices (Fin.ofNat record035.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record035_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record035) (record035.maps 2)
      (record035.inverseMaps 2) record035_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record035_frame002_links_0000 record035_frame002_links_0064)
theorem record035_frame002_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) : Supported record035 2 :=
  of_group record035 2 (embedding record035) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record035_frame002_indices record035_frame002_graph record035_frame002_links
def record035_frame003_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0xb0ab08affae3ae1adca92a8ca7ea74a6ca57a50a479ff9fc9d59cf9bf9ac9a796995a94894192091590f8f48f08e08dd8da8d78c28b68a97136f26e068b6266015c15bb5af58f5645415284c949747b4123af3a437737136234530c2f22de2a628327b26524623c20f1fb1e51d41c91b919618017916f15a11810e1070fc0ea0d20ca0c10b907507407206c06105805605504003f03d03602c02302102001a01701301200f00e00d00c00b00a008006005003001000 } : Fields).get c.val)
theorem record035_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record035) (record035.maps 3) (record035.inverseMaps 3) record035_frame003_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record035) (record035.maps 3) (record035.inverseMaps 3) record035_frame003_indices (Fin.ofNat record035.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record035_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record035) (record035.maps 3)
      (record035.inverseMaps 3) record035_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record035_frame003_links_0000 record035_frame003_links_0064)
theorem record035_frame003_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) : Supported record035 3 :=
  of_group record035 3 (embedding record035) hcells Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record035_frame003_indices record035_frame003_graph record035_frame003_links
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (Fin.cases (record035_frame001_supported hcells) (Fin.cases (record035_frame002_supported hcells) (Fin.cases (record035_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xaa554e29ab4bd935495e47321f88443c21af0c37c43dd9ec0f5171e35f1aa2d3c69a349da24d0a67bb3c16d0b3a57e2b214eca6b4fe273932095c48523fd1de8e6470a35518a8be45aa2c51528a244ca25511a71a3731ae0d0063e3131714b2256329593a49a24c826192cc95649f24c124891048323e91e08de46b1f70ea46dc32d16f0b245722a313b096c498237115087441c1fb0f787903ac1c00c985e02d21540a384e825611808604041ee0f0075838c1b60d403b01bc0d6067030017007603601900b004e023006002c0100070030014004001 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record036_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record036_frame001_links_0000 (interval_append _ 64 128 132 record036_frame001_links_0064 record036_frame001_links_0128))
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (embedding record036) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
def record036_frame002_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0562.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0562.count (({ width := 11, code := 0x94728a4e49b9052063e47a8cd1963045e8851061f43d85106205406806fd9f63e67b0f49d8ba973ce4dbbb736c2d61a4b3d646c758b30c616c1d7b2ee5c4b856c2cd57eaf959a935169fd3ba5d4a290d1d22b43e814fe9f83ea79cef1d63a272cdd9b73606a0cb1953045e0b516229c524a193925c4a09111922643c840fe1ee3d4780e91c0364698ca1883045d8b21562a05009a12e240440840b815c2a8510981201a83105c0a81282101802c0400700c01401001 } : Fields).get c.val)
theorem record036_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0562.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (embedding (N := 44310) record036) (record036.maps 2) (record036.inverseMaps 2) record036_frame002_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (embedding (N := 44310) record036) (record036.maps 2) (record036.inverseMaps 2) record036_frame002_indices (Fin.ofNat record036.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record036_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (embedding (N := 44310) record036) (record036.maps 2) (record036.inverseMaps 2) record036_frame002_indices (Fin.ofNat record036.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record036_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (embedding (N := 44310) record036) (record036.maps 2)
      (record036.inverseMaps 2) record036_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record036_frame002_links_0000 (interval_append _ 64 128 132 record036_frame002_links_0064 record036_frame002_links_0128))
theorem record036_frame002_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) : Supported record036 2 :=
  of_group record036 2 (embedding record036) hcells Papers.RationalityTen.SharedFrameCatalogue.group0562
    Papers.RationalityTen.SharedFrameCatalogue.group0562_facts record036_frame002_indices record036_frame002_graph record036_frame002_links
def record036_frame003_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0x91321e3ec7b8851021d43783706609c117d2f9df03de786ed1d53a5742e71ca38f6fcde9a6b43672cbd8d318604bdd752de58ab095eab4566ab55129c526a4946a88502a013da4e47a8d11220f4127ecf71e53b4720e11bf3746c0d49a333c664c818e314618bf17d2c2544a31372484848e91721040c7f0f71e43bc758e51c23806e0d418e3085e8b51622b8548a414027c4d0961282404608a0c81802e8590a613c1b83205c0ac1382301802c0400700c01401001 } : Fields).get c.val)
theorem record036_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record036) (record036.maps 3) (record036.inverseMaps 3) record036_frame003_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record036) (record036.maps 3) (record036.inverseMaps 3) record036_frame003_indices (Fin.ofNat record036.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record036_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record036) (record036.maps 3) (record036.inverseMaps 3) record036_frame003_indices (Fin.ofNat record036.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record036_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record036) (record036.maps 3)
      (record036.inverseMaps 3) record036_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record036_frame003_links_0000 (interval_append _ 64 128 132 record036_frame003_links_0064 record036_frame003_links_0128))
theorem record036_frame003_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) : Supported record036 3 :=
  of_group record036 3 (embedding record036) hcells Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record036_frame003_indices record036_frame003_graph record036_frame003_links
def record036_frame004_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0xdb7b5f656c6cfd9ef39e6fc8b9071d637bff7f2f9df0b816a6c9d87b095eab956aab754e7c4e89b130a51c9f9071d232c518670be13c1c83304200bf97e0fbdf3bdd79ef35e0b6569ccfd97b1861cbcd6e2cd57aaa14ea9952aa0d3ca6f4d098527a4d4929091aa333fc790e79b9334648c59812d0584ac14d2844f49b12723e4688b90f1f63d0770e81c23706b8ce1923105f0b816a2b8530a10dc1a4328610b41581d0350640b01382301802c0400700c01401001 } : Fields).get c.val)
theorem record036_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record036) (record036.maps 4) (record036.inverseMaps 4) record036_frame004_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record036) (record036.maps 4) (record036.inverseMaps 4) record036_frame004_indices (Fin.ofNat record036.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record036_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record036) (record036.maps 4) (record036.inverseMaps 4) record036_frame004_indices (Fin.ofNat record036.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record036_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record036) (record036.maps 4)
      (record036.inverseMaps 4) record036_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record036_frame004_links_0000 (interval_append _ 64 128 132 record036_frame004_links_0064 record036_frame004_links_0128))
theorem record036_frame004_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) : Supported record036 4 :=
  of_group record036 4 (embedding record036) hcells Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record036_frame004_indices record036_frame004_graph record036_frame004_links
def record036_frame005_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0xb06b01adfad7a039fa9ec9e698197d96795e8c88c18b48b083f8047e37ca7c57b57a47977817776f26e26cd6b368c6866576406246045d05c75bd5ae5a759a58057656a56855a54e53d53a52949a47945f4434194083e23c53b13a438537837336d34f3423313273203083032fd2f62e32df2a828526824822221920f2031e31d41c91c21b81ad1a319418918117916c14e13e13112211710e1070f90f30eb0e20da0d40cb0c00b807206c06806405d05903a03503102c02702300c00b008007006005002001 } : Fields).get c.val)
theorem record036_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record036) (record036.maps 5) (record036.inverseMaps 5) record036_frame005_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record036) (record036.maps 5) (record036.inverseMaps 5) record036_frame005_indices (Fin.ofNat record036.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record036_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record036) (record036.maps 5) (record036.inverseMaps 5) record036_frame005_indices (Fin.ofNat record036.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record036_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record036) (record036.maps 5)
      (record036.inverseMaps 5) record036_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record036_frame005_links_0000 (interval_append _ 64 128 132 record036_frame005_links_0064 record036_frame005_links_0128))
theorem record036_frame005_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) : Supported record036 5 :=
  of_group record036 5 (embedding record036) hcells Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record036_frame005_indices record036_frame005_graph record036_frame005_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (Fin.cases (record036_frame002_supported hcells) (Fin.cases (record036_frame003_supported hcells) (Fin.cases (record036_frame004_supported hcells) (Fin.cases (record036_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x27ff3f39b6ca6e4e121e898c3b21a30a083abfe5fccfab7cc3b35d6ee99741b4c99bac74607abe158ca9853328f546a9c34c5a57924c8ff47b23a11b6863429a1210468134041fa0e2e6ae3401934c3e5f82f99634ac455629c1434a024ee274938898c4bb23b11a88b244721d90a88363af1be8d3c63a2f71780b8859428b134096c49423d11708844202030fd07b43ae1b70c185dc2d21520a304e024c11908403ec1b80d2032017c0b603e01b80cc05e02c014009c04802300b804801c00c005802000e006002800c004001 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (embedding record037) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x9f74db650725890dc4c61d90d1847418e09cfe07c93e356c6af35632a4d4cca3b51aa70131695b49323f91ec8e8431a14d0468133f41c5cd5c680326987cbf05f32c79588a7450d27793a49c4476235111c87641b1d68df46de34d18e8c3c5ec2f01710ae451626812d88f445c22110187e83da1d90db860c2ee16b0a9051827412608c84201b80d203b01bc0d606402f816c07c03701980b004e02300d005c026012007803801800b005002000e006002800c004001 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (embedding record038) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
def record038_frame002_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0xa25402764e49b52ea58cad9412624a4848f91e9eabc1768e95c9b796e8d81a9346666c6187b0c5e8bb56e2d6590a593fa724c89491d23543a841019f13b2740e69b535e67ccc98c2e2590b09572804e89592824c4788a1102164007e0f51cc3886f0d81a6324618bc1682b85289a128240430820c41782d8570a613c1b03205e0ac1382303405c0981201e0380600b0140200380600a00c01001 } : Fields).get c.val)
theorem record038_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (embedding (N := 44310) record038) (record038.maps 2) (record038.inverseMaps 2) record038_frame002_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (embedding (N := 44310) record038) (record038.maps 2) (record038.inverseMaps 2) record038_frame002_indices (Fin.ofNat record038.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record038_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (embedding (N := 44310) record038) (record038.maps 2)
      (record038.inverseMaps 2) record038_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record038_frame002_links_0000 record038_frame002_links_0064)
theorem record038_frame002_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) : Supported record038 2 :=
  of_group record038 2 (embedding record038) hcells Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record038_frame002_indices record038_frame002_graph record038_frame002_links
def record038_frame003_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0xf77e3ba1739e51b0f596aad019bb3363fc5389a6b4bb94f2624246e8d71561e42f839022014007b8f55e0bbb750d699d32862cc1175ae8598ad552a944fc9e13b25a4aa9111f22e402798f09d13706c4ca98e3145f0b51622b4534a213c256494901182183e0778e41ac340638bb16a2bc4d8960e41b4348630bc16c1f0370660b01382303405c0981201e0380600b0140200380600a00c01001 } : Fields).get c.val)
theorem record038_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record038) (record038.maps 3) (record038.inverseMaps 3) record038_frame003_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record038) (record038.maps 3) (record038.inverseMaps 3) record038_frame003_indices (Fin.ofNat record038.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record038_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record038) (record038.maps 3)
      (record038.inverseMaps 3) record038_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record038_frame003_links_0000 record038_frame003_links_0064)
theorem record038_frame003_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) : Supported record038 3 :=
  of_group record038 3 (embedding record038) hcells Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record038_frame003_indices record038_frame003_graph record038_frame003_links
def record038_frame004_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcdde41efbd795bafd6f6ae7567a6ed2528b53b39b74dad740b295782ac14eaa22509268d2d493347ca2bd13088b4112040fb87cb3cc19b0bea5bc2be15049dc4de23790d87fe3c51bd8d906ae2ee16e0aa052e264118887042c2070f907b03aa1ce0e486ec35619f0cc062430617c0b6859c2c01570a584d825e12708d044c2160fe07a83b81b20d303b01bc0d606402f816c07c03701980b004e02300d005c026012007803801800b005002000e006002800c004001 } : Fields).get c.val)
theorem record038_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record038) (record038.maps 4) (record038.inverseMaps 4) record038_frame004_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record038) (record038.maps 4) (record038.inverseMaps 4) record038_frame004_indices (Fin.ofNat record038.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record038_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record038) (record038.maps 4)
      (record038.inverseMaps 4) record038_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record038_frame004_links_0000 record038_frame004_links_0064)
theorem record038_frame004_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) : Supported record038 4 :=
  of_group record038 4 (embedding record038) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record038_frame004_indices record038_frame004_graph record038_frame004_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (Fin.cases (record038_frame002_supported hcells) (Fin.cases (record038_frame003_supported hcells) (Fin.cases (record038_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x2d5169ab0cd81aa81533a83d3aa6d735799a4c7656d2a093a49723811a78c445c9b60d4f68a3371948c5261f2d2d5d4aaf53ba8fd3da9d94d4a65131897f4b5258929e94849fa4e924a91548724212028f947923b11ca8dd3e91d84e466e53569960c865d12cc1618ac052a28c137c99e4be25511d48aa44321890888244021f80f807a23621948c5c5e22bb15489c04c024f11d88183cc1d40e106cc3461930c085c42c41570a7052428413909a04b424c11d08b044421610307e03dc1dc0e807203781ac0d001780b0050027012008c04202000e8070034017009804801e00e006002c010007 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record039_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record039_frame001_links_0000 (interval_append _ 64 128 142 record039_frame001_links_0064 record039_frame001_links_0128))
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (embedding record039) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
def record039_frame002_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x28153fc9c1cdb6537283938496228b13188043b214108e83ac18e010ff27dd3e91a64cd465031ad86ec0d6032d8d5eaac654aa999478a354e42659306963498a4792008f9476a37113086642b212507282640b2024ff27ea38b9ac0d0064f30f97e4be658d2b11558a7050d28093b89d24df26492448e846822e114088a43921690848343ad1be8dbc69a31d1878bd85e02e21660a2c4d025b12608f445c221109080c3f41f00eb072c37419f0ca86142f21680ae0550290137095849c22c10507e03b01b40d001780b0050027012008c04202000e8070034017009804801e00e006002c010007 } : Fields).get c.val)
theorem record039_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record039) (record039.maps 2) (record039.inverseMaps 2) record039_frame002_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record039) (record039.maps 2) (record039.inverseMaps 2) record039_frame002_indices (Fin.ofNat record039.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record039_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record039) (record039.maps 2) (record039.inverseMaps 2) record039_frame002_indices (Fin.ofNat record039.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record039_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record039) (record039.maps 2)
      (record039.inverseMaps 2) record039_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record039_frame002_links_0000 (interval_append _ 64 128 142 record039_frame002_links_0064 record039_frame002_links_0128))
theorem record039_frame002_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) : Supported record039 2 :=
  of_group record039 2 (embedding record039) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record039_frame002_indices record039_frame002_graph record039_frame002_links
def record039_frame003_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1079.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1079.count (({ width := 11, code := 0x35ceb7d63ac343e85d05a0326e49c878ff1ae33c618bb12621c37862c6572abd53e9d524a413de704cb97729e47c8b8d11562643f85908e0a410815015fa3e57baf59e7bc677ceddd83a96f0d6da4b33642c3584ae1598b1d5ba9d52ea093ea764d8955252444788dd182294428650a1ec3a4730de9a8346638c49822f0584aa94e28c4f89b9312524909011b226440851032003e8798eb1ca3846d0d2198328610bd1742d0568a905e0b01402704808c1082003a0700d0170260480780e01802c04007 } : Fields).get c.val)
theorem record039_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record039) (record039.maps 3) (record039.inverseMaps 3) record039_frame003_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record039) (record039.maps 3) (record039.inverseMaps 3) record039_frame003_indices (Fin.ofNat record039.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record039_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record039) (record039.maps 3) (record039.inverseMaps 3) record039_frame003_indices (Fin.ofNat record039.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record039_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record039) (record039.maps 3)
      (record039.inverseMaps 3) record039_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record039_frame003_links_0000 (interval_append _ 64 128 142 record039_frame003_links_0064 record039_frame003_links_0128))
theorem record039_frame003_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) : Supported record039 3 :=
  of_group record039 3 (embedding record039) hcells Papers.RationalityTen.SharedFrameCatalogue.group1079
    Papers.RationalityTen.SharedFrameCatalogue.group1079_facts record039_frame003_indices record039_frame003_graph record039_frame003_links
def record039_frame004_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x2ccd98b13622c1d81aff5fab3564abd56ea6d4ba935229f53ca6d4ce774eb9cf37a6bcc998b27646c7d8db1762143b86308e0e4117f8fc5eb3cb780ef5d639e72ee41c4b816f0dc1b3b5e65ac7187b025e6b69692c1562ab95129251c9c5342644be94525a4647c8e51a22d44a8790d9fd3d2790eb1c13766a8d219f32c610bd1702cc574a994a27e4d89992e2484888f11322242c818f61da3a06e8cc17e2ec570a51422604688705a0b01402704808c1082003a0700d0170260480780e01802c04007 } : Fields).get c.val)
theorem record039_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record039) (record039.maps 4) (record039.inverseMaps 4) record039_frame004_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record039) (record039.maps 4) (record039.inverseMaps 4) record039_frame004_indices (Fin.ofNat record039.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record039_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record039) (record039.maps 4) (record039.inverseMaps 4) record039_frame004_indices (Fin.ofNat record039.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record039_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record039) (record039.maps 4)
      (record039.inverseMaps 4) record039_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record039_frame004_links_0000 (interval_append _ 64 128 142 record039_frame004_links_0064 record039_frame004_links_0128))
theorem record039_frame004_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) : Supported record039 4 :=
  of_group record039 4 (embedding record039) hcells Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record039_frame004_indices record039_frame004_graph record039_frame004_links
def record039_frame005_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0x259cae94527e4748d91722a2c45389511e19c3085f0b60c41381701dc5b826f8dc9b2b52690ce59932b640c597eaf85dab8d6fada59eb295fab9566ac150296520a294227e4f09c9362664828b91221b4167e0f89dd39e738e31b6368690ce99b32e61cc017b2ec5c4b61682c657cae14927c4ec9992524243c851082043cc768e71c43746c8d419e32c648c517e2f85c8b11602b4550a51442804e096124244460891102144087f05e0b01402704808c1082003a0700d0170260480780e01802c04007 } : Fields).get c.val)
theorem record039_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record039) (record039.maps 5) (record039.inverseMaps 5) record039_frame005_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record039) (record039.maps 5) (record039.inverseMaps 5) record039_frame005_indices (Fin.ofNat record039.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record039_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record039) (record039.maps 5) (record039.inverseMaps 5) record039_frame005_indices (Fin.ofNat record039.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record039_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record039) (record039.maps 5)
      (record039.inverseMaps 5) record039_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record039_frame005_links_0000 (interval_append _ 64 128 142 record039_frame005_links_0064 record039_frame005_links_0128))
theorem record039_frame005_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) : Supported record039 5 :=
  of_group record039 5 (embedding record039) hcells Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record039_frame005_indices record039_frame005_graph record039_frame005_links
def record039_frame006_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x2b2d63a9351a95526a494867a4ef9d1392694cf991312594ae94b282274408750da16c2183d011f6be37bcf4de0bbe756e61ca38c700dd5b33606b4d559e32963ec6d88b09606be979ae9590aa94f29851c9ed3c2694ba96d2aa4a48c8e91b233458861062053fc7d8f99ec3c6778ed1b434667cca9873025c8b716b2c451c9d93225a48c8e916218420810fe1ea3cc768e21c036c6a8ce190314600b71642bc5209c1322444408305e0b01402704808c1082003a0700d0170260480780e01802c04007 } : Fields).get c.val)
theorem record039_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record039) (record039.maps 6) (record039.inverseMaps 6) record039_frame006_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record039) (record039.maps 6) (record039.inverseMaps 6) record039_frame006_indices (Fin.ofNat record039.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record039_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record039) (record039.maps 6) (record039.inverseMaps 6) record039_frame006_indices (Fin.ofNat record039.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record039_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record039) (record039.maps 6)
      (record039.inverseMaps 6) record039_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record039_frame006_links_0000 (interval_append _ 64 128 142 record039_frame006_links_0064 record039_frame006_links_0128))
theorem record039_frame006_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) : Supported record039 6 :=
  of_group record039 6 (embedding record039) hcells Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record039_frame006_indices record039_frame006_graph record039_frame006_links
def record039_frame007_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0x397f2ce3bc6776ee8dc9b8b556a7d3ba674067cce79b72ce56c9f932c6576acd572a5d34a5940a76cde9a130a544a18f717a2cc4986b0a208c0a806ffdf53dc7a4f31e13b8762ea1cfb956aecd18f3105f8b956fac3562abd50a8c50a9c135a684be9191da3045688d0da12410800fc9d73806ecd79a233c620c21822f2580aa14a2824dc9792923c4608990f20c4147f8f41e63b8740de1b0358678c51802fc5b8b115c2a45109e05e0b01402704808c1082003a0700d0170260480780e01802c04007 } : Fields).get c.val)
theorem record039_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (embedding (N := 44310) record039) (record039.maps 7) (record039.inverseMaps 7) record039_frame007_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (embedding (N := 44310) record039) (record039.maps 7) (record039.inverseMaps 7) record039_frame007_indices (Fin.ofNat record039.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record039_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (embedding (N := 44310) record039) (record039.maps 7) (record039.inverseMaps 7) record039_frame007_indices (Fin.ofNat record039.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record039_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (embedding (N := 44310) record039) (record039.maps 7)
      (record039.inverseMaps 7) record039_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record039_frame007_links_0000 (interval_append _ 64 128 142 record039_frame007_links_0064 record039_frame007_links_0128))
theorem record039_frame007_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) : Supported record039 7 :=
  of_group record039 7 (embedding record039) hcells Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record039_frame007_indices record039_frame007_graph record039_frame007_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (Fin.cases (record039_frame002_supported hcells) (Fin.cases (record039_frame003_supported hcells) (Fin.cases (record039_frame004_supported hcells) (Fin.cases (record039_frame005_supported hcells) (Fin.cases (record039_frame006_supported hcells) (Fin.cases (record039_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
def record048_frame001_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x29f14d3a12503677f38b9ae44561c30ac83dc1ae0bd048811c035fbcf8b7b9bd69e96f3378d367da0cca464f323d8f4abe555aa7533a96148d24291d48ae433a15d09a84541b20bcefc6d433e19a0cbe65332618fcba256a2a89500a4c50927e13749884b324c91f08de46523091588a236117f0bb45ba2c012e8930478232115087042a1ef0db06882ae14509d84c42100fe07a03480fa073030016c0b405602a811407602f0140098046022010807803a017009804001c00d00580240100040018008002000 } : Fields).get c.val)
theorem record048_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record048_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record048) (record048.maps 1)
      (record048.inverseMaps 1) record048_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record048_frame001_links_0000 record048_frame001_links_0064)
theorem record048_frame001_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) : Supported record048 1 :=
  of_group record048 1 (embedding record048) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record048_frame001_indices record048_frame001_graph record048_frame001_links
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (Fin.cases (record048_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record051_frames_supported
theorem record052_frame000_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) :
    Supported record052 0 :=
  of_identity record052 0 (by decide +kernel)
def record052_frame001_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x29a94c391fc8aa2c515487bc38a0c104e7eb3f01beccdd650313d878b9153c28ed3d49d74d4a6153009704b2a56d2a894e4a324e524891c481a4011f48f3475a3811b26b63239744af4543291942c9f44d725591d88ce42320b10187b43ca1b10c2c5a82b414e0a2c4d023c10387e03681a70cb85ac2b61570a7052428413909a04b424c11d08c044c21a10007c83c01d40e206e03581a60a0049023411807d03781a80d203701780b005001f00f00740340170098028012008 } : Fields).get c.val)
theorem record052_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record052_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record052) (record052.maps 1)
      (record052.inverseMaps 1) record052_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record052_frame001_links_0000 record052_frame001_links_0064)
theorem record052_frame001_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) : Supported record052 1 :=
  of_group record052 1 (embedding record052) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record052_frame001_indices record052_frame001_graph record052_frame001_links
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (Fin.cases (record052_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record052_frames_supported
theorem record053_frame000_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) :
    Supported record053 0 :=
  of_identity record053 0 (by decide +kernel)
theorem record053_frames_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) :
    ∀ f : Fin record053.g, Supported record053 f :=
  (Fin.cases (record053_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record053_frames_supported
theorem record054_frame000_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) :
    Supported record054 0 :=
  of_identity record054 0 (by decide +kernel)
theorem record054_frames_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) :
    ∀ f : Fin record054.g, Supported record054 f :=
  (Fin.cases (record054_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record054_frames_supported
theorem record055_frame000_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) :
    Supported record055 0 :=
  of_identity record055 0 (by decide +kernel)
def record055_frame001_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x58fac4d518a7dd30296b33e993cc125db1cb8d944a622d08f83f4096024ff87f2b7d1920c4b61fae3d4569e64ed26a52f49704b525892b69494a324e526291f48e2439206900476a3991be8203309910bac55b29e94a8a0a4db26892c088642c2118fd87be3cf1b38bb059c2bb14b09b04c42410ea06f43681870b805802ae1520a104e425a126090046021e10b08303f01ea0f007403941b80d6069028c13809604902000f207303780ec058026011808804001e00e805c02200e006802c012008 } : Fields).get c.val)
theorem record055_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record055) (record055.maps 1)
      (record055.inverseMaps 1) record055_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame001_links_0000 record055_frame001_links_0064)
theorem record055_frame001_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) : Supported record055 1 :=
  of_group record055 1 (embedding record055) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record055_frame001_indices record055_frame001_graph record055_frame001_links
theorem record055_frames_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) :
    ∀ f : Fin record055.g, Supported record055 f :=
  (Fin.cases (record055_frame000_supported hcells) (Fin.cases (record055_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record055_frames_supported
theorem record056_frame000_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    Supported record056 0 :=
  of_identity record056 0 (by decide +kernel)
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record056_frames_supported
theorem record057_frame000_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) :
    Supported record057 0 :=
  of_identity record057 0 (by decide +kernel)
def record057_frame001_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x96396195f95a91991691390e9059028fd8fa85d82880e80874d6ec6bb6af6695f95be5ab59958b58858057357056856055154e54653e53652a52246f3ff3c43b135f2fe2cd2c12b62a82a529d29028d28527d26e26b26325b25324723f2191de1c21bd1b81ad1a91a219619118918217617216a16315c15014914613b13713012411f1171101041000f80f10ea0de0d70d50d10cd0c90c50c109909609208d08c07607306f06a06902f02c02802302201a01701300e00d } : Fields).get c.val)
theorem record057_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record057) (record057.maps 1) (record057.inverseMaps 1) record057_frame001_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record057) (record057.maps 1) (record057.inverseMaps 1) record057_frame001_indices (Fin.ofNat record057.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record057_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record057) (record057.maps 1)
      (record057.inverseMaps 1) record057_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record057_frame001_links_0000 record057_frame001_links_0064)
theorem record057_frame001_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) : Supported record057 1 :=
  of_group record057 1 (embedding record057) hcells Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record057_frame001_indices record057_frame001_graph record057_frame001_links
def record057_frame002_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1106.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1106.count (({ width := 10, code := 0x8a2268922283e0c8260680e017fdfd78dd0721c66c59e659946117159d625815d5715a55d565515253d4e5314a5214550d2e46d11430ff3b0e4388df370db364d6354d3344ce334cb324c7310c22d8a326c9925893248902348c2288821484208801f87b1e4781d4741c86f1b86c1a86719864188601745b168591605715855118430fc3a0e4310b82a09424070190541003c0d0280600400 } : Fields).get c.val)
theorem record057_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (embedding (N := 44310) record057) (record057.maps 2) (record057.inverseMaps 2) record057_frame002_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (embedding (N := 44310) record057) (record057.maps 2) (record057.inverseMaps 2) record057_frame002_indices (Fin.ofNat record057.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record057_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (embedding (N := 44310) record057) (record057.maps 2)
      (record057.inverseMaps 2) record057_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record057_frame002_links_0000 record057_frame002_links_0064)
theorem record057_frame002_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) : Supported record057 2 :=
  of_group record057 2 (embedding record057) hcells Papers.RationalityTen.SharedFrameCatalogue.group1106
    Papers.RationalityTen.SharedFrameCatalogue.group1106_facts record057_frame002_indices record057_frame002_graph record057_frame002_links
def record057_frame003_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1102.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1102.count (({ width := 10, code := 0x9ee799de7598a5f9725995a5494a508da2386e19811f17a5e775dc46e5b36c1ac6ada868da267d9c65d9664d906358a621735815553d414b926491214751c4651444d104350841d04404fe3ecf93b4da348d0334c9320c5300bf2f0b92d0b32c0ad2a8a7294a42809f27097258932408b22887210811f87c1ec7a1e4781dc7619c641805b1685213c4b118450bc2c0a0230881a05c130380d } : Fields).get c.val)
theorem record057_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (embedding (N := 44310) record057) (record057.maps 3) (record057.inverseMaps 3) record057_frame003_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (embedding (N := 44310) record057) (record057.maps 3) (record057.inverseMaps 3) record057_frame003_indices (Fin.ofNat record057.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record057_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (embedding (N := 44310) record057) (record057.maps 3)
      (record057.inverseMaps 3) record057_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record057_frame003_links_0000 record057_frame003_links_0064)
theorem record057_frame003_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) : Supported record057 3 :=
  of_group record057 3 (embedding record057) hcells Papers.RationalityTen.SharedFrameCatalogue.group1102
    Papers.RationalityTen.SharedFrameCatalogue.group1102_facts record057_frame003_indices record057_frame003_graph record057_frame003_links
def record057_frame004_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0xa78a6ea62a5c95195093b9358e18de8d58d17db79c77c7726f26af68d68365d60b5d65ca5be5ad5aa5a358b58958157856956755b55154552c5244a144941c40e3de3a438037a37435e35d35134133f33232831230f3052fe2f52e22da2a62462202182102021fe1f41e21de1d61cb1c01bc1b01a619b18717f17a16e16615c14d14813f13312311c1101090ff0f10e90e70df0d60cd0c40bc09109008c08708607207006c06706602e02c02802302201a01701300e00d } : Fields).get c.val)
theorem record057_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record057) (record057.maps 4) (record057.inverseMaps 4) record057_frame004_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record057) (record057.maps 4) (record057.inverseMaps 4) record057_frame004_indices (Fin.ofNat record057.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record057_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record057) (record057.maps 4)
      (record057.inverseMaps 4) record057_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record057_frame004_links_0000 record057_frame004_links_0064)
theorem record057_frame004_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) : Supported record057 4 :=
  of_group record057 4 (embedding record057) hcells Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record057_frame004_indices record057_frame004_graph record057_frame004_links
def record057_frame005_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0537.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0537.count (({ width := 9, code := 0x23b1c8dc6a33188bc5a2b1489c4a13027ebede6ec73b95c0d9693419ecc65b2990c762b0d84c15faf978ba5c2c956a4512752c9147a351489442190a8340a00fe7d3e1e8f076389a8ca6330978ba5c2d164ae552a14ca250271309449231148842208fc7a3c1d8e470361a0c86230178b85a2c150a44c221087c3c1b0b8582813080301609040140200 } : Fields).get c.val)
theorem record057_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0537.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0537.localPairCheck (embedding (N := 44310) record057) (record057.maps 5) (record057.inverseMaps 5) record057_frame005_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0537.localPairCheck (embedding (N := 44310) record057) (record057.maps 5) (record057.inverseMaps 5) record057_frame005_indices (Fin.ofNat record057.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record057_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0537.localPairCheck (embedding (N := 44310) record057) (record057.maps 5)
      (record057.inverseMaps 5) record057_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record057_frame005_links_0000 record057_frame005_links_0064)
theorem record057_frame005_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) : Supported record057 5 :=
  of_group record057 5 (embedding record057) hcells Papers.RationalityTen.SharedFrameCatalogue.group0537
    Papers.RationalityTen.SharedFrameCatalogue.group0537_facts record057_frame005_indices record057_frame005_graph record057_frame005_links
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (Fin.cases (record057_frame001_supported hcells) (Fin.cases (record057_frame002_supported hcells) (Fin.cases (record057_frame003_supported hcells) (Fin.cases (record057_frame004_supported hcells) (Fin.cases (record057_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record059_frames_supported
theorem record060_frame000_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    Supported record060 0 :=
  of_identity record060 0 (by decide +kernel)
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
def record061_frame001_indices (c : Fin record061.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x50aa82d3959c04dca6b531c9834af653923290c45c62b50ca85b3929b14d3c696b4a1a26d0367e33bd5f6ac954ea99531e95d498a3e51cc8da46a233118a8b7457229d14689b44a222cf1a6e635c99fcc986272c89590a544f726913089744ab253126092248824211ec8ee4712348dbc65c2c615209dc4d623c10c082c4001f20e0865031015909a84a023a10f07c83c41d20e206d83500ec06e03681a40ce05f02f016807603601a00c4058027012808802400d0050024010007002000c004001 } : Fields).get c.val)
theorem record061_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record061.data.requiredEdges q = true := by decide +kernel
theorem record061_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record061_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record061_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record061) (record061.maps 1)
      (record061.inverseMaps 1) record061_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record061_frame001_links_0000 record061_frame001_links_0064)
theorem record061_frame001_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) : Supported record061 1 :=
  of_group record061 1 (embedding record061) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record061_frame001_indices record061_frame001_graph record061_frame001_links
theorem record061_frames_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    ∀ f : Fin record061.g, Supported record061 f :=
  (Fin.cases (record061_frame000_supported hcells) (Fin.cases (record061_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record061_frames_supported
theorem record062_frame000_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    Supported record062 0 :=
  of_identity record062 0 (by decide +kernel)
def record062_frame001_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19e9cdae4d720784ac19e042f0b774bae5d02e61700b715b16d5d599abf55a28f345ea294e626ff374998cc626112ea967cb11b18d42557a9d949a93447c23050e68414181fecfd27d63e39edcf4e57b2a114648003c41c68cfc61a2fc1638ad454429314189cc41e2060f887943bc1b40d6069833e1910c505ec2ea16e0ac054827a12f094048423210c08283d81e008c03b01b40d206402e81680ae05602a815007c03501880b004a02200f807803a01c00d005c0220100068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record062_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record062_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record062) (record062.maps 1)
      (record062.inverseMaps 1) record062_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record062_frame001_links_0000 record062_frame001_links_0064)
theorem record062_frame001_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) : Supported record062 1 :=
  of_group record062 1 (embedding record062) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record062_frame001_indices record062_frame001_graph record062_frame001_links
def record062_frame002_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x51ca234167fcf39e53be714e19af35a694d199f32e63cb59652ba4bc9692320a3fc7d8f11d239c718db1aa0740a748e51c4347664c79832fc5f0b9d712da5a8b45662634a6921021f03be71cde9b9352690ce997328640af95627e4d49811b22a44c881062023d0788e71b2358658c317a2e8598a61442544886c0c41742c8570a21382584a0921201b03105a0ac1282203e0780e81c03405c0881001a0300500901001c0280400600800800 } : Fields).get c.val)
theorem record062_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (embedding (N := 44310) record062) (record062.maps 2) (record062.inverseMaps 2) record062_frame002_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (embedding (N := 44310) record062) (record062.maps 2) (record062.inverseMaps 2) record062_frame002_indices (Fin.ofNat record062.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record062_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (embedding (N := 44310) record062) (record062.maps 2)
      (record062.inverseMaps 2) record062_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record062_frame002_links_0000 record062_frame002_links_0064)
theorem record062_frame002_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) : Supported record062 2 :=
  of_group record062 2 (embedding record062) hcells Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record062_frame002_indices record062_frame002_graph record062_frame002_links
def record062_frame003_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0x48c90d2023e4708df1aa32c648bf16e2d4588a914e2843d8770da13c2684905a0a41281702203405802ffdcdb93670cb993aed5b4b315b2a8548a5547a8b50ca0d3f23044e870f21d93986d4d59a632c648c6188308600a49432684bc9491021641c818f91ea3a8738e31ae344630bd1702cc568a614426c4b8720c817c2d8570a01342504909011c1c83105a0ac1282203e0780e81c03405c0881001a0300500901001c0280400600800800 } : Fields).get c.val)
theorem record062_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record062) (record062.maps 3) (record062.inverseMaps 3) record062_frame003_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record062) (record062.maps 3) (record062.inverseMaps 3) record062_frame003_indices (Fin.ofNat record062.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record062_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record062) (record062.maps 3)
      (record062.inverseMaps 3) record062_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record062_frame003_links_0000 record062_frame003_links_0064)
theorem record062_frame003_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) : Supported record062 3 :=
  of_group record062 3 (embedding record062) hcells Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record062_frame003_indices record062_frame003_graph record062_frame003_links
theorem record062_frames_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    ∀ f : Fin record062.g, Supported record062 f :=
  (Fin.cases (record062_frame000_supported hcells) (Fin.cases (record062_frame001_supported hcells) (Fin.cases (record062_frame002_supported hcells) (Fin.cases (record062_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record062_frames_supported
theorem record063_frame000_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    Supported record063 0 :=
  of_identity record063 0 (by decide +kernel)
def record063_frame001_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x1682cfd9eb2163ec757daf75e2bad73ae15beb756bac1576ad547a8b50a9c535a654b295527a4d496914df9b11ba2f41580efc9f2bda76ce95cfb8c70adedb936b6c4c0d7a2ac542a4542a7b4c09492623f4748cd1622643e784ea9c036e6c4cb98530059caf1522925009b92d2424748810a2043e8788d11882c85486e0b215c2b05009e1302484808e1181782d0580981282203e0780e81c03405c0881001a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record063_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record063_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record063) (record063.maps 1)
      (record063.inverseMaps 1) record063_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record063_frame001_links_0000 record063_frame001_links_0064)
theorem record063_frame001_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 1 :=
  of_group record063 1 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record063_frame001_indices record063_frame001_graph record063_frame001_links
def record063_frame002_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x5b5ada16bcb2ad926c634e5a6a530e92f483a34516287b4229a2ccba62f25491fc8aa3371858b7c4fa25911988643de1c4cdd652a9e14809844bda5992b495349b248523690647fa3dd1e08ea4719b98d5c5742af94a4a0a4f425591d88ce43221190448023f11f08c145e02ba14b0a144782070fc070c3681a20c906082e41560a4050426612c092847822e10407e83bc1d208c034819c0c805e02e81680ae05602a815006202f016009804a02200f807803a01c00d005c0220100068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record063_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record063) (record063.maps 2) (record063.inverseMaps 2) record063_frame002_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record063) (record063.maps 2) (record063.inverseMaps 2) record063_frame002_indices (Fin.ofNat record063.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record063_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record063) (record063.maps 2)
      (record063.inverseMaps 2) record063_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record063_frame002_links_0000 record063_frame002_links_0064)
theorem record063_frame002_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 2 :=
  of_group record063 2 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record063_frame002_indices record063_frame002_graph record063_frame002_links
def record063_frame003_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0x12e65c4b69532a253c899092063ec798ed1ca37c6c89912622c2c85309206c0980cff9fe3f87e6fc1f6b736ccc858badb5acb2d632c2558a714ba885049ed3aa704d4871061ca38a6d4d81ab330620c21772e45acb39642c04dc9912423c460818f41e238c6f0d81a6340660c31782dc570ac15229c52098128238458690b61642c0520a21382584a0921201882f0580981282203e0780e81c03405c0881001a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record063_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record063) (record063.maps 3) (record063.inverseMaps 3) record063_frame003_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record063) (record063.maps 3) (record063.inverseMaps 3) record063_frame003_indices (Fin.ofNat record063.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record063_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record063) (record063.maps 3)
      (record063.inverseMaps 3) record063_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record063_frame003_links_0000 record063_frame003_links_0064)
theorem record063_frame003_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 3 :=
  of_group record063 3 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record063_frame003_indices record063_frame003_graph record063_frame003_links
def record063_frame004_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x67ff3e99e9cb5654326b783bb95d9ee47710b805b82d876b8acbd5f2ae3479a2f514a73137f9ba4cc66313089754b3e588d896a12acd4ec94649823e11a88c143aa1050607fb3f49f60f8e7b73d395fca844121fe0f1074038d1a08c345f82c715a8a90526283139883c40c1f10f287783821ac0d306443141820bd85d42dc1600a9052c27a13609784a024210c08283dc1e008c034819c0c805e02e81680ae05602a815006202f016009804a02200f807803a01c00d005c0220100068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record063_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record063) (record063.maps 4) (record063.inverseMaps 4) record063_frame004_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record063) (record063.maps 4) (record063.inverseMaps 4) record063_frame004_indices (Fin.ofNat record063.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record063_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record063) (record063.maps 4)
      (record063.inverseMaps 4) record063_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record063_frame004_links_0000 record063_frame004_links_0064)
theorem record063_frame004_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 4 :=
  of_group record063 4 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record063_frame004_indices record063_frame004_graph record063_frame004_links
def record063_frame005_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0562.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0562.count (({ width := 11, code := 0x12a253ca59432824f49892b25247c8e919226444879011fa3dc6e8d71aa31c628bf16a2bc558a9146283f27d0e81c934e690ce998b29620bfd7cae65b6b5164ac35709f93ca304508790920b3da788ed9c537e6ccd61a23345b8b41602b254c9e1312564708b10e20e4047d0f01d039c6e8d91a6334638b515c2884e0660a61442804a092118218420821001682b0540901182003a0700d81a03005c0881001a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record063_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0562.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (embedding (N := 44310) record063) (record063.maps 5) (record063.inverseMaps 5) record063_frame005_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (embedding (N := 44310) record063) (record063.maps 5) (record063.inverseMaps 5) record063_frame005_indices (Fin.ofNat record063.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record063_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (embedding (N := 44310) record063) (record063.maps 5)
      (record063.inverseMaps 5) record063_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record063_frame005_links_0000 record063_frame005_links_0064)
theorem record063_frame005_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 5 :=
  of_group record063 5 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group0562
    Papers.RationalityTen.SharedFrameCatalogue.group0562_facts record063_frame005_indices record063_frame005_graph record063_frame005_links
def record063_frame006_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0559.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0559.count (({ width := 8, code := 0xecebeae9e8e7e6e5e4e3e2e1e0dfdedddcdbdad9d8d7d6d5d4d3d2d1d0cfcccbc1c0b7b6b5b3b1aba7a6a3a2a09e9d9c98978e8d8c8a88827e7d7a7977757473706f6e6c6a64605f5c5b595756555351504e4d4c4b4a474645443e3938373433302d2c2b2a252423201f1c19181716151411100d0a09080706050403020100 } : Fields).get c.val)
theorem record063_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0559.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0559.localPairCheck (embedding (N := 44310) record063) (record063.maps 6) (record063.inverseMaps 6) record063_frame006_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0559.localPairCheck (embedding (N := 44310) record063) (record063.maps 6) (record063.inverseMaps 6) record063_frame006_indices (Fin.ofNat record063.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record063_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0559.localPairCheck (embedding (N := 44310) record063) (record063.maps 6)
      (record063.inverseMaps 6) record063_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record063_frame006_links_0000 record063_frame006_links_0064)
theorem record063_frame006_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 6 :=
  of_group record063 6 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group0559
    Papers.RationalityTen.SharedFrameCatalogue.group0559_facts record063_frame006_indices record063_frame006_graph record063_frame006_links
def record063_frame007_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x139a724e29a733a64ca093b26a4b49191922242c828ab14225c3886f0da12c2384307a0d41682503a053716beb516127b4ec9b534a664b2941272454848f91da3946c738de1752e059cb19602a6528a413f2784e09a933260430838fe1f43dc750e11be358698cf198328638c117e2f85e0bb1742e45c0b51682c8588880ce1943105c0b61602a8540a61481882f0580981282203e0780e81c03405c0881001a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record063_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record063) (record063.maps 7) (record063.inverseMaps 7) record063_frame007_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record063) (record063.maps 7) (record063.inverseMaps 7) record063_frame007_indices (Fin.ofNat record063.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record063_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record063) (record063.maps 7)
      (record063.inverseMaps 7) record063_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record063_frame007_links_0000 record063_frame007_links_0064)
theorem record063_frame007_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 7 :=
  of_group record063 7 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record063_frame007_indices record063_frame007_graph record063_frame007_links
def record063_frame008_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0558.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0558.count (({ width := 7, code := 0x1fbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record063_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0558.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0558.localPairCheck (embedding (N := 44310) record063) (record063.maps 8) (record063.inverseMaps 8) record063_frame008_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0558.localPairCheck (embedding (N := 44310) record063) (record063.maps 8) (record063.inverseMaps 8) record063_frame008_indices (Fin.ofNat record063.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record063_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0558.localPairCheck (embedding (N := 44310) record063) (record063.maps 8)
      (record063.inverseMaps 8) record063_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record063_frame008_links_0000 record063_frame008_links_0064)
theorem record063_frame008_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 8 :=
  of_group record063 8 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group0558
    Papers.RationalityTen.SharedFrameCatalogue.group0558_facts record063_frame008_indices record063_frame008_graph record063_frame008_links
def record063_frame009_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0267.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0267.count (({ width := 8, code := 0xfefdfcfbfaf9f8f7f6f4f3f2f1f0efeae9e8e7e6e5e3e2e1dfdedddcdbdad4d3cac9bdbbb9b7b5b3b1afadaba9a7a5a39d9c91908f8e8c88878683817f7e7d7c6e6d6c6b686362615e5b58575655524e4c484643403d383633312c2b2a29282726252423221d1c1b1a19181716151413120d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record063_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0267.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0267.localPairCheck (embedding (N := 44310) record063) (record063.maps 9) (record063.inverseMaps 9) record063_frame009_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0267.localPairCheck (embedding (N := 44310) record063) (record063.maps 9) (record063.inverseMaps 9) record063_frame009_indices (Fin.ofNat record063.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record063_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0267.localPairCheck (embedding (N := 44310) record063) (record063.maps 9)
      (record063.inverseMaps 9) record063_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record063_frame009_links_0000 record063_frame009_links_0064)
theorem record063_frame009_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 9 :=
  of_group record063 9 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group0267
    Papers.RationalityTen.SharedFrameCatalogue.group0267_facts record063_frame009_indices record063_frame009_graph record063_frame009_links
def record063_frame010_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0133.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0133.count (({ width := 7, code := 0x1fbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record063_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0133.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0133.localPairCheck (embedding (N := 44310) record063) (record063.maps 10) (record063.inverseMaps 10) record063_frame010_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0133.localPairCheck (embedding (N := 44310) record063) (record063.maps 10) (record063.inverseMaps 10) record063_frame010_indices (Fin.ofNat record063.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record063_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0133.localPairCheck (embedding (N := 44310) record063) (record063.maps 10)
      (record063.inverseMaps 10) record063_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record063_frame010_links_0000 record063_frame010_links_0064)
theorem record063_frame010_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 10 :=
  of_group record063 10 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group0133
    Papers.RationalityTen.SharedFrameCatalogue.group0133_facts record063_frame010_indices record063_frame010_graph record063_frame010_links
def record063_frame011_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0265.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0265.count (({ width := 8, code := 0xe2e1e0dfdedddcdbdad8d7d6d5d4d3cecdcccbcac9c7c6c5c3c2c1c0bfbeb8b7b0afa9a7a5a3a19f9d9b99979593918f8b8a7f7e7d7c7a767574716f6d6c6b6a6261605f5d5958575452504f4e4d4a4644403e3c3a3834322f2d2827262524232221201f1e191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record063_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0265.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0265.localPairCheck (embedding (N := 44310) record063) (record063.maps 11) (record063.inverseMaps 11) record063_frame011_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0265.localPairCheck (embedding (N := 44310) record063) (record063.maps 11) (record063.inverseMaps 11) record063_frame011_indices (Fin.ofNat record063.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record063_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0265.localPairCheck (embedding (N := 44310) record063) (record063.maps 11)
      (record063.inverseMaps 11) record063_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record063_frame011_links_0000 record063_frame011_links_0064)
theorem record063_frame011_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 11 :=
  of_group record063 11 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group0265
    Papers.RationalityTen.SharedFrameCatalogue.group0265_facts record063_frame011_indices record063_frame011_graph record063_frame011_links
def record063_frame012_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0266.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0266.count (({ width := 8, code := 0xa2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a89888786858483807f7877767574737271706f6e6d6c6b6867605f5e5d5c5b5a595857565554534c4b4a494745444342403e3d3c3b3a3837353432302e2c2b2a292827262524232221201f1e1d1c1b1a19181716151413120d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record063_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0266.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0266.localPairCheck (embedding (N := 44310) record063) (record063.maps 12) (record063.inverseMaps 12) record063_frame012_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0266.localPairCheck (embedding (N := 44310) record063) (record063.maps 12) (record063.inverseMaps 12) record063_frame012_indices (Fin.ofNat record063.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record063_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0266.localPairCheck (embedding (N := 44310) record063) (record063.maps 12)
      (record063.inverseMaps 12) record063_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record063_frame012_links_0000 record063_frame012_links_0064)
theorem record063_frame012_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 12 :=
  of_group record063 12 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group0266
    Papers.RationalityTen.SharedFrameCatalogue.group0266_facts record063_frame012_indices record063_frame012_graph record063_frame012_links
def record063_frame013_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0132.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0132.count (({ width := 7, code := 0x1fbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record063_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0132.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0132.localPairCheck (embedding (N := 44310) record063) (record063.maps 13) (record063.inverseMaps 13) record063_frame013_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0132.localPairCheck (embedding (N := 44310) record063) (record063.maps 13) (record063.inverseMaps 13) record063_frame013_indices (Fin.ofNat record063.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record063_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0132.localPairCheck (embedding (N := 44310) record063) (record063.maps 13)
      (record063.inverseMaps 13) record063_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record063_frame013_links_0000 record063_frame013_links_0064)
theorem record063_frame013_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 13 :=
  of_group record063 13 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group0132
    Papers.RationalityTen.SharedFrameCatalogue.group0132_facts record063_frame013_indices record063_frame013_graph record063_frame013_links
def record063_frame014_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0263.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0263.count (({ width := 7, code := 0x1fbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record063_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0263.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0263.localPairCheck (embedding (N := 44310) record063) (record063.maps 14) (record063.inverseMaps 14) record063_frame014_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0263.localPairCheck (embedding (N := 44310) record063) (record063.maps 14) (record063.inverseMaps 14) record063_frame014_indices (Fin.ofNat record063.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record063_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0263.localPairCheck (embedding (N := 44310) record063) (record063.maps 14)
      (record063.inverseMaps 14) record063_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record063_frame014_links_0000 record063_frame014_links_0064)
theorem record063_frame014_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 14 :=
  of_group record063 14 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group0263
    Papers.RationalityTen.SharedFrameCatalogue.group0263_facts record063_frame014_indices record063_frame014_graph record063_frame014_links
def record063_frame015_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0131.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0131.count (({ width := 7, code := 0x1fbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record063_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0131.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0131.localPairCheck (embedding (N := 44310) record063) (record063.maps 15) (record063.inverseMaps 15) record063_frame015_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0131.localPairCheck (embedding (N := 44310) record063) (record063.maps 15) (record063.inverseMaps 15) record063_frame015_indices (Fin.ofNat record063.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record063_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0131.localPairCheck (embedding (N := 44310) record063) (record063.maps 15)
      (record063.inverseMaps 15) record063_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record063_frame015_links_0000 record063_frame015_links_0064)
theorem record063_frame015_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 15 :=
  of_group record063 15 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group0131
    Papers.RationalityTen.SharedFrameCatalogue.group0131_facts record063_frame015_indices record063_frame015_graph record063_frame015_links
def record063_frame016_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0264.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0264.count (({ width := 7, code := 0x1fbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record063_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0264.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0264.localPairCheck (embedding (N := 44310) record063) (record063.maps 16) (record063.inverseMaps 16) record063_frame016_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0264.localPairCheck (embedding (N := 44310) record063) (record063.maps 16) (record063.inverseMaps 16) record063_frame016_indices (Fin.ofNat record063.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record063_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0264.localPairCheck (embedding (N := 44310) record063) (record063.maps 16)
      (record063.inverseMaps 16) record063_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record063_frame016_links_0000 record063_frame016_links_0064)
theorem record063_frame016_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 16 :=
  of_group record063 16 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group0264
    Papers.RationalityTen.SharedFrameCatalogue.group0264_facts record063_frame016_indices record063_frame016_graph record063_frame016_links
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (Fin.cases (record063_frame001_supported hcells) (Fin.cases (record063_frame002_supported hcells) (Fin.cases (record063_frame003_supported hcells) (Fin.cases (record063_frame004_supported hcells) (Fin.cases (record063_frame005_supported hcells) (Fin.cases (record063_frame006_supported hcells) (Fin.cases (record063_frame007_supported hcells) (Fin.cases (record063_frame008_supported hcells) (Fin.cases (record063_frame009_supported hcells) (Fin.cases (record063_frame010_supported hcells) (Fin.cases (record063_frame011_supported hcells) (Fin.cases (record063_frame012_supported hcells) (Fin.cases (record063_frame013_supported hcells) (Fin.cases (record063_frame014_supported hcells) (Fin.cases (record063_frame015_supported hcells) (Fin.cases (record063_frame016_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))
#print axioms record063_frames_supported
theorem record064_frame000_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) :
    Supported record064 0 :=
  of_identity record064 0 (by decide +kernel)
def record064_frame001_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x30a1839acdd6029354549e1cc3a53d27f93546923190e686a430215709d7b03bb5bcebfd5efabc9572a614d525592748e946ca30d15e8244079f9cfa67c53d39b24d565be2c294b48ec4222030ed474a38f1bd8bc05b62b314f8a444e622b10e88043d41dc0ea86b434a1960c405d02dc13c097049c22410b08283f81de0db04802080d805f02b0150094034013807803801600a004c024010007802c0120070018008002000 } : Fields).get c.val)
theorem record064_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record064) (record064.maps 1) (record064.inverseMaps 1) record064_frame001_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record064) (record064.maps 1) (record064.inverseMaps 1) record064_frame001_indices (Fin.ofNat record064.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record064_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record064) (record064.maps 1)
      (record064.inverseMaps 1) record064_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record064_frame001_links_0000 record064_frame001_links_0064)
theorem record064_frame001_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) : Supported record064 1 :=
  of_group record064 1 (embedding record064) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record064_frame001_indices record064_frame001_graph record064_frame001_links
theorem record064_frames_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) :
    ∀ f : Fin record064.g, Supported record064 f :=
  (Fin.cases (record064_frame000_supported hcells) (Fin.cases (record064_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record064_frames_supported
theorem record065_frame000_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) :
    Supported record065 0 :=
  of_identity record065 0 (by decide +kernel)
theorem record065_frames_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) :
    ∀ f : Fin record065.g, Supported record065 f :=
  (Fin.cases (record065_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record065_frames_supported
theorem record066_frame000_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSix0.cells (embedding record066 c)) :
    Supported record066 0 :=
  of_identity record066 0 (by decide +kernel)
theorem record066_frames_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSix0.cells (embedding record066 c)) :
    ∀ f : Fin record066.g, Supported record066 f :=
  (Fin.cases (record066_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record066_frames_supported
theorem record067_frame000_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSix0.cells (embedding record067 c)) :
    Supported record067 0 :=
  of_identity record067 0 (by decide +kernel)
theorem record067_frames_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSix0.cells (embedding record067 c)) :
    ∀ f : Fin record067.g, Supported record067 f :=
  (Fin.cases (record067_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record067_frames_supported
theorem record068_frame000_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c)) :
    Supported record068 0 :=
  of_identity record068 0 (by decide +kernel)
theorem record068_frames_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c)) :
    ∀ f : Fin record068.g, Supported record068 f :=
  (Fin.cases (record068_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record068_frames_supported
theorem record069_frame000_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSix0.cells (embedding record069 c)) :
    Supported record069 0 :=
  of_identity record069 0 (by decide +kernel)
def record069_frame001_indices (c : Fin record069.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x157cab45576a87536a6ed33266131995f4aa232117a8a244de24911288343c61ab0bc851c26e11b07c824bde5ee0f67797b425924aa4516a6492a28fd478238d13683240ba030f2e75b39d9c20d285992c19468a0e4f227191908ae434210903c8023ee1f08ca86282ab14c0a0c4e81f50f407143641a00c905fc2e413a07e83d81d20d705b81840be05d02b015009c04a02400f807403501980a404e02500f0070028012008002400e0050018008002000 } : Fields).get c.val)
theorem record069_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record069.data.requiredEdges q = true := by decide +kernel
theorem record069_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record069) (record069.maps 1) (record069.inverseMaps 1) record069_frame001_indices (Fin.ofNat record069.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record069_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record069) (record069.maps 1) (record069.inverseMaps 1) record069_frame001_indices (Fin.ofNat record069.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record069_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record069) (record069.maps 1)
      (record069.inverseMaps 1) record069_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record069_frame001_links_0000 record069_frame001_links_0064)
theorem record069_frame001_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSix0.cells (embedding record069 c)) : Supported record069 1 :=
  of_group record069 1 (embedding record069) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record069_frame001_indices record069_frame001_graph record069_frame001_links
theorem record069_frames_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSix0.cells (embedding record069 c)) :
    ∀ f : Fin record069.g, Supported record069 f :=
  (Fin.cases (record069_frame000_supported hcells) (Fin.cases (record069_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record069_frames_supported
theorem record070_frame000_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSix0.cells (embedding record070 c)) :
    Supported record070 0 :=
  of_identity record070 0 (by decide +kernel)
theorem record070_frames_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSix0.cells (embedding record070 c)) :
    ∀ f : Fin record070.g, Supported record070 f :=
  (Fin.cases (record070_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record070_frames_supported
theorem record071_frame000_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSix0.cells (embedding record071 c)) :
    Supported record071 0 :=
  of_identity record071 0 (by decide +kernel)
theorem record071_frames_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSix0.cells (embedding record071 c)) :
    ∀ f : Fin record071.g, Supported record071 f :=
  (Fin.cases (record071_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record071_frames_supported
theorem record072_frame000_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSix0.cells (embedding record072 c)) :
    Supported record072 0 :=
  of_identity record072 0 (by decide +kernel)
theorem record072_frames_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSix0.cells (embedding record072 c)) :
    ∀ f : Fin record072.g, Supported record072 f :=
  (Fin.cases (record072_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record072_frames_supported
theorem record073_frame000_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) :
    Supported record073 0 :=
  of_identity record073 0 (by decide +kernel)
def record073_frame001_indices (c : Fin record073.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xc34d806b85571ab4549ea313a99c84c3a53d27f93548561810ab84ebba9b5ed2664030297feaf2572aae14c89a94a9a4e51d88d6461a2c905480f4001f9cf8a7b13d39d30dac6cb2df16c4b0853023a907c80a3b81d10e3c6fc2f616d8b3056629113e89cc47222410e883c3c61dc0d686583101820b704d425c11908904141fc0ef06d829412a08e036017c0ac05401a009c03c01c00a8050024011008002c0120070018008002000 } : Fields).get c.val)
theorem record073_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record073.data.requiredEdges q = true := by decide +kernel
theorem record073_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record073) (record073.maps 1) (record073.inverseMaps 1) record073_frame001_indices (Fin.ofNat record073.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record073_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record073) (record073.maps 1) (record073.inverseMaps 1) record073_frame001_indices (Fin.ofNat record073.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record073_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record073) (record073.maps 1)
      (record073.inverseMaps 1) record073_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record073_frame001_links_0000 record073_frame001_links_0064)
theorem record073_frame001_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) : Supported record073 1 :=
  of_group record073 1 (embedding record073) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record073_frame001_indices record073_frame001_graph record073_frame001_links
theorem record073_frames_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) :
    ∀ f : Fin record073.g, Supported record073 f :=
  (Fin.cases (record073_frame000_supported hcells) (Fin.cases (record073_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record073_frames_supported
theorem record074_frame000_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    Supported record074 0 :=
  of_identity record074 0 (by decide +kernel)
theorem record074_frames_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    ∀ f : Fin record074.g, Supported record074 f :=
  (Fin.cases (record074_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record074_frames_supported
theorem record075_frame000_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) :
    Supported record075 0 :=
  of_identity record075 0 (by decide +kernel)
def record075_frame001_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x30a1839bffdfceb4f58ca4b51528133c39b64d8d76aaf253a26752aa937474236518689c43da0c504880f3f59f4cf8a7a434096f8a80469210900c7683a51c78da068e2fd1780b6c56e29f14889c045621d0f987ac3b81ce0d6869432c18809d84b824011208604101fc0ef07483841b60a904802080d806a030015009403401900a003801600a004c024010007002c0120070020008002000 } : Fields).get c.val)
theorem record075_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record075) (record075.maps 1) (record075.inverseMaps 1) record075_frame001_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record075) (record075.maps 1) (record075.inverseMaps 1) record075_frame001_indices (Fin.ofNat record075.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record075_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record075) (record075.maps 1)
      (record075.inverseMaps 1) record075_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record075_frame001_links_0000 record075_frame001_links_0064)
theorem record075_frame001_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) : Supported record075 1 :=
  of_group record075 1 (embedding record075) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record075_frame001_indices record075_frame001_graph record075_frame001_links
theorem record075_frames_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) :
    ∀ f : Fin record075.g, Supported record075 f :=
  (Fin.cases (record075_frame000_supported hcells) (Fin.cases (record075_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record075_frames_supported
theorem record076_frame000_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) :
    Supported record076 0 :=
  of_identity record076 0 (by decide +kernel)
theorem record076_frames_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) :
    ∀ f : Fin record076.g, Supported record076 f :=
  (Fin.cases (record076_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record076_frames_supported
theorem record077_frame000_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) :
    Supported record077 0 :=
  of_identity record077 0 (by decide +kernel)
theorem record077_frames_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) :
    ∀ f : Fin record077.g, Supported record077 f :=
  (Fin.cases (record077_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record077_frames_supported
theorem record078_frame000_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSix0.cells (embedding record078 c)) :
    Supported record078 0 :=
  of_identity record078 0 (by decide +kernel)
theorem record078_frames_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSix0.cells (embedding record078 c)) :
    ∀ f : Fin record078.g, Supported record078 f :=
  (Fin.cases (record078_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record078_frames_supported
theorem record079_frame000_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSix0.cells (embedding record079 c)) :
    Supported record079 0 :=
  of_identity record079 0 (by decide +kernel)
def record079_frame001_indices (c : Fin record079.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x613306b5a7ac6525a8133c19ba4d965952a8944c9964a923b915c82e3ef15b8a244a61cb0da826c059deee205daacd15acab652f26a91b28bf44e21f50487fd3f59f4cf8e7a43409800b4458229511d874a38b1b40d245e02c915b8a7c52627011588743e61eb0ee073831e1880bd85d424e12008203f81e00e8070836c12008203901a80c205d02a0128074032014809403801600a004c02401000700280120070028008002000 } : Fields).get c.val)
theorem record079_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record079.data.requiredEdges q = true := by decide +kernel
theorem record079_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record079) (record079.maps 1) (record079.inverseMaps 1) record079_frame001_indices (Fin.ofNat record079.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record079_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record079) (record079.maps 1) (record079.inverseMaps 1) record079_frame001_indices (Fin.ofNat record079.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record079_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record079) (record079.maps 1)
      (record079.inverseMaps 1) record079_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record079_frame001_links_0000 record079_frame001_links_0064)
theorem record079_frame001_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSix0.cells (embedding record079 c)) : Supported record079 1 :=
  of_group record079 1 (embedding record079) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record079_frame001_indices record079_frame001_graph record079_frame001_links
theorem record079_frames_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSix0.cells (embedding record079 c)) :
    ∀ f : Fin record079.g, Supported record079 f :=
  (Fin.cases (record079_frame000_supported hcells) (Fin.cases (record079_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record079_frames_supported
theorem record080_frame000_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSix0.cells (embedding record080 c)) :
    Supported record080 0 :=
  of_identity record080 0 (by decide +kernel)
theorem record080_frames_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSix0.cells (embedding record080 c)) :
    ∀ f : Fin record080.g, Supported record080 f :=
  (Fin.cases (record080_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record080_frames_supported
theorem record081_frame000_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) :
    Supported record081 0 :=
  of_identity record081 0 (by decide +kernel)
theorem record081_frames_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) :
    ∀ f : Fin record081.g, Supported record081 f :=
  (Fin.cases (record081_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record081_frames_supported
theorem record082_frame000_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSix0.cells (embedding record082 c)) :
    Supported record082 0 :=
  of_identity record082 0 (by decide +kernel)
theorem record082_frames_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSix0.cells (embedding record082 c)) :
    ∀ f : Fin record082.g, Supported record082 f :=
  (Fin.cases (record082_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record082_frames_supported
theorem record083_frame000_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSix0.cells (embedding record083 c)) :
    Supported record083 0 :=
  of_identity record083 0 (by decide +kernel)
theorem record083_frames_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSix0.cells (embedding record083 c)) :
    ∀ f : Fin record083.g, Supported record083 f :=
  (Fin.cases (record083_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record083_frames_supported
theorem record084_frame000_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSix0.cells (embedding record084 c)) :
    Supported record084 0 :=
  of_identity record084 0 (by decide +kernel)
theorem record084_frames_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSix0.cells (embedding record084 c)) :
    ∀ f : Fin record084.g, Supported record084 f :=
  (Fin.cases (record084_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record084_frames_supported
theorem record085_frame000_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) :
    Supported record085 0 :=
  of_identity record085 0 (by decide +kernel)
theorem record085_frames_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) :
    ∀ f : Fin record085.g, Supported record085 f :=
  (Fin.cases (record085_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record085_frames_supported
theorem record086_frame000_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) :
    Supported record086 0 :=
  of_identity record086 0 (by decide +kernel)
theorem record086_frames_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) :
    ∀ f : Fin record086.g, Supported record086 f :=
  (Fin.cases (record086_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record086_frames_supported
theorem record087_frame000_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) :
    Supported record087 0 :=
  of_identity record087 0 (by decide +kernel)
theorem record087_frames_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) :
    ∀ f : Fin record087.g, Supported record087 f :=
  (Fin.cases (record087_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record087_frames_supported
theorem record088_frame000_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) :
    Supported record088 0 :=
  of_identity record088 0 (by decide +kernel)
theorem record088_frames_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) :
    ∀ f : Fin record088.g, Supported record088 f :=
  (Fin.cases (record088_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record088_frames_supported
theorem record089_frame000_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) :
    Supported record089 0 :=
  of_identity record089 0 (by decide +kernel)
theorem record089_frames_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) :
    ∀ f : Fin record089.g, Supported record089 f :=
  (Fin.cases (record089_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record089_frames_supported
theorem record090_frame000_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) :
    Supported record090 0 :=
  of_identity record090 0 (by decide +kernel)
theorem record090_frames_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) :
    ∀ f : Fin record090.g, Supported record090 f :=
  (Fin.cases (record090_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record090_frames_supported
theorem record091_frame000_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) :
    Supported record091 0 :=
  of_identity record091 0 (by decide +kernel)
theorem record091_frames_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) :
    ∀ f : Fin record091.g, Supported record091 f :=
  (Fin.cases (record091_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record091_frames_supported
theorem record092_frame000_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) :
    Supported record092 0 :=
  of_identity record092 0 (by decide +kernel)
theorem record092_frames_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) :
    ∀ f : Fin record092.g, Supported record092 f :=
  (Fin.cases (record092_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record092_frames_supported
theorem record093_frame000_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) :
    Supported record093 0 :=
  of_identity record093 0 (by decide +kernel)
theorem record093_frames_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) :
    ∀ f : Fin record093.g, Supported record093 f :=
  (Fin.cases (record093_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record093_frames_supported
theorem record094_frame000_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) :
    Supported record094 0 :=
  of_identity record094 0 (by decide +kernel)
theorem record094_frames_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) :
    ∀ f : Fin record094.g, Supported record094 f :=
  (Fin.cases (record094_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record094_frames_supported
theorem record095_frame000_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) :
    Supported record095 0 :=
  of_identity record095 0 (by decide +kernel)
def record095_frame001_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x18a5c34e08b0335c2a93d46274f38e985ca9e51126c929c8ea4550727753a6dbfadc1690b20186ebff5e5ae9d5e4ae555c296535296149ca3bd1ac8b244e20e10168003f59f20f627a43a61c0cd9669733996f8b6258429291d485a4051dd8e886fc3681820b5c5982b714a09f44e023911208743f41e30e706b432c1880c105f026a12008c844c2080fe070836c16608e03501840b005401900a404001c00a8050024011007002c0120070028008002000 } : Fields).get c.val)
theorem record095_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record095) (record095.maps 1) (record095.inverseMaps 1) record095_frame001_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record095) (record095.maps 1) (record095.inverseMaps 1) record095_frame001_indices (Fin.ofNat record095.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record095_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record095) (record095.maps 1)
      (record095.inverseMaps 1) record095_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record095_frame001_links_0000 record095_frame001_links_0064)
theorem record095_frame001_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) : Supported record095 1 :=
  of_group record095 1 (embedding record095) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record095_frame001_indices record095_frame001_graph record095_frame001_links
theorem record095_frames_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) :
    ∀ f : Fin record095.g, Supported record095 f :=
  (Fin.cases (record095_frame000_supported hcells) (Fin.cases (record095_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record095_frames_supported
theorem record096_frame000_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) :
    Supported record096 0 :=
  of_identity record096 0 (by decide +kernel)
theorem record096_frames_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) :
    ∀ f : Fin record096.g, Supported record096 f :=
  (Fin.cases (record096_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record096_frames_supported
theorem record097_frame000_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) :
    Supported record097 0 :=
  of_identity record097 0 (by decide +kernel)
theorem record097_frames_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) :
    ∀ f : Fin record097.g, Supported record097 f :=
  (Fin.cases (record097_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record097_frames_supported
theorem record098_frame000_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSix0.cells (embedding record098 c)) :
    Supported record098 0 :=
  of_identity record098 0 (by decide +kernel)
def record098_frame001_indices (c : Fin record098.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x283d40a9cbce0a45d2148ba457619b0b97203601a74cfa67632d1836bdb59e2cad564aa4546a9fd4d49d04dfa519270921489a3f91a48ba456228512688a4261eecf086ed36f99d0ccc65032018b0b3058a28f94449f64eb26b92b092848623e11c08d042d18b89e84d421c10707fc3e41970c384e425611c087831c12609104602000b005602a012004001e00e006802c011007802c012007002800c002000 } : Fields).get c.val)
theorem record098_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record098.data.requiredEdges q = true := by decide +kernel
theorem record098_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record098) (record098.maps 1) (record098.inverseMaps 1) record098_frame001_indices (Fin.ofNat record098.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record098_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record098) (record098.maps 1) (record098.inverseMaps 1) record098_frame001_indices (Fin.ofNat record098.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record098_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record098) (record098.maps 1)
      (record098.inverseMaps 1) record098_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record098_frame001_links_0000 record098_frame001_links_0064)
theorem record098_frame001_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSix0.cells (embedding record098 c)) : Supported record098 1 :=
  of_group record098 1 (embedding record098) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record098_frame001_indices record098_frame001_graph record098_frame001_links
theorem record098_frames_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSix0.cells (embedding record098 c)) :
    ∀ f : Fin record098.g, Supported record098 f :=
  (Fin.cases (record098_frame000_supported hcells) (Fin.cases (record098_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record098_frames_supported
theorem record099_frame000_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) :
    Supported record099 0 :=
  of_identity record099 0 (by decide +kernel)
theorem record099_frames_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) :
    ∀ f : Fin record099.g, Supported record099 f :=
  (Fin.cases (record099_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record099_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067
