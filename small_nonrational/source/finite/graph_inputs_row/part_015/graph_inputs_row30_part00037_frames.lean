module
prelude
public import GraphInputsRow30Part00037Data
public import RawFrameSupport
public import SharedFrameGroups030Checked
public import SharedFrameGroups032Checked
public import SharedFrameGroups033Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd4266dad9d4ec9ed4d1a4cd1f08c145521dd0a28413fc1fa4f8e7b43d398cca844b92378ffc78838d1bb0d0c63a30d1620ad4526280139893848a23110388043e21de0e086cc3581a60c505ec2dc1600ab84d825e127090846821610507b83c01d00b004601e40de06b03481940c805d02d01580aa05402080dc06603101680b004a02200f007403801a00c005c0260100078034014009004001c00c0050018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33796eeb2b55928853b8878427a034ff47e93e41ed8f4e6432fb95f89da4a81a20c6c5b22c615a8a5050427312709144622070e4870033e1980c8062830617c0ba05b82b01520a504f425e12108984141ec0e904e025811807903a01cc0d206403001700b405802b01540a804101e00ec06202c014009004402000f007403801a00c005c02600f0068030016009004001c00a0040018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x74a7266f168667865a6436376155fc5e15cb58f5705675535235125034fc4c74b44a549e48246944c43e4104093fd3c93c239839135533e3263192e92d82cc2bd28d27a26e25d2482382132091fe1ef1e61da1c91ba1ad1a91a119118017116416015813f13612911d11110c1070fe0f60ed0e50de0da0cf0c60be0ba0af0a509e09909108a08908206a06905e05a05505204c03403202702301e01c01501401000b007002001000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x6fc355d97cc34602af0d728b63590abc959aab5533a8613e29b64a6a4bd23290e44d21f10cc85b421a0d0fd07b33a39cece1269d3489980cae6122ec96b8b0653028d143c9f44a324692088da45f22c90907da3ce1d28e186c43401928bf05e42df1608a7c50825b12888f844221b0fb073435218d0bd85902a813b09604882300fe07783941b60cc059829413e095047023410c06c03581800b805702a0130068032013808c03c01c00a805002000b0038008002000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0x1ff3da776ebdd63836ead61a7b4065ec29712d759ab015e2aa5429f539a634aa93525a4746e8ad14a0d4027c8f01d7394704d49a434062cbe96a2b6564a09362504788990f2103f8748e31ae334638bc16428c4d09512022c3b0710d81942e05b0a61402704909011c1f03a06e0c81882f0520a01282203e0740e0180280400700d0120200380600a00800800 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xdb667cafd15baa8b51c275d2ae9344872305158842417a034ff47e93d39b00b52557282128c8464001ed0e346f030e17d8b6458c2b513988c442820f10307e03ca1de0eb06cc35a1a50cc06403141820b705602a414a0a204bc24211908604141d208f04602240d806903181800ba05a02c01580aa05402880d006202b014009404402000f007403801a00c00580260110080034016009004001c00a0040018008002000 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x67cab754c2a38510a75934695b499a3a51828aa428a10901a7e93d396a4a5a50427692888de4271ff8ed471a37618e8c385b22b513988c442820710087a83bc1b30d686943301900c505d02dc1600ab8510278136097849c24211a08584141ee08f04602240f206c03481940ba05a02c01580aa0540288104068031016809404402000f007403801a00c00580260100078034016009004001c00c0050018008002000 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x67f338d86abdf58229d146ca264ee267d3008e7461a2ad0147fa3f49f14f6c7953809aacba054028113c895046b2260ecc71e37716b0b1856a291141098448a239115888840e2010fc87cc3d81dc0ea86cc35a19e0c806282e81670ac052827a13509704842240fe07783a411a08603801b00d406002e016c0ac05502a013807003401900a004802300f007403801a00c0054028013008003c01c00b004802000e0040018008002000 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xe9067f338d998c7e61aaf7d76aba0595ac0d564a8a51b28994249dc4aca39d1868ab44c21e10a880a3fd1fa0f8a7b63d31e54e947013559a04cd85f72e795f8aac50227913789504251d98e3c6ee3641a20c805ac2c615a0a44504272130891446222b111887442c20710087e43e61ec0ee075439c1c90e006c833e1900c4860c2e816d0b3856029413d09704481fc0f607783a41c407003601800be05c02d81540a803801a00a004e024011807403801a00c0050026012008003c01c00c005802000e0040018008002000 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
def record024_frame002_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xd3260ab03580cbce5cc2dd96d2b6357aab5552aa7552128f146a9f94bda45920a8fd47b234114684e42020c101c8003f81f9cf447563951c74e2e6b0348193cc5e5fe2fc97ccb8055628093d09dc4e9266929c8ca45c22810d885a42120d0f8075a39e1c68df86de34d19f0cb463c30f17e8bd85e02e21660a844d024c11e88b84242030fd076836c1920bb051424c11a08483e41d207003601800be05c02d81540a803801a00a004e024011807403801a00c0050026012008003c01c00c005802000e0040018008002000 } : Fields).get c.val)
theorem record024_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record024_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record024) (record024.maps 2)
      (record024.inverseMaps 2) record024_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record024_frame002_links_0000 record024_frame002_links_0064)
theorem record024_frame002_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 2 :=
  of_group record024 2 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record024_frame002_indices record024_frame002_graph record024_frame002_links
def record024_frame003_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x7416e06d96d26b369367766c6676336215fa5e85c75c25bb5a456352a51c51550e4fb4e74c04b94b149c49348948146344442741c4173e13cf3a739537737236b35430c2d92cc2c52be2ab29726c26325924724023823121b2051fd1f51ee1e71d41cc1c41bd1b61ab1a71a319f19618817516315a15214013713112811d1131050eb0d90d50cf0c90c307006c06005f05c05b05505403803402802702402301d01c01a01801401301201000f00e00c00b008007004003002001000 } : Fields).get c.val)
theorem record024_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record024) (record024.maps 3) (record024.inverseMaps 3) record024_frame003_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record024) (record024.maps 3) (record024.inverseMaps 3) record024_frame003_indices (Fin.ofNat record024.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record024_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record024) (record024.maps 3)
      (record024.inverseMaps 3) record024_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record024_frame003_links_0000 record024_frame003_links_0064)
theorem record024_frame003_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 3 :=
  of_group record024 3 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record024_frame003_indices record024_frame003_graph record024_frame003_links
def record024_frame004_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xca05e62ecd73ab7f5b2acd5638b14569aae9512a7251aa88d4209ef4c724b12068e846922c911e846419a078fe27dd3e39ec4f2076d3a29cbce4c6e13639a5ccf463f3189880bfa5b12b2951ca6852628513b095c4a124991b88c045122110607de3e11e98f1477a39a1c60de86d836219d8c9c62a3061790b44550280137096c46a22310807b43a01b90cb854024211008003d01ce07003601800be05c02d81540a803801a00a004e024011807403801a00c0050026012008003c01c00c005802000e0040018008002000 } : Fields).get c.val)
theorem record024_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record024) (record024.maps 4) (record024.inverseMaps 4) record024_frame004_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record024) (record024.maps 4) (record024.inverseMaps 4) record024_frame004_indices (Fin.ofNat record024.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record024_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record024) (record024.maps 4)
      (record024.inverseMaps 4) record024_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record024_frame004_links_0000 record024_frame004_links_0064)
theorem record024_frame004_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 4 :=
  of_group record024 4 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record024_frame004_indices record024_frame004_graph record024_frame004_links
def record024_frame005_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6d466d66766364b63862a6246215f15e15ca5c05a75a359f58654d51d51250a5064f34dc4b04a749d48447e47346b45444143442e42b3fa3e83cf3c53aa3a73a338f36033833032b3293183002d92d52cd2ba2b52b02a928926c26425925324e23c23622c22421c2102092051fd1eb1cf1b019b19018917316d16414b1361251150f50e00d50c80be0b206a06605a05905605504f04e03803402802702402301d01c01a01801401301201000f00e00c00b008007004003002001000 } : Fields).get c.val)
theorem record024_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record024) (record024.maps 5) (record024.inverseMaps 5) record024_frame005_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record024) (record024.maps 5) (record024.inverseMaps 5) record024_frame005_indices (Fin.ofNat record024.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record024_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record024) (record024.maps 5)
      (record024.inverseMaps 5) record024_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record024_frame005_links_0000 record024_frame005_links_0064)
theorem record024_frame005_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 5 :=
  of_group record024 5 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record024_frame005_indices record024_frame005_graph record024_frame005_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (Fin.cases (record024_frame002_supported hcells) (Fin.cases (record024_frame003_supported hcells) (Fin.cases (record024_frame004_supported hcells) (Fin.cases (record024_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x72a6fa66e65f65761b59658b57855a54e53852b51050b5024f44e74cd4c44bc4af4a649e49a49047d46945d45744b40e3dc3ca3b83ab37d37436a34a34333931830c3062f02e32be2a729227b27224023022720c1fb1f41da1d11c31b31a41801711541461341291211141040f60f00eb0de0d70d10cb0c50bf0ba08608206c06805f05b05305203703603303202f02902802502401f01d01c01801401201000e009008007006005002001000 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
def record025_frame002_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x36d9a88c14606301d6d2a4351ea8d138699f4af24e92088ff47ba34914485041e20b90207fc3f71f9cf447563951c74e2e6e43371834bfe5f82f91634b0257329c14b0a3c4f327713a89944a6233913887041f20d0ebc71a37e1a78cb463c2fd17b8bc059e2a212d09284402100fd07b43ae1b50c185a42be15209c04b824c11b08503d81d009204701b80d406102e81540a803701b00cc06402f01480a004a02400f807403801800a004802000e004802000e0060028008002000 } : Fields).get c.val)
theorem record025_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record025_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record025) (record025.maps 2)
      (record025.inverseMaps 2) record025_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record025_frame002_links_0000 record025_frame002_links_0064)
theorem record025_frame002_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 2 :=
  of_group record025 2 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record025_frame002_indices record025_frame002_graph record025_frame002_links
def record025_frame003_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0xffdf43b0756e9dc6b596aad3997b22624c297a2f05d6b896bac0578ad9552a5542a714b29050aa013f2744c895927a4a48c8ad14a25428841069f53e27b8f01d73826d0d49a03385f4b896d2c656cac94928c5009b12822643c7f0f61e03a4718d718e2f05b8b214828c4f09a12a240458710dc17c2e0530a01242403706c0cc1902f0520a01282403e0740e0180280480800e0120200380600a00800800 } : Fields).get c.val)
theorem record025_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record025) (record025.maps 3) (record025.inverseMaps 3) record025_frame003_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record025) (record025.maps 3) (record025.inverseMaps 3) record025_frame003_indices (Fin.ofNat record025.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record025_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record025) (record025.maps 3)
      (record025.inverseMaps 3) record025_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record025_frame003_links_0000 record025_frame003_links_0064)
theorem record025_frame003_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 3 :=
  of_group record025 3 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record025_frame003_indices record025_frame003_graph record025_frame003_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (Fin.cases (record025_frame002_supported hcells) (Fin.cases (record025_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1afcc6858ca80d3749a64d025b92d095149b24a123690c47fa3c11d48dc3cd19b8c0c5d12e014f0a564f2255921c8ce44221190047e23d11cb8d886a22cd15e0a0c4782180fc074c3681920c105882ac14809d04cc25811708804101ec0ef074824811a06f035019c0ca06103001740b605702b01540a803701900bc05a029014009404601f00f007403801a00c00500260100070028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
def record027_frame002_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0x1ecbb0704d659fb2d650c2181af45c0b55662c056eaa953a9c4e893d1c22b45282d031f53c0754e59c136e6a4d219c3185ecbb15b2b25249a12823e44c840fe1f23c0748de1a4330638b81642984f09a12a1c4368600b81642b8530a41402784b094124240370640bc168290500941181f03c0740e01a0300500981001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record027_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record027_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record027) (record027.maps 2)
      (record027.inverseMaps 2) record027_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record027_frame002_links_0000 record027_frame002_links_0064)
theorem record027_frame002_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 2 :=
  of_group record027 2 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record027_frame002_indices record027_frame002_graph record027_frame002_links
def record027_frame003_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1ca8cfb5b3a8e93b09a14c8a42d1f48bf43aa14506080c3f49f1cf6e795319941894846d22e8f5c78c38b1a08c745f82d815a8a4c50626112288c44561f90f987703821b30d3065c31417b0ba859c2c01520a204f426c12108d04301fc0f7078024811a06f035019c0ca06103001740b605702b01540a803701900bc05a029014009404601f00f007403801a00c00500260100070028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record027_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record027) (record027.maps 3) (record027.inverseMaps 3) record027_frame003_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record027) (record027.maps 3) (record027.inverseMaps 3) record027_frame003_indices (Fin.ofNat record027.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record027_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record027) (record027.maps 3)
      (record027.inverseMaps 3) record027_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record027_frame003_links_0000 record027_frame003_links_0064)
theorem record027_frame003_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 3 :=
  of_group record027 3 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record027_frame003_indices record027_frame003_graph record027_frame003_links
def record027_frame004_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x248478862f91e6bbe772e65c9b836e4da5b0b5569acfd9db2f5e4a954727c4ec95d292444668a9112154147f8fd1f03bc72ce219631e600b31562924e4949172204047e8f21d03906f8cd18e2ec580ad1501fc3d8660c21782e0580ae1502904e09a130258370640bc168290500941181f03c0740e01a0300500981001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record027_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record027) (record027.maps 4) (record027.inverseMaps 4) record027_frame004_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record027) (record027.maps 4) (record027.inverseMaps 4) record027_frame004_indices (Fin.ofNat record027.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record027_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record027) (record027.maps 4)
      (record027.inverseMaps 4) record027_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record027_frame004_links_0000 record027_frame004_links_0064)
theorem record027_frame004_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 4 :=
  of_group record027 4 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record027_frame004_indices record027_frame004_graph record027_frame004_links
def record027_frame005_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x1ce34b5feab948a8950e9c537a644b294d272474848ed1ca333f26a0c59833025acb495e2a6534a41412784d49992d2444688c1022003d4750e41be360698cc194310608bf17a2f05d8b816e2d4598b21622384486d0d01943185f0bc16c2c8550a814c290370640bc168290500941181f03c0740e01a0300500981001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record027_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record027) (record027.maps 5) (record027.inverseMaps 5) record027_frame005_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record027) (record027.maps 5) (record027.inverseMaps 5) record027_frame005_indices (Fin.ofNat record027.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record027_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record027) (record027.maps 5)
      (record027.inverseMaps 5) record027_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record027_frame005_links_0000 record027_frame005_links_0064)
theorem record027_frame005_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 5 :=
  of_group record027 5 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record027_frame005_indices record027_frame005_graph record027_frame005_links
def record027_frame006_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0980.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0980.count (({ width := 8, code := 0xfaf5ece7dfdad9d3d2cec9c6c4c1c0bdbcbbb5b0a8a3a29c9b97928f8d8a898685847f7a7973726e69666461605d5c5b5a5856555452514f4e4d4c49484443403e3a393736333231302d2c29272322201f1c1b1a19171511100e0d0a09080706050403020100 } : Fields).get c.val)
theorem record027_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0980.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0980.localPairCheck (smallEmbedding record027) (record027.maps 6) (record027.inverseMaps 6) record027_frame006_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0980.localPairCheck (smallEmbedding record027) (record027.maps 6) (record027.inverseMaps 6) record027_frame006_indices (Fin.ofNat record027.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record027_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0980.localPairCheck (smallEmbedding record027) (record027.maps 6)
      (record027.inverseMaps 6) record027_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record027_frame006_links_0000 record027_frame006_links_0064)
theorem record027_frame006_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 6 :=
  of_group record027 6 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0980
    Papers.RationalityTen.SharedFrameCatalogue.group0980_facts record027_frame006_indices record027_frame006_graph record027_frame006_links
def record027_frame007_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0978.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0978.count (({ width := 8, code := 0xf8f4ede9e1dcdbd6d5d2cdcac8c5c3c0bfbdb9b5ada8a7a2a19e999694918f8c8b89847f7e797875706d6b68666362605f5d5b5a5956555351504f4b4a4544413f3b3a3837343332312d2c29272322201f1c1b1a19171511100e0d0a09080706050403020100 } : Fields).get c.val)
theorem record027_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0978.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0978.localPairCheck (smallEmbedding record027) (record027.maps 7) (record027.inverseMaps 7) record027_frame007_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0978.localPairCheck (smallEmbedding record027) (record027.maps 7) (record027.inverseMaps 7) record027_frame007_indices (Fin.ofNat record027.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record027_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0978.localPairCheck (smallEmbedding record027) (record027.maps 7)
      (record027.inverseMaps 7) record027_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record027_frame007_links_0000 record027_frame007_links_0064)
theorem record027_frame007_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 7 :=
  of_group record027 7 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0978
    Papers.RationalityTen.SharedFrameCatalogue.group0978_facts record027_frame007_indices record027_frame007_graph record027_frame007_links
def record027_frame008_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0497.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0497.count (({ width := 9, code := 0x33f97c1dd6d162b056ab153a551e873d994be572087c05eef479bbddcea71b85bcda693419ac55f2e56eac552993a9b4d25d269147a3112833f1f0f06e36198c05c2d1208a401e8e872371b0d06430178b85a291308c44200f87436190c05c2c1409844200e060281208038180a04018080200 } : Fields).get c.val)
theorem record027_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0497.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0497.localPairCheck (smallEmbedding record027) (record027.maps 8) (record027.inverseMaps 8) record027_frame008_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0497.localPairCheck (smallEmbedding record027) (record027.maps 8) (record027.inverseMaps 8) record027_frame008_indices (Fin.ofNat record027.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record027_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0497.localPairCheck (smallEmbedding record027) (record027.maps 8)
      (record027.inverseMaps 8) record027_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record027_frame008_links_0000 record027_frame008_links_0064)
theorem record027_frame008_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 8 :=
  of_group record027 8 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0497
    Papers.RationalityTen.SharedFrameCatalogue.group0497_facts record027_frame008_indices record027_frame008_graph record027_frame008_links
def record027_frame009_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0475.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0475.count (({ width := 9, code := 0x277379748e331489436170780bf9f4f7783b5d2e26db4192c662b0982be5cadd68b256aad50a34f2652e9147a310a83411fcf87a3c1d8e66d34198c65b2c94c9e4c250f076361a8c8622f170b4582a148a04e231107c3c1c0d86832170b05428120883c1c0d060281208038180a04018080200 } : Fields).get c.val)
theorem record027_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0475.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0475.localPairCheck (smallEmbedding record027) (record027.maps 9) (record027.inverseMaps 9) record027_frame009_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0475.localPairCheck (smallEmbedding record027) (record027.maps 9) (record027.inverseMaps 9) record027_frame009_indices (Fin.ofNat record027.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record027_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0475.localPairCheck (smallEmbedding record027) (record027.maps 9)
      (record027.inverseMaps 9) record027_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record027_frame009_links_0000 record027_frame009_links_0064)
theorem record027_frame009_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 9 :=
  of_group record027 9 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0475
    Papers.RationalityTen.SharedFrameCatalogue.group0475_facts record027_frame009_indices record027_frame009_graph record027_frame009_links
def record027_frame010_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0495.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0495.count (({ width := 9, code := 0x1faf97abc1d0e370b75b6d86ab4da2ce653218cc25e2cd5cab5529d4ca451a853c9c4c2592890452210e854220d04803e9f0ee76399bcd86731984bc582b1489c4b24904803b1d0dc6c34198c8622f170b458241107c3c1c0d86832170b05428120883c1c0d060281208038180a04018080200 } : Fields).get c.val)
theorem record027_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0495.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0495.localPairCheck (smallEmbedding record027) (record027.maps 10) (record027.inverseMaps 10) record027_frame010_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0495.localPairCheck (smallEmbedding record027) (record027.maps 10) (record027.inverseMaps 10) record027_frame010_indices (Fin.ofNat record027.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record027_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0495.localPairCheck (smallEmbedding record027) (record027.maps 10)
      (record027.inverseMaps 10) record027_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record027_frame010_links_0000 record027_frame010_links_0064)
theorem record027_frame010_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 10 :=
  of_group record027 10 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0495
    Papers.RationalityTen.SharedFrameCatalogue.group0495_facts record027_frame010_indices record027_frame010_graph record027_frame010_links
def record027_frame011_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0496.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0496.count (({ width := 9, code := 0x365a5cbe06f576badc6e169b0572ad50a450e7f3793c5a150682c0a02fd793b5d0e56db65a6cb622f576b358aa93a994ba4d1c8a43a0cfe7a3b1d4e46a3418cbe5b2c110863b1d0e06e351a0cc642f170b4582612088421f0f07438190c05c2c1409844200e060281208038180a04018080200 } : Fields).get c.val)
theorem record027_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0496.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0496.localPairCheck (smallEmbedding record027) (record027.maps 11) (record027.inverseMaps 11) record027_frame011_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0496.localPairCheck (smallEmbedding record027) (record027.maps 11) (record027.inverseMaps 11) record027_frame011_indices (Fin.ofNat record027.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record027_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0496.localPairCheck (smallEmbedding record027) (record027.maps 11)
      (record027.inverseMaps 11) record027_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record027_frame011_links_0000 record027_frame011_links_0064)
theorem record027_frame011_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 11 :=
  of_group record027 11 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0496
    Papers.RationalityTen.SharedFrameCatalogue.group0496_facts record027_frame011_indices record027_frame011_graph record027_frame011_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (Fin.cases (record027_frame002_supported hcells) (Fin.cases (record027_frame003_supported hcells) (Fin.cases (record027_frame004_supported hcells) (Fin.cases (record027_frame005_supported hcells) (Fin.cases (record027_frame006_supported hcells) (Fin.cases (record027_frame007_supported hcells) (Fin.cases (record027_frame008_supported hcells) (Fin.cases (record027_frame009_supported hcells) (Fin.cases (record027_frame010_supported hcells) (Fin.cases (record027_frame011_supported hcells) (fun j => Fin.elim0 j)))))))))))))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x19c6cbd62929f94b09ed4c5a5d9294922486a4151d28e346e2278ec273737c9b80d7c6583051618abc54f29f937c95c48523b910c86240f1f80f847a239b18b8bbc5c02d013808fc42c2080ea07083401810b9058829013a09984941fa0f6071824411e06e03601800be05d02e01600ac05502a012007803601a80d0050027012809004001e00e8070026012008003c016009004001c00a0040018008002000 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record029_frame001_links_0000 record029_frame001_links_0064)
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19c6c7e545a8993b8959497a47921c8ab4212034ff47b63d39e54e9455727912a084a3fb1f50f686ee30e16c8b18504273130891446222310b083c4021f80ea86cc35a1980c806082e816e0b385602a414a0a204f425e11908283f81d209104782000dc06c030017c0ba05c02c01580aa05402400d8068028013809404802000f007403801a00c004c024011008003c016009004001c00a0040018008002000 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x36dd9c4ccb63f2fd1792b6756f2acd516a25508a7712b2934487230515889943221090607f93f39edcf4e7943a51b00d2a6332d515fcaae4f126e92a084a4001ed0e346f03651980c385f82c51598a0c4e626012288c444621610788183f01e50ef075839e1c10dd86cc35a1a60c786203041750b705982b01520a5051027a12f08c843020a0db04781b00c005f02e81680b005702b0150068028013809404402000f807803801a00c004c024011008003401600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
def record031_frame002_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x30e1764b9c5bfad05650afb553aa294e6a22507a7bd31c96d4a524051d28d344f21ed0e283240e9f78f907b03c81d38e707083599a60cf663030f97f4b625992be9514a6a52727c936c9a44a024911848a444120c0fbc7a63bd1d68e646f235219e8ca062c2f31718b485842b813f89b44b4236112083c3da1e00e8070c3721980b285082640d804781b00c005f02e81680b005702b0150068028013809404402000f807803801a00c004c024011008003401600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record031_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record031_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record031) (record031.maps 2)
      (record031.inverseMaps 2) record031_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record031_frame002_links_0000 record031_frame002_links_0064)
theorem record031_frame002_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 2 :=
  of_group record031 2 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record031_frame002_indices record031_frame002_graph record031_frame002_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (Fin.cases (record031_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
def record032_frame001_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x7a679b78677b75f7586f96896496405be59158357656854d54553e52952251c5024e54a646e45b43742e4223e43dc3a339236d35634d31a30c3062fe2f02df2d82d02c92c42b62b02ab28f24722420c2041dd1d31c11bc1b619718515f15814413312e11710c0e60d80cd0c40c108d06f06c06b05f05d05b05805505403e03703403302d02702502302102001d01c01301201000f00e00b00a008007005003002001000 } : Fields).get c.val)
theorem record032_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record032_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record032) (record032.maps 1)
      (record032.inverseMaps 1) record032_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record032_frame001_links_0000 record032_frame001_links_0064)
theorem record032_frame001_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 1 :=
  of_group record032 1 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record032_frame001_indices record032_frame001_graph record032_frame001_links
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (Fin.cases (record032_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xce666631f986aba054ea8894249a34bea4cd2168fa457a2610ee80d3fc1fa0f687a63ca9d28e0266c2b493b89bc46f2248ffc7ae3c61bd8d906862d91620ad0500272130891446222310b081c4021f90f987b03aa1ce0e086ec3301890b6859c2c01570a204d825e12708d042c1fc0f7074038811e06f03601ac0ca05f02e816c0b005502a00dc068033016809c04a023010007403801a00c004c024010007803801600a004001c00c0050018008002000 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
def record034_frame001_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a86cfc666afd16cea7751da84d3b8934484a3e91828ac44d21910848304069fa4f8c7a53c99b00c66543283937c9504001ea8f1871a3781b30cc061c2fc16c8ad452427112f891446220f10307cc3ca1de0eb07403821bb0d986b434c1980c505e82d81650ac054829414409e84bc242119086035412407e03781800ba05b02d01600ae05602a811806e028012808c04402000f807803a01a00c004c022010007003401600a004802000a0040018008002000 } : Fields).get c.val)
theorem record034_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record034_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record034) (record034.maps 1)
      (record034.inverseMaps 1) record034_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record034_frame001_links_0000 record034_frame001_links_0064)
theorem record034_frame001_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) : Supported record034 1 :=
  of_group record034 1 (smallEmbedding record034) (small_cells_exact record034 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record034_frame001_indices record034_frame001_graph record034_frame001_links
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (Fin.cases (record034_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd4367e33b199ac355b3aa814eea6251da87d4269a3499a42d1f48c145522690ee8514212034ff07e93e31ee4f4a79338098ccad8543297141c9d64df2378ffc7ae3c61c68dd86cc34318e8c385b22c415a8a4850a27112f891446220710087e43e61ec0ef07403821bb0d986b434c1980c505e82e616c0b285802ae14409b04bc24e12108d042c1ee0e806a81e40de06502e816c0b405802b01540820370168094046022010007803a01a00c004c02000f007003401600a004802000c0050018008002000 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record036_frame001_links_0000 record036_frame001_links_0064)
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (smallEmbedding record036) (small_cells_exact record036 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
def record036_frame002_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xc9d64432098f4bfe5ae2b39580ab9555aa8953aa1c4cca5d52c892d48c24291cc8c2458a1e90ca85742220f906c82f3d71c10cde66132d1930c8663f2e995b4aa054328c141c9f84e026192d891647a23791808b845622890547a835e1a78cf866031f17f0b7457a2ae14e8a3c4fc25d11e08a844621c10a88183e01b70c705f02d21570a404c02160f306901e40de06502e816c0b405802b01540820370168094046022010007803a01a00c004c02000f007003401600a004802000c0050018008002000 } : Fields).get c.val)
theorem record036_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record036) (record036.maps 2) (record036.inverseMaps 2) record036_frame002_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record036) (record036.maps 2) (record036.inverseMaps 2) record036_frame002_indices (Fin.ofNat record036.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record036_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record036) (record036.maps 2)
      (record036.inverseMaps 2) record036_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record036_frame002_links_0000 record036_frame002_links_0064)
theorem record036_frame002_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) : Supported record036 2 :=
  of_group record036 2 (smallEmbedding record036) (small_cells_exact record036 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record036_frame002_indices record036_frame002_graph record036_frame002_links
def record036_frame003_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x698d11a0b3de4ec0b6ead7daab3964ec7d53a3b41e7fce39af3465eca693b20239c6c8b51562844a83ef51c5b806f6db5b2360648bb96bace562a914ea884e49a9272424788ad1322143681cfc1d439c714e01b835266cc51842f65d8b715f2a2518a113e2744d49691e224430831021f43a8698c315c1d8368630b61642c0560a814c2003705a094118220400780e81a03004c0800f01c0340580a0120200300500600800800 } : Fields).get c.val)
theorem record036_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record036) (record036.maps 3) (record036.inverseMaps 3) record036_frame003_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record036) (record036.maps 3) (record036.inverseMaps 3) record036_frame003_indices (Fin.ofNat record036.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record036_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record036) (record036.maps 3)
      (record036.inverseMaps 3) record036_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record036_frame003_links_0000 record036_frame003_links_0064)
theorem record036_frame003_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) : Supported record036 3 :=
  of_group record036 3 (smallEmbedding record036) (small_cells_exact record036 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record036_frame003_indices record036_frame003_graph record036_frame003_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (Fin.cases (record036_frame002_supported hcells) (Fin.cases (record036_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a8ccff675b34186aa7451c28854209d84d0a4851fa8ea46222a113a8514212034ff47e93e21ee0f467913809500a084ed26e12908da3ed1e48ed87203741b48c7461c2d91630ad4520284137897448a23110388043f21f30f607783a01b30d6866032018a0ba05802a414409e84d825e12108884282060fc07b83a41a807903601a80d206703281800b005602a810406803201880bc05a028010007803a01a00c004c02000f0070034016009004001c00c005002000c004000 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0550.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0550.count (({ width := 11, code := 0x20ac14802ff1f83c4768e89c7b8c6ecdbdb534967ecbd90b1c632c09792ee5c4b4557aa653ca4d382664b29591c22743c81cff9fb3c6774eb9ce384620ba1642ac540a71462784bc8e9172284387f0f71e03ac730dd19c3005d8b71602a4528a31362544888b10e1d03986c0d21a02e8540a012c2304007e0dc1902904a0800e0160260480780900e00800800 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0550
    Papers.RationalityTen.SharedFrameCatalogue.group0550_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0550.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0550.count (({ width := 11, code := 0x42b84d04e043fb7e8f0dda3aa740e4dc6b836eedb9b434a67ccd998325646c59893015ecbb5732e358eac154a9f520a2d3826e4ca9692a2374508890ea0a40c7f0f91e43c0764e99cb36e63cc39732e058caa9522964fc9d12e238464859082023e4798e91c6370668c71842f45a8ae1542884e89b124234450870f81ec3c8760e41c4360680b61482704908c1001b83004e08c0f01c02a0500880b00e00800800 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record039_frame001_links_0000 record039_frame001_links_0064)
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0550
    Papers.RationalityTen.SharedFrameCatalogue.group0550_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x8928428087e27bd7b97367106f56e46a36a167861c6015f05e55e35bb5b25a55a15895855705415175075024b648c48443c4303ae38437c37336733232831730d2fc2b629228025e23a22822021a1fc1cf1c51b81b11ab1a319a19117616613912f12711e0ff0f80f20ea0e00da0d50c60c20b909608608007b07907105e05905604204103b03802c02502001e01601300f00d009008003001000 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record040_frame001_links_0000 record040_frame001_links_0064)
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
def record040_frame002_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0525.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0525.count (({ width := 10, code := 0x26c9725192a4390a2a88e1f8720b829ff7b1e8795e077dd3741ca725bf6f9b46a9a36819e64d8b6297b5dd6156558555515053d4d9324a91743106404f63c0ed3ace2354cf328c530cc02f0b72a4a52609223c8a1e4741c86f1b06a1985f170581404b1284911c440f4390d82e0b42b0a82508c1e0701604c0f034090200300400 } : Fields).get c.val)
theorem record040_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0525.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record040) (record040.maps 2) (record040.inverseMaps 2) record040_frame002_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record040) (record040.maps 2) (record040.inverseMaps 2) record040_frame002_indices (Fin.ofNat record040.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record040_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record040) (record040.maps 2)
      (record040.inverseMaps 2) record040_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record040_frame002_links_0000 record040_frame002_links_0064)
theorem record040_frame002_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 2 :=
  of_group record040 2 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0525
    Papers.RationalityTen.SharedFrameCatalogue.group0525_facts record040_frame002_indices record040_frame002_graph record040_frame002_links
def record040_frame003_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0519.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0519.count (({ width := 10, code := 0x21882e017e9f37c9dc759d3745c470db96b5a9699a2685956418b62982605775b969591625594f53944505324b52c4a92745d1343108400f03a4e5380d8348ce32cc12d8b22bcac2a8a7290a02488f224842087f1d0721bc6c1a46518459158521304711843108400e8350c82a0a42508c1e07019060120400d02c070180300400 } : Fields).get c.val)
theorem record040_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0519.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0519.localPairCheck (smallEmbedding record040) (record040.maps 3) (record040.inverseMaps 3) record040_frame003_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0519.localPairCheck (smallEmbedding record040) (record040.maps 3) (record040.inverseMaps 3) record040_frame003_indices (Fin.ofNat record040.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record040_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0519.localPairCheck (smallEmbedding record040) (record040.maps 3)
      (record040.inverseMaps 3) record040_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record040_frame003_links_0000 record040_frame003_links_0064)
theorem record040_frame003_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 3 :=
  of_group record040 3 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0519
    Papers.RationalityTen.SharedFrameCatalogue.group0519_facts record040_frame003_indices record040_frame003_graph record040_frame003_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (Fin.cases (record040_frame002_supported hcells) (Fin.cases (record040_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x87882880e7ee7c87b97b177075272f7166eb6e66bf69c6936716496225f75f25de5d55c05b15aa59e59358257757054a5204fc4f34b14894814574354223d43a938137936c35933b32b31b3103002fc2b929628326123e22b21920d1f81d81c21bb1af1ac1a019217f17616214212c11f10c1020f60f30e70e00d40ca0c60c20b60ae0a009609507b07a07005d05805704304003a03602b02301f01e01a01501100d00a008004001000 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (Fin.cases (record042_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record043_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037
