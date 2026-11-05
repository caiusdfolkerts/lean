module
prelude
public import GraphInputsSix0Part00041Data
public import RawFrameSupport
public import SharedFrameGroups031Checked
public import SharedFrameGroups033Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups043Checked
public import SharedFrameGroups047Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups080Checked
public import SharedFrameGroups081Checked
public import SharedFrameGroups082Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups096Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups105Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups107Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0xaadaa2a8da88a65a5fa51a26a17a13a079df9cb9ca9a699f98898396e95f94093c92991d9149128718217e67c07b57b176974b7206df6b469569363e62c5eb5d75d55c05aa59759357b5775704fc4ec4bd47d44a42e4223c73b537536535933d33532431b3093002fc2ca28827223021320d2031ca1bb1b31a71a018917f17616d13411610c1020fa0ee0e70e00ce0ca0c60c20b50ad09f09507b07906f05c05805704304003602302001e01b01501100d00b008005001000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0613.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0613.count (({ width := 10, code := 0x2619825f9725b9665795a539424f93a4b92a4991a4590e429023d8f2398e2378da2887e1884e1083a097f5fa7b5e276dda72dc76e9b56d1ad6899e66d956498e5f9765bd605454c519344bd204751743507410ff3f0f73d0ef38cdf34cca318c12d4b12b4a92949b25490234811e0721b46919461170541404c1244410c400f03b0e4370c42e0b4280942206c1905c16054110340b0200500400 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0613.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (embedding (N := 44310) record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (embedding (N := 44310) record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (embedding (N := 44310) record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group0613
    Papers.RationalityTen.SharedFrameCatalogue.group0613_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0608.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0608.count (({ width := 9, code := 0x71387c1de6ef73b7db6cf61afd66a751a7d16873f9ece6673194c96472187c0df2f176ba5c2cf65afd6eab54a6526873f9f4e6612d95496451e89c3a13017dbdde4ea73b7db8d76933594c661afd78b857ab1469c4c251168843211047c3b9c8e06731174b2572a94c9c48221007a391c0dc6833190c0542813888401d0b054261208838160a038140200 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0608.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0608.localPairCheck (embedding (N := 44310) record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0608.localPairCheck (embedding (N := 44310) record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0608.localPairCheck (embedding (N := 44310) record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record008_frame003_links_0000 record008_frame003_links_0064)
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group0608
    Papers.RationalityTen.SharedFrameCatalogue.group0608_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
def record008_frame004_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x89a89488d88c88288086985585084d83782380b8058007ff7f27e77de7d47c17ba7ad7a779b79874f7256f06cd6af6a366063e6275f75cf5a85a555754f5235024fd4df4c74a449f4794734664164043ed3bd39537536131d3152e92cd2bc29428d26f25c24223222c2071e61df1ba1a519d19717116b16615c15414313a13012c1111020fa0f20ee0e50de0d90c60be0b90b40ab0a609909107907706d05a05605504304003602302001e01b01501100d00b008005001000 } : Fields).get c.val)
theorem record008_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record008_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record008) (record008.maps 4)
      (record008.inverseMaps 4) record008_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record008_frame004_links_0000 record008_frame004_links_0064)
theorem record008_frame004_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 4 :=
  of_group record008 4 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record008_frame004_indices record008_frame004_graph record008_frame004_links
def record008_frame005_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0976.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0976.count (({ width := 10, code := 0x3c8f1bc3f0bbfefbbbedbb3ecbafeaba5e93a3e8b9fe739ae6798e5f95e4b91e436dd5f4bd033ccdf1fc3705bdeecb72dbb0abaa9294a46849ea709b25c966518ce2787a087e5e8779cd715b76bda86619462d815dd705ad575153d4ad1d45d15404fa3d8f33ace0374d5344bd2c4a9290a026097244872087f1ec751c46c19c5915c5111c43108360cc2e08c200781b054110340b0200500400 } : Fields).get c.val)
theorem record008_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (embedding (N := 44310) record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (embedding (N := 44310) record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record008_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (embedding (N := 44310) record008) (record008.maps 5)
      (record008.inverseMaps 5) record008_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record008_frame005_links_0000 record008_frame005_links_0064)
theorem record008_frame005_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 5 :=
  of_group record008 5 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group0976
    Papers.RationalityTen.SharedFrameCatalogue.group0976_facts record008_frame005_indices record008_frame005_graph record008_frame005_links
def record008_frame006_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0525.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0525.count (({ width := 10, code := 0x2a8a9aa3a86a0a7e9da6e9aa6698a5694a4e91a428fa3a8ca2a87a1a85a1283a0a6695a4c916408fa368ba2686a1181a057cdef78ddb769d5731c670dbb6e1b466d97651885fd765c566589565414b519424ed384c12d4a91b421053c8e8394e4344cb31cc22fcb32b8a929c94218811e8761c46e1b0631845f170561545213c4911c430f0380dc2f0b0280841e07019054110340b0200500400 } : Fields).get c.val)
theorem record008_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0525.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (embedding (N := 44310) record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (embedding (N := 44310) record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record008_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (embedding (N := 44310) record008) (record008.maps 6)
      (record008.inverseMaps 6) record008_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record008_frame006_links_0000 record008_frame006_links_0064)
theorem record008_frame006_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 6 :=
  of_group record008 6 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group0525
    Papers.RationalityTen.SharedFrameCatalogue.group0525_facts record008_frame006_indices record008_frame006_graph record008_frame006_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (Fin.cases (record008_frame004_supported hcells) (Fin.cases (record008_frame005_supported hcells) (Fin.cases (record008_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0xaadaa2a61a5ba4da22a17a13a079df9cb9ca98597e96b95a94093c92991d9149128718217e67c07b57b172069a69362c5dc5d559a59357e5775705094fc4bd43e4294223bb3b536035934833d32131b3063002fc2ca27221420d2031bb1b31a91a018817f17616d11510c1020fa0f00e70e00cf0ca0c60c20b50ad09f09507b05804a04404304104003a03703602b02402302001f01e01b01501100d00b008005001000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (embedding record009) hcells Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x10b684b41be0c702c7f2bf29f7cf877a03b91dacea974c39e5ccae2a70cb7e9bccdb06d533f193ac355f62efd752ae5515285d2fc8f146da0ed04c7e33e69ecce9a737379997cc546192d816a0a6452427c936c93c49022f91408883ff1d58c986283051538a504fc26c11c089841c1fc0c405e02ca15109f84bc2400f1072035c1920b7058827c12a07b02c0128088043020810007403701b00ac048023010007c03c01b00a804401a00b0040014002000 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record009_frame002_links_0000 record009_frame002_links_0064)
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (embedding record009) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
def record009_frame003_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x67cce991b21637c4b85b07e05bd777eeedc2b7f6ead9da0b3b636c4583b0546e7a4c59472664943d7f4fd9dd397720d91af34b688cf57f2f45a0a414027a47a8e506a0a3f87c4ed1d43846f0dc9992ee530a394324e48c8f91a21841c808fc1aa340650c61802f85d0ac15029c5209d12e230438710a811c2104107e0f81c83606a0ac1202304007c0f01b02a0440680b01001400800 } : Fields).get c.val)
theorem record009_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record009_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record009) (record009.maps 3)
      (record009.inverseMaps 3) record009_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record009_frame003_links_0000 record009_frame003_links_0064)
theorem record009_frame003_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) : Supported record009 3 :=
  of_group record009 3 (embedding record009) hcells Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record009_frame003_indices record009_frame003_graph record009_frame003_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (Fin.cases (record009_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xa96a6193192e90d9088f18ed8c28b58a689b8968928027bd79177175c75571d70b6f56d66a867466d64564361b5ed5b95b259457f55a54d54553e52c5255194cd4b84a345144540e40a3e13df38437834133d31d3092e52d32cc2bd2b62b02a927625f24523421c2031ff1e31d91ca1bc1a71a318b18817d16616115b14a12e12712310f1030fd0e80df0db0c40c10bb0b60ad0a409908a08206f05f05805504403302302001c01b01600b00a005003000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (embedding record011) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x23c71948a3c4ce2050ee816bfc9fc0fa47c93dd1ec0f4f798bc75e18ed67633a89d24e6e699b3a18fec1c6032d8560caa6525a8f146a978489a3f91ec8514182044fe07e73981c90e2a6bc32d980cbf25f32cf154ca924fe27c93bc9d24dc23891a08a044221c90848343c01b00c145ec2f016f89944b624c11e88ac44221210187e83481910bb85ac28c13a09303a410407c02f816c0b005502a012808803f01c80d404e0230100074038016009804801e00e005802000e0050018008002000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x47c23b31a18c544ea2510f5871bffdfdafb17cfbd59e8ef1378236d1a60c8760f303d810b7d5b2ac0d55aaa3526a929476a364e7a5d52d491048623f51f08ba440a14d07a8384099ff4ff07e83921c60d8066832f981cc085fa2f91678aa254927e13e49e04e924b12248d446222690ec86641e20d8ef06e835c18a0c105f02f11708a004ce25b12408ec45a22110708043f41ec0cc06082ee1670ae854428c13609604982100fd07583701a40b8059829413e06f03581800b8036019009c04601b00a80440160080038014004001 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
def record013_frame002_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x4ca66272f797049ae4b123a91044221e10d7861c16208302780ab8d1ae8d3068333dd9e0c255ee2df9638b115552a7d4eca6b50926c134a93e499a4291fe8e146722f916a8b1451226512a88d3d01e0ce526d136319b0cc263e3131750af857128b94309d24d1256929c93049224411f48f046f235900473237d18f8c085bc2c915c09bc4b424c11b88a843820e0fd87bc3c81d50c605dc2d21540a384e425611808604041e00eb071836c1a80b9059829413e06f03581800b8036019009c04601b00a80440160080038014004001 } : Fields).get c.val)
theorem record013_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record013_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record013) (record013.maps 2)
      (record013.inverseMaps 2) record013_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record013_frame002_links_0000 record013_frame002_links_0064)
theorem record013_frame002_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 2 :=
  of_group record013 2 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record013_frame002_indices record013_frame002_graph record013_frame002_links
def record013_frame003_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0xa51a44a31a26a079fc9ea9df98397796895f93c93492491d8728227e57bf7b67b276a7517206df6d96a96a669769266363362c5eb5e85d95d45c15b05a059659458457a5785714fd4f04bd47d47743d43a42d4243f43ba3b537537136435b33e33932a32531a30f30a2ff2fd2ca28827223022221720f2031ca1bb1b31a71a019719018317b17716d13412411d1101081020fa0ee0e70e10d60d20cc0c50c10ad0ac0a509f06f06b06005c03603202702301b01501100b008007005002001 } : Fields).get c.val)
theorem record013_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record013_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record013) (record013.maps 3)
      (record013.inverseMaps 3) record013_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record013_frame003_links_0000 record013_frame003_links_0064)
theorem record013_frame003_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 3 :=
  of_group record013 3 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record013_frame003_indices record013_frame003_graph record013_frame003_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (Fin.cases (record013_frame002_supported hcells) (Fin.cases (record013_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x11e98e9c66a30913a89443d61c6ff97f33eadf30f567a3bc4de08db4698321d83cc0f6042c0d546a4a51ea8d939e96a48623fd1f085342420e10268083fc1fa0e6072438a9b00cbe6042fc17c8b3c54927c93b89d24bb24b11f48d445922690ec85441e20d8ef06b830417b8bc45c226712d892847622d11088404021fa0f606082ee1690ae854428c13809604982100fb07583701a40b8059829413e04a02200e806e03601980c8056028013809004601b00a80440160080038014004001 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (embedding record014) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
def record014_frame002_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1325987cbce5b926b92c48ea441102875434a17d058820c09e02ae346ba34c1a0ccf76782df9622a9f53ea9ad4249a5499a4451fe8be45c22c514489c44aa234f8c7a03bb1ca4d8c66131b9898ba857128613889a24ba256929093048f24411f48ea46f23590046fa30216e0b2457025a12608e445421c10707f43de1e40ea85dc2d21560a384e425611a08604041e00ea071836c1a80b9059829413e04a02200e806e03601980c8056028013809004601b00a80440160080038014004001 } : Fields).get c.val)
theorem record014_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record014_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record014) (record014.maps 2)
      (record014.inverseMaps 2) record014_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record014_frame002_links_0000 record014_frame002_links_0064)
theorem record014_frame002_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) : Supported record014 2 :=
  of_group record014 2 (embedding record014) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record014_frame002_indices record014_frame002_graph record014_frame002_links
def record014_frame003_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0xa4da41a2ea22a079fc9ea9df97e97496595a93c93492491d8728227e57bf7b67b27206d96a669969266362c5e85db5d45a059b59458457f57857150a4fd4ed4bd47743a42b4243f43b537136235b34933e33632a32031a30f3052ff2fd2ca27222221620f2031bb1b31a91a019719018417b17716d12411d1111081020fa0f00e70e10d60d10cc0c50c10ad0ac0a509f04a04403a03703603303202b02802702402301b01501100b008007005002001 } : Fields).get c.val)
theorem record014_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record014_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record014) (record014.maps 3)
      (record014.inverseMaps 3) record014_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record014_frame003_links_0000 record014_frame003_links_0064)
theorem record014_frame003_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) : Supported record014 3 :=
  of_group record014 3 (embedding record014) hcells Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record014_frame003_indices record014_frame003_graph record014_frame003_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (Fin.cases (record014_frame002_supported hcells) (Fin.cases (record014_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x285f41894cc9ba27512887ac38dfe4fe07d23e49efaf567a3bce9e26f046dbb4cd80ab7d5b2ac0d574aa352d2929478a364e7a6052d491c48623f91f08514162044fd87e73981c90e2a6c0335997cc146042fc97c8b3c5532a493f89f24ef274924c8d043920d0ef075c36b1ae0d3861630417b0bc45c227a133896c49823b11688844242010fd07b03261820bb85ac2ba1510a304e8258126073024411a05802a815009404401b00c804e023010007803a01c00d8054026011007802c0100070028008002000 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (embedding record017) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
def record017_frame002_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x2aeb5539fc4eee4d725891d48821f90e4866c2e60d1058820c0ce04f01572136099d6c255ee2df9652b1155baa7d4f4a6b50926f534a94b499a4391fe8bd456a28512288c3e31e80eec72936a1b18cde66131d9898ba857f2b89468a184e626892b092e47c23510047d438f1be8da862a30216c0b2457026c12d093047622a10e08383fe1ef0f207543121770b4856028e1390958470218101070824411a05802a815009404401b00c804e023010007803a01c00d8054026011007802c0100070028008002000 } : Fields).get c.val)
theorem record017_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record017_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record017) (record017.maps 2)
      (record017.inverseMaps 2) record017_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record017_frame002_links_0000 record017_frame002_links_0064)
theorem record017_frame002_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) : Supported record017 2 :=
  of_group record017 2 (embedding record017) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record017_frame002_indices record017_frame002_graph record017_frame002_links
def record017_frame003_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0xaefaeba82a78a079fc9ea9df97c97296395894493c93492d92491d8768267b076a7517206e96d96b16a669869266363b62c5f55e85da5d459f58e58357256f50a4fd4ed4bd47f47744043a42c4243f43bd3b537737136335b33d32930e2fb2ca2bb27e27226322622221520f2031c71bb1b31ab1a019719018617b17716d13112411d1131081020fa0f20e70e10ca09108d05805505404a04403603202702302001e01d01c01b01501301100f00b008007005002001000 } : Fields).get c.val)
theorem record017_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record017_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record017) (record017.maps 3)
      (record017.inverseMaps 3) record017_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record017_frame003_links_0000 record017_frame003_links_0064)
theorem record017_frame003_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) : Supported record017 3 :=
  of_group record017 3 (embedding record017) hcells Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record017_frame003_indices record017_frame003_graph record017_frame003_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (Fin.cases (record017_frame002_supported hcells) (Fin.cases (record017_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1553a60d2a68ed4019d9cab651922e90a45d22bb0cd85cc1a60bd0478043fedfdae406c033b1850bdb595ac45564aa453fa9a937e9a54a324e12268fe46922b11428934451f0ceee72936a1b18ce865c31b189cba857f2b8947ca0e4e126912b092e47c2380fb477e38e1be8da862e30016b0b2057027a135097047a22910e08383fe1f20f0875432e1870bc856828c139095847021e0fe06d024411805802b015009404302080d8062027011008003c01d00e006c02c011007802c012007002800c002000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0xb04ad5ac0aada9fa84a76a3da109df9dc9c69b299d96d9529439288fa8eb83c8017c47967797707106f36db6ab68a6886616316065fa5e25d55c05bc58757d56c56254f5445365254c649c47446643643041140d3c03a539b38637637233d33331e30e2fb2ee2e62db2aa29327825e24a23922421b20e2071db1d11c11bb1a419518d1831781521461401281151040fe0f20ed0e30dc0d20ca0bf0b70af0a209308607e06e06c05c05204303202502301c01b01600c00a005003000 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (embedding record021) hcells Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
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
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x18edc6fe2570fd84ec1bdb9ad935e7ae7d526a6139d9c24a8a50724c919ba259c6ccc5cc2cf5588a2650922ad13081c3fd1fa0f8a7b63d31e54cc86092c813c89bc3771b20ba058c2b41488a084e426111e08cc44a21310888083e81e90ed074c38c19c0cc864c3181840bc85dc2e016809d04e024a11e08a84242040ff07c83c81d40e306c034814a09f04101f00ee071036018c0c005f02e016c0aa054025011007e03901a00ac050027012008c03a01c } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (embedding record024) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0xea5d378ef16d9db2751ea0cf99df1d635c37852ec5d5abd5369951ca2543e69cbc9472863ec6e8d716e1bc1d829022013ff7c2f69e6bc5772ec1d5ba66aeced913205f6bad742d355ca5545a7e4f09d52ea5849a91d1e2354628b1072063e877cef1cd37a6bccd19331861cb495d2a2540a393e2624bc931222103fc7d0f21d0364658ca17c2f05c0b21562904d0950fa1e03706d0d21782e85b0aa150250440720dc1982704a08c0e81c } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (embedding record025) hcells Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
def record025_frame002_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0xa9fa9aa70a69a10a099db9d89ba9b297596d94693d8fd8f88418067c479677d7737126f36db6d66a468c6846616316025f15d45c25bc58757d56c56254c53e5325274c849846b46643641340b3eb3b93a539b38337837233d32e31730a2fb2ee2e62dd2b52ab29527727626024b23822521c21320b1e11cf1bf1be1b21a719219018417d15614b14213612a1141021010f00ee0e60de0d50cc0be0b607e07806e06c06805c05a05805205104804303803603202702502301d01c } : Fields).get c.val)
theorem record025_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record025_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record025) (record025.maps 2)
      (record025.inverseMaps 2) record025_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record025_frame002_links_0000 record025_frame002_links_0064)
theorem record025_frame002_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) : Supported record025 2 :=
  of_group record025 2 (embedding record025) hcells Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record025_frame002_indices record025_frame002_graph record025_frame002_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (Fin.cases (record025_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x2eadcfb71692d0d9ab15606bd576ae35aab3d65ac1556a9d4ca8b4ca94523a3f4728cd17a2737660c8d8bd0de17c16808ff9f7bd676ce95cfb99700db1b33566a6c35792e35c0af9592ab5369e53325b4a09252322e42a80cf59e537e6ecd718f2fc5e4ba1502824e89a12f24c46c8b9121dc39c708d819a3005c8b51622b45087c0f21902a84d0981081e0340640b8130250460780e81c0360540981001e0300400700a00800800 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (embedding (N := 44310) record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record026_frame001_links_0000 record026_frame001_links_0064)
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x92390c9068ee8e38df8d98ce8ca8c68bf8bd8a689787186e86385183082d80d80b7f07e67e47de7db7b97b57b37b17aa6ef6b167f6175d95a755e54351f50b5024f94db4c74bf4b04a649e45540d38837e35c32a30c3062f82e92d32b22ab29327b24a23121e1ec1d11c31ba19d19517516915514610a0fd0f60f00eb0e50de0d70d10cb0bf0ba0b509c08206806606005605204a04403a03303203002a02802402001f01c01b01501200e00b009007006005002001000 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record028_frame001_links_0000 record028_frame001_links_0064)
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (Fin.cases (record028_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1482a33cf467873999c2c90a45b1c08d3b6bdac4d0167731dd878b4a57eaa71512a124eba6c535098e4c3a5c12c69574a7251928092348ea45921c90848023e91e48e046c9f44e1e6412f41610af251728013809a2477233110c8624232010de462a30a1540a444e226210407dc3a81c20da064c2b014909d84c825c12608e846022410b08283f01ea0e807203701ac0d004f023411807b03501a406403101580a0046022010007803a01c00b004c01c00d0058024010007 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record029_frame001_links_0000 record029_frame001_links_0064)
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (embedding record029) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x31e36e3b635a72d0f5e9ae8d686b0d496a2c4e6a70336c9854b16545283931c93246722275cb6d5b2ed29687b331688adc55fa9814a4a124ac25391cc8d944c223d05c8193fd9fa0fa67c53db9e98f2a6102d4162ca5851e26f10908343b21d28d906b62fa1728b1c56829f1488a0c4e426110a87cc3d61ce0dd86903301910c485d42da16709404482180fe077838817009404801b00c605f02d815c0aa05401a00ac04e02300f8074038016009004001c00b005002000e0040018008002000 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (embedding record030) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xb505a4a87d4239ffcf926db35999b4c7e4b324d91c44361f90e786bc306150d6568033c591cc7e61f2c01536a8c514a8653b298a4b0250d260919486a4191fc8f147523891b87f93b99c38dee69733f990cbca5852bb145ca0e4cf25d92688ca45222190c884440f2010fc47c03d11bb0c5860e2a814c098049822b0fb078c3a81c30d986803261820b8858829013a092847821410407b03740c605f02d81600ae05502a00fc072035015809c04602000f8074038016009003801600a004001c00a0040018008002000 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (embedding record033) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
def record033_frame002_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xa024fda3e71dd8d2463a28f13388143ba0c30588253dd1ec0f4f798bc75e18ce8647b1fd84cc1c6032c1956aaa652aa92d46a97a48aa3d916e872428a1050608114009fc0fce72435e19bccb660e30197ccb3c5552a494009f24e926e12e090047123411748a044221c90b884241a1e00db86c030e1828bc05be2b913b89944b624d11e88ac44221310187e83901a40bb85b028c13b09303a40c605f02d81600ae05502a00fc072035015809c04602000f8074038016009003801600a004001c00a0040018008002000 } : Fields).get c.val)
theorem record033_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record033) (record033.maps 2) (record033.inverseMaps 2) record033_frame002_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record033) (record033.maps 2) (record033.inverseMaps 2) record033_frame002_indices (Fin.ofNat record033.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record033_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record033) (record033.maps 2)
      (record033.inverseMaps 2) record033_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record033_frame002_links_0000 record033_frame002_links_0064)
theorem record033_frame002_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) : Supported record033 2 :=
  of_group record033 2 (embedding record033) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record033_frame002_indices record033_frame002_graph record033_frame002_links
def record033_frame003_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1079.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1079.count (({ width := 11, code := 0xd71adb3966ccc59732764ac899031662ac5184706606c057f2fbd7bab155a9ad33a4139e634c494327a45c49841039fe3e97b6f4de5bbc768eb1d3b806c0d099c31a62ac25742c657ea594827d4e6999272474888f51ba2d4528890ca143e872ce21a2338624bf9722b4548a714727c4d09892a248480879041e43b46c8d41902cc3005c0b01542a0520a20fc1c83505609c1182003e0740e0160240380580a01001c0280400600800800 } : Fields).get c.val)
theorem record033_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record033) (record033.maps 3) (record033.inverseMaps 3) record033_frame003_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record033) (record033.maps 3) (record033.inverseMaps 3) record033_frame003_indices (Fin.ofNat record033.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record033_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record033) (record033.maps 3)
      (record033.inverseMaps 3) record033_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record033_frame003_links_0000 record033_frame003_links_0064)
theorem record033_frame003_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) : Supported record033 3 :=
  of_group record033 3 (embedding record033) hcells Papers.RationalityTen.SharedFrameCatalogue.group1079
    Papers.RationalityTen.SharedFrameCatalogue.group1079_facts record033_frame003_indices record033_frame003_graph record033_frame003_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (Fin.cases (record033_frame002_supported hcells) (Fin.cases (record033_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
def record034_frame001_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xce066db321933c7bdf7ef2d6b7b56d9e2cdd48ba3851625dd2d3962ca825032736dab4a5998bcb5a0ab7158ea60527a8493709584a423991ac89843220b901a7fb3f41f20f6e7a63ca9a5cc1a5a82c994b0a364de24210908283b21d10d906602fa16c8b1c56829414189c84c2237112085441a1fa0f5878c39c1c80dd869033c1980c8862430417c0ba85b42ce15f0a9051026a12f094046422610c07f03880c605f02d81600ae05502a00ac04e023010007c03a01c00d805802a012008803801600a004001c00a0040018008002000 } : Fields).get c.val)
theorem record034_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record034_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record034) (record034.maps 1)
      (record034.inverseMaps 1) record034_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record034_frame001_links_0000 record034_frame001_links_0064)
theorem record034_frame001_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 1 :=
  of_group record034 1 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record034_frame001_indices record034_frame001_graph record034_frame001_links
def record034_frame002_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x9fa4f9a78d3a09ab4a164b51db8e246322eb06182c4129ee8f607a7bcc5e3af0c647b09980cb70581aad5546a5552528d539e97a4b524552188f645ba1c90a284141820450027f03f39c90d8066f32f9838c085f32cf1554a9250027c93a497048023411748a043921710848343bc1c70db86b832e1870c105e02e115c89dc4ce25b12688f445a221109880c3f41ec0e406903041770b6054428c13b09303a40c605f02d81600ae05502a00ac04e023010007c03a01c00d805802a012008803801600a004001c00a0040018008002000 } : Fields).get c.val)
theorem record034_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record034) (record034.maps 2) (record034.inverseMaps 2) record034_frame002_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record034) (record034.maps 2) (record034.inverseMaps 2) record034_frame002_indices (Fin.ofNat record034.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record034_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record034) (record034.maps 2)
      (record034.inverseMaps 2) record034_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record034_frame002_links_0000 record034_frame002_links_0064)
theorem record034_frame002_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 2 :=
  of_group record034 2 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record034_frame002_indices record034_frame002_graph record034_frame002_links
def record034_frame003_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x9589549499439328f78ec8cd8c98bc8b885184f84d8087ff7f77ec7e37db70b6e86d26716406116065d55ce5bb58d56255952952250e4ef4d14c34ba4b149f4944894814213ed3bc3b438537e36b33b30b3032d82d22be29f28126f26425924a24123823120d1f61e61dc1c51b51af1a319e19117b17416d16415a15114a14113713112d12311910b1060ff0f10ec0e50d90c306305f05b05805705505402b02702302001f01d01c01b01601501201100e00b00a008007005004003002001000 } : Fields).get c.val)
theorem record034_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record034) (record034.maps 3) (record034.inverseMaps 3) record034_frame003_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record034) (record034.maps 3) (record034.inverseMaps 3) record034_frame003_indices (Fin.ofNat record034.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record034_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record034) (record034.maps 3)
      (record034.inverseMaps 3) record034_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record034_frame003_links_0000 record034_frame003_links_0064)
theorem record034_frame003_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 3 :=
  of_group record034 3 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record034_frame003_indices record034_frame003_graph record034_frame003_links
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (Fin.cases (record034_frame001_supported hcells) (Fin.cases (record034_frame002_supported hcells) (Fin.cases (record034_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xad4d65aaf7567a1e508674138c9b9cd7e30b16f897446e1950b170333f9918ba154ca89d36299a4c6a6192d29634ae255128491848b241d1f88f3475a3811b28313889a68c765e12c515cca3850427a132c8c045421910748023f11ed8dc86363041568a5450a25c0f887943861ae0c906082d81550a8052426c12b093047c23211108484141fe0f507803a81c40df06b034015e09b04a824411a08c03c01c80dc06a03480c406002a012808803e01d00e006c02a0100068028010007 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (embedding record037) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x54ba934fe97d2ba4547a8d512a1f43684d04a074027fcf59e739a71cde9b335268cd099932e64cc78d319627c3e82d001f53d9748e11b936f6a8d35a0b37652c898c3125aaae95a29950e99d2da5746e8991121e4047d0f59e33b875ce59c435a634bd9742c8580ab9402724cc97122222420810fe1c0358638c216e2c8568a31021982e85a0ae14c2885007e0e41a02b05409c1182103e0740e0160240400700b0140200380400600800800 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (embedding (N := 44310) record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (embedding (N := 44310) record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (embedding (N := 44310) record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (embedding record038) hcells Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33879b6cc864c31ef8a4befddb2dc36c4b56d7fabcf5cfab9d57ea93530a8f52d69434969cc4dfe6e933698ecc2a495231913b6d5a52ccc56e2b194c0a124dc25611f48e644c222905c81c3fd9fa0f8e7b73d31e54b5059229613789084241e30ec86c835617d0ba058e2b41498a0c4e426111b889042a20e0f987ac39c1c70e106903221890c185ec2ea16d0b3857c2a414409a84bc25010c07f03d81e00e2038818c0be05d02d815c0aa05401c80ac04e025011807c03a01c00d805802a012008003801800a004001c00a0040018008002000 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record039_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record039_frame001_links_0000 (interval_append _ 64 128 130 record039_frame001_links_0064 record039_frame001_links_0128))
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (embedding record039) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x66432618cfc5ce29311f878c33e127065825befdd86dbf6c2b5bd7fabd95d4ab55586a8f52ea92525a8993989bfcdd26152bd9544a264cb24a918c89db70d2c667ab694bca0e4da256928a8e844e20b103c7fb3f31f1cf6e7a43ca9698a544da24010988223b41b40be05d42c71590a4c50627013088dc44821510707cc3d61ce0cf06442f61750b385642a413b09784a024011a08604101fc0f707803840e406e03501a00c405d02b81540a803a01b00c806002a012807c03a01c00d805802a0120080038014009004001c00c0050020008002000 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record040_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record040_frame001_links_0000 (interval_append _ 64 128 131 record040_frame001_links_0064 record040_frame001_links_0128))
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (embedding record040) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
def record040_frame002_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x1f13dffbbf73edfd9fb0f5bea3d2fa2f23e07bbf72ed9d3ba6746e6dccb96f2be53c53846efdd5b936aeccd93b0f5ceb4d65ac31be17c1167abbd64a7f45e86ce59932323fc6b8b311e1cc27842eb1c236e69ecd195b105f6b25612b454ea6948a844fc96923a34458845031ed354664bd9722ba540a29212244247f0f61ca368698cc1842a0350670c81882e0590a61442803806a0c81802a04a07c0e81c0360580a8120200380500901001c0300500800800800 } : Fields).get c.val)
theorem record040_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record040) (record040.maps 2) (record040.inverseMaps 2) record040_frame002_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record040) (record040.maps 2) (record040.inverseMaps 2) record040_frame002_indices (Fin.ofNat record040.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record040_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record040) (record040.maps 2) (record040.inverseMaps 2) record040_frame002_indices (Fin.ofNat record040.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record040_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record040) (record040.maps 2)
      (record040.inverseMaps 2) record040_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record040_frame002_links_0000 (interval_append _ 64 128 131 record040_frame002_links_0064 record040_frame002_links_0128))
theorem record040_frame002_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) : Supported record040 2 :=
  of_group record040 2 (embedding record040) hcells Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record040_frame002_indices record040_frame002_graph record040_frame002_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (Fin.cases (record040_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
def record041_frame001_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x675b3979c0cc8640b18b8afc50626b10786bc21e0b30477dfbb0d8aec215c2ab55586a9b534a9352428eb44c964caf654f288936494246f229904c7d62130f0871b4b19a4a5e50626d12b48e8469a25d10e8644161facf907b73d21e50a544d8240109876839f1b18d4c6602f815b8a5050627013008dc4482150f587903901bb0d686202f81750b305642a413b09784a024011a08984302080f7070836c0f007203501a00c405a02c015c0a804001d00c806002a011008003e01c00d805802a012007003401600a004801c00c0050020008002000 } : Fields).get c.val)
theorem record041_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record041_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record041_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record041) (record041.maps 1)
      (record041.inverseMaps 1) record041_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record041_frame001_links_0000 (interval_append _ 64 128 131 record041_frame001_links_0064 record041_frame001_links_0128))
theorem record041_frame001_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) : Supported record041 1 :=
  of_group record041 1 (embedding record041) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record041_frame001_indices record041_frame001_graph record041_frame001_links
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (Fin.cases (record041_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xb8f5c2ed3f68aaf1d72eb37580a4d515273b3849b1ca7a4ff26a8ec46fe3611958bec5c9fe8d976953031688abf530a91d47094e472a33915a88f417a064fd27d33e29ed8f4e6d8308162ca5a513282106876239a1bc8d6c5f62e515a8a7c52228213988043d41de0eb86b434a1980c505d02dc128090844820a0ef07482e016409e04a024011806c034818c0b805a02b01540a803401880ac04802200f0074038016008003c01a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (embedding record042) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (Fin.cases (record042_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
def record043_frame001_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x287d4239ffcf926cf3539984c663371858b7c3561790a3704b3d18e8ba4547a83d2a690647fa3c11d48e34169bd4bca57128113d0980452219108c81e4011f88f846ec3021498a144a21e30e186d03401920c105c829013a092847822e10407e83a416409504601c80d206302e81680ae05602a815009204301d00e406a031015809404401f00f00740380160080034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record043_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record043_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record043) (record043.maps 1)
      (record043.inverseMaps 1) record043_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record043_frame001_links_0000 record043_frame001_links_0064)
theorem record043_frame001_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) : Supported record043 1 :=
  of_group record043 1 (embedding record043) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record043_frame001_indices record043_frame001_graph record043_frame001_links
def record043_frame002_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x2065024800bfc5f1af7f7ae3d31cfce73735b7fdbe8dec66830bd7b2b5454fa91d20283440f9fccfbc7c83ac9a80bd85a32aa9514a364c1251125090247023091488063aa1a78cf46102a514089bc4b024811b08903c01c30cc06182ec142099040415809504601c80d206302e81680ae05602a815009204301d00e406a031015809404401f00f00740380160080034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record043_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record043) (record043.maps 2) (record043.inverseMaps 2) record043_frame002_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record043) (record043.maps 2) (record043.inverseMaps 2) record043_frame002_indices (Fin.ofNat record043.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record043_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record043) (record043.maps 2)
      (record043.inverseMaps 2) record043_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record043_frame002_links_0000 record043_frame002_links_0064)
theorem record043_frame002_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) : Supported record043 2 :=
  of_group record043 2 (embedding record043) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record043_frame002_indices record043_frame002_graph record043_frame002_links
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (Fin.cases (record043_frame001_supported hcells) (Fin.cases (record043_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
def record046_frame001_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33819b6c8163ded6f6adb3c59bab775b2ab8d5a1682ac752526e12908d1432210901a7fb3f49f20f6e7a7306964ca2c48420a0e7466030e16c8b1c56a29414189cc46e20d0e406ec35a19e0cc06443141820be05d42dc15f0a9051026a12f0940484232113086041412a08c03d81c80d206302d01600ae05602a815008603a01880ac04402000f807803a01c00d805802a011006802c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record046_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record046_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record046) (record046.maps 1)
      (record046.inverseMaps 1) record046_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record046_frame001_links_0000 record046_frame001_links_0064)
theorem record046_frame001_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 1 :=
  of_group record046 1 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record046_frame001_indices record046_frame001_graph record046_frame001_links
def record046_frame002_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x2a75528a60d2a662f301973cb424bf24c91748516fcb1154d284934a92e470234917a8b6457a2851348933949b18cb85d42b8941c9724ac24b924091247c23b11c080237d15c0a644f425a12608f045a21c10708003e41d50db065c2ee1690ac852827212b08e843c12a08c03d81c80d206302d01600ae05602a815008603a01880ac04402000f807803a01c00d805802a011006802c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record046_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record046) (record046.maps 2) (record046.inverseMaps 2) record046_frame002_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record046) (record046.maps 2) (record046.inverseMaps 2) record046_frame002_indices (Fin.ofNat record046.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record046_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record046) (record046.maps 2)
      (record046.inverseMaps 2) record046_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record046_frame002_links_0000 record046_frame002_links_0064)
theorem record046_frame002_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 2 :=
  of_group record046 2 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record046_frame002_indices record046_frame002_graph record046_frame002_links
def record046_frame003_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x98a98898197f95695595194f93b93893393075f7196d16706215d058657655e55554c53c53452c4764273d637132b2e32a329327b27226925925124921e1f81b61a819918718117917116816215b15314413612711510f1070ff0f60f00e90e109508c07b07206906305a05805705605505404303a03102b02202001f01e01d01c01b01601501100d00b00a009008007005004003002001000 } : Fields).get c.val)
theorem record046_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record046) (record046.maps 3) (record046.inverseMaps 3) record046_frame003_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record046) (record046.maps 3) (record046.inverseMaps 3) record046_frame003_indices (Fin.ofNat record046.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record046_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record046) (record046.maps 3)
      (record046.inverseMaps 3) record046_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record046_frame003_links_0000 record046_frame003_links_0064)
theorem record046_frame003_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 3 :=
  of_group record046 3 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record046_frame003_indices record046_frame003_graph record046_frame003_links
def record046_frame004_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x27e93e69b2cd5a3b71c48c645d625711a8734355606aa3524273d2d490a45ba2290a2841418a0450027f1360197cc0459e2a493dc97049323411748a2439217108877835c1708ae451a26712d893447c22d110884c4081ec0e406903041770b605802a214609d84bc12a08c03d81c80d206302d01600ae05602a815008603a01880ac04402000f807803a01c00d805802a011006802c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record046_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record046) (record046.maps 4) (record046.inverseMaps 4) record046_frame004_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record046) (record046.maps 4) (record046.inverseMaps 4) record046_frame004_indices (Fin.ofNat record046.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record046_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record046) (record046.maps 4)
      (record046.inverseMaps 4) record046_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record046_frame004_links_0000 record046_frame004_links_0064)
theorem record046_frame004_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 4 :=
  of_group record046 4 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record046_frame004_indices record046_frame004_graph record046_frame004_links
def record046_frame005_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x9589549349328cd8c98bc8b889789287b8766406065cc58d5595204ef4dd4c34ba4b249f49448a3ed3b437c33b3032d029f28d26f26425a24a24123920d1dc19e19118317416d16415b15114a14113812d12311910b1060ff0f90f10ec0e50df09508c07b07206906305a05805705605505404303a03102b02202001f01e01d01c01b01601501100d00b00a009008007005004003002001000 } : Fields).get c.val)
theorem record046_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record046) (record046.maps 5) (record046.inverseMaps 5) record046_frame005_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record046) (record046.maps 5) (record046.inverseMaps 5) record046_frame005_indices (Fin.ofNat record046.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record046_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record046) (record046.maps 5)
      (record046.inverseMaps 5) record046_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record046_frame005_links_0000 record046_frame005_links_0064)
theorem record046_frame005_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 5 :=
  of_group record046 5 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record046_frame005_indices record046_frame005_graph record046_frame005_links
def record046_frame006_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0xae6ae3acbac7a47a3ba28a1ca009f59e39d87206d96a466362c5e65c05b459f59859158357c5754bd4774383f43b536f34833d32932231c30e3073012ca2722031eb1d21bb1b31ac1a319719018717e16d15513c12411d11410b1020fa0f30ea09508c07b07206906305a05805705605505404303a03102b02202001f01e01d01c01b01601501100d00b00a009008007005004003002001000 } : Fields).get c.val)
theorem record046_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record046) (record046.maps 6) (record046.inverseMaps 6) record046_frame006_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record046) (record046.maps 6) (record046.inverseMaps 6) record046_frame006_indices (Fin.ofNat record046.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record046_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record046) (record046.maps 6)
      (record046.inverseMaps 6) record046_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record046_frame006_links_0000 record046_frame006_links_0064)
theorem record046_frame006_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 6 :=
  of_group record046 6 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record046_frame006_indices record046_frame006_graph record046_frame006_links
def record046_frame007_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1074.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1074.count (({ width := 10, code := 0xfebf9fdbf5fc3effbbedf93e3f8be1d834acdb1bc0ae7b22bfac6ada9e9ca669296640896087d9dd70dba6b5aa68d9764d8d5d55b4d12a485174490d421003f0f73c8e4368d131cc32f8b92c0ab298a11bc6817c571404d120461144410c420e4330b8290882007c1e0741c06c16054110340b02809020070140400c0200400 } : Fields).get c.val)
theorem record046_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1074.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (embedding (N := 44310) record046) (record046.maps 7) (record046.inverseMaps 7) record046_frame007_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (embedding (N := 44310) record046) (record046.maps 7) (record046.inverseMaps 7) record046_frame007_indices (Fin.ofNat record046.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record046_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (embedding (N := 44310) record046) (record046.maps 7)
      (record046.inverseMaps 7) record046_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record046_frame007_links_0000 record046_frame007_links_0064)
theorem record046_frame007_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 7 :=
  of_group record046 7 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group1074
    Papers.RationalityTen.SharedFrameCatalogue.group1074_facts record046_frame007_indices record046_frame007_graph record046_frame007_links
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (Fin.cases (record046_frame001_supported hcells) (Fin.cases (record046_frame002_supported hcells) (Fin.cases (record046_frame003_supported hcells) (Fin.cases (record046_frame004_supported hcells) (Fin.cases (record046_frame005_supported hcells) (Fin.cases (record046_frame006_supported hcells) (Fin.cases (record046_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
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
def record048_frame001_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x2e5dc9b7f6f6cb592b1b5e6bbd75a814f29c522a4147a38c2f816fbdd4b99700dd9b7b666c0d6592ae0574a6d2aa4645c8910f21541e824f59bb314610ba16f2c05089e13425e49c8f1122103e4738e11b2340608bb1622b43f8780ca1902e85a0aa1482784e09a1301a83405a0a81282203e0780e81c0360580a81001a0300500901001c0280400600800800 } : Fields).get c.val)
theorem record048_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (embedding (N := 44310) record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (embedding (N := 44310) record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record048_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (embedding (N := 44310) record048) (record048.maps 1)
      (record048.inverseMaps 1) record048_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record048_frame001_links_0000 record048_frame001_links_0064)
theorem record048_frame001_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) : Supported record048 1 :=
  of_group record048 1 (embedding record048) hcells Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record048_frame001_indices record048_frame001_graph record048_frame001_links
def record048_frame002_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33879b6c82e3dedc36c4b56d786b935b29cc4dfe6e929c93ec9c5812ac652626e118288a40e1fecfd27c73db9e9cdaa59228c121071a3561740b1c56a29314189cc46e20e0f2077838e1c20da06443141830bd85d42dc15f0a9051026a12f094048421810507b03c012a08c03901c40d206302e81680ae05602a815007403901880ac04a02200f807803a01c00d805802a0100068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record048_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record048) (record048.maps 2) (record048.inverseMaps 2) record048_frame002_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record048) (record048.maps 2) (record048.inverseMaps 2) record048_frame002_indices (Fin.ofNat record048.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record048_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record048) (record048.maps 2)
      (record048.inverseMaps 2) record048_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record048_frame002_links_0000 record048_frame002_links_0064)
theorem record048_frame002_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) : Supported record048 2 :=
  of_group record048 2 (embedding record048) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record048_frame002_indices record048_frame002_graph record048_frame002_links
def record048_frame003_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x302e02bf17daeb5d5ba1702df5bbb2d646c757caf15da56c728ad0c9efbc9752e75cb3866fedddaa2ff5b8add41a704968f51aa2a448874ff9d635a698cc192308584ad1502925009c1272364347f0f51d8390668c616e2c44187c0d019c3005a0a81442784e09a1301b03505a0a41202103e0780e81c0360580a81001a0300500901001c0280400600800800 } : Fields).get c.val)
theorem record048_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (embedding (N := 44310) record048) (record048.maps 3) (record048.inverseMaps 3) record048_frame003_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (embedding (N := 44310) record048) (record048.maps 3) (record048.inverseMaps 3) record048_frame003_indices (Fin.ofNat record048.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record048_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (embedding (N := 44310) record048) (record048.maps 3)
      (record048.inverseMaps 3) record048_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record048_frame003_links_0000 record048_frame003_links_0064)
theorem record048_frame003_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) : Supported record048 3 :=
  of_group record048 3 (embedding record048) hcells Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record048_frame003_indices record048_frame003_graph record048_frame003_links
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (Fin.cases (record048_frame001_supported hcells) (Fin.cases (record048_frame002_supported hcells) (Fin.cases (record048_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record055_frames_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) :
    ∀ f : Fin record055.g, Supported record055 f :=
  (Fin.cases (record055_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record055_frames_supported
theorem record056_frame000_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    Supported record056 0 :=
  of_identity record056 0 (by decide +kernel)
def record056_frame001_indices (c : Fin record056.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xaaea97a7fa62a43a36a29a20a0ca089f49c79c09a097796894994593192e92990f8ed8e58da8c489b89a88087586d8678238027de7bd7ae78f76d7676f56c06a86746456435f55ed5b959457f57d54c51f4a346a45144143840e3f63e13df38e38437435734132931d3093052db2c32be2ad2692522452031e31d91c81bc1a719118b18816616115b14812e12711110f1030e80df0db0cf0c90bf0b80ad0a409908207006f06105f04403f03503303002602301600b00a005003 } : Fields).get c.val)
theorem record056_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record056.data.requiredEdges q = true := by decide +kernel
theorem record056_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record056_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record056_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record056) (record056.maps 1)
      (record056.inverseMaps 1) record056_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record056_frame001_links_0000 record056_frame001_links_0064)
theorem record056_frame001_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) : Supported record056 1 :=
  of_group record056 1 (embedding record056) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record056_frame001_indices record056_frame001_graph record056_frame001_links
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (Fin.cases (record056_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record056_frames_supported
theorem record057_frame000_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) :
    Supported record057 0 :=
  of_identity record057 0 (by decide +kernel)
def record057_frame001_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x28972b695147ba3b91cc8df43ea18b07d836c13e028fce7deb879b56d12647b2098f6b8056f2b5558eab75532a7d350931490a43d1ea87e437217109683e41ba0c4cb064331e95f8a2e50727c93c491447a236119c8b84572288f0c7303791b88bfc5d42d91680978492238119888c43821610005e02d61580a184f026012408a84181fe0f307383601a40c205c81f00e406802f0164094044020810007403701b00a404401d00b003c01c00a0048014002000 } : Fields).get c.val)
theorem record057_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record057) (record057.maps 1) (record057.inverseMaps 1) record057_frame001_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record057) (record057.maps 1) (record057.inverseMaps 1) record057_frame001_indices (Fin.ofNat record057.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record057_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record057) (record057.maps 1)
      (record057.inverseMaps 1) record057_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record057_frame001_links_0000 record057_frame001_links_0064)
theorem record057_frame001_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) : Supported record057 1 :=
  of_group record057 1 (embedding record057) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record057_frame001_indices record057_frame001_graph record057_frame001_links
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (Fin.cases (record057_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
def record058_frame001_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x539a98344a9d8cdf657f2ab932488e3971bd87fc32a10f077827c051f9cfbd70f3555978c9863fb1ed700ade56aab1d56eaa654fa8253949ac4a7a4c522a90f47ca2710fc86242e213107a8374189e38e566e434099a0cb665332318f4b2257b29e145ca084f927712bc91447723611988ba4572288e6071236b19f8c685fe2f416c8b2853c27912f094c470231112887042c2050d385e02e01580a384f025812408a84281fe0ef07383601a40c205c827012407c03901700ae04001b00a404401d00d804401c00c0048014002000 } : Fields).get c.val)
theorem record058_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record058_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record058) (record058.maps 1)
      (record058.inverseMaps 1) record058_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record058_frame001_links_0000 record058_frame001_links_0064)
theorem record058_frame001_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) : Supported record058 1 :=
  of_group record058 1 (embedding record058) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record058_frame001_indices record058_frame001_graph record058_frame001_links
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (Fin.cases (record058_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
def record059_frame001_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x8ea8e48bb8b987a87387084083282f82081f8188168017f17db7d97ce7ba7aa7a86ef6b16a167f6175d95ba5a755f54353b51f50b5024f84db4c74bf4a649e45540d37435c35732a30c3062fd2d32b22ab29b27b22721e2191ec1d11c31bf19517516915d14612710a0f60f00e90e50de0d70d10c90c50bf0ba0b509c08408206b06806605f05c05705204a04403a03303202902802401f01c01401200e009007005002001000 } : Fields).get c.val)
theorem record059_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record059_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record059) (record059.maps 1)
      (record059.inverseMaps 1) record059_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record059_frame001_links_0000 record059_frame001_links_0064)
theorem record059_frame001_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) : Supported record059 1 :=
  of_group record059 1 (embedding record059) hcells Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record059_frame001_indices record059_frame001_graph record059_frame001_links
def record059_frame002_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x52928f13de9ee4b065792a88fc47ba3b91c38dac66a311102866c2060e303f8023f39f7ad6966832c1924b925782b1956ca304e2a6a12b492048623d514e86d42ca0ed06a72c341170cb0a57e29894209fc4f125211ec8e246322a8e546f637118e0bc05b62d013d893c47422f11108003481670ab050c27812e092046020c0ff078839c1b60b304802380da06a03401840bc05902a012808803a01980c8052028012007c03801400900380120070028008002000 } : Fields).get c.val)
theorem record059_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record059) (record059.maps 2) (record059.inverseMaps 2) record059_frame002_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record059) (record059.maps 2) (record059.inverseMaps 2) record059_frame002_indices (Fin.ofNat record059.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record059_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record059) (record059.maps 2)
      (record059.inverseMaps 2) record059_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record059_frame002_links_0000 record059_frame002_links_0064)
theorem record059_frame002_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) : Supported record059 2 :=
  of_group record059 2 (embedding record059) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record059_frame002_indices record059_frame002_graph record059_frame002_links
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (Fin.cases (record059_frame001_supported hcells) (Fin.cases (record059_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record059_frames_supported
theorem record060_frame000_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    Supported record060 0 :=
  of_identity record060 0 (by decide +kernel)
def record060_frame001_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xa91d11a56329d94bca523ef1f48f147423911ba8c944a6072ffe7ea3f0daccccd651b1d97c4b8f5a02bb5562a9a503272d35095749724712208f545221ed0d285d41a20b8e5c6842e31680b0857e29a1464a164f8278929c91847e235918c8a03c01bd0dc46402fd1768b685a027f12e093047222f10d88003c019e0bd05a02b214309e04c424411708303fc1e80e506d02bc12008d03681a40d005e02c815009404001b00c806202b011807803801400980340100070028010002000 } : Fields).get c.val)
theorem record060_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record060_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record060) (record060.maps 1)
      (record060.inverseMaps 1) record060_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record060_frame001_links_0000 record060_frame001_links_0064)
theorem record060_frame001_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) : Supported record060 1 :=
  of_group record060 1 (embedding record060) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record060_frame001_indices record060_frame001_graph record060_frame001_links
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (Fin.cases (record060_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
def record061_frame001_indices (c : Fin record061.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x14079b6491a4592038e946d230713e89043e61b6fea7ce3e25e8af02777b511a68cc564c317185eb695b22b2157aa6852ea73130496748ea4111fe8f743da13d088832407a010fe47153349820b405522a593f49ea4ee275136099647e235916c8a443c216108c78236c1b08c305fe2f71780b7054627612f093847822410a08083cc1940c185c82d215f0a9050427012e09304101ec0e806e834c13407703401840ba05902c012808803a014009004201f00900380180090030008002000 } : Fields).get c.val)
theorem record061_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record061.data.requiredEdges q = true := by decide +kernel
theorem record061_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record061_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record061_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record061) (record061.maps 1)
      (record061.inverseMaps 1) record061_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record061_frame001_links_0000 record061_frame001_links_0064)
theorem record061_frame001_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) : Supported record061 1 :=
  of_group record061 1 (embedding record061) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record061_frame001_indices record061_frame001_graph record061_frame001_links
theorem record061_frames_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    ∀ f : Fin record061.g, Supported record061 f :=
  (Fin.cases (record061_frame000_supported hcells) (Fin.cases (record061_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record061_frames_supported
theorem record062_frame000_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    Supported record062 0 :=
  of_identity record062 0 (by decide +kernel)
theorem record062_frames_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    ∀ f : Fin record062.g, Supported record062 f :=
  (Fin.cases (record062_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record062_frames_supported
theorem record063_frame000_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    Supported record063 0 :=
  of_identity record063 0 (by decide +kernel)
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record063_frames_supported
theorem record064_frame000_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) :
    Supported record064 0 :=
  of_identity record064 0 (by decide +kernel)
def record064_frame001_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcf2e6db20b8f7bcd5da2d3b688b325666afd568a0ed02e7ff2e99674b0e3b11bf8d846562fb1726953021680a61526a5211ca8c0456a22905e80c3f49f58f6c7a736a1830a5a51920a0ec47183791ab0bec5b02b51510a084e623810688203d41e50ee875c38e1b40d2867c32e18a0ba05b82be1520a204a024211908984141ec0f007482300da06903181840b805a02b01540a803501880ac052024011007803a01c00d80580280110078034018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record064_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record064) (record064.maps 1) (record064.inverseMaps 1) record064_frame001_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record064) (record064.maps 1) (record064.inverseMaps 1) record064_frame001_indices (Fin.ofNat record064.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record064_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record064) (record064.maps 1)
      (record064.inverseMaps 1) record064_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record064_frame001_links_0000 record064_frame001_links_0064)
theorem record064_frame001_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) : Supported record064 1 :=
  of_group record064 1 (embedding record064) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record064_frame001_indices record064_frame001_graph record064_frame001_links
def record064_frame002_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x8c68b789888d8508498228208147ed7eb7e27b27a77a177376876274874674374173f73c67162d5f75bf5b95505285105094f84d04b84a94a04944904473f83ae3a833b3173012fd2ec2c82b22a729f29729426922a2252081fe1ee1e81d31c01b11a719718a17517116114f13d11610b0ff0f70e70d50cd0c408606b06706105f05a05805405305203503102b02902402201e01d01c01b01601401100f00d00c009008007005004003002001000 } : Fields).get c.val)
theorem record064_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record064) (record064.maps 2) (record064.inverseMaps 2) record064_frame002_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record064) (record064.maps 2) (record064.inverseMaps 2) record064_frame002_indices (Fin.ofNat record064.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record064_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record064) (record064.maps 2)
      (record064.inverseMaps 2) record064_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record064_frame002_links_0000 record064_frame002_links_0064)
theorem record064_frame002_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) : Supported record064 2 :=
  of_group record064 2 (embedding record064) hcells Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record064_frame002_indices record064_frame002_graph record064_frame002_links
theorem record064_frames_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) :
    ∀ f : Fin record064.g, Supported record064 f :=
  (Fin.cases (record064_frame000_supported hcells) (Fin.cases (record064_frame001_supported hcells) (Fin.cases (record064_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record064_frames_supported
theorem record065_frame000_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) :
    Supported record065 0 :=
  of_identity record065 0 (by decide +kernel)
def record065_frame001_indices (c : Fin record065.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x9279198f38e58b687584d84483a83182a81d81880b7f37c47ae7a779a79178978277a77376e76c7447427406c76986915f95b65b55ac53a52f5134fd4e84e14d84af4a649048a4864814793f83ac3aa39f33132830c3032f32ec2e42c42b52ac2a82a72a029c2291da1d51d119c17d17b17316b15d1261070f60ef0e60dc0d00c90c00ba0b009609007c07606d05d05c05905705304804203702702502302001d01601301200f00e00a008003002001000 } : Fields).get c.val)
theorem record065_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record065.data.requiredEdges q = true := by decide +kernel
theorem record065_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record065_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record065_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record065) (record065.maps 1)
      (record065.inverseMaps 1) record065_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record065_frame001_links_0000 record065_frame001_links_0064)
theorem record065_frame001_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) : Supported record065 1 :=
  of_group record065 1 (embedding record065) hcells Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record065_frame001_indices record065_frame001_graph record065_frame001_links
theorem record065_frames_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) :
    ∀ f : Fin record065.g, Supported record065 f :=
  (Fin.cases (record065_frame000_supported hcells) (Fin.cases (record065_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record065_frames_supported
theorem record066_frame000_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSix0.cells (embedding record066 c)) :
    Supported record066 0 :=
  of_identity record066 0 (by decide +kernel)
def record066_frame001_indices (c : Fin record066.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x93b92e92090f8ec8db8ac86b84c84383782e82681b8148097e27d479878f78678077777176e76c7447427406c76986945f95b65b45a553a5354fd4e84e14de4af49048a4884804793f83ac3a73a439f3313293143032f32ec2e52c42bd2ac2a82a52a129c22120c1fc1da1d51c91b419c18f17d17a17216b15a1261070f80f00e60dc0d20ca0c00ba0b007c07606d05d05905304804704203e03702702602302101d01601301201000f00e00b00a008003002001000 } : Fields).get c.val)
theorem record066_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record066.data.requiredEdges q = true := by decide +kernel
theorem record066_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record066) (record066.maps 1) (record066.inverseMaps 1) record066_frame001_indices (Fin.ofNat record066.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record066_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record066) (record066.maps 1) (record066.inverseMaps 1) record066_frame001_indices (Fin.ofNat record066.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record066_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record066) (record066.maps 1)
      (record066.inverseMaps 1) record066_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record066_frame001_links_0000 record066_frame001_links_0064)
theorem record066_frame001_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSix0.cells (embedding record066 c)) : Supported record066 1 :=
  of_group record066 1 (embedding record066) hcells Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record066_frame001_indices record066_frame001_graph record066_frame001_links
theorem record066_frames_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSix0.cells (embedding record066 c)) :
    ∀ f : Fin record066.g, Supported record066 f :=
  (Fin.cases (record066_frame000_supported hcells) (Fin.cases (record066_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record066_frames_supported
theorem record067_frame000_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSix0.cells (embedding record067 c)) :
    Supported record067 0 :=
  of_identity record067 0 (by decide +kernel)
def record067_frame001_indices (c : Fin record067.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x8a186085084783482b8228198108077eb7bc7b07a979878f78678077777177076c7447427406c46955fd5ba5b15394fc4e94e14b048f48a48748047a3f83ac3a73a439f2f02ec2c12a82a62a129b22f2031fc1f01dd1d519f19618f18317d17917216c1251060f90f00e50dc0d30ca0bf0ba0b009709208c07b07305d05905304804704203e03702b02802702402301f01d01b01201101000e00c00b008003002001000 } : Fields).get c.val)
theorem record067_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record067.data.requiredEdges q = true := by decide +kernel
theorem record067_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record067) (record067.maps 1) (record067.inverseMaps 1) record067_frame001_indices (Fin.ofNat record067.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record067_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record067) (record067.maps 1) (record067.inverseMaps 1) record067_frame001_indices (Fin.ofNat record067.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record067_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record067) (record067.maps 1)
      (record067.inverseMaps 1) record067_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record067_frame001_links_0000 record067_frame001_links_0064)
theorem record067_frame001_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSix0.cells (embedding record067 c)) : Supported record067 1 :=
  of_group record067 1 (embedding record067) hcells Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record067_frame001_indices record067_frame001_graph record067_frame001_links
theorem record067_frames_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSix0.cells (embedding record067 c)) :
    ∀ f : Fin record067.g, Supported record067 f :=
  (Fin.cases (record067_frame000_supported hcells) (Fin.cases (record067_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record069_frames_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSix0.cells (embedding record069 c)) :
    ∀ f : Fin record069.g, Supported record069 f :=
  (Fin.cases (record069_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record073_frames_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) :
    ∀ f : Fin record073.g, Supported record073 f :=
  (Fin.cases (record073_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record073_frames_supported
theorem record074_frame000_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    Supported record074 0 :=
  of_identity record074 0 (by decide +kernel)
def record074_frame001_indices (c : Fin record074.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x28fd15a0f3ee7b4f49cd37669cba9672b254ca8935236424808f31d62f45a86508e09c1080eff5fbbb1760eb1c934e69ace997b0b5f2b9970add5aeb4966a944de9a932a4e4748d5062073e47acec9d03986e8d41a333a65cc998f316578ad9532985109c925248448881001f03d8768e81ba344650c31782d4550a713c2544888d1122043505e0a6124210410780c81882f04e0941181d03806c0b0130240300500800a00c01000 } : Fields).get c.val)
theorem record074_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record074.data.requiredEdges q = true := by decide +kernel
theorem record074_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (embedding (N := 44310) record074) (record074.maps 1) (record074.inverseMaps 1) record074_frame001_indices (Fin.ofNat record074.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record074_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (embedding (N := 44310) record074) (record074.maps 1) (record074.inverseMaps 1) record074_frame001_indices (Fin.ofNat record074.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record074_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (embedding (N := 44310) record074) (record074.maps 1)
      (record074.inverseMaps 1) record074_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record074_frame001_links_0000 record074_frame001_links_0064)
theorem record074_frame001_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) : Supported record074 1 :=
  of_group record074 1 (embedding record074) hcells Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record074_frame001_indices record074_frame001_graph record074_frame001_links
theorem record074_frames_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    ∀ f : Fin record074.g, Supported record074 f :=
  (Fin.cases (record074_frame000_supported hcells) (Fin.cases (record074_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record074_frames_supported
theorem record075_frame000_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) :
    Supported record075 0 :=
  of_identity record075 0 (by decide +kernel)
theorem record075_frames_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) :
    ∀ f : Fin record075.g, Supported record075 f :=
  (Fin.cases (record075_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record075_frames_supported
theorem record076_frame000_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) :
    Supported record076 0 :=
  of_identity record076 0 (by decide +kernel)
def record076_frame001_indices (c : Fin record076.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x16c4b58501a7d733298dcbe25c3284936480a3d30bc851c21a0eacfc675323d8a4a97542a8a93da9884c0a5f92ee9644a7a50525491d48aa4211f88f5479a3b11c88dd3851c00d306582b7153ca2c4df261919886240d2008fc07c23d117f8b8054e27012a07dc38419e0c906042e41620ac0524276132093047422c112084840c1fc0f707883a81c80dc06b034014a0a4048824010408103701b409403601580a004e025012007803a01c00b004c0240100078024010007 } : Fields).get c.val)
theorem record076_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record076.data.requiredEdges q = true := by decide +kernel
theorem record076_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record076) (record076.maps 1) (record076.inverseMaps 1) record076_frame001_indices (Fin.ofNat record076.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record076_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record076) (record076.maps 1) (record076.inverseMaps 1) record076_frame001_indices (Fin.ofNat record076.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record076_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record076) (record076.maps 1)
      (record076.inverseMaps 1) record076_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record076_frame001_links_0000 record076_frame001_links_0064)
theorem record076_frame001_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) : Supported record076 1 :=
  of_group record076 1 (embedding record076) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record076_frame001_indices record076_frame001_graph record076_frame001_links
theorem record076_frames_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) :
    ∀ f : Fin record076.g, Supported record076 f :=
  (Fin.cases (record076_frame000_supported hcells) (Fin.cases (record076_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record076_frames_supported
theorem record077_frame000_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) :
    Supported record077 0 :=
  of_identity record077 0 (by decide +kernel)
def record077_frame001_indices (c : Fin record077.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x140f9fa4cba62f2f496ec6522fd0bc851c21a0eac8b62728993d29884c0a5f92ee9644a7a4612068fc47d23cd1ce8e446e9c1cd3665b2c014749cc46121610448023eb1f08f446222ae13b87c837a1a20c905f02e41620aa85082761350968498240116087842420c0fe07b83c01d40e506e03581a00b9052829012a092048823810408103901bc0dc06b02480d8060027013009403c01d00e006c0240110080024010007 } : Fields).get c.val)
theorem record077_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record077.data.requiredEdges q = true := by decide +kernel
theorem record077_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record077) (record077.maps 1) (record077.inverseMaps 1) record077_frame001_indices (Fin.ofNat record077.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record077_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record077) (record077.maps 1) (record077.inverseMaps 1) record077_frame001_indices (Fin.ofNat record077.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record077_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record077) (record077.maps 1)
      (record077.inverseMaps 1) record077_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record077_frame001_links_0000 record077_frame001_links_0064)
theorem record077_frame001_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) : Supported record077 1 :=
  of_group record077 1 (embedding record077) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record077_frame001_indices record077_frame001_graph record077_frame001_links
theorem record077_frames_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) :
    ∀ f : Fin record077.g, Supported record077 f :=
  (Fin.cases (record077_frame000_supported hcells) (Fin.cases (record077_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record077_frames_supported
theorem record078_frame000_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSix0.cells (embedding record078 c)) :
    Supported record078 0 :=
  of_identity record078 0 (by decide +kernel)
def record078_frame001_indices (c : Fin record078.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x92090f8ec8db8aa86984984083782e82982081b81780e8097e97ba7ac7a579878f78b78878077c77977175a75675474e74a74868f6625b05815354fe4e14de49148a48447e47146c37d3293143052ec2e52bd2ae2a829f2972942211fc1f21d51c918f18517d17816616215a0f80f00e70dc0d20ca0c10ba0a109708a07c06a06105e05d05905305204804703e03503402b02802702602302101d01c01601301201000e00b008007004003002001000 } : Fields).get c.val)
theorem record078_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record078.data.requiredEdges q = true := by decide +kernel
theorem record078_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record078) (record078.maps 1) (record078.inverseMaps 1) record078_frame001_indices (Fin.ofNat record078.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record078_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record078) (record078.maps 1) (record078.inverseMaps 1) record078_frame001_indices (Fin.ofNat record078.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record078_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record078) (record078.maps 1)
      (record078.inverseMaps 1) record078_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record078_frame001_links_0000 record078_frame001_links_0064)
theorem record078_frame001_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSix0.cells (embedding record078 c)) : Supported record078 1 :=
  of_group record078 1 (embedding record078) hcells Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record078_frame001_indices record078_frame001_graph record078_frame001_links
theorem record078_frames_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSix0.cells (embedding record078 c)) :
    ∀ f : Fin record078.g, Supported record078 f :=
  (Fin.cases (record078_frame000_supported hcells) (Fin.cases (record078_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record078_frames_supported
theorem record079_frame000_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSix0.cells (embedding record079 c)) :
    Supported record079 0 :=
  of_identity record079 0 (by decide +kernel)
theorem record079_frames_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSix0.cells (embedding record079 c)) :
    ∀ f : Fin record079.g, Supported record079 f :=
  (Fin.cases (record079_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record081_frame001_indices (c : Fin record081.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x8d28cb8c08b88ac89c89789689488588487e87986385184b84782d81f81280a8007ff7f27e77de7d47c17ba7ad7a779b79874f7256f06cd6af6a363e5f75cf5a85a555754b5455235024fd4ed4df4c74a449f4794734664043bd39537536131d3112fa2e92cd2bc2b329428d26f25c24223222c1e61df1ba1b61a519d19717116615c15414313a1301111020fa0ee0e50de0d90d50c60be0b90b40ab0a609909107706d06605c05a05605504003603002602302001e01b01100d00b008006005001000 } : Fields).get c.val)
theorem record081_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record081.data.requiredEdges q = true := by decide +kernel
theorem record081_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record081) (record081.maps 1) (record081.inverseMaps 1) record081_frame001_indices (Fin.ofNat record081.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record081_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record081) (record081.maps 1) (record081.inverseMaps 1) record081_frame001_indices (Fin.ofNat record081.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record081_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record081) (record081.maps 1) (record081.inverseMaps 1) record081_frame001_indices (Fin.ofNat record081.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record081_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record081) (record081.maps 1)
      (record081.inverseMaps 1) record081_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record081_frame001_links_0000 (interval_append _ 64 128 130 record081_frame001_links_0064 record081_frame001_links_0128))
theorem record081_frame001_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) : Supported record081 1 :=
  of_group record081 1 (embedding record081) hcells Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record081_frame001_indices record081_frame001_graph record081_frame001_links
def record081_frame002_indices (c : Fin record081.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x83782d80f7fc7e77d67d37cf7cb7c27be79378876675875274f74273572a72270d7076e56d66ca6bd6b16af6a369868367f6275e65b55905815785315004e04c44c348b48447f45e44644343c43041a4064033ed3e93e23a137034e33732b2ef2e42c82b72a329728f27126925a25123a23022b1ea1df1b41a719619218a16415614e14c13512c1231000ef0e90de0d60d20cd0c80bb0b90b60b10a70a309308a07506c06505b05905505404003603002602302001e01b01100d00b008006005001000 } : Fields).get c.val)
theorem record081_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record081.data.requiredEdges q = true := by decide +kernel
theorem record081_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record081) (record081.maps 2) (record081.inverseMaps 2) record081_frame002_indices (Fin.ofNat record081.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record081_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record081) (record081.maps 2) (record081.inverseMaps 2) record081_frame002_indices (Fin.ofNat record081.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record081_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record081) (record081.maps 2) (record081.inverseMaps 2) record081_frame002_indices (Fin.ofNat record081.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record081_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record081) (record081.maps 2)
      (record081.inverseMaps 2) record081_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record081_frame002_links_0000 (interval_append _ 64 128 130 record081_frame002_links_0064 record081_frame002_links_0128))
theorem record081_frame002_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) : Supported record081 2 :=
  of_group record081 2 (embedding record081) hcells Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record081_frame002_indices record081_frame002_graph record081_frame002_links
def record081_frame003_indices (c : Fin record081.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0936.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0936.count (({ width := 9, code := 0x29549a451e8d45a250e8541a04f679399b4d66931974b655299449e4d259248e45219047e3d1b8b44a150983c05faf879bc9daeb75391c0df6e369aad16832992c861afd74b659abd5aaa5328d409e4d25d28914622d1486421fcfa793b9d4e06d351a0c66230964a852279389a4c2592490472311086411f8e87034190c0582b13090401e0d8602c13088341608030140200 } : Fields).get c.val)
theorem record081_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0936.graphBitCheck record081.data.requiredEdges q = true := by decide +kernel
theorem record081_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0936.localPairCheck (embedding (N := 44310) record081) (record081.maps 3) (record081.inverseMaps 3) record081_frame003_indices (Fin.ofNat record081.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record081_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0936.localPairCheck (embedding (N := 44310) record081) (record081.maps 3) (record081.inverseMaps 3) record081_frame003_indices (Fin.ofNat record081.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record081_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0936.localPairCheck (embedding (N := 44310) record081) (record081.maps 3) (record081.inverseMaps 3) record081_frame003_indices (Fin.ofNat record081.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record081_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0936.localPairCheck (embedding (N := 44310) record081) (record081.maps 3)
      (record081.inverseMaps 3) record081_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record081_frame003_links_0000 (interval_append _ 64 128 130 record081_frame003_links_0064 record081_frame003_links_0128))
theorem record081_frame003_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) : Supported record081 3 :=
  of_group record081 3 (embedding record081) hcells Papers.RationalityTen.SharedFrameCatalogue.group0936
    Papers.RationalityTen.SharedFrameCatalogue.group0936_facts record081_frame003_indices record081_frame003_graph record081_frame003_links
def record081_frame004_indices (c : Fin record081.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x3dafb0f4de87ccf95f29e4bc8789f0bde3b6765ebbd47a6742e7bcd79a72fe57c7b8970ce09bd377ee9dc9b736dea6cf79572263ec717c6dd5a7b2f652a5540a71436754e49a931e50c7e8f11822dc53808f31dc3ac746d79a9b3e64ac4d7eaf75b6b255baa152ea414623c45e830fe9e73b875cda19e31e610bc1702d24d4880ff1d437c6b8cf18c2cc558a3136248470840fc1a83185e0a81482704d0780d0180260460800f01b0220340580800c01400800 } : Fields).get c.val)
theorem record081_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record081.data.requiredEdges q = true := by decide +kernel
theorem record081_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record081) (record081.maps 4) (record081.inverseMaps 4) record081_frame004_indices (Fin.ofNat record081.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record081_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record081) (record081.maps 4) (record081.inverseMaps 4) record081_frame004_indices (Fin.ofNat record081.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record081_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record081) (record081.maps 4) (record081.inverseMaps 4) record081_frame004_indices (Fin.ofNat record081.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record081_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record081) (record081.maps 4)
      (record081.inverseMaps 4) record081_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record081_frame004_links_0000 (interval_append _ 64 128 130 record081_frame004_links_0064 record081_frame004_links_0128))
theorem record081_frame004_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) : Supported record081 4 :=
  of_group record081 4 (embedding record081) hcells Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record081_frame004_indices record081_frame004_graph record081_frame004_links
def record081_frame005_indices (c : Fin record081.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0550.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0550.count (({ width := 11, code := 0x2764e89c93826ccd69ab34a67cca98d2fa5e4b49592a653c9c92b24246c8a91120a3fc7a8e718e3145c8af14627c1d80efcdf13db7b0e9dbfb6c6b2d619d334666c958ab13616c157b2e55c8b39662c550e9ad2c2484828990fa134147f4f89ef3ce780ea1ca3786d0d89702d4548a693b26c4c48c90d2083f4768e71c431c5c8b214e2884e89a12e234450861082003f0790ec1942f8580a0138250490700d0170260460800f01b0220340580800c01400800 } : Fields).get c.val)
theorem record081_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.graphBitCheck record081.data.requiredEdges q = true := by decide +kernel
theorem record081_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (embedding (N := 44310) record081) (record081.maps 5) (record081.inverseMaps 5) record081_frame005_indices (Fin.ofNat record081.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record081_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (embedding (N := 44310) record081) (record081.maps 5) (record081.inverseMaps 5) record081_frame005_indices (Fin.ofNat record081.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record081_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (embedding (N := 44310) record081) (record081.maps 5) (record081.inverseMaps 5) record081_frame005_indices (Fin.ofNat record081.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record081_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (embedding (N := 44310) record081) (record081.maps 5)
      (record081.inverseMaps 5) record081_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record081_frame005_links_0000 (interval_append _ 64 128 130 record081_frame005_links_0064 record081_frame005_links_0128))
theorem record081_frame005_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) : Supported record081 5 :=
  of_group record081 5 (embedding record081) hcells Papers.RationalityTen.SharedFrameCatalogue.group0550
    Papers.RationalityTen.SharedFrameCatalogue.group0550_facts record081_frame005_indices record081_frame005_graph record081_frame005_links
def record081_frame006_indices (c : Fin record081.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0589.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0589.count (({ width := 11, code := 0x2cf59ab1b612bd56fad75a2b3559aa950e9e532a4f4868d508a013d276ce49c133a61cbd96928a4ec939151f63cc3382eff9f43dd7aeec1cdb886eadd1a7b47684c85853075f8bc56c2c1578a9950a994f0995292444788810ca0d4087e8f99f03b674ce21ba35a69cd21842f8580ab94a28c50c971262404748890c20a3a06b8d018c2f05d8b61622884f09c12e240460830fc1b0338610ae154288500780d01702504407c0e81a0220340580800c01400800 } : Fields).get c.val)
theorem record081_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0589.graphBitCheck record081.data.requiredEdges q = true := by decide +kernel
theorem record081_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (embedding (N := 44310) record081) (record081.maps 6) (record081.inverseMaps 6) record081_frame006_indices (Fin.ofNat record081.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record081_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (embedding (N := 44310) record081) (record081.maps 6) (record081.inverseMaps 6) record081_frame006_indices (Fin.ofNat record081.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record081_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (embedding (N := 44310) record081) (record081.maps 6) (record081.inverseMaps 6) record081_frame006_indices (Fin.ofNat record081.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record081_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (embedding (N := 44310) record081) (record081.maps 6)
      (record081.inverseMaps 6) record081_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record081_frame006_links_0000 (interval_append _ 64 128 130 record081_frame006_links_0064 record081_frame006_links_0128))
theorem record081_frame006_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) : Supported record081 6 :=
  of_group record081 6 (embedding record081) hcells Papers.RationalityTen.SharedFrameCatalogue.group0589
    Papers.RationalityTen.SharedFrameCatalogue.group0589_facts record081_frame006_indices record081_frame006_graph record081_frame006_links
theorem record081_frames_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) :
    ∀ f : Fin record081.g, Supported record081 f :=
  (Fin.cases (record081_frame000_supported hcells) (Fin.cases (record081_frame001_supported hcells) (Fin.cases (record081_frame002_supported hcells) (Fin.cases (record081_frame003_supported hcells) (Fin.cases (record081_frame004_supported hcells) (Fin.cases (record081_frame005_supported hcells) (Fin.cases (record081_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record081_frames_supported
theorem record082_frame000_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSix0.cells (embedding record082 c)) :
    Supported record082 0 :=
  of_identity record082 0 (by decide +kernel)
def record082_frame001_indices (c : Fin record082.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0xf69ebfd279ff33e57ca792f21e23c0f74ed5d8fae740e79cd79a72ee4fc6b8870ae07b9f71edcdb7a9b2463ebe56eed359ab235028b4f49a92aa444628b514ddaba9746d4da6b26610bdd762ca558a5548a8c46a8bd0da043fa7a4eb9bc358678c89772de5a49910e1d43846c8cf18c2d4568a3136248470690c41782a04e0880fc1e83c06e0d41a03004c0901001f0360480880e01a02c0480800c01400800 } : Fields).get c.val)
theorem record082_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record082.data.requiredEdges q = true := by decide +kernel
theorem record082_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record082) (record082.maps 1) (record082.inverseMaps 1) record082_frame001_indices (Fin.ofNat record082.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record082_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record082) (record082.maps 1) (record082.inverseMaps 1) record082_frame001_indices (Fin.ofNat record082.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record082_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record082) (record082.maps 1)
      (record082.inverseMaps 1) record082_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record082_frame001_links_0000 record082_frame001_links_0064)
theorem record082_frame001_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSix0.cells (embedding record082 c)) : Supported record082 1 :=
  of_group record082 1 (embedding record082) hcells Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record082_frame001_indices record082_frame001_graph record082_frame001_links
theorem record082_frames_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSix0.cells (embedding record082 c)) :
    ∀ f : Fin record082.g, Supported record082 f :=
  (Fin.cases (record082_frame000_supported hcells) (Fin.cases (record082_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record084_frame001_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x2c83629ad1563ea2b4f8a07cfd274338d97a4b763971b28c9c5f61f90e7860c2a1d50da967db3b9912c4e61f2d1152ca8951227a53b29884c3a5f92e095e4a7a52128093148f243920690147d23c91ce8e546e9f60e2a6fb34f196cc865802b914f4a244e626792f48d844321610888224021f58f807a23111818b3854627713009383fa1d40de86cc3441930be05c42c41550a104ec26a12d093048022c10f08584181f80f707803a01ca0de06b034014a09f049023810407c03781ac060027013008c04001d00e006c024011007002c010007 } : Fields).get c.val)
theorem record084_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record084) (record084.maps 1) (record084.inverseMaps 1) record084_frame001_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record084) (record084.maps 1) (record084.inverseMaps 1) record084_frame001_indices (Fin.ofNat record084.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record084_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record084) (record084.maps 1) (record084.inverseMaps 1) record084_frame001_indices (Fin.ofNat record084.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record084_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record084) (record084.maps 1)
      (record084.inverseMaps 1) record084_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record084_frame001_links_0000 (interval_append _ 64 128 130 record084_frame001_links_0064 record084_frame001_links_0128))
theorem record084_frame001_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSix0.cells (embedding record084 c)) : Supported record084 1 :=
  of_group record084 1 (embedding record084) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record084_frame001_indices record084_frame001_graph record084_frame001_links
theorem record084_frames_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSix0.cells (embedding record084 c)) :
    ∀ f : Fin record084.g, Supported record084 f :=
  (Fin.cases (record084_frame000_supported hcells) (Fin.cases (record084_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record084_frames_supported
theorem record085_frame000_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) :
    Supported record085 0 :=
  of_identity record085 0 (by decide +kernel)
def record085_frame001_indices (c : Fin record085.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x7ac7a977d77376575b74c74974173872972570d7076e56d66ca6bd6b16af6a369868367f6275e65b55905815785315004e04c44c348b45e44644343743041a4064033ed3e93e23a137034e33732b2ef2b72a329727627126925a25123a23022b1ea1b419619216415b15614e14c13512c1231000ef0e90e30de0d60d20cd0bb0b90b60b10a70a309308f08a07507306c06505905605505404003f03603002302102001e01b00d00c00b008006005001000 } : Fields).get c.val)
theorem record085_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record085.data.requiredEdges q = true := by decide +kernel
theorem record085_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record085) (record085.maps 1) (record085.inverseMaps 1) record085_frame001_indices (Fin.ofNat record085.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record085_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record085) (record085.maps 1) (record085.inverseMaps 1) record085_frame001_indices (Fin.ofNat record085.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record085_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record085) (record085.maps 1)
      (record085.inverseMaps 1) record085_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record085_frame001_links_0000 record085_frame001_links_0064)
theorem record085_frame001_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) : Supported record085 1 :=
  of_group record085 1 (embedding record085) hcells Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record085_frame001_indices record085_frame001_graph record085_frame001_links
def record085_frame002_indices (c : Fin record085.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0936.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0936.count (({ width := 9, code := 0x27f3e9dcea713799cca612f964ae532893c9a4b2491c8a43208fc7a37168942a130780bf5f0f3793b5c8e06fb6db4d568b4194c96430d7eba5b2cd5ea651a81369a4ba51228c45a290c7f3c9dce06e369a8d06331184b254291409e4e269309248239188843209007e3a1c8e06830168b0562612890401b0c8602c13068301608030140200 } : Fields).get c.val)
theorem record085_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0936.graphBitCheck record085.data.requiredEdges q = true := by decide +kernel
theorem record085_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0936.localPairCheck (embedding (N := 44310) record085) (record085.maps 2) (record085.inverseMaps 2) record085_frame002_indices (Fin.ofNat record085.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record085_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0936.localPairCheck (embedding (N := 44310) record085) (record085.maps 2) (record085.inverseMaps 2) record085_frame002_indices (Fin.ofNat record085.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record085_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0936.localPairCheck (embedding (N := 44310) record085) (record085.maps 2)
      (record085.inverseMaps 2) record085_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record085_frame002_links_0000 record085_frame002_links_0064)
theorem record085_frame002_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) : Supported record085 2 :=
  of_group record085 2 (embedding record085) hcells Papers.RationalityTen.SharedFrameCatalogue.group0936
    Papers.RationalityTen.SharedFrameCatalogue.group0936_facts record085_frame002_indices record085_frame002_graph record085_frame002_links
def record085_frame003_indices (c : Fin record085.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0xa72a6da57a50a38a25a0da069f09de9d09cc9a699f98898396e95f94093c92991d9149128718217e67c07b57b174b6df6b469569363e5eb5d75d55c75c05aa59759357b5775704ec47d44a42e4223c737536535934233d33532431b3093002fc28823021320d1ca1bc1b31a71a018917f17613411610c1030fa0ee0e70e00ce0ca0c60c20b50ad09f09a09507907706f06805c05905805704003f03603002302102001e01b00d00c00b008006005001000 } : Fields).get c.val)
theorem record085_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record085.data.requiredEdges q = true := by decide +kernel
theorem record085_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record085) (record085.maps 3) (record085.inverseMaps 3) record085_frame003_indices (Fin.ofNat record085.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record085_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record085) (record085.maps 3) (record085.inverseMaps 3) record085_frame003_indices (Fin.ofNat record085.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record085_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record085) (record085.maps 3)
      (record085.inverseMaps 3) record085_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record085_frame003_links_0000 record085_frame003_links_0064)
theorem record085_frame003_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) : Supported record085 3 :=
  of_group record085 3 (embedding record085) hcells Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record085_frame003_indices record085_frame003_graph record085_frame003_links
def record085_frame004_indices (c : Fin record085.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0976.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0976.count (({ width := 10, code := 0xf07c0ef3baee3b5ec3aeeb3a9e9fa6e8fa2e7f9ce6b99e6397e5792e4790db757d2f40cf337c36f7bb2dcb6ec2a9294a4688a127a9c26c9725994627821f97a1de735b76bda8671986518b605775c16b5152b47517404fb3d8f33ace0374d52f4b12a4a52809825c9121c821fc7b1d4711b06a19c57154511304711043108330c82e0a823084200781b0340c02c080180500400 } : Fields).get c.val)
theorem record085_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.graphBitCheck record085.data.requiredEdges q = true := by decide +kernel
theorem record085_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (embedding (N := 44310) record085) (record085.maps 4) (record085.inverseMaps 4) record085_frame004_indices (Fin.ofNat record085.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record085_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (embedding (N := 44310) record085) (record085.maps 4) (record085.inverseMaps 4) record085_frame004_indices (Fin.ofNat record085.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record085_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (embedding (N := 44310) record085) (record085.maps 4)
      (record085.inverseMaps 4) record085_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record085_frame004_links_0000 record085_frame004_links_0064)
theorem record085_frame004_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) : Supported record085 4 :=
  of_group record085 4 (embedding record085) hcells Papers.RationalityTen.SharedFrameCatalogue.group0976
    Papers.RationalityTen.SharedFrameCatalogue.group0976_facts record085_frame004_indices record085_frame004_graph record085_frame004_links
def record085_frame005_indices (c : Fin record085.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0897.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0897.count (({ width := 7, code := 0x3af4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record085_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0897.graphBitCheck record085.data.requiredEdges q = true := by decide +kernel
theorem record085_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0897.localPairCheck (embedding (N := 44310) record085) (record085.maps 5) (record085.inverseMaps 5) record085_frame005_indices (Fin.ofNat record085.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record085_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0897.localPairCheck (embedding (N := 44310) record085) (record085.maps 5) (record085.inverseMaps 5) record085_frame005_indices (Fin.ofNat record085.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record085_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0897.localPairCheck (embedding (N := 44310) record085) (record085.maps 5)
      (record085.inverseMaps 5) record085_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record085_frame005_links_0000 record085_frame005_links_0064)
theorem record085_frame005_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) : Supported record085 5 :=
  of_group record085 5 (embedding record085) hcells Papers.RationalityTen.SharedFrameCatalogue.group0897
    Papers.RationalityTen.SharedFrameCatalogue.group0897_facts record085_frame005_indices record085_frame005_graph record085_frame005_links
def record085_frame006_indices (c : Fin record085.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0941.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0941.count (({ width := 7, code := 0x3af4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record085_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0941.graphBitCheck record085.data.requiredEdges q = true := by decide +kernel
theorem record085_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0941.localPairCheck (embedding (N := 44310) record085) (record085.maps 6) (record085.inverseMaps 6) record085_frame006_indices (Fin.ofNat record085.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record085_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0941.localPairCheck (embedding (N := 44310) record085) (record085.maps 6) (record085.inverseMaps 6) record085_frame006_indices (Fin.ofNat record085.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record085_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0941.localPairCheck (embedding (N := 44310) record085) (record085.maps 6)
      (record085.inverseMaps 6) record085_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record085_frame006_links_0000 record085_frame006_links_0064)
theorem record085_frame006_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) : Supported record085 6 :=
  of_group record085 6 (embedding record085) hcells Papers.RationalityTen.SharedFrameCatalogue.group0941
    Papers.RationalityTen.SharedFrameCatalogue.group0941_facts record085_frame006_indices record085_frame006_graph record085_frame006_links
def record085_frame007_indices (c : Fin record085.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1027.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1027.count (({ width := 7, code := 0x3af4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record085_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1027.graphBitCheck record085.data.requiredEdges q = true := by decide +kernel
theorem record085_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1027.localPairCheck (embedding (N := 44310) record085) (record085.maps 7) (record085.inverseMaps 7) record085_frame007_indices (Fin.ofNat record085.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record085_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1027.localPairCheck (embedding (N := 44310) record085) (record085.maps 7) (record085.inverseMaps 7) record085_frame007_indices (Fin.ofNat record085.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record085_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1027.localPairCheck (embedding (N := 44310) record085) (record085.maps 7)
      (record085.inverseMaps 7) record085_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record085_frame007_links_0000 record085_frame007_links_0064)
theorem record085_frame007_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) : Supported record085 7 :=
  of_group record085 7 (embedding record085) hcells Papers.RationalityTen.SharedFrameCatalogue.group1027
    Papers.RationalityTen.SharedFrameCatalogue.group1027_facts record085_frame007_indices record085_frame007_graph record085_frame007_links
def record085_frame008_indices (c : Fin record085.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0919.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0919.count (({ width := 7, code := 0x3af4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record085_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0919.graphBitCheck record085.data.requiredEdges q = true := by decide +kernel
theorem record085_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0919.localPairCheck (embedding (N := 44310) record085) (record085.maps 8) (record085.inverseMaps 8) record085_frame008_indices (Fin.ofNat record085.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record085_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0919.localPairCheck (embedding (N := 44310) record085) (record085.maps 8) (record085.inverseMaps 8) record085_frame008_indices (Fin.ofNat record085.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record085_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0919.localPairCheck (embedding (N := 44310) record085) (record085.maps 8)
      (record085.inverseMaps 8) record085_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record085_frame008_links_0000 record085_frame008_links_0064)
theorem record085_frame008_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) : Supported record085 8 :=
  of_group record085 8 (embedding record085) hcells Papers.RationalityTen.SharedFrameCatalogue.group0919
    Papers.RationalityTen.SharedFrameCatalogue.group0919_facts record085_frame008_indices record085_frame008_graph record085_frame008_links
def record085_frame009_indices (c : Fin record085.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0896.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0896.count (({ width := 7, code := 0x3af4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record085_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0896.graphBitCheck record085.data.requiredEdges q = true := by decide +kernel
theorem record085_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0896.localPairCheck (embedding (N := 44310) record085) (record085.maps 9) (record085.inverseMaps 9) record085_frame009_indices (Fin.ofNat record085.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record085_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0896.localPairCheck (embedding (N := 44310) record085) (record085.maps 9) (record085.inverseMaps 9) record085_frame009_indices (Fin.ofNat record085.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record085_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0896.localPairCheck (embedding (N := 44310) record085) (record085.maps 9)
      (record085.inverseMaps 9) record085_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record085_frame009_links_0000 record085_frame009_links_0064)
theorem record085_frame009_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) : Supported record085 9 :=
  of_group record085 9 (embedding record085) hcells Papers.RationalityTen.SharedFrameCatalogue.group0896
    Papers.RationalityTen.SharedFrameCatalogue.group0896_facts record085_frame009_indices record085_frame009_graph record085_frame009_links
def record085_frame010_indices (c : Fin record085.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0905.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0905.count (({ width := 7, code := 0x3af4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record085_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0905.graphBitCheck record085.data.requiredEdges q = true := by decide +kernel
theorem record085_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0905.localPairCheck (embedding (N := 44310) record085) (record085.maps 10) (record085.inverseMaps 10) record085_frame010_indices (Fin.ofNat record085.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record085_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0905.localPairCheck (embedding (N := 44310) record085) (record085.maps 10) (record085.inverseMaps 10) record085_frame010_indices (Fin.ofNat record085.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record085_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0905.localPairCheck (embedding (N := 44310) record085) (record085.maps 10)
      (record085.inverseMaps 10) record085_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record085_frame010_links_0000 record085_frame010_links_0064)
theorem record085_frame010_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) : Supported record085 10 :=
  of_group record085 10 (embedding record085) hcells Papers.RationalityTen.SharedFrameCatalogue.group0905
    Papers.RationalityTen.SharedFrameCatalogue.group0905_facts record085_frame010_indices record085_frame010_graph record085_frame010_links
theorem record085_frames_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) :
    ∀ f : Fin record085.g, Supported record085 f :=
  (Fin.cases (record085_frame000_supported hcells) (Fin.cases (record085_frame001_supported hcells) (Fin.cases (record085_frame002_supported hcells) (Fin.cases (record085_frame003_supported hcells) (Fin.cases (record085_frame004_supported hcells) (Fin.cases (record085_frame005_supported hcells) (Fin.cases (record085_frame006_supported hcells) (Fin.cases (record085_frame007_supported hcells) (Fin.cases (record085_frame008_supported hcells) (Fin.cases (record085_frame009_supported hcells) (Fin.cases (record085_frame010_supported hcells) (fun j => Fin.elim0 j))))))))))))
#print axioms record085_frames_supported
theorem record086_frame000_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) :
    Supported record086 0 :=
  of_identity record086 0 (by decide +kernel)
def record086_frame001_indices (c : Fin record086.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x8b28b089688a88187185084983883080d80b7f07e67e07db7b97b57ad7aa6ea6b16846125d95ac54351f5074fe4db4c74bf4a94a140d3db35c32a3012f12e92d32b22ab28727f21e1ec1cc1a519d19517516914a13d10a1040fd0f60f00eb0e50de0d70bf0ba0b50ae0a508e08c07407306605805705604a04404104003f03a03002802402202102001f01b01200e00d00c00b009006005002001000 } : Fields).get c.val)
theorem record086_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record086.data.requiredEdges q = true := by decide +kernel
theorem record086_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record086_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record086_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record086) (record086.maps 1)
      (record086.inverseMaps 1) record086_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record086_frame001_links_0000 record086_frame001_links_0064)
theorem record086_frame001_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) : Supported record086 1 :=
  of_group record086 1 (embedding record086) hcells Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record086_frame001_indices record086_frame001_graph record086_frame001_links
def record086_frame002_indices (c : Fin record086.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xe26e1cdefdd4dcadb7d81d74d62d58d18d0ece1cc6cbcca9c73c66c54c4aacda9ca5999b95190c8567fd7b97a57567187026cd6b75dd5995004b947d46d4604324023f73c53ba3372e42bb27526725722a2181eb1d918417316515314513712b11910a0d80cd0c00b40a609609407607506605805705604a04404104003f03a03002802402202102001f01b01200e00d00c00b009006005002001000 } : Fields).get c.val)
theorem record086_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record086.data.requiredEdges q = true := by decide +kernel
theorem record086_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record086) (record086.maps 2) (record086.inverseMaps 2) record086_frame002_indices (Fin.ofNat record086.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record086_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record086) (record086.maps 2) (record086.inverseMaps 2) record086_frame002_indices (Fin.ofNat record086.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record086_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record086) (record086.maps 2)
      (record086.inverseMaps 2) record086_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record086_frame002_links_0000 record086_frame002_links_0064)
theorem record086_frame002_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) : Supported record086 2 :=
  of_group record086 2 (embedding record086) hcells Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record086_frame002_indices record086_frame002_graph record086_frame002_links
def record086_frame003_indices (c : Fin record086.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0x90d20a3846a8cd18e2a45089111215425833046064057dcfadf2be4714dedb2338652c496f2c9574ad14c2895069c535a2140c734d999c332650c19752e6588b093a2404387c0f51e03906e0d11942bc560a914c28c4f89b12e24c430831042003e8720e21903185a09c134260460881042003f0740c0140240440841001f0360480700d01802c0480600a00800800 } : Fields).get c.val)
theorem record086_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record086.data.requiredEdges q = true := by decide +kernel
theorem record086_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record086) (record086.maps 3) (record086.inverseMaps 3) record086_frame003_indices (Fin.ofNat record086.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record086_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record086) (record086.maps 3) (record086.inverseMaps 3) record086_frame003_indices (Fin.ofNat record086.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record086_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record086) (record086.maps 3)
      (record086.inverseMaps 3) record086_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record086_frame003_links_0000 record086_frame003_links_0064)
theorem record086_frame003_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) : Supported record086 3 :=
  of_group record086 3 (embedding record086) hcells Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record086_frame003_indices record086_frame003_graph record086_frame003_links
theorem record086_frames_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) :
    ∀ f : Fin record086.g, Supported record086 f :=
  (Fin.cases (record086_frame000_supported hcells) (Fin.cases (record086_frame001_supported hcells) (Fin.cases (record086_frame002_supported hcells) (Fin.cases (record086_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record086_frames_supported
theorem record087_frame000_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) :
    Supported record087 0 :=
  of_identity record087 0 (by decide +kernel)
def record087_frame001_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x205b01c7fb3f89f10f777a8bcf5d34e8b737398dc36e0c6f7b79154aa5e473a34506c8213f01f28d6265f299949494849623191505e82e31698b084fe26d11a08883561980c285d42cc1510a084c41e60e606c032416e09a04101f00f207803b81c80d005a02c8160094044020810007e03a018008804202000d8058026012007803801a00c00580280120060028008002000 } : Fields).get c.val)
theorem record087_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record087) (record087.maps 1) (record087.inverseMaps 1) record087_frame001_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record087) (record087.maps 1) (record087.inverseMaps 1) record087_frame001_indices (Fin.ofNat record087.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record087_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record087) (record087.maps 1)
      (record087.inverseMaps 1) record087_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record087_frame001_links_0000 record087_frame001_links_0064)
theorem record087_frame001_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) : Supported record087 1 :=
  of_group record087 1 (embedding record087) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record087_frame001_indices record087_frame001_graph record087_frame001_links
def record087_frame002_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xde4dd2dc1db4d81d74d62d58cd6cc4cb3ca6c73c66c54c4a9439007bc7a57157026ca6b75dd59948d47d4063f73c93ba2962862752672262181e71d917316515514513712b11b10a0da0cd0c00b40a609407e07a07707607507006605805705604a04404104003f03a03002202102001b01601301200f00e00d00c00b00a009006005002001000 } : Fields).get c.val)
theorem record087_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record087) (record087.maps 2) (record087.inverseMaps 2) record087_frame002_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record087) (record087.maps 2) (record087.inverseMaps 2) record087_frame002_indices (Fin.ofNat record087.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record087_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record087) (record087.maps 2)
      (record087.inverseMaps 2) record087_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record087_frame002_links_0000 record087_frame002_links_0064)
theorem record087_frame002_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) : Supported record087 2 :=
  of_group record087 2 (embedding record087) hcells Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record087_frame002_indices record087_frame002_graph record087_frame002_links
def record087_frame003_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x2b656aad35a2b2d62ab95669ed3aa694c691d21a4147e3c45979af09c6b866dad91852ee4e099d2023b450884cc19231c618b295c27c4d4851021f23c0730db1a030c4f09512022c4087a0d81a8338660ca1882c04c0961282204007a0f01d83805c088108200360580981201e0380680c0160280480600a00800800 } : Fields).get c.val)
theorem record087_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record087) (record087.maps 3) (record087.inverseMaps 3) record087_frame003_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record087) (record087.maps 3) (record087.inverseMaps 3) record087_frame003_indices (Fin.ofNat record087.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record087_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record087) (record087.maps 3)
      (record087.inverseMaps 3) record087_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record087_frame003_links_0000 record087_frame003_links_0064)
theorem record087_frame003_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) : Supported record087 3 :=
  of_group record087 3 (embedding record087) hcells Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record087_frame003_indices record087_frame003_graph record087_frame003_links
def record087_frame004_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0492.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0492.count (({ width := 9, code := 0x38bc3e06fb73b7d96c747a0cf66f2991c6e2adf6baf5729d4aa2d0a3d1881401e2ed7439576b75aac54aa14ca59027f3c9d4e873369a8c05d2d15caa522612c924823910803a1c8e06431178b85a29128783a1c0b8502411078381a0c058281206028080200 } : Fields).get c.val)
theorem record087_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (embedding (N := 44310) record087) (record087.maps 4) (record087.inverseMaps 4) record087_frame004_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (embedding (N := 44310) record087) (record087.maps 4) (record087.inverseMaps 4) record087_frame004_indices (Fin.ofNat record087.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record087_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (embedding (N := 44310) record087) (record087.maps 4)
      (record087.inverseMaps 4) record087_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record087_frame004_links_0000 record087_frame004_links_0064)
theorem record087_frame004_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) : Supported record087 4 :=
  of_group record087 4 (embedding record087) hcells Papers.RationalityTen.SharedFrameCatalogue.group0492
    Papers.RationalityTen.SharedFrameCatalogue.group0492_facts record087_frame004_indices record087_frame004_graph record087_frame004_links
def record087_frame005_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0478.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0478.count (({ width := 9, code := 0x2793b9c4de6933984be532692c8a3f1c8dc621f0c82c0df2f678bb9b6d664b1d7aba5aac93a9a4ca591889409f8de6e34998ca642f970a8512712c9246211047e3e1e8e87034198c8582b148a04e24110783a1c0b8502411078381a0c058281206028080200 } : Fields).get c.val)
theorem record087_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0478.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0478.localPairCheck (embedding (N := 44310) record087) (record087.maps 5) (record087.inverseMaps 5) record087_frame005_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0478.localPairCheck (embedding (N := 44310) record087) (record087.maps 5) (record087.inverseMaps 5) record087_frame005_indices (Fin.ofNat record087.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record087_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0478.localPairCheck (embedding (N := 44310) record087) (record087.maps 5)
      (record087.inverseMaps 5) record087_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record087_frame005_links_0000 record087_frame005_links_0064)
theorem record087_frame005_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) : Supported record087 5 :=
  of_group record087 5 (embedding record087) hcells Papers.RationalityTen.SharedFrameCatalogue.group0478
    Papers.RationalityTen.SharedFrameCatalogue.group0478_facts record087_frame005_indices record087_frame005_graph record087_frame005_links
theorem record087_frames_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) :
    ∀ f : Fin record087.g, Supported record087 f :=
  (Fin.cases (record087_frame000_supported hcells) (Fin.cases (record087_frame001_supported hcells) (Fin.cases (record087_frame002_supported hcells) (Fin.cases (record087_frame003_supported hcells) (Fin.cases (record087_frame004_supported hcells) (Fin.cases (record087_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record087_frames_supported
theorem record088_frame000_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) :
    Supported record088 0 :=
  of_identity record088 0 (by decide +kernel)
def record088_frame001_indices (c : Fin record088.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x13289894bda5bf26a92bc8e643f108878435e187058820c09e02ae346ba34c1a0ccf76782f71638aaa53b29ad36093e48523fd1da8e8470a33918a8be45aa2c51528a244ca25511a78336899b0c7c6262be145c9d24d126312cc95a4a724f926092448824191f48f046f2358e6463e2de16489bc4b624c11b88a843a20e0fd87bc3c818c0bc05a42a814709d04ac23010c08083dc1e00eb071836c1a80b9059829413e07703781ac0d006002e00fc06c032018009c04601b006002c0100070030014004001 } : Fields).get c.val)
theorem record088_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record088.data.requiredEdges q = true := by decide +kernel
theorem record088_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record088) (record088.maps 1) (record088.inverseMaps 1) record088_frame001_indices (Fin.ofNat record088.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record088_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record088) (record088.maps 1) (record088.inverseMaps 1) record088_frame001_indices (Fin.ofNat record088.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record088_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record088) (record088.maps 1)
      (record088.inverseMaps 1) record088_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record088_frame001_links_0000 record088_frame001_links_0064)
theorem record088_frame001_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) : Supported record088 1 :=
  of_group record088 1 (embedding record088) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record088_frame001_indices record088_frame001_graph record088_frame001_links
def record088_frame002_indices (c : Fin record088.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x11ef8ec4682313139893c3d21c4fff7f6bec5f3ef567a3bc4de08db4698321d83cc0f6042d9555aa4d51da8d92ea91047ea3e11c08d145d22050c685341ea0e10468133fe9fe0fd0718334181cbf45f22a893f09e04e926d12a092c48923b11a88c444d22390ec86641e20d8dd06282f81788a004d025b12408ec45c22110708043f41980c185dc2ce15d0a9051826c12c09304642100fd07583701a40b8059829413e07703781ac0d006002e00fc06c032018009c04601b006002c0100070030014004001 } : Fields).get c.val)
theorem record088_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record088.data.requiredEdges q = true := by decide +kernel
theorem record088_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record088) (record088.maps 2) (record088.inverseMaps 2) record088_frame002_indices (Fin.ofNat record088.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record088_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record088) (record088.maps 2) (record088.inverseMaps 2) record088_frame002_indices (Fin.ofNat record088.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record088_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record088) (record088.maps 2)
      (record088.inverseMaps 2) record088_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record088_frame002_links_0000 record088_frame002_links_0064)
theorem record088_frame002_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) : Supported record088 2 :=
  of_group record088 2 (embedding record088) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record088_frame002_indices record088_frame002_graph record088_frame002_links
def record088_frame003_indices (c : Fin record088.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0xa50a43a30a25a069fb9e99de98397796895f93c93492491d8728227e57bf7b67b27516df6a96976926335eb5d95d45cb5c85c15b05a75a059659458b58457a5785714f047d43d42d4243ba37536435b35434333e33933132a32531a31630f30a2ff2fd28823021720f1ca1bc1b31a71a019819018317b17713412511d1101081030fa0ee0e70e10dc0d60d20cc0c50c10ad0ac0a509f07706f06b06806005c03f03603203002702301b00c00b008007006005002001 } : Fields).get c.val)
theorem record088_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record088.data.requiredEdges q = true := by decide +kernel
theorem record088_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record088) (record088.maps 3) (record088.inverseMaps 3) record088_frame003_indices (Fin.ofNat record088.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record088_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record088) (record088.maps 3) (record088.inverseMaps 3) record088_frame003_indices (Fin.ofNat record088.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record088_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record088) (record088.maps 3)
      (record088.inverseMaps 3) record088_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record088_frame003_links_0000 record088_frame003_links_0064)
theorem record088_frame003_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) : Supported record088 3 :=
  of_group record088 3 (embedding record088) hcells Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record088_frame003_indices record088_frame003_graph record088_frame003_links
theorem record088_frames_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) :
    ∀ f : Fin record088.g, Supported record088 f :=
  (Fin.cases (record088_frame000_supported hcells) (Fin.cases (record088_frame001_supported hcells) (Fin.cases (record088_frame002_supported hcells) (Fin.cases (record088_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record088_frames_supported
theorem record089_frame000_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) :
    Supported record089 0 :=
  of_identity record089 0 (by decide +kernel)
def record089_frame001_indices (c : Fin record089.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x48763d11d28ccc60e2630ec868c0cdff2fe67d5be61e9ef0c77b36e1a60c0f5b22aed4b6a3d51aa5d92228ff47b23810c6853424208d0268083f41c54cd46092fc17cc9dc4e926d1338976476235116488e43b215106c6d830c17b8bc04f626812d892847a22e11088404061fa0db869031e1830bb85a42a414609c049823210807d83701a40a504f81dc0d005f02d812808803f01b80cc06002b014009c04802300d804801c00c005802000e006002800c004001 } : Fields).get c.val)
theorem record089_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record089.data.requiredEdges q = true := by decide +kernel
theorem record089_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record089) (record089.maps 1) (record089.inverseMaps 1) record089_frame001_indices (Fin.ofNat record089.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record089_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record089) (record089.maps 1) (record089.inverseMaps 1) record089_frame001_indices (Fin.ofNat record089.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record089_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record089) (record089.maps 1)
      (record089.inverseMaps 1) record089_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record089_frame001_links_0000 record089_frame001_links_0064)
theorem record089_frame001_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) : Supported record089 1 :=
  of_group record089 1 (embedding record089) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record089_frame001_indices record089_frame001_graph record089_frame001_links
def record089_frame002_indices (c : Fin record089.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xe0ede0dd4dbedb7d7dd5ed56d00cd2cc6cb0ca9c6fc50c48b1facea2d9a794f90a8db8c584c7f17c37a679a73e72a71b6f06de6d06a46375de59a56e56348e47e4744704634284183ff3e93db3c23ab3372e42c02aa25c2492392252192091fa1e61da1cd1a019118017316515313712b1190fe0f10e60dc0be0b209b09707506605d05904a04403f03703303002b02802702402301b01200e00c00b008007006005003002001 } : Fields).get c.val)
theorem record089_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record089.data.requiredEdges q = true := by decide +kernel
theorem record089_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record089) (record089.maps 2) (record089.inverseMaps 2) record089_frame002_indices (Fin.ofNat record089.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record089_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record089) (record089.maps 2) (record089.inverseMaps 2) record089_frame002_indices (Fin.ofNat record089.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record089_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record089) (record089.maps 2)
      (record089.inverseMaps 2) record089_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record089_frame002_links_0000 record089_frame002_links_0064)
theorem record089_frame002_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) : Supported record089 2 :=
  of_group record089 2 (embedding record089) hcells Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record089_frame002_indices record089_frame002_graph record089_frame002_links
def record089_frame003_indices (c : Fin record089.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x1e03b876aec3d6b9ff39e67c1f7e6f5dd1b8b67ebcd759df2ce0eba3692bed6bacb44e70cd1991306414768e314e2543f844f91d53826e8dbd7fafa5ecbc974ac5578ac15129d51a9fd192043e87b4da9ab340658c69822f85bcb315d2744bc9011a2244187b0ee1c434c650c016e27c4c08b1121b43105a0ae11c2103d06c0cc1802b05009c120230360480700c0160200380600a00c01001 } : Fields).get c.val)
theorem record089_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record089.data.requiredEdges q = true := by decide +kernel
theorem record089_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record089) (record089.maps 3) (record089.inverseMaps 3) record089_frame003_indices (Fin.ofNat record089.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record089_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record089) (record089.maps 3) (record089.inverseMaps 3) record089_frame003_indices (Fin.ofNat record089.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record089_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record089) (record089.maps 3)
      (record089.inverseMaps 3) record089_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record089_frame003_links_0000 record089_frame003_links_0064)
theorem record089_frame003_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) : Supported record089 3 :=
  of_group record089 3 (embedding record089) hcells Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record089_frame003_indices record089_frame003_graph record089_frame003_links
theorem record089_frames_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) :
    ∀ f : Fin record089.g, Supported record089 f :=
  (Fin.cases (record089_frame000_supported hcells) (Fin.cases (record089_frame001_supported hcells) (Fin.cases (record089_frame002_supported hcells) (Fin.cases (record089_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record089_frames_supported
theorem record090_frame000_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) :
    Supported record090 0 :=
  of_identity record090 0 (by decide +kernel)
def record090_frame001_indices (c : Fin record090.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x48c242d1ca8bdc5ca2630ec868c12a05afe07c93e35e9ef0c77b3b6dd9cea774d39cdb70d335b0aac14a0a3b51aa5e12268fe47b23810c6853411a04cfd07153351824bf05f32a993f89de4e926d11d88d444721d906c5ec2f01670ae44ee26812d88f445c22110187e836e1a40c8860c2ee16b0a9051827412608c84201b80d204101f00ee06f03581a00be05b025011007e03701980c004e02300d8058026012007803801800b005002000e006002800c004001 } : Fields).get c.val)
theorem record090_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record090.data.requiredEdges q = true := by decide +kernel
theorem record090_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record090) (record090.maps 1) (record090.inverseMaps 1) record090_frame001_indices (Fin.ofNat record090.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record090_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record090) (record090.maps 1) (record090.inverseMaps 1) record090_frame001_indices (Fin.ofNat record090.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record090_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record090) (record090.maps 1)
      (record090.inverseMaps 1) record090_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record090_frame001_links_0000 record090_frame001_links_0064)
theorem record090_frame001_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) : Supported record090 1 :=
  of_group record090 1 (embedding record090) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record090_frame001_indices record090_frame001_graph record090_frame001_links
def record090_frame002_indices (c : Fin record090.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x1e13bff66eb1d5b9ff39e67c2f836f3dbdb7767ebcd75ab754e9fd37a473be5bb9d672bad69acb452714d0991306414768a712a113e4754e09ba36f660c31802fa5ecb155e2a253a9fcf99ed3be750d99ab340634c117c2cc5749d12f244468891081ec3b8720d31943004f8980ec1c8368680ca1882d05708e1081e8360660c0138230360580981201e0380600b0140200380600a00c01001 } : Fields).get c.val)
theorem record090_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record090.data.requiredEdges q = true := by decide +kernel
theorem record090_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record090) (record090.maps 2) (record090.inverseMaps 2) record090_frame002_indices (Fin.ofNat record090.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record090_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record090) (record090.maps 2) (record090.inverseMaps 2) record090_frame002_indices (Fin.ofNat record090.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record090_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record090) (record090.maps 2)
      (record090.inverseMaps 2) record090_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record090_frame002_links_0000 record090_frame002_links_0064)
theorem record090_frame002_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) : Supported record090 2 :=
  of_group record090 2 (embedding record090) hcells Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record090_frame002_indices record090_frame002_graph record090_frame002_links
def record090_frame003_indices (c : Fin record090.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xa019fe9cd9b49b198496d96193192e8fb8e68e58ba89f89a87587386f86d8678077c26f76a86706496405ed5b559158357a55554e53953251d4a444d40e3e43dc38034131a30c3052e02d92c52be2ac1dd1d31c31bc1a71a119718517c17015f15813512e12712111710c0fc0f00e60d80ce0c90bd0b708207c07706f06b06805f05b04a04403f03703303002702301b01601301200f00e00c00b00a008007006005003002001 } : Fields).get c.val)
theorem record090_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record090.data.requiredEdges q = true := by decide +kernel
theorem record090_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record090) (record090.maps 3) (record090.inverseMaps 3) record090_frame003_indices (Fin.ofNat record090.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record090_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record090) (record090.maps 3) (record090.inverseMaps 3) record090_frame003_indices (Fin.ofNat record090.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record090_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record090) (record090.maps 3)
      (record090.inverseMaps 3) record090_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record090_frame003_links_0000 record090_frame003_links_0064)
theorem record090_frame003_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) : Supported record090 3 :=
  of_group record090 3 (embedding record090) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record090_frame003_indices record090_frame003_graph record090_frame003_links
def record090_frame004_indices (c : Fin record090.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x194326e32c4387700decbd574ee8dbdb616b6cd589b0f5c6b7567ac95768fcf88a709e03bf87e8efdd239671ce29b73676aad399f2ea56ea4540a7e47c8810920b40c7a0f11d03946e8a69482804ec9512824646c8b11020a408770e91c637c6c8d3196318608bb16c2c8530a30ee1c8368670c81842d05708e1081e8360640bc138230360580981201e0380600b0140200380600a00c01001 } : Fields).get c.val)
theorem record090_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record090.data.requiredEdges q = true := by decide +kernel
theorem record090_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record090) (record090.maps 4) (record090.inverseMaps 4) record090_frame004_indices (Fin.ofNat record090.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record090_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record090) (record090.maps 4) (record090.inverseMaps 4) record090_frame004_indices (Fin.ofNat record090.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record090_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record090) (record090.maps 4)
      (record090.inverseMaps 4) record090_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record090_frame004_links_0000 record090_frame004_links_0064)
theorem record090_frame004_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) : Supported record090 4 :=
  of_group record090 4 (embedding record090) hcells Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record090_frame004_indices record090_frame004_graph record090_frame004_links
def record090_frame005_indices (c : Fin record090.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x1cbb92ef4dc9b8761eb2d5598f2ee3fc5389b00de0bbf6c2d6da2b3f652af54d9a728e3ec6e8d70de0a408804ff5ee3d5782eedd4357644bed75ae855ca2d3f2784e69692aa4447c8b8ca98e3085f0b31622b4534a213c256494861051f83e0778e41ac340638bb16a2bc4d8960fa1e03986d0d21982f05b0941101f8370660c0138230360580981201e0380600b0140200380600a00c01001 } : Fields).get c.val)
theorem record090_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record090.data.requiredEdges q = true := by decide +kernel
theorem record090_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record090) (record090.maps 5) (record090.inverseMaps 5) record090_frame005_indices (Fin.ofNat record090.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record090_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record090) (record090.maps 5) (record090.inverseMaps 5) record090_frame005_indices (Fin.ofNat record090.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record090_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record090) (record090.maps 5)
      (record090.inverseMaps 5) record090_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record090_frame005_links_0000 record090_frame005_links_0064)
theorem record090_frame005_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) : Supported record090 5 :=
  of_group record090 5 (embedding record090) hcells Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record090_frame005_indices record090_frame005_graph record090_frame005_links
def record090_frame006_indices (c : Fin record090.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x5db2ebb6afb3859b6b7b573ab3d1628913b39b74dae58b273934c6ae3271668a7c495f42e985cc2b5d4b6a2250925591c88af44c220d0448103ee1f2cf306642d1949c9dc4de2110ec06f63641a78bb85b82a814b89903aa1ce0e106ec34819f0cc062430617c0b6859c29614409e04d825e12708d044c2160fe07a83b81b20d304101f00ee06f03581a00be05b025011007e03701980c004e02300d8058026012007803801800b005002000e006002800c004001 } : Fields).get c.val)
theorem record090_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record090.data.requiredEdges q = true := by decide +kernel
theorem record090_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record090) (record090.maps 6) (record090.inverseMaps 6) record090_frame006_indices (Fin.ofNat record090.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record090_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record090) (record090.maps 6) (record090.inverseMaps 6) record090_frame006_indices (Fin.ofNat record090.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record090_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record090) (record090.maps 6)
      (record090.inverseMaps 6) record090_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record090_frame006_links_0000 record090_frame006_links_0064)
theorem record090_frame006_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) : Supported record090 6 :=
  of_group record090 6 (embedding record090) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record090_frame006_indices record090_frame006_graph record090_frame006_links
def record090_frame007_indices (c : Fin record090.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x92491d8f78e18dd8b189488b86585e83882281e7f27d57cc79f79978978377571e6e45e65a557355554e4f84c84ac49c49445c44d42941c3fe3ad36c33a31c3152bf28f27326325b2212141ed1e41c515f15b15414f13b13813212812511f1121101000fb0f50f00ea0e40da0d40ce0c50be0b80aa0a707807406f06806406105805404704303e03703303002702301b01601301200f00e00c00b00a008007006005003002001 } : Fields).get c.val)
theorem record090_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record090.data.requiredEdges q = true := by decide +kernel
theorem record090_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record090) (record090.maps 7) (record090.inverseMaps 7) record090_frame007_indices (Fin.ofNat record090.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record090_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record090) (record090.maps 7) (record090.inverseMaps 7) record090_frame007_indices (Fin.ofNat record090.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record090_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record090) (record090.maps 7)
      (record090.inverseMaps 7) record090_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record090_frame007_links_0000 record090_frame007_links_0064)
theorem record090_frame007_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) : Supported record090 7 :=
  of_group record090 7 (embedding record090) hcells Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record090_frame007_indices record090_frame007_graph record090_frame007_links
def record090_frame008_indices (c : Fin record090.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0x11863045189712a20c3886b09610c1881f03a003f97f0fb5f5be57c6f75e2bb66b8cf99531a62ebc16b2c7580ae95129c51aa213da5e47287d06a0b3d4758e39c237868ccf18e3145f49111f234454831031fc3d0778eb1c4380670ca18a3085e8b715c2a45289f1342584608a0d81a8328600ba1682904e0820fc1d03305e0b0138230360580981201e0380600b0140200380600a00c01001 } : Fields).get c.val)
theorem record090_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record090.data.requiredEdges q = true := by decide +kernel
theorem record090_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record090) (record090.maps 8) (record090.inverseMaps 8) record090_frame008_indices (Fin.ofNat record090.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record090_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record090) (record090.maps 8) (record090.inverseMaps 8) record090_frame008_indices (Fin.ofNat record090.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record090_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record090) (record090.maps 8)
      (record090.inverseMaps 8) record090_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record090_frame008_links_0000 record090_frame008_links_0064)
theorem record090_frame008_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) : Supported record090 8 :=
  of_group record090 8 (embedding record090) hcells Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record090_frame008_indices record090_frame008_graph record090_frame008_links
theorem record090_frames_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) :
    ∀ f : Fin record090.g, Supported record090 f :=
  (Fin.cases (record090_frame000_supported hcells) (Fin.cases (record090_frame001_supported hcells) (Fin.cases (record090_frame002_supported hcells) (Fin.cases (record090_frame003_supported hcells) (Fin.cases (record090_frame004_supported hcells) (Fin.cases (record090_frame005_supported hcells) (Fin.cases (record090_frame006_supported hcells) (Fin.cases (record090_frame007_supported hcells) (Fin.cases (record090_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
#print axioms record090_frames_supported
theorem record091_frame000_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) :
    Supported record091 0 :=
  of_identity record091 0 (by decide +kernel)
def record091_frame001_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x510a84f4029f3cdae6af33498ec70234f1888b943f21cf0c185436a58a4c3e5a227b53b29884af253d29093b48aa43921090147ca3c91d88e546e9f28cb064326f933c8aa44321890888244021f80f807a227013007983a81c20d9868c3261810b885882aa1500a48508276132096849823a116088842c2060fc07b83b81d00e406f03581a00a504f826810407c03b812808803f01800ac050027012008c04202000e8070036016009804801e00e006002c010007 } : Fields).get c.val)
theorem record091_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record091) (record091.maps 1) (record091.inverseMaps 1) record091_frame001_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record091) (record091.maps 1) (record091.inverseMaps 1) record091_frame001_indices (Fin.ofNat record091.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record091_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record091) (record091.maps 1)
      (record091.inverseMaps 1) record091_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record091_frame001_links_0000 record091_frame001_links_0064)
theorem record091_frame001_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) : Supported record091 1 :=
  of_group record091 1 (embedding record091) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record091_frame001_indices record091_frame001_graph record091_frame001_links
def record091_frame002_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x47da3c31a78c945162631008764021fe4fba7d23d81e9ef1d78634c181ac065b0a8f146a974487a4011f28dd433215909283941320590127f93f51c54bf25f327713a48e846822e114088a43921690848342f617809a04b624c11e88b844221210187e83d01de0e586e834e18d0c285e42d015c0aa052026e12b093845820a0fc07603681a00a504f826810407c03b812808803f01800ac050027012008c04202000e8070036016009804801e00e006002c010007 } : Fields).get c.val)
theorem record091_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record091) (record091.maps 2) (record091.inverseMaps 2) record091_frame002_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record091) (record091.maps 2) (record091.inverseMaps 2) record091_frame002_indices (Fin.ofNat record091.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record091_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record091) (record091.maps 2)
      (record091.inverseMaps 2) record091_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record091_frame002_links_0000 record091_frame002_links_0064)
theorem record091_frame002_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) : Supported record091 2 :=
  of_group record091 2 (embedding record091) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record091_frame002_indices record091_frame002_graph record091_frame002_links
def record091_frame003_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1079.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1079.count (({ width := 11, code := 0x19cf36e63cbb93724e43c7f89310e1bc31833035fcbef62e925209ed23e45c4683b052084067caf75eb3cf78cef9dbbb0752dd986b095049f5252444788dd182294428650a18e312554a714627c4dc989292484808c915220428828fe1f43cc758e51c2368690cc1943085e8ba1682b4548951262383e0780e61242203f0600ac1402704808c1082003a0700d8160260480780e01802c04007 } : Fields).get c.val)
theorem record091_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record091) (record091.maps 3) (record091.inverseMaps 3) record091_frame003_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record091) (record091.maps 3) (record091.inverseMaps 3) record091_frame003_indices (Fin.ofNat record091.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record091_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record091) (record091.maps 3)
      (record091.inverseMaps 3) record091_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record091_frame003_links_0000 record091_frame003_links_0064)
theorem record091_frame003_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) : Supported record091 3 :=
  of_group record091 3 (embedding record091) hcells Papers.RationalityTen.SharedFrameCatalogue.group1079
    Papers.RationalityTen.SharedFrameCatalogue.group1079_facts record091_frame003_indices record091_frame003_graph record091_frame003_links
theorem record091_frames_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) :
    ∀ f : Fin record091.g, Supported record091 f :=
  (Fin.cases (record091_frame000_supported hcells) (Fin.cases (record091_frame001_supported hcells) (Fin.cases (record091_frame002_supported hcells) (Fin.cases (record091_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record091_frames_supported
theorem record092_frame000_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) :
    Supported record092 0 :=
  of_identity record092 0 (by decide +kernel)
def record092_frame001_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x927c8f23c31ce89142be032f2d763391db42d956b7b58da78c5d5fc2af94b6a57509278936a93f49d246d1de8c345c223110c86e4192038ffc7da3e91b00ca864e2ff9748b6c5492a294549ee4e226612dc96649f232115887842e2130d846b02bf15c097c47223111488543e41e50ee05902b8146097848822c10307c03ac13407c03c818c0c005902b015408804101580a004001e00e805802600f0070034012008002000c004000 } : Fields).get c.val)
theorem record092_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record092_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record092) (record092.maps 1)
      (record092.inverseMaps 1) record092_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record092_frame001_links_0000 record092_frame001_links_0064)
theorem record092_frame001_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) : Supported record092 1 :=
  of_group record092 1 (embedding record092) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record092_frame001_indices record092_frame001_graph record092_frame001_links
theorem record092_frames_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) :
    ∀ f : Fin record092.g, Supported record092 f :=
  (Fin.cases (record092_frame000_supported hcells) (Fin.cases (record092_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record092_frames_supported
theorem record093_frame000_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) :
    Supported record093 0 :=
  of_identity record093 0 (by decide +kernel)
def record093_frame001_indices (c : Fin record093.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x258925692248963d11d68dbc65a2270a080bbc75d6ce79732b915c0cdbc6d6b685b2ad6f6b1b4f18babf855f296d4aaa024e926d527e8c344622190f880e3ed1f48d8065431f9838bfe5e12e916d8a9252a28293889b44b725992848e245622490b884c3611a68c9060c2d915f8ab84da25f12388e446222610887c83ca1d80b2056425e12208b04181f40eb03e01e40c606002b015409204402080fc056028010807803a016009804001e00e006802c012008002000c004000 } : Fields).get c.val)
theorem record093_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record093.data.requiredEdges q = true := by decide +kernel
theorem record093_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record093) (record093.maps 1) (record093.inverseMaps 1) record093_frame001_indices (Fin.ofNat record093.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record093_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record093) (record093.maps 1) (record093.inverseMaps 1) record093_frame001_indices (Fin.ofNat record093.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record093_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record093) (record093.maps 1)
      (record093.inverseMaps 1) record093_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record093_frame001_links_0000 record093_frame001_links_0064)
theorem record093_frame001_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) : Supported record093 1 :=
  of_group record093 1 (embedding record093) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record093_frame001_indices record093_frame001_graph record093_frame001_links
theorem record093_frames_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) :
    ∀ f : Fin record093.g, Supported record093 f :=
  (Fin.cases (record093_frame000_supported hcells) (Fin.cases (record093_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record095_frame001_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x92bc93a42d1e98f046a2345124858c085e90f14770bab5c9ee156e5b6b199cc5d5fbab014b8a124fba78938e9b54a0a4ad1de8de46822e114e89944321cd06480b3ff1f5cfa46c0329979cb745b62a49514a2a4f7271133096e4b325510986c434a1830bd05b22c715f8ad84ba23711888a44061f20f2874033818d0bc85a82c815c0a104cc24411608183ec1d009504902040d005902b015408804101d00dc05602800f807803a0100070034012008002800c004000 } : Fields).get c.val)
theorem record095_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record095) (record095.maps 1) (record095.inverseMaps 1) record095_frame001_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record095) (record095.maps 1) (record095.inverseMaps 1) record095_frame001_indices (Fin.ofNat record095.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record095_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record095) (record095.maps 1)
      (record095.inverseMaps 1) record095_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record095_frame001_links_0000 record095_frame001_links_0064)
theorem record095_frame001_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) : Supported record095 1 :=
  of_group record095 1 (embedding record095) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record095_frame001_indices record095_frame001_graph record095_frame001_links
theorem record095_frames_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) :
    ∀ f : Fin record095.g, Supported record095 f :=
  (Fin.cases (record095_frame000_supported hcells) (Fin.cases (record095_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record095_frames_supported
theorem record096_frame000_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) :
    Supported record096 0 :=
  of_identity record096 0 (by decide +kernel)
def record096_frame001_indices (c : Fin record096.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x48ae4251bd8d244be20b0bc8494081fb6f907bbbd21e28ee1756b93dc2adcb6d633398babf756029714249f74f1271d36a94146f234114e89944321dd0167d73e91b00ca6632307179cbc25ba2db1524a2a4f7271133096e4b325390986c43151830bd05d02d91638afc55e27812e894846e231111080c3e41e50ea867031a1790b5059028413309104582100fb074025412408102b015409204402080e806e02b014007c03c01d00d804402000e0068030012008002800c004000 } : Fields).get c.val)
theorem record096_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record096.data.requiredEdges q = true := by decide +kernel
theorem record096_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record096) (record096.maps 1) (record096.inverseMaps 1) record096_frame001_indices (Fin.ofNat record096.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record096_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record096) (record096.maps 1) (record096.inverseMaps 1) record096_frame001_indices (Fin.ofNat record096.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record096_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record096) (record096.maps 1)
      (record096.inverseMaps 1) record096_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record096_frame001_links_0000 record096_frame001_links_0064)
theorem record096_frame001_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) : Supported record096 1 :=
  of_group record096 1 (embedding record096) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record096_frame001_indices record096_frame001_graph record096_frame001_links
theorem record096_frames_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) :
    ∀ f : Fin record096.g, Supported record096 f :=
  (Fin.cases (record096_frame000_supported hcells) (Fin.cases (record096_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record098_frames_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSix0.cells (embedding record098 c)) :
    ∀ f : Fin record098.g, Supported record098 f :=
  (Fin.cases (record098_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record098_frames_supported
theorem record099_frame000_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) :
    Supported record099 0 :=
  of_identity record099 0 (by decide +kernel)
theorem record099_frames_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) :
    ∀ f : Fin record099.g, Supported record099 f :=
  (Fin.cases (record099_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record099_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041
