module

public import Papers.GraphicalZonotopes.TetrahedralGrowth
public import Papers.GraphicalZonotopes.CliqueDegreeObstruction

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem TetrahedralGrowth.four_isClique {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hS : S.card=4) : G.IsClique S := by
  cases h with
  | base C hc hcl => exact hcl
  | @attach R h u hu T hT hTR hcl ha =>
    have hr := h.card_ge_four
    rw [card_insert_of_notMem hu] at hS
    omega

theorem TetrahedralGrowth.five_structure {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hS : S.card=5) :
    ∃ C T : Finset V, ∃ e : V, C.card=4 ∧ G.IsClique C ∧
      T.card=3 ∧ T ⊆ C ∧ e ∉ C ∧ (∀ v ∈ T,G.Adj e v) ∧ S=insert e C := by
  cases h with
  | base C hc hcl => omega
  | @attach R h u hu T hT hTR hcl ha =>
    have hr : R.card=4 := by rw [card_insert_of_notMem hu] at hS; omega
    exact ⟨R,T,u,hr,h.four_isClique hr,hT,hTR,hu,ha,rfl⟩

def sixPreimage (f : Fin 6 ↪ V) (T : Finset V) : Finset (Fin 6) :=
  univ.filter (fun i => f i ∈ T)

theorem sixPreimage_image (f : Fin 6 ↪ V) (T : Finset V)
    (hT : ∀ v ∈ T,v ∈ Set.range f) : (sixPreimage f T).map f=T := by
  ext v
  constructor
  · intro hv
    obtain ⟨i,hi,rfl⟩ := mem_map.mp hv
    exact (mem_filter.mp hi).2
  · intro hv
    obtain ⟨i,rfl⟩ := hT v hv
    exact mem_map.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hv⟩,rfl⟩

theorem sixPreimage_card (f : Fin 6 ↪ V) (T : Finset V)
    (hT : ∀ v ∈ T,v ∈ Set.range f) : (sixPreimage f T).card=T.card := by
  have h := congrArg Finset.card (sixPreimage_image f T hT)
  simpa using h

/-- Every six-vertex growth stage is exactly an embedded instance of the
local six-vertex obstruction. No graph edges are discarded by the pullback. -/
theorem TetrahedralGrowth.six_model {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hS : S.card=6) :
    ∃ f : Fin 6 ↪ V, Set.range f=(S : Set V) ∧
      (G.comap f).IsClique ({0,1,2,3} : Finset (Fin 6)) ∧
      (G.comap f).IsClique ({0,1,2,4} : Finset (Fin 6)) ∧
      CliqueDegree.HasSixthAttachment (G.comap f) := by
  classical
  cases h with
  | base C hc hcl => omega
  | @attach R h f hf U hU hUR hclU hadj =>
    have hR : R.card=5 := by rw [card_insert_of_notMem hf] at hS; omega
    obtain ⟨C,T,e,hC,hclC,hT,hTC,he,heAdj,hRC⟩ := h.five_structure hR
    have hdiff : (C \ T).card=1 := by rw [card_sdiff_of_subset hTC,hC,hT]
    obtain ⟨d,hd⟩ := card_eq_one.mp hdiff
    have hdmem : d ∈ C \ T := by rw [hd]; simp
    have hdC := (mem_sdiff.mp hdmem).1
    have hdT := (mem_sdiff.mp hdmem).2
    have hCT : C=insert d T := by
      have hu := union_sdiff_of_subset hTC
      rw [hd] at hu
      simpa [union_comm] using hu.symm
    obtain ⟨a,b,c,hab,hac,hbc,hTabc⟩ := card_eq_three.mp hT
    have haC : a ∈ C := hTC (by simp [hTabc])
    have hbC : b ∈ C := hTC (by simp [hTabc])
    have hcC : c ∈ C := hTC (by simp [hTabc])
    have hda : d ≠ a := by intro hda; exact hdT (by simp [hda,hTabc])
    have hdb : d ≠ b := by intro hdb; exact hdT (by simp [hdb,hTabc])
    have hdc : d ≠ c := by intro hdc; exact hdT (by simp [hdc,hTabc])
    have hea : e ≠ a := by
      intro heq
      apply he
      simpa only [heq] using haC
    have heb : e ≠ b := by
      intro heq
      apply he
      simpa only [heq] using hbC
    have hec : e ≠ c := by
      intro heq
      apply he
      simpa only [heq] using hcC
    have hed : e ≠ d := by
      intro heq
      apply he
      simpa only [heq] using hdC
    have hCR : C ⊆ R := by rw [hRC]; exact subset_insert _ _
    have heR : e ∈ R := by rw [hRC]; exact mem_insert_self _ _
    have hfa : f ≠ a := by
      intro heq
      apply hf
      simpa only [heq] using hCR haC
    have hfb : f ≠ b := by
      intro heq
      apply hf
      simpa only [heq] using hCR hbC
    have hfc : f ≠ c := by
      intro heq
      apply hf
      simpa only [heq] using hCR hcC
    have hfd : f ≠ d := by
      intro heq
      apply hf
      simpa only [heq] using hCR hdC
    have hfe : f ≠ e := by
      intro heq
      apply hf
      simpa only [heq] using heR
    let names : Fin 6 → V := ![a,b,c,d,e,f]
    have hinj : Function.Injective names := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp only [names,Matrix.cons_val_zero,Matrix.cons_val_succ,
          Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
          Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] at hij ⊢
      all_goals first | rfl | exact False.elim (hab hij) | exact False.elim (hab hij.symm) |
        exact False.elim (hac hij) | exact False.elim (hac hij.symm) |
        exact False.elim (hbc hij) | exact False.elim (hbc hij.symm) |
        exact False.elim (hda hij) | exact False.elim (hda hij.symm) |
        exact False.elim (hdb hij) | exact False.elim (hdb hij.symm) |
        exact False.elim (hdc hij) | exact False.elim (hdc hij.symm) |
        exact False.elim (hea hij) | exact False.elim (hea hij.symm) |
        exact False.elim (heb hij) | exact False.elim (heb hij.symm) |
        exact False.elim (hec hij) | exact False.elim (hec hij.symm) |
        exact False.elim (hed hij) | exact False.elim (hed hij.symm) |
        exact False.elim (hfa hij) | exact False.elim (hfa hij.symm) |
        exact False.elim (hfb hij) | exact False.elim (hfb hij.symm) |
        exact False.elim (hfc hij) | exact False.elim (hfc hij.symm) |
        exact False.elim (hfd hij) | exact False.elim (hfd hij.symm) |
        exact False.elim (hfe hij) | exact False.elim (hfe hij.symm)
    let emb : Fin 6 ↪ V := ⟨names,hinj⟩
    have hnames : ∀ v,v ∈ insert f R ↔ ∃ i : Fin 6,emb i=v := by
      intro v
      rw [hRC,hCT,hTabc]
      simp only [mem_insert,mem_singleton]
      constructor
      · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
        · exact ⟨5,rfl⟩
        · exact ⟨4,rfl⟩
        · exact ⟨3,rfl⟩
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
        · exact ⟨2,rfl⟩
      · rintro ⟨i,rfl⟩
        fin_cases i <;> simp [emb,names]
    have hrange : Set.range emb=((insert f R : Finset V) : Set V) := by
      ext v
      exact (hnames v).symm
    have hfirst : ∀ i ∈ ({0,1,2,3} : Finset (Fin 6)),emb i ∈ C := by
      intro i hi
      simp only [mem_insert,mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact haC
      · exact hbC
      · exact hcC
      · exact hdC
    have hsecond : ∀ i ∈ ({0,1,2,4} : Finset (Fin 6)),emb i ∈ insert e T := by
      intro i hi
      simp only [mem_insert,mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp [emb,names,hTabc]
    have hclSecond : G.IsClique (insert e T : Finset V) := by
      intro x hx y hy hxy
      rcases mem_insert.mp hx with hxe | hxT
      · rcases mem_insert.mp hy with hye | hyT
        · exact False.elim (hxy (hxe.trans hye.symm))
        · rw [hxe]
          exact heAdj y hyT
      · rcases mem_insert.mp hy with hye | hyT
        · rw [hye]
          exact G.adj_symm (heAdj x hxT)
        · exact hclC (hTC hxT) (hTC hyT) hxy
    refine ⟨emb,hrange,?_,?_,?_⟩
    · intro i hi j hj hij
      exact hclC (hfirst i hi) (hfirst j hj) (fun he => hij (emb.injective he))
    · intro i hi j hj hij
      exact hclSecond (hsecond i hi) (hsecond j hj) (fun he => hij (emb.injective he))
    · have hUrange : ∀ v ∈ U,v ∈ Set.range emb := by
        intro v hv
        rw [hrange]
        exact mem_insert_of_mem (hUR hv)
      refine ⟨sixPreimage emb U,(sixPreimage_card emb U hUrange).trans hU,?_,?_,?_⟩
      · intro h5
        have hmem := (mem_filter.mp h5).2
        change f ∈ U at hmem
        exact hf (hUR hmem)
      · intro i hi j hj hij
        exact hclU (mem_filter.mp hi).2 (mem_filter.mp hj).2
          (fun he => hij (emb.injective he))
      · intro i hi
        exact G.adj_symm (hadj (emb i) (mem_filter.mp hi).2)

theorem degree_comap_le (G : SimpleGraph V) (f : Fin 6 ↪ V) (i : Fin 6) :
    (G.comap f).degree i ≤ G.degree (f i) := by
  classical
  have hsub : ((G.comap f).neighborFinset i).map f ⊆ G.neighborFinset (f i) := by
    intro v hv
    obtain ⟨j,hj,rfl⟩ := mem_map.mp hv
    exact (G.mem_neighborFinset _ _).mpr ((G.comap f).mem_neighborFinset _ _ |>.mp hj)
  have hcard := card_le_card hsub
  simpa only [card_map,SimpleGraph.card_neighborFinset_eq_degree] using hcard

/-- The local certificate applies to every triangle of every six-vertex
growth stage inside an arbitrary finite ambient graph. -/
theorem TetrahedralGrowth.six_triangle_saturated {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hS : S.card=6) (T : Finset V)
    (hT : T.card=3) (hTS : T ⊆ S) (hcT : G.IsClique T) :
    ∃ v ∈ T,5 ≤ G.degree v := by
  classical
  obtain ⟨f,hrange,h₃,h₄,ha⟩ := h.six_model hS
  have hTrange : ∀ v ∈ T,v ∈ Set.range f := by
    intro v hv
    rw [hrange]
    exact hTS hv
  have hc : (G.comap f).IsClique (sixPreimage f T) := by
    intro i hi j hj hij
    exact hcT (mem_filter.mp hi).2 (mem_filter.mp hj).2
      (fun he => hij (f.injective he))
  obtain ⟨i,hi,hdeg⟩ := CliqueDegree.six_vertex_obstruction_graph (G.comap f)
    h₃ h₄ ha (sixPreimage f T) ((sixPreimage_card f T hTrange).trans hT) hc
  exact ⟨f i,(mem_filter.mp hi).2,hdeg.trans (degree_comap_le G f i)⟩

theorem TetrahedralGrowth.six_cannot_attach_at_degree_five {G : SimpleGraph V}
    {S : Finset V} (h : TetrahedralGrowth G S) (hS : S.card=6)
    (hdeg : ∀ v,G.degree v ≤ 5) (u : V) (hu : u ∉ S) (T : Finset V)
    (hT : T.card=3) (hTS : T ⊆ S) (hcT : G.IsClique T)
    (hadj : ∀ v ∈ T,G.Adj u v) : False := by
  classical
  obtain ⟨f,hrange,h₃,h₄,ha⟩ := h.six_model hS
  have hTrange : ∀ v ∈ T,v ∈ Set.range f := by
    intro v hv
    rw [hrange]
    exact hTS hv
  apply CliqueDegree.no_seventh_triangle_attachment G f hdeg h₃ h₄ ha u
    (by simpa [hrange] using hu) (sixPreimage f T)
    ((sixPreimage_card f T hTrange).trans hT)
  · intro i hi j hj hij
    exact hcT (mem_filter.mp hi).2 (mem_filter.mp hj).2
      (fun he => hij (f.injective he))
  · intro i hi
    exact G.adj_symm (hadj (f i) (mem_filter.mp hi).2)

theorem clique_degree_lower (G : SimpleGraph V) (C : Finset V)
    (hC : G.IsClique C) (v : V) (hv : v ∈ C) : C.card-1 ≤ G.degree v := by
  classical
  have hsub : C.erase v ⊆ G.neighborFinset v := by
    intro w hw
    have hm := mem_erase.mp hw
    exact (G.mem_neighborFinset _ _).mpr (hC hv hm.2 (Ne.symm hm.1))
  have h := card_le_card hsub
  simpa only [card_erase_of_mem hv,SimpleGraph.card_neighborFinset_eq_degree] using h

theorem TetrahedralGrowth.contains_triangle {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) :
    ∃ T : Finset V,T.card=3 ∧ T ⊆ S ∧ G.IsClique T := by
  induction h with
  | base C hc hcl =>
    obtain ⟨T,hTC,hT⟩ := exists_subset_card_eq (show 3 ≤ C.card by omega)
    exact ⟨T,hT,hTC,fun u hu v hv huv => hcl (hTC hu) (hTC hv) huv⟩
  | attach h u hu T hT hsub hcl hadj ih =>
    obtain ⟨A,hA,hAS,hclA⟩ := ih
    exact ⟨A,hA,hAS.trans (subset_insert _ _),hclA⟩

theorem TetrahedralGrowth.five_has_degree_four {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hS : S.card=5) : ∃ v,4 ≤ G.degree v := by
  classical
  obtain ⟨C,T,e,hC,hclC,hT,hTC,he,heAdj,hSC⟩ := h.five_structure hS
  obtain ⟨v,hv⟩ := card_pos.mp (show 0<T.card by omega)
  have hvC := hTC hv
  have heErase : e ∉ C.erase v := fun h => he (mem_of_mem_erase h)
  have hsub : insert e (C.erase v) ⊆ G.neighborFinset v := by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact (G.mem_neighborFinset _ _).mpr (G.adj_symm (heAdj v hv))
    · obtain ⟨hwv,hwC⟩ := mem_erase.mp hw
      exact (G.mem_neighborFinset _ _).mpr (hclC hvC hwC (Ne.symm hwv))
  have hcard := card_le_card hsub
  rw [card_insert_of_notMem heErase,card_erase_of_mem hvC,hC] at hcard
  exact ⟨v,hcard⟩

theorem TetrahedralGrowth.seven_has_degree_six {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hS : 7 ≤ S.card) : ∃ v,6 ≤ G.degree v := by
  classical
  induction h with
  | base C hc hcl => omega
  | @attach R h u hu T hT hTR hcl hadj ih =>
    by_cases hlarge : 7 ≤ R.card
    · exact ih hlarge
    · have hR : R.card=6 := by rw [card_insert_of_notMem hu] at hS; omega
      by_contra hno
      have hdeg : ∀ v,G.degree v ≤ 5 := by
        intro v
        have hv : ¬6 ≤ G.degree v := fun hv => hno ⟨v,hv⟩
        omega
      exact h.six_cannot_attach_at_degree_five hR hdeg u hu T hT hTR hcl hadj

/-- The complete arbitrary-size degree bound, using the finite certificate
only at the six-to-seven transition of a genuine tetrahedral growth. -/
theorem TetrahedralGrowth.degree_lower {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) : ∃ v,min (S.card-1) 6 ≤ G.degree v := by
  classical
  have hmin := h.card_ge_four
  by_cases h4 : S.card=4
  · obtain ⟨v,hv⟩ := card_pos.mp (show 0<S.card by omega)
    have hd := clique_degree_lower G S (h.four_isClique h4) v hv
    exact ⟨v,by simpa [h4] using hd⟩
  · by_cases h5 : S.card=5
    · obtain ⟨v,hv⟩ := h.five_has_degree_four h5
      exact ⟨v,by simpa [h5] using hv⟩
    · by_cases h6 : S.card=6
      · obtain ⟨T,hT,hTS,hclT⟩ := h.contains_triangle
        obtain ⟨v,hv,hdeg⟩ := h.six_triangle_saturated h6 T hT hTS hclT
        exact ⟨v,by simpa [h6] using hdeg⟩
      · obtain ⟨v,hv⟩ := h.seven_has_degree_six (by omega)
        exact ⟨v,(min_le_right _ _).trans hv⟩

theorem maximum_degree_bound_of_connected_tetrahedra (G : SimpleGraph V)
    (F : Finset (Finset V)) (hne : F.Nonempty)
    (hcl : ∀ C ∈ F,C.card=4 ∧ G.IsClique C)
    (hconn : (tetrahedronGraph F).Preconnected) (hcover : F.biUnion id=univ) :
    min (Fintype.card V-1) 6 ≤ G.maxDegree := by
  classical
  have hg := tetrahedralGrowth_of_connected_family G F hne hcl hconn
  rw [hcover] at hg
  obtain ⟨v,hv⟩ := hg.degree_lower
  have h := hv.trans (G.degree_le_maxDegree v)
  simpa using h

end GraphicalZonotopes
