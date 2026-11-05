module

public import Papers.GraphicalZonotopes.ThreeTreeIncidenceTree
public import Papers.GraphicalZonotopes.ThreeTreeDeletion

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace GraphicalZonotopes.FourPartThreeTreeCounts
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def Proper (c : V → Fin 4) (G : SimpleGraph V) : Prop :=
  ∀ u v,G.Adj u v → c u≠c v

def Avoids (c : V → Fin 4) (i : Fin 4) (T : Finset V) : Prop :=
  ∀ v∈T,c v≠i

def missingFacet (c : V → Fin 4) (i : Fin 4) (D : Finset V) : Finset V :=
  D.filter (fun v => c v≠i)

def avoidingTriangles (G : SimpleGraph V) (c : V → Fin 4) (i : Fin 4) :
    Finset (Finset V) := (triangles G).filter (Avoids c i)

@[simp] theorem mem_avoidingTriangles (G : SimpleGraph V) (c : V → Fin 4)
    (i : Fin 4) (T : Finset V) :
    T∈avoidingTriangles G c i ↔ T.card=3 ∧ G.IsClique T ∧ Avoids c i T := by
  simp only [avoidingTriangles,mem_filter,mem_triangles,and_assoc]

theorem color_injective_on_clique {G : SimpleGraph V} {c : V → Fin 4}
    (hc : Proper c G) {D : Finset V} (hD : G.IsClique D) : Set.InjOn c D := by
  intro u hu v hv he
  by_contra huv
  exact hc u v (hD hu hv huv) he

theorem color_count_tetrahedron {G : SimpleGraph V} {c : V → Fin 4}
    (hc : Proper c G) {D : Finset V} (hD : D.card=4) (hcl : G.IsClique D)
    (i : Fin 4) : (D.filter (fun v => c v=i)).card=1 := by
  have hinj := color_injective_on_clique hc hcl
  have himage : (D.image c).card=4 := (card_image_iff.mpr hinj).trans hD
  have hsurj : D.image c=univ := eq_of_subset_of_card_le (subset_univ _) (by simpa using himage.ge)
  have hi : i∈D.image c := by rw [hsurj]; simp
  obtain ⟨v,hv,hvi⟩ := mem_image.mp hi
  have he : D.filter (fun u => c u=i)={v} := by
    ext u
    simp only [mem_filter,mem_singleton]
    constructor
    · rintro ⟨hu,hui⟩
      exact hinj hu hv (hui.trans hvi.symm)
    · rintro rfl
      exact ⟨hv,hvi⟩
  rw [he,card_singleton]

theorem missingFacet_card {G : SimpleGraph V} {c : V → Fin 4}
    (hc : Proper c G) {D : Finset V} (hD : D.card=4) (hcl : G.IsClique D)
    (i : Fin 4) : (missingFacet c i D).card=3 := by
  have h1 := color_count_tetrahedron hc hD hcl i
  have hsum := card_filter_add_card_filter_not (s := D) (fun v => c v=i)
  change (D.filter (fun v => c v=i)).card+(missingFacet c i D).card=D.card at hsum
  omega

theorem missingFacet_avoids (c : V → Fin 4) (i : Fin 4) (D : Finset V) :
    Avoids c i (missingFacet c i D) := fun v hv => (mem_filter.mp hv).2

theorem missingFacet_subset (c : V → Fin 4) (i : Fin 4) (D : Finset V) :
    missingFacet c i D⊆D := filter_subset _ _

theorem missingFacet_clique {G : SimpleGraph V} {c : V → Fin 4}
    {D : Finset V} (hcl : G.IsClique D) (i : Fin 4) :
    G.IsClique (missingFacet c i D) := by
  intro u hu v hv huv
  exact hcl (missingFacet_subset c i D hu) (missingFacet_subset c i D hv) huv

theorem avoiding_triangle_unique {G : SimpleGraph V} {c : V → Fin 4}
    (hc : Proper c G) {D T : Finset V} (hD : D.card=4) (hcl : G.IsClique D)
    (hT : T.card=3) (hTD : T⊆D) {i : Fin 4} (havoid : Avoids c i T) :
    T=missingFacet c i D := by
  apply eq_of_subset_of_card_le
  · intro v hv
    exact mem_filter.mpr ⟨hTD hv,havoid v hv⟩
  · rw [missingFacet_card hc hD hcl,hT]

theorem avoidingTriangles_mono {G H : SimpleGraph V} (hGH : G≤H)
    (c : V → Fin 4) (i : Fin 4) :
    avoidingTriangles G c i⊆avoidingTriangles H c i := by
  intro T hT
  obtain ⟨ht,hcl,ha⟩ := (mem_avoidingTriangles _ _ _ _).mp hT
  exact (mem_avoidingTriangles _ _ _ _).mpr
    ⟨ht,fun u hu v hv huv => hGH (hcl hu hv huv),ha⟩

theorem missingFacet_mem {G : SimpleGraph V} {c : V → Fin 4}
    (hc : Proper c G) {D : Finset V} (hD : D.card=4) (hcl : G.IsClique D)
    (i : Fin 4) : missingFacet c i D∈avoidingTriangles G c i :=
  (mem_avoidingTriangles _ _ _ _).mpr
    ⟨missingFacet_card hc hD hcl i,missingFacet_clique hcl i,missingFacet_avoids c i D⟩

theorem avoiding_subsets_singleton {G : SimpleGraph V} {c : V → Fin 4}
    (hc : Proper c G) {D : Finset V} (hD : D.card=4) (hcl : G.IsClique D)
    (i : Fin 4) :
    (avoidingTriangles G c i).filter (fun T => T⊆D)={missingFacet c i D} := by
  ext T
  simp only [mem_filter,mem_singleton]
  constructor
  · rintro ⟨hT,hTD⟩
    obtain ⟨ht,_,ha⟩ := (mem_avoidingTriangles _ _ _ _).mp hT
    exact avoiding_triangle_unique hc hD hcl ht hTD ha
  · rintro rfl
    exact ⟨missingFacet_mem hc hD hcl i,missingFacet_subset c i D⟩

theorem avoidingTriangles_cliqueGraph {D : Finset V} (hD : D.card=4)
    {c : V → Fin 4} (hc : Proper c (cliqueGraph D)) (i : Fin 4) :
    avoidingTriangles (cliqueGraph D) c i={missingFacet c i D} := by
  have hcl : (cliqueGraph D).IsClique D := fun u hu v hv huv => ⟨huv,hu,hv⟩
  rw [← avoiding_subsets_singleton hc hD hcl i]
  symm
  apply filter_eq_self.mpr
  intro T hT
  have hh := (mem_avoidingTriangles _ _ _ _).mp hT
  exact (ThreeTreeOn.tetrahedron D hD).clique_subset_active (by omega) hh.2.1

theorem avoidingTriangles_after_attachment {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {T : Finset V}
    (hT : T.card=3) (hTS : T⊆S) (hcl : G.IsClique T)
    {c : V → Fin 4} (hc : Proper c (G⊔attachmentStar u T)) (i : Fin 4) :
    avoidingTriangles (G⊔attachmentStar u T) c i =
      if i=c u then avoidingTriangles G c i
      else insert (missingFacet c i (insert u T)) (avoidingTriangles G c i) := by
  have huT : u∉T := fun hm => hu (hTS hm)
  have hD : (insert u T).card=4 := by rw [card_insert_of_notMem huT,hT]
  have hDcl := attached_tetrahedron_clique h hu hTS hcl
  have hM := missingFacet_mem hc hD hDcl i
  have hold := avoidingTriangles_mono (show G≤G⊔attachmentStar u T from le_sup_left) c i
  ext A
  by_cases hi : i=c u
  · simp only [if_pos hi]
    constructor
    · intro hA
      obtain ⟨ha,hacl,havoid⟩ := (mem_avoidingTriangles _ _ _ _).mp hA
      have huA : u∉A := fun hm => havoid u hm hi.symm
      exact (mem_avoidingTriangles _ _ _ _).mpr ⟨ha,clique_before_attachment huA hacl,havoid⟩
    · exact fun hA => hold hA
  · simp only [if_neg hi,mem_insert]
    constructor
    · intro hA
      obtain ⟨ha,hacl,havoid⟩ := (mem_avoidingTriangles _ _ _ _).mp hA
      by_cases huA : u∈A
      · left
        apply avoiding_triangle_unique hc hD hDcl ha _ havoid
        intro v hv
        by_cases hvu : v=u
        · exact mem_insert.mpr (Or.inl hvu)
        · exact mem_insert.mpr (Or.inr ((attached_vertex_adj_iff h hu hTS v).mp
            (hacl huA hv (Ne.symm hvu))))
      · right
        exact (mem_avoidingTriangles _ _ _ _).mpr ⟨ha,clique_before_attachment huA hacl,havoid⟩
    · rintro (rfl | hA)
      · exact hM
      · exact hold hA

theorem missingFacet_not_old {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {T : Finset V}
    {c : V → Fin 4} {i : Fin 4} (hi : i≠c u) :
    missingFacet c i (insert u T)∉avoidingTriangles G c i := by
  intro hM
  obtain ⟨hm,hcl,_⟩ := (mem_avoidingTriangles _ _ _ _).mp hM
  have hsub := h.clique_subset_active (by omega) hcl
  exact hu (hsub (mem_filter.mpr ⟨mem_insert_self _ _,Ne.symm hi⟩))

/-- The exact number of triangles missing color i is |S|−n_i−2,
expressed without truncated subtraction. -/
theorem avoiding_triangles_card {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {c : V → Fin 4} (hc : Proper c G) (i : Fin 4) :
    (avoidingTriangles G c i).card+(S.filter (fun v => c v=i)).card+2=S.card := by
  induction h with
  | tetrahedron D hD =>
    have hcl : (cliqueGraph D).IsClique D := fun u hu v hv huv => ⟨huv,hu,hv⟩
    rw [avoidingTriangles_cliqueGraph hD hc,card_singleton,color_count_tetrahedron hc hD hcl,hD]
  | @attach S G h u hu T hT hTS hcl ih =>
    have hcG : Proper c G := fun v w hvw => hc v w (Or.inl hvw)
    have hold := ih hcG
    have htri := avoidingTriangles_after_attachment h hu hT hTS hcl hc i
    rw [htri,card_insert_of_notMem hu]
    by_cases hi : i=c u
    · rw [if_pos hi]
      have hcolor : ((insert u S).filter (fun v => c v=i)).card=
          (S.filter (fun v => c v=i)).card+1 := by
        rw [filter_insert]
        simp [hi,hu]
      rw [hcolor]
      omega
    · rw [if_neg hi,card_insert_of_notMem (missingFacet_not_old h hu hi)]
      have hcolor : (insert u S).filter (fun v => c v=i)=S.filter (fun v => c v=i) := by
        simp [filter_insert,Ne.symm hi]
      rw [hcolor]
      omega

/-- Every tetrahedron contributes exactly one incidence to triangles missing
each fixed color, so this sum is the actual tetrahedron count. -/
theorem incidence_sum {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {c : V → Fin 4} (hc : Proper c G) (i : Fin 4) :
    ∑ T∈avoidingTriangles G c i,triangleMultiplicity G T=S.card-3 := by
  have hcount : (∑ T∈avoidingTriangles G c i,triangleMultiplicity G T)=
      ∑ D∈tetrahedra G,((avoidingTriangles G c i).filter (fun T => T⊆D)).card := by
    simp only [triangleMultiplicity,card_eq_sum_ones,sum_filter]
    rw [sum_comm]
  rw [hcount]
  calc
    (∑ D∈tetrahedra G,((avoidingTriangles G c i).filter (fun T => T⊆D)).card)=
        ∑ _D∈tetrahedra G,1 := by
      apply sum_congr rfl
      intro D hD
      obtain ⟨hd,hcl⟩ := (mem_filter.mp hD).2
      rw [avoiding_subsets_singleton hc hd hcl,card_singleton]
    _ = (tetrahedra G).card := by simp
    _ = S.card-3 := h.tetrahedra_card

theorem capacity_nonnegative {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {c : V → Fin 4} (hc : Proper c G)
    (hA : Admissible G) (i : Fin 4) :
    (0 : ℤ)≤2*(S.card : ℤ)-3*((S.filter (fun v => c v=i)).card : ℤ)-3 := by
  have ht := avoiding_triangles_card h hc i
  have hi := incidence_sum h hc i
  have hN := h.active_card_ge_four
  have hb : (∑ T∈avoidingTriangles G c i,triangleMultiplicity G T)≤
      3*(avoidingTriangles G c i).card := by
    calc
      _ ≤ ∑ _T∈avoidingTriangles G c i,3 := by
        apply sum_le_sum
        intro T hT
        obtain ⟨ht,hcl,_⟩ := (mem_avoidingTriangles _ _ _ _).mp hT
        exact hA T ht hcl
      _ = _ := by simp [Nat.mul_comm]
  omega

theorem free_triangle {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {c : V → Fin 4} (hc : Proper c G)
    (i : Fin 4)
    (hpos : (0 : ℤ)<2*(S.card : ℤ)-3*((S.filter (fun v => c v=i)).card : ℤ)-3) :
    ∃ T : Finset V,T.card=3 ∧ G.IsClique T ∧ Avoids c i T ∧
      triangleMultiplicity G T<3 := by
  have ht := avoiding_triangles_card h hc i
  have hi := incidence_sum h hc i
  have hN := h.active_card_ge_four
  by_contra hn
  have hge : ∀ T∈avoidingTriangles G c i,3≤triangleMultiplicity G T := by
    intro T hT
    obtain ⟨hcard,hcl,ha⟩ := (mem_avoidingTriangles _ _ _ _).mp hT
    by_contra hlt
    exact hn ⟨T,hcard,hcl,ha,by omega⟩
  have hb : 3*(avoidingTriangles G c i).card≤
      ∑ T∈avoidingTriangles G c i,triangleMultiplicity G T := by
    calc
      _ = ∑ _T∈avoidingTriangles G c i,3 := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum hge
  omega

end GraphicalZonotopes.FourPartThreeTreeCounts
