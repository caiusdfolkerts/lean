module

public import Papers.GraphicalZonotopes.TetrahedralGrowth
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace GraphicalZonotopes.FourPartCompletion
open Finset Function

variable {V : Type*} [Fintype V] [DecidableEq V]

def vertices (v : Fin 4 → V) : Finset V := univ.image v

def Face (C : Finset (Finset V)) (v : Fin 4 → V) : Prop := vertices v ∈ C

def Thin (C : Finset (Finset V)) : Prop :=
  ∀ v, Injective v → Face C v → ∀ i x y,
    x ∉ vertices v → y ∉ vertices v →
    Face C (update v i x) → Face C (update v i y) → x=y

def SquareClosed (C : Finset (Finset V)) : Prop :=
  ∀ v, Injective v → Face C v → ∀ i j, i≠j → ∀ x y,
    x ∉ vertices v → y ∉ vertices v →
    Face C (update v i x) → Face C (update v j y) →
    x≠y ∧ Face C (update (update v i x) j y)

@[simp] theorem mem_vertices (v : Fin 4 → V) (x : V) :
    x ∈ vertices v ↔ ∃ i, v i=x := by simp [vertices]

theorem self_mem_vertices (v : Fin 4 → V) (i : Fin 4) : v i∈vertices v :=
  (mem_vertices v _).mpr ⟨i,rfl⟩

theorem vertices_card (v : Fin 4 → V) (hv : Injective v) : (vertices v).card=4 := by
  simp [vertices, card_image_of_injective _ hv]

theorem vertices_update (v : Fin 4 → V) (hv : Injective v) (i : Fin 4) (x : V) :
    vertices (update v i x)=insert x ((vertices v).erase (v i)) := by
  ext a
  simp only [mem_vertices,mem_insert,mem_erase]
  constructor
  · rintro ⟨j,hj⟩
    by_cases hji : j=i
    · subst j; exact Or.inl (by simpa using hj.symm)
    · right
      have hval : v j=a := by simpa [update_of_ne hji] using hj
      exact ⟨fun he => hji (hv (hval.trans he)),⟨j,hval⟩⟩
  · rintro (rfl | ⟨ha,j,hj⟩)
    · exact ⟨i,by simp⟩
    · refine ⟨j,?_⟩
      have hji : j≠i := fun he => ha (by simpa [he] using hj.symm)
      simpa [update_of_ne hji] using hj

def rootParts (C : Finset (Finset V)) (v : Fin 4 → V) (i : Fin 4) : Finset V :=
  insert (v i) (univ.filter (fun x => x∉vertices v ∧ Face C (update v i x)))

@[simp] theorem mem_rootParts (C : Finset (Finset V)) (v : Fin 4 → V)
    (i : Fin 4) (x : V) :
    x∈rootParts C v i ↔ x=v i ∨ x∉vertices v ∧ Face C (update v i x) := by
  simp [rootParts]

theorem root_mem_part (C : Finset (Finset V)) (v : Fin 4 → V) (i : Fin 4) :
    v i∈rootParts C v i := (mem_rootParts _ _ _ _).mpr (Or.inl rfl)

theorem rootParts_small {C : Finset (Finset V)} (hthin : Thin C)
    {v : Fin 4 → V} (hv : Injective v) (hf : Face C v) (i : Fin 4) :
    (rootParts C v i).card=1 ∨ (rootParts C v i).card=2 := by
  let A := univ.filter (fun x => x∉vertices v ∧ Face C (update v i x))
  have hsub : A.card≤1 := card_le_one.mpr (by
    intro x hx y hy
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_filter.mp hy).2
    exact hthin v hv hf i x y hx'.1 hy'.1 hx'.2 hy'.2)
  have hnot : v i∉A := by
    intro h
    exact (mem_filter.mp h).2.1 (self_mem_vertices v i)
  have hc : (rootParts C v i).card=A.card+1 := card_insert_of_notMem hnot
  omega

theorem rootParts_disjoint {C : Finset (Finset V)} (hsq : SquareClosed C)
    {v : Fin 4 → V} (hv : Injective v) (hf : Face C v) :
    ∀ i j, i≠j → Disjoint (rootParts C v i) (rootParts C v j) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  rcases (mem_rootParts _ _ _ _).mp hxi with rfl | ⟨hxi,hfi⟩
  · rcases (mem_rootParts _ _ _ _).mp hxj with he | ⟨hn,_⟩
    · exact hij (hv he)
    · exact hn (self_mem_vertices v i)
  · rcases (mem_rootParts _ _ _ _).mp hxj with rfl | ⟨hxj,hfj⟩
    · exact hxi (self_mem_vertices v j)
    · exact (hsq v hv hf i j hij x x hxi hxj hfi hfj).1 rfl

theorem injective_of_parts {A : Fin 4 → Finset V}
    (hA : ∀ i j, i≠j → Disjoint (A i) (A j))
    {v : Fin 4 → V} (hv : ∀ i,v i∈A i) : Injective v := by
  intro i j he
  by_contra hij
  exact (disjoint_left.mp (hA i j hij)) (hv i) (by rw [he]; exact hv j)

def patch (v w : Fin 4 → V) (S : Finset (Fin 4)) (i : Fin 4) : V :=
  if i∈S then w i else v i

@[simp] theorem patch_empty (v w : Fin 4 → V) : patch v w ∅=v := by
  funext i; simp [patch]

theorem patch_insert (v w : Fin 4 → V) (S : Finset (Fin 4)) (i : Fin 4) :
    patch v w (insert i S)=update (patch v w S) i (w i) := by
  funext j
  by_cases hji : j=i <;> simp [patch,hji]

theorem patch_mem_parts {A : Fin 4 → Finset V} {v w : Fin 4 → V}
    (hv : ∀ i,v i∈A i) (hw : ∀ i,w i∈A i) (S : Finset (Fin 4)) :
    ∀ i,patch v w S i∈A i := by
  intro i
  by_cases hi : i∈S <;> simp [patch,hi,hv i,hw i]

theorem outside_patch {A : Fin 4 → Finset V}
    (hA : ∀ i j, i≠j → Disjoint (A i) (A j))
    {v w : Fin 4 → V} (hv : ∀ i,v i∈A i) (hw : ∀ i,w i∈A i)
    (S : Finset (Fin 4)) {i : Fin 4} (hi : i∉S) (hne : w i≠v i) :
    w i∉vertices (patch v w S) := by
  rintro hx
  obtain ⟨j,hj⟩ := (mem_vertices _ _).mp hx
  have hm := patch_mem_parts hv hw S j
  by_cases hij : i=j
  · subst j
    exact hne (by simpa [patch,hi] using hj.symm)
  · exact (disjoint_left.mp (hA i j hij)) (hw i) (hj ▸ hm)

/-- Every independent combination of the root's elementary replacements is
present. The proof transports each remaining replacement across a square. -/
theorem fill_product {C : Finset (Finset V)} (hsq : SquareClosed C)
    {v : Fin 4 → V} (hv : Injective v) (hf : Face C v)
    {w : Fin 4 → V} (hw : ∀ i,w i∈rootParts C v i) : Face C w := by
  let A := rootParts C v
  have hA : ∀ i j,i≠j → Disjoint (A i) (A j) := rootParts_disjoint hsq hv hf
  have hvA : ∀ i,v i∈A i := root_mem_part C v
  let D : Finset (Fin 4) := univ.filter (fun i => w i≠v i)
  have hD (i : Fin 4) : i∈D ↔ w i≠v i := by simp [D]
  have hfill : ∀ S : Finset (Fin 4),S⊆D →
      Face C (patch v w S) ∧
      ∀ i∈D,i∉S → Face C (update (patch v w S) i (w i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨by simpa using hf,?_⟩
      intro i hi _
      have hn := (hD i).mp hi
      have hm := (mem_rootParts C v i (w i)).mp (hw i)
      simpa using (hm.resolve_left hn).2
    | @insert i S hi ih =>
      intro hSD
      have hS : S⊆D := fun j hj => hSD (mem_insert_of_mem hj)
      have hiD : i∈D := hSD (mem_insert_self _ _)
      obtain ⟨hface,hedge⟩ := ih hS
      have hnext := hedge i hiD hi
      refine ⟨by simpa [patch_insert] using hnext,?_⟩
      intro j hjD hj
      have hji : j≠i := fun he => hj (by simp [he])
      have hjS : j∉S := fun hm => hj (mem_insert_of_mem hm)
      have hwi := outside_patch hA hvA hw S hi ((hD i).mp hiD)
      have hwj := outside_patch hA hvA hw S hjS ((hD j).mp hjD)
      have hinj := injective_of_parts hA (patch_mem_parts hvA hw S)
      have hsquare := (hsq _ hinj hface i j hji.symm (w i) (w j)
        hwi hwj hnext (hedge j hjD hjS)).2
      simpa [patch_insert] using hsquare
  have he : patch v w D=w := by
    funext i
    by_cases hi : w i=v i <;> simp [patch,D,hi]
  rw [← he]
  exact (hfill D (Subset.refl _)).1

theorem outside_of_parts {A : Fin 4 → Finset V}
    (hA : ∀ i j,i≠j → Disjoint (A i) (A j))
    {v : Fin 4 → V} (hv : ∀ i,v i∈A i)
    {i : Fin 4} {x : V} (hx : x∈A i) (hne : x≠v i) :
    x∉vertices v := by
  rintro hm
  obtain ⟨j,hj⟩ := (mem_vertices v x).mp hm
  by_cases hij : i=j
  · subst j; exact hne hj.symm
  · exact (disjoint_left.mp (hA i j hij)) hx (hj ▸ hv j)

def changed (v w : Fin 4 → V) : Finset (Fin 4) := univ.filter (fun i => w i≠v i)

@[simp] theorem mem_changed (v w : Fin 4 → V) (i : Fin 4) :
    i∈changed v w ↔ w i≠v i := by simp [changed]

theorem changed_update (v w : Fin 4 → V) (j : Fin 4) :
    changed v (update w j (v j))=(changed v w).erase j := by
  ext i
  by_cases hij : i=j <;> simp [changed,hij]

/-- Any new facet adjacent to the root cube stays within its four parts.
An alleged new vertex is transported back to the root by square closure. -/
theorem replacement_mem_part {C : Finset (Finset V)}
    (hthin : Thin C) (hsq : SquareClosed C)
    {v : Fin 4 → V} (hv : Injective v) (hf : Face C v)
    {w : Fin 4 → V} (hw : ∀ i,w i∈rootParts C v i)
    (i : Fin 4) (x : V) (hx : x∉vertices w)
    (hfx : Face C (update w i x)) : x∈rootParts C v i := by
  let A := rootParts C v
  have hA : ∀ i j,i≠j → Disjoint (A i) (A j) := rootParts_disjoint hsq hv hf
  have hvA : ∀ i,v i∈A i := root_mem_part C v
  have hmain : ∀ n : ℕ,∀ w : Fin 4 → V,(changed v w).card=n →
      (∀ i,w i∈A i) → ∀ i x,x∉vertices w →
      Face C (update w i x) → x∈A i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hc hw i x hx hfx
      have hwi : Injective w := injective_of_parts hA hw
      have hfw : Face C w := fill_product hsq hv hf hw
      by_cases hival : w i=v i
      · by_cases he : w=v
        · subst w
          exact (mem_rootParts C v i x).mpr (Or.inr ⟨hx,hfx⟩)
        · obtain ⟨j,hj⟩ : ∃ j,w j≠v j := by
            by_contra h
            push_neg at h
            exact he (funext h)
          have hij : i≠j := by intro h; subst j; exact hj hival
          let w' := update w j (v j)
          have hw' : ∀ k,w' k∈A k := by
            intro k
            by_cases hkj : k=j
            · subst k; simpa [w'] using hvA j
            · simpa [w',update_of_ne hkj] using hw k
          have hvj : v j∉vertices w := outside_of_parts hA hw (hvA j) (Ne.symm hj)
          have hfw' : Face C w' := fill_product hsq hv hf hw'
          have hs := hsq w hwi hfw i j hij x (v j) hx hvj hfx hfw'
          have hx' : x∉vertices w' := by
            rw [show vertices w'=insert (v j) ((vertices w).erase (w j)) from
              vertices_update w hwi j (v j)]
            intro hm
            rcases mem_insert.mp hm with he | he
            · exact hs.1 he
            · exact hx (mem_of_mem_erase he)
          have hfx' : Face C (update w' i x) := by
            simpa only [w',update_comm hij] using hs.2
          have hlt : (changed v w').card<n := by
            rw [show changed v w'=(changed v w).erase j from changed_update v w j]
            rw [← hc]
            exact card_erase_lt_of_mem ((mem_changed v w j).mpr hj)
          exact ih _ hlt w' rfl hw' i x hx' hfx'
      · have hvi : v i∉vertices w := outside_of_parts hA hw (hvA i) (Ne.symm hival)
        have hback : Face C (update w i (v i)) := by
          apply fill_product hsq hv hf
          change ∀ j,update w i (v i) j∈A j
          intro j
          by_cases hji : j=i
          · subst j; simp only [update_self]; exact hvA i
          · rw [update_of_ne hji]; exact hw j
        have he := hthin w hwi hfw i x (v i) hx hvi hfx hback
        simpa [he] using hvA i
  exact hmain _ w rfl hw i x hx hfx

theorem adjacent_replacement {D E : Finset V}
    (hD : D.card=4) (hE : E.card=4) (hne : D≠E)
    (hinter : 3≤(D∩E).card) :
    ∃ u∈D,∃ x,x∉D ∧ E=insert x (D.erase u) := by
  have hle : (D∩E).card≤4 := (card_le_card inter_subset_left).trans_eq hD
  have hne4 : (D∩E).card≠4 := by
    intro he
    have hDI : D∩E=D := eq_of_subset_of_card_le inter_subset_left (by omega)
    have hDE : D⊆E := by rw [← hDI]; exact inter_subset_right
    exact hne (eq_of_subset_of_card_le hDE (by omega))
  have hthree : (D∩E).card=3 := by omega
  have hdiffD : (D\E).card=1 := by
    have hh := card_sdiff_add_card_inter D E
    omega
  have hdiffE : (E\D).card=1 := by
    have hh := card_sdiff_add_card_inter E D
    rw [inter_comm E D] at hh
    omega
  obtain ⟨u,hu⟩ := card_eq_one.mp hdiffD
  obtain ⟨x,hx⟩ := card_eq_one.mp hdiffE
  have hum : u∈D\E := by rw [hu]; simp
  have hxm : x∈E\D := by rw [hx]; simp
  refine ⟨u,(mem_sdiff.mp hum).1,x,(mem_sdiff.mp hxm).2,?_⟩
  ext a
  constructor
  · intro ha
    by_cases haD : a∈D
    · apply mem_insert_of_mem
      exact mem_erase.mpr ⟨fun he => (mem_sdiff.mp hum).2 (he ▸ ha),haD⟩
    · have he : a=x := by
        have hm : a∈E\D := mem_sdiff.mpr ⟨ha,haD⟩
        rw [hx] at hm
        exact mem_singleton.mp hm
      exact mem_insert.mpr (Or.inl he)
  · intro ha
    rcases mem_insert.mp ha with rfl | ha
    · exact (mem_sdiff.mp hxm).1
    · by_contra hn
      have hm : a∈D\E := mem_sdiff.mpr ⟨mem_of_mem_erase ha,hn⟩
      rw [hu] at hm
      exact (mem_erase.mp ha).1 (mem_singleton.mp hm)

theorem exists_vertices {D : Finset V} (hD : D.card=4) :
    ∃ v : Fin 4 → V,Injective v ∧ vertices v=D := by
  let e : Fin 4 ≃ D := (Finset.equivFinOfCardEq hD).symm
  let v : Fin 4 → V := fun i => (e i).val
  refine ⟨v,Subtype.val_injective.comp e.injective,?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i,rfl⟩ := (mem_vertices v x).mp hx
    exact (e i).property
  · intro hx
    apply (mem_vertices v x).mpr
    exact ⟨e.symm ⟨x,hx⟩,congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)⟩

/-- A connected family of tetrahedra with thin facets and commuting
facet replacements is exactly the Cartesian product of four parts of size
one or two. No bound on the ambient finite vertex type is assumed. -/
theorem cartesian_completion (C : Finset (Finset V))
    (hfour : ∀ D∈C,D.card=4) (hne : C.Nonempty)
    (hconn : (tetrahedronGraph C).Preconnected)
    (hthin : Thin C) (hsq : SquareClosed C) :
    ∃ A : Fin 4 → Finset V,
      (∀ i,(A i).card=1 ∨ (A i).card=2) ∧
      (∀ i j,i≠j → Disjoint (A i) (A j)) ∧
      ∀ D : Finset V,D∈C ↔ ∃ w : Fin 4 → V,(∀ i,w i∈A i) ∧ D=univ.image w := by
  obtain ⟨D₀,hD₀⟩ := hne
  obtain ⟨v,hv,hev⟩ := exists_vertices (hfour D₀ hD₀)
  have hf : Face C v := by simpa [Face,hev] using hD₀
  let A := rootParts C v
  have hA : ∀ i j,i≠j → Disjoint (A i) (A j) := rootParts_disjoint hsq hv hf
  let P : {D : Finset V // D∈C} → Prop :=
    fun D => ∃ w : Fin 4 → V,(∀ i,w i∈A i) ∧ D.val=vertices w
  have hroot : P ⟨D₀,hD₀⟩ := ⟨v,root_mem_part C v,hev.symm⟩
  have hstep : ∀ D E : {D : Finset V // D∈C},
      (tetrahedronGraph C).Adj D E → P D → P E := by
    intro D E hadj hPD
    obtain ⟨w,hw,hew⟩ := hPD
    have hwi : Injective w := injective_of_parts hA hw
    have hDE : D.val≠E.val := fun he => hadj.1 (Subtype.ext he)
    obtain ⟨u,hu,x,hx,he⟩ := adjacent_replacement
      (hfour _ D.property) (hfour _ E.property) hDE hadj.2
    rw [hew] at hu hx he
    obtain ⟨i,hi⟩ := (mem_vertices w u).mp hu
    subst u
    have hrep : E.val=vertices (update w i x) := by
      rw [vertices_update w hwi i x]
      exact he
    have hfx : Face C (update w i x) := by
      rw [Face,← hrep]
      exact E.property
    have hxi := replacement_mem_part hthin hsq hv hf hw i x hx hfx
    refine ⟨update w i x,?_,hrep⟩
    intro j
    change update w i x j∈A j
    by_cases hji : j=i
    · subst j; simp only [update_self]; exact hxi
    · rw [update_of_ne hji]; exact hw j
  refine ⟨A,rootParts_small hthin hv hf,hA,?_⟩
  intro D
  constructor
  · intro hD
    have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).mp
      (hconn ⟨D₀,hD₀⟩ ⟨D,hD⟩)
    have hclosed : ∀ E : {E : Finset V // E∈C},
        Relation.ReflTransGen (tetrahedronGraph C).Adj ⟨D₀,hD₀⟩ E → P E := by
      intro E hr
      induction hr with
      | refl => exact hroot
      | tail _ ha ih => exact hstep _ _ ha ih
    exact hclosed ⟨D,hD⟩ hr
  · rintro ⟨w,hw,rfl⟩
    exact fill_product hsq hv hf hw

end GraphicalZonotopes.FourPartCompletion
