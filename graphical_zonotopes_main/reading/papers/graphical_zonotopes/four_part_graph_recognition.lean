module

public import Papers.GraphicalZonotopes.RefinedTriangleComponents
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace FourPartGraphRecognition
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

structure FourParts (V : Type*) [Fintype V] [DecidableEq V] where
  parts : Fin 4 → Finset V
  nonempty : ∀ i,(parts i).Nonempty
  disjoint : ∀ i j,i≠j → Disjoint (parts i) (parts j)
  covers : ∀ v : V,∃ i,v∈parts i

namespace FourParts
variable (P : FourParts V)

def color (v : V) : Fin 4 := Classical.choose (P.covers v)

theorem color_mem (v : V) : v∈P.parts (P.color v) := Classical.choose_spec (P.covers v)

theorem color_eq_of_mem {v : V} {i : Fin 4} (hv : v∈P.parts i) : P.color v=i := by
  by_contra hi
  exact Finset.disjoint_left.mp (P.disjoint _ _ hi) (P.color_mem v) hv

def chosen (i : Fin 4) : V := Classical.choose (P.nonempty i)

theorem chosen_mem (i : Fin 4) : P.chosen i∈P.parts i := Classical.choose_spec (P.nonempty i)

theorem different_of_mem {i j : Fin 4} (hij : i≠j) {u v : V}
    (hu : u∈P.parts i) (hv : v∈P.parts j) : u≠v := by
  intro he
  exact Finset.disjoint_left.mp (P.disjoint i j hij) hu (he.symm ▸ hv)

def transversal (u v : V) : Fin 4 → V :=
  fun i => if i=P.color u then u else if i=P.color v then v else P.chosen i

theorem transversal_mem (u v : V) (i : Fin 4) : P.transversal u v i∈P.parts i := by
  unfold transversal
  split_ifs with hi hj
  · simpa only [hi] using P.color_mem u
  · simpa only [hj] using P.color_mem v
  · exact P.chosen_mem i

theorem transversal_left (u v : V) : P.transversal u v (P.color u)=u := by
  simp [transversal]

theorem transversal_right {u v : V} (h : P.color u≠P.color v) :
    P.transversal u v (P.color v)=v := by simp [transversal,Ne.symm h]

theorem choice_injective (w : Fin 4 → V) (hw : ∀ i,w i∈P.parts i) :
    Function.Injective w := by
  intro i j he
  by_contra hij
  exact P.different_of_mem hij (hw i) (hw j) he

def coordinateEquiv : (Σ i : Fin 4,Fin ((P.parts i).card)) ≃ V := by
  let e (i : Fin 4) : Fin ((P.parts i).card) ≃ {v : V // v∈P.parts i} :=
    Fintype.equivOfCardEq (by simp)
  let f : (Σ i : Fin 4,Fin ((P.parts i).card)) → V := fun x => (e x.1 x.2).1
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨i,a⟩ ⟨j,b⟩ he
    have hi : i=j := by
      have hci := P.color_eq_of_mem (e i a).2
      have hcj := P.color_eq_of_mem (e j b).2
      exact hci.symm.trans ((congrArg P.color he).trans hcj)
    subst j
    have hab : a=b := (e i).injective (Subtype.ext he)
    subst b
    rfl
  · intro v
    refine ⟨⟨P.color v,(e (P.color v)).symm ⟨v,P.color_mem v⟩⟩,?_⟩
    exact congrArg Subtype.val ((e (P.color v)).apply_symm_apply _)

theorem coordinateEquiv_mem (x : Σ i : Fin 4,Fin ((P.parts i).card)) :
    P.coordinateEquiv x∈P.parts x.1 := by
  change (Fintype.equivOfCardEq _ x.2 : {v : V // v∈P.parts x.1}).1∈P.parts x.1
  exact (Fintype.equivOfCardEq _ x.2 : {v : V // v∈P.parts x.1}).2

theorem card_eq : Fintype.card V=∑ i : Fin 4,(P.parts i).card := by
  rw [← Fintype.card_congr P.coordinateEquiv,Fintype.card_sigma]
  simp

theorem card_le_eight (hsize : ∀ i,(P.parts i).card≤2) : Fintype.card V≤8 := by
  rw [P.card_eq]
  calc
    ∑ i : Fin 4,(P.parts i).card ≤ ∑ _i : Fin 4,2 := sum_le_sum (fun i _ => hsize i)
    _ = 8 := by norm_num

end FourParts

def unionGraph (F : Finset (Finset V)) : SimpleGraph V where
  Adj u v := u≠v ∧ ∃ D∈F,u∈D ∧ v∈D
  symm := ⟨by rintro u v ⟨hne,D,hD,hu,hv⟩;exact ⟨Ne.symm hne,D,hD,hv,hu⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def ProductFamily (F : Finset (Finset V)) (A : Fin 4 → Finset V) : Prop :=
  ∀ D : Finset V,D∈F ↔ ∃ w : Fin 4 → V,(∀ i,w i∈A i) ∧ D=univ.image w

variable (P : FourParts V) (F : Finset (Finset V))

theorem unionGraph_adj_iff (hprod : ProductFamily F P.parts) (u v : V) :
    (unionGraph F).Adj u v ↔ P.color u≠P.color v := by
  constructor
  · rintro ⟨hne,D,hD,hu,hv⟩ he
    obtain ⟨w,hw,rfl⟩ := (hprod D).mp hD
    obtain ⟨i,_,hi⟩ := mem_image.mp hu
    obtain ⟨j,_,hj⟩ := mem_image.mp hv
    have hci : P.color u=i := P.color_eq_of_mem (hi ▸ hw i)
    have hcj : P.color v=j := P.color_eq_of_mem (hj ▸ hw j)
    have hij : i=j := hci.symm.trans (he.trans hcj)
    rw [← hij] at hj
    exact hne (hi.symm.trans hj)
  · intro hne
    refine ⟨fun he => hne (congrArg P.color he),univ.image (P.transversal u v),?_,?_,?_⟩
    · exact (hprod _).mpr ⟨P.transversal u v,P.transversal_mem u v,rfl⟩
    · exact mem_image.mpr ⟨P.color u,mem_univ _,P.transversal_left u v⟩
    · exact mem_image.mpr ⟨P.color v,mem_univ _,P.transversal_right hne⟩

theorem unionGraph_le {G : SimpleGraph V} (hcl : ∀ D∈F,G.IsClique D) : unionGraph F≤G := by
  rintro u v ⟨hne,D,hD,hu,hv⟩
  exact hcl D hD hu hv hne

/-- A K5-free supergraph of a full four-part product has no additional edge:
any within-part edge, together with one vertex from each other part, is a K5. -/
theorem ambient_eq {G : SimpleGraph V} (hprod : ProductFamily F P.parts)
    (hcl : ∀ D∈F,G.IsClique D)
    (hfour : ∀ D : Finset V,G.IsClique D → D.card≤4) : unionGraph F=G := by
  apply le_antisymm (unionGraph_le F hcl)
  intro u v huv
  apply (unionGraph_adj_iff P F hprod u v).mpr
  intro hecolor
  let w := P.transversal u u
  have hw : ∀ i,w i∈P.parts i := P.transversal_mem u u
  let D := univ.image w
  have hDF : D∈F := (hprod D).mpr ⟨w,hw,rfl⟩
  have hDc : D.card=4 := by
    dsimp only [D]
    rw [card_image_of_injective _ (P.choice_injective w hw)]
    simp
  have hvD : v∉D := by
    intro hv
    obtain ⟨i,_,hi⟩ := mem_image.mp hv
    have hci : P.color v=i := P.color_eq_of_mem (hi ▸ hw i)
    have hii : i=P.color u := hci.symm.trans hecolor.symm
    have hwi : w i=u := by simpa only [hii] using P.transversal_left u u
    exact G.ne_of_adj huv (hwi.symm.trans hi)
  have hclE : G.IsClique ((insert v D : Finset V) : Set V) := by
    intro x hx y hy hxy
    rcases mem_insert.mp hx with rfl | hxD
    · rcases mem_insert.mp hy with rfl | hyD
      · exact False.elim (hxy rfl)
      · obtain ⟨i,_,hi⟩ := mem_image.mp hyD
        by_cases hii : i=P.color u
        · have hyu : y=u := hi.symm.trans (by simpa only [hii] using P.transversal_left u u)
          simpa only [hyu] using G.adj_symm huv
        · apply unionGraph_le F hcl
          apply (unionGraph_adj_iff P F hprod x y).mpr
          have hcy : P.color y=i := P.color_eq_of_mem (hi ▸ hw i)
          rw [hcy,← hecolor]
          exact Ne.symm hii
    · rcases mem_insert.mp hy with rfl | hyD
      · apply G.adj_symm
        obtain ⟨i,_,hi⟩ := mem_image.mp hxD
        by_cases hii : i=P.color u
        · have hxu : x=u := hi.symm.trans (by simpa only [hii] using P.transversal_left u u)
          simpa only [hxu] using G.adj_symm huv
        · apply unionGraph_le F hcl
          apply (unionGraph_adj_iff P F hprod y x).mpr
          have hcx : P.color x=i := P.color_eq_of_mem (hi ▸ hw i)
          rw [hcx,← hecolor]
          exact Ne.symm hii
      · exact hcl D hDF hxD hyD hxy
  have hb := hfour (insert v D) hclE
  rw [card_insert_of_notMem hvD,hDc] at hb
  omega

theorem graphIso {G : SimpleGraph V} (heq : unionGraph F=G)
    (hprod : ProductFamily F P.parts) :
    Nonempty (G ≃g fourPartite (fun i => (P.parts i).card)) := by
  let e := P.coordinateEquiv
  have iso : fourPartite (fun i => (P.parts i).card) ≃g G :=
    { toEquiv := e
      map_rel_iff' := by
        intro x y
        rw [← heq,unionGraph_adj_iff P F hprod]
        rw [P.color_eq_of_mem (P.coordinateEquiv_mem x),P.color_eq_of_mem (P.coordinateEquiv_mem y)]
        rfl }
  exact ⟨iso.symm⟩

/-- The global family conclusion produces the precise ambient graph
classification, including its vertex bound and graph isomorphism. -/
theorem recognize {G : SimpleGraph V} (hprod : ProductFamily F P.parts)
    (hsize : ∀ i,(P.parts i).card=1 ∨ (P.parts i).card=2)
    (hcl : ∀ D∈F,G.IsClique D)
    (hfour : ∀ D : Finset V,G.IsClique D → D.card≤4) :
    unionGraph F=G ∧ Fintype.card V≤8 ∧
      ∃ a : Fin 4 → ℕ,(∀ i,a i=1 ∨ a i=2) ∧ Nonempty (G ≃g fourPartite a) := by
  have heq := ambient_eq P F hprod hcl hfour
  exact ⟨heq,P.card_le_eight (fun i => by rcases hsize i with h | h <;> omega),
    (fun i => (P.parts i).card),hsize,graphIso P F heq hprod⟩

/-- A Cartesian family covering every vertex gives the needed literal
partition without adding an ambient coverage assumption. -/
theorem parts_of_cover (A : Fin 4 → Finset V)
    (hne : ∀ i,(A i).Nonempty) (hdis : ∀ i j,i≠j → Disjoint (A i) (A j))
    (hprod : ProductFamily F A) (hcover : F.biUnion id=univ) :
    ∃ P : FourParts V,P.parts=A := by
  refine ⟨⟨A,hne,hdis,?_⟩,rfl⟩
  intro v
  have hv : v∈F.biUnion id := by rw [hcover];exact mem_univ _
  obtain ⟨D,hD,hv⟩ := mem_biUnion.mp hv
  obtain ⟨w,hw,rfl⟩ := (hprod D).mp hD
  obtain ⟨i,_,hi⟩ := mem_image.mp hv
  exact ⟨i,hi ▸ hw i⟩

end FourPartGraphRecognition
end GraphicalZonotopes
