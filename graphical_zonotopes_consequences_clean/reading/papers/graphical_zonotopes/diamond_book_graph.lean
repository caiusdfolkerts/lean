module

public import Papers.GraphicalZonotopes.ThreeTreeCliques
public import Papers.GraphicalZonotopes.SupportDimensionBound

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open Finset
open scoped BigOperators

abbrev Vertex (k : ℕ) := Fin (k+4)
def a (k : ℕ) : Vertex k := ⟨0,by omega⟩
def b (k : ℕ) : Vertex k := ⟨1,by omega⟩
def u (k : ℕ) : Vertex k := ⟨2,by omega⟩
def v (k : ℕ) : Vertex k := ⟨3,by omega⟩

@[simp] theorem a_ne_b (k : ℕ) : a k≠b k := by
  simp [a,b,Fin.ext_iff]

@[simp] theorem a_ne_u (k : ℕ) : a k≠u k := by
  simp [a,u,Fin.ext_iff]

@[simp] theorem a_ne_v (k : ℕ) : a k≠v k := by
  simp [a,v,Fin.ext_iff]

@[simp] theorem b_ne_a (k : ℕ) : b k≠a k := by
  simp [b,a,Fin.ext_iff]

@[simp] theorem b_ne_u (k : ℕ) : b k≠u k := by
  simp [b,u,Fin.ext_iff]

@[simp] theorem b_ne_v (k : ℕ) : b k≠v k := by
  simp [b,v,Fin.ext_iff]

@[simp] theorem u_ne_a (k : ℕ) : u k≠a k := by
  simp [u,a,Fin.ext_iff]

@[simp] theorem u_ne_b (k : ℕ) : u k≠b k := by
  simp [u,b,Fin.ext_iff]

@[simp] theorem u_ne_v (k : ℕ) : u k≠v k := by
  simp [u,v,Fin.ext_iff]

@[simp] theorem v_ne_a (k : ℕ) : v k≠a k := by
  simp [v,a,Fin.ext_iff]

@[simp] theorem v_ne_b (k : ℕ) : v k≠b k := by
  simp [v,b,Fin.ext_iff]

@[simp] theorem v_ne_u (k : ℕ) : v k≠u k := by
  simp [v,u,Fin.ext_iff]

/-- The four actual multipartite classes have sizes1,1,2,k. -/
def part (k : ℕ) (x : Vertex k) : Fin 4 :=
  if x.val=0 then 0 else if x.val=1 then 1 else if x.val<4 then 2 else 3

def graph (k : ℕ) : SimpleGraph (Vertex k) where
  Adj x y:=part k x≠part k y
  symm:=⟨fun _ _ => Ne.symm⟩
  loopless:=⟨fun _ h => h rfl⟩

instance graphDecidable (k : ℕ) : DecidableRel (graph k).Adj :=
  fun x y => inferInstanceAs (Decidable (part k x≠part k y))

theorem part_zero_iff (k : ℕ) (x : Vertex k) : part k x=0 ↔ x=a k := by
  constructor
  · intro h
    apply Fin.ext
    change x.val=0
    by_contra hx
    unfold part at h
    rw [if_neg hx] at h
    split_ifs at h <;> norm_num at h
  · intro h
    subst x
    rfl

@[simp] theorem part_a (k : ℕ) : part k (a k)=0 := rfl
@[simp] theorem part_b (k : ℕ) : part k (b k)=1 := rfl
@[simp] theorem part_u (k : ℕ) : part k (u k)=2 := rfl
@[simp] theorem part_v (k : ℕ) : part k (v k)=2 := rfl

theorem part_one_iff (k : ℕ) (x : Vertex k) : part k x=1 ↔ x=b k := by
  simp only [Fin.ext_iff,b]
  unfold part
  split_ifs <;> norm_num <;> omega

theorem part_two_iff (k : ℕ) (x : Vertex k) : part k x=2 ↔ x=u k ∨ x=v k := by
  simp only [Fin.ext_iff,u,v]
  unfold part
  split_ifs <;> norm_num <;> omega

/-- Every tetrahedron uses the two singleton vertices and one vertex from
the two-element part. This is an unrestricted statement for everyk. -/
theorem tetrahedron_contains_boundary (k : ℕ) (C : Finset (Vertex k))
    (hcard : C.card=4) (hc : (graph k).IsClique C) :
    a k∈C ∧ b k∈C ∧ (u k∈C ∨ v k∈C) := by
  have hinj : Set.InjOn (part k) C := by
    intro x hx y hy he
    by_contra hne
    exact hc hx hy hne he
  have himcard : (C.image (part k)).card=4 := (card_image_of_injOn hinj).trans hcard
  have him : C.image (part k)=univ := eq_univ_of_card (C.image (part k)) (by simpa using himcard)
  have hex (i : Fin 4) : ∃ x∈C,part k x=i := by
    apply mem_image.mp
    rw [him]
    exact mem_univ _
  obtain ⟨x,hx,hpx⟩:=hex 0
  obtain ⟨y,hy,hpy⟩:=hex 1
  obtain ⟨z,hz,hpz⟩:=hex 2
  refine ⟨(part_zero_iff k x).mp hpx ▸ hx,(part_one_iff k y).mp hpy ▸ hy,?_⟩
  rcases (part_two_iff k z).mp hpz with he | he
  · exact Or.inl (he ▸ hz)
  · exact Or.inr (he ▸ hz)

theorem admissible_triangle_bound {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} (hH : Admissible H) (T : Finset V) (hT : T.card=3) :
    triangleMultiplicity H T≤3 := by
  classical
  by_cases hc : H.IsClique T
  · exact hH T hT hc
  · have he : (tetrahedra H).filter (fun C => T⊆C)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro C hC
      obtain ⟨hC,hTC⟩:=mem_filter.mp hC
      have hcC : H.IsClique C:=((mem_filter.mp hC).2).2
      exact hc (fun x hx y hy hxy => hcC (hTC hx) (hTC hy) hxy)
    simp [triangleMultiplicity,he]

/-- No member of this unbounded family beyond the capacity threshold has
an admissible spanning3-tree. Counting all actual tetrahedra proves this
without assuming that a chosen construction is a double cone. -/
theorem no_admissible_spanning_threeTree (k : ℕ) (hk : 6≤k) :
    ¬HasAdmissibleSpanningThreeTree (graph k) := by
  classical
  rintro ⟨H,hsub,hthree,hadm⟩
  let U : Finset (Vertex k):={a k,b k,u k}
  let W : Finset (Vertex k):={a k,b k,v k}
  have hU : U.card=3:=by simp [U,a,b,u,Fin.ext_iff]
  have hW : W.card=3:=by simp [W,a,b,v,Fin.ext_iff]
  have hcapU:=admissible_triangle_bound hadm U hU
  have hcapW:=admissible_triangle_bound hadm W hW
  have hcover : tetrahedra H⊆
      (tetrahedra H).filter (fun C => U⊆C) ∪
      (tetrahedra H).filter (fun C => W⊆C) := by
    intro C hC
    have hc:=((mem_filter.mp hC).2)
    have hcG : (graph k).IsClique C:=fun x hx y hy hxy => hsub (hc.2 hx hy hxy)
    obtain ⟨ha,hb,hu|hv⟩:=tetrahedron_contains_boundary k C hc.1 hcG
    · apply mem_union_left
      exact mem_filter.mpr ⟨hC,by simpa [U,insert_subset_iff,singleton_subset_iff] using And.intro ha (And.intro hb hu)⟩
    · apply mem_union_right
      exact mem_filter.mpr ⟨hC,by simpa [W,insert_subset_iff,singleton_subset_iff] using And.intro ha (And.intro hb hv)⟩
  have hbound:=(card_le_card hcover).trans (card_union_le _ _)
  change (tetrahedra H).card≤triangleMultiplicity H U+triangleMultiplicity H W at hbound
  have hcount:=ThreeTreeOn.tetrahedra_card hthree
  rw [card_univ,Fintype.card_fin] at hcount
  omega

end GraphicalZonotopes.DiamondBook
