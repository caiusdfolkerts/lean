module

public import Papers.GraphicalZonotopes.ThreeTreeCoefficients
public import Papers.GraphicalZonotopes.ConditionalQuadratic
public import Papers.GraphicalZonotopes.CliqueLinkEquivalence

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ComplementPair.ne_val {C E : Finset V} (p : ComplementPair C E) :
    p.first.1≠p.second.1 := fun he => p.ne (Subtype.ext he)

theorem ComplementPair.first_notMem {C E : Finset V} (p : ComplementPair C E) :
    p.first.1∉E := by
  simpa only [p.erase_eq] using
    (show p.first.1 ∉ (C.erase p.first.1).erase p.second.1 from by simp)

theorem ComplementPair.second_notMem {C E : Finset V} (p : ComplementPair C E) :
    p.second.1∉E := by
  simpa only [p.erase_eq] using
    (show p.second.1 ∉ (C.erase p.first.1).erase p.second.1 from notMem_erase _ _)

theorem ComplementPair.mem_complement_iff {C E : Finset V}
    (p : ComplementPair C E) (w : V) :
    w∈C ∧ w∉E ↔ w=p.first.1 ∨ w=p.second.1 := by
  rw [← mem_sdiff,← p.pair_eq_complement]
  simp only [mem_insert,mem_singleton]

theorem ComplementPair.erase_first {C E : Finset V} (p : ComplementPair C E) :
    C.erase p.first.1=insert p.second.1 E := by
  simpa only [p.erase_eq] using
    (insert_erase (mem_erase.mpr ⟨p.ne_val.symm,p.second.2⟩)).symm

theorem ComplementPair.erase_second {C E : Finset V} (p : ComplementPair C E) :
    C.erase p.second.1=insert p.first.1 E := by
  have he : (C.erase p.second.1).erase p.first.1 = E := by
    rw [erase_right_comm]
    exact p.erase_eq
  simpa only [he] using (insert_erase (mem_erase.mpr ⟨p.ne_val,p.first.2⟩)).symm

/-- The linear coefficient contributed by one tetrahedron to the
elemental row at its complementary pair. This is expressed on every
ambient vertex, with exact zeros off the two remaining vertices. -/
def pairLinear (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) (w : V) : ℝ :=
  let p:=complementPair G C.1 E hE C.2
  if w=p.first.1 then realBit ((s.clique C.1).row p.second p.first)
  else if w=p.second.1 then realBit ((s.clique C.1).row p.first p.second)
  else 0

theorem pairLinear_eq_zero_of_notMem (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) (w : V)
    (hw : w∉C.1.1) : pairLinear G s E hE C w=0 := by
  let p:=complementPair G C.1 E hE C.2
  have ha : w≠p.first.1 := fun he => hw (he.symm ▸ p.first.2)
  have hb : w≠p.second.1 := fun he => hw (he.symm ▸ p.second.2)
  dsimp only [p] at ha hb
  simp only [pairLinear,ha,hb,ite_false]

theorem pairLinear_eq_zero_of_mem (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) (w : V)
    (hw : w∈E) : pairLinear G s E hE C w=0 := by
  let p:=complementPair G C.1 E hE C.2
  have ha : w≠p.first.1 := fun he => p.first_notMem (he ▸ hw)
  have hb : w≠p.second.1 := fun he => p.second_notMem (he ▸ hw)
  dsimp only [p] at ha hb
  simp only [pairLinear,ha,hb,ite_false]

def pairTriangleIncidenceEquiv (G : SimpleGraph V) (E : Finset V) (w : V)
    (hT : insert w E∈triangles G) :
    AllIncidentClique G ⟨insert w E,hT⟩ ≃
      {C : IncidentPairClique G E // w∈C.1.1} where
  toFun C:=⟨⟨C.1,(subset_insert w E).trans C.2⟩,C.2 (mem_insert_self _ _)⟩
  invFun C:=⟨C.1.1,insert_subset_iff.mpr ⟨C.2,C.1.2⟩⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem faceRow_eq_pairLinear (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (w : V) (hw : w∉E)
    (hT : insert w E∈triangles G)
    (D : AllIncidentClique G ⟨insert w E,hT⟩) :
    realBit (faceRow G s ⟨insert w E,hT⟩ D ⟨w,mem_insert_self _ _⟩)=
      pairLinear G s E hE ((pairTriangleIncidenceEquiv G E w hT) D).1 w := by
  let C:=((pairTriangleIncidenceEquiv G E w hT) D).1
  let p:=complementPair G C.1 E hE C.2
  have hwC : w∈C.1.1:=D.2 (mem_insert_self _ _)
  change realBit ((s.clique C.1).row (faceMissing G C.1 ⟨insert w E,hT⟩ D.2) ⟨w,hwC⟩) =
    if w=p.first.1 then realBit ((s.clique C.1).row p.second p.first)
    else if w=p.second.1 then realBit ((s.clique C.1).row p.first p.second) else 0
  rcases (p.mem_complement_iff w).mp ⟨hwC,hw⟩ with ha | hb
  · have hm : faceMissing G C.1 ⟨insert w E,hT⟩ D.2=p.second := by
      apply Subtype.ext
      apply (erase_inj C.1.1 (faceMissing G C.1 ⟨insert w E,hT⟩ D.2).2).mp
      rw [faceMissing_spec]
      change insert w E = C.1.1.erase p.second.1
      rw [p.erase_second,ha]
    have hwv : (⟨w,hwC⟩ : ↥C.1.1)=p.first:=Subtype.ext ha
    rw [hm, if_pos ha]
    exact congrArg (fun j => realBit ((s.clique C.1).row p.second j)) hwv
  · have hm : faceMissing G C.1 ⟨insert w E,hT⟩ D.2=p.first := by
      apply Subtype.ext
      apply (erase_inj C.1.1 (faceMissing G C.1 ⟨insert w E,hT⟩ D.2).2).mp
      rw [faceMissing_spec]
      change insert w E = C.1.1.erase p.first.1
      rw [p.erase_first,hb]
    have hna : w≠p.first.1 := by rw [hb]; exact p.ne_val.symm
    have hwv : (⟨w,hwC⟩ : ↥C.1.1)=p.second:=Subtype.ext hb
    rw [hm, if_neg hna, if_pos hb]
    exact congrArg (fun j => realBit ((s.clique C.1).row p.first j)) hwv

/-- Every actual triangle column is exactly the sum of its contributions
from tetrahedra incident with a fixed edge of that triangle. -/
theorem column_eq_sum_pairLinear (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (w : V) (hw : w∉E)
    (hT : insert w E∈triangles G) :
    columnValue G s ⟨insert w E,hT⟩ ⟨w,mem_insert_self _ _⟩=
      ∑ C : IncidentPairClique G E,pairLinear G s E hE C w := by
  classical
  unfold columnValue
  calc
    _=∑ C : {C : IncidentPairClique G E // w∈C.1.1},
        pairLinear G s E hE C.1 w :=
      Fintype.sum_equiv (pairTriangleIncidenceEquiv G E w hT) _ _
        (faceRow_eq_pairLinear G s E hE w hw hT)
    _=∑ C∈(univ : Finset (IncidentPairClique G E)).filter (fun C => w∈C.1.1),
        pairLinear G s E hE C w :=
      (sum_subtype ((univ : Finset (IncidentPairClique G E)).filter (fun C => w∈C.1.1))
        (by intro C; simp) (fun C => pairLinear G s E hE C w)).symm
    _=∑ C : IncidentPairClique G E,pairLinear G s E hE C w := by
      apply sum_subset (filter_subset _ _)
      intro C hC hnot
      exact pairLinear_eq_zero_of_notMem G s E hE C w
        (fun hwC => hnot (mem_filter.mpr ⟨hC,hwC⟩))

theorem coefficients_insert_pair {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (E : Finset V) (hE : E.card=2)
    (w : V) (hw : w∉E) :
    coefficients h s (insert w E)=
      -(∑ C : IncidentPairClique G E,pairLinear G s E hE C w) := by
  classical
  by_cases hT : insert w E∈triangles G
  · rw [coefficients_triangle h s hT,
      ← column_eq_triangleWeight h s ⟨insert w E,hT⟩ ⟨w,mem_insert_self _ _⟩,
      column_eq_sum_pairLinear G s E hE w hw hT]
  · have hzero : coefficients h s (insert w E)=0 := by
      by_contra hn
      have hcl:=(coefficients_cliqueSupported h s).clique_of_nonzero hn
      exact hT (mem_triangles.mpr ⟨by rw [card_insert_of_notMem hw,hE],hcl⟩)
    rw [hzero]
    symm
    rw [neg_eq_zero]
    apply sum_eq_zero
    intro C hC
    apply pairLinear_eq_zero_of_notMem G s E hE C w
    intro hwC
    apply hT
    refine mem_triangles.mpr ⟨by rw [card_insert_of_notMem hw,hE],?_⟩
    have hs : insert w E ⊆ C.1.1 := insert_subset_iff.mpr ⟨hwC,C.2⟩
    intro a ha b hb hab
    exact (mem_filter.mp C.1.2).2.2 (hs ha) (hs hb) hab

theorem pairLinear_sum (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) (x : V → ℝ) :
    (∑ w,pairLinear G s E hE C w*x w)=
      let p:=complementPair G C.1 E hE C.2
      realBit ((s.clique C.1).row p.second p.first)*x p.first.1+
      realBit ((s.clique C.1).row p.first p.second)*x p.second.1 := by
  let p:=complementPair G C.1 E hE C.2
  calc
    _=pairLinear G s E hE C p.first.1*x p.first.1+
        pairLinear G s E hE C p.second.1*x p.second.1 := by
      apply sum_eq_add_of_mem p.first.1 p.second.1 (mem_univ _) (mem_univ _) p.ne_val
      intro w hw hne
      dsimp only [p] at hne
      simp only [pairLinear,hne.1,hne.2,ite_false,zero_mul]
    _=_ := by
      have hp := p.ne_val.symm
      dsimp only [p] at hp ⊢
      simp only [pairLinear,ite_true,hp,ite_false]

end ThreeTreeStates
end GraphicalZonotopes
