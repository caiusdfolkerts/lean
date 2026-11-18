module

public import Papers.GraphicalZonotopes.SmallBooleanGeometry
public import Papers.GraphicalZonotopes.DoubledPairData
public import Papers.GraphicalZonotopes.SmallPartTarget
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Tactic.IntervalCases

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace FourSmallParts
open Finset

/-- There is always the zero-labelled vertex of each part; precisely the
parts in `s` also have their one-labelled vertex. -/
abbrev Vertices (s : Finset (Fin 4)) :=
  {v : Fin 4×Fin 2 // v.2=0 ∨ v.1∈s}

def graph (s : Finset (Fin 4)) : SimpleGraph (Vertices s) :=
  (DoubledParts.graph (Fin 4)).comap Subtype.val

def canonicalParts (d : ℕ) : Finset (Fin 4) := (univ : Finset (Fin 4)).filter (fun i => (4 - d : ℕ) ≤ i.val)

theorem canonicalParts_card {d : ℕ} (hd : d≤4) : (canonicalParts d).card=d := by
  interval_cases d <;> decide

def canonicalZeroEquiv : Vertices (canonicalParts 0) ≃ Fin 4 :=
  Equiv.ofBijective (fun v => v.1.1) (by decide)

def canonicalOneMap (v : Vertices (canonicalParts 1)) : Fin 5 :=
  ⟨if v.1.1=3 then 3+v.1.2.val else v.1.1.val,by
    have hi := v.1.1.isLt
    have hb := v.1.2.isLt
    split <;> omega⟩

def canonicalOneEquiv : Vertices (canonicalParts 1) ≃ Fin 5 :=
  Equiv.ofBijective canonicalOneMap (by decide)

def canonicalTwoMap (v : Vertices (canonicalParts 2)) : Fin 6 :=
  ⟨if v.1.1.val<2 then v.1.1.val else 2*v.1.1.val-2+v.1.2.val,by
    have hi := v.1.1.isLt
    have hb := v.1.2.isLt
    split <;> omega⟩

def canonicalTwoEquiv : Vertices (canonicalParts 2) ≃ Fin 6 :=
  Equiv.ofBijective canonicalTwoMap (by decide)

def canonicalThreeEquiv : Vertices (canonicalParts 3) ≃ DoubledParts.SingletonVertices (0 : Fin 4) :=
  Equiv.subtypeEquivRight (by decide)

def canonicalFourEquiv : Vertices (canonicalParts 4) ≃ Fin 4×Fin 2 :=
  Equiv.subtypeUnivEquiv (by decide)

theorem canonicalZero_graph : SmallBoolean.K4.graph.comap canonicalZeroEquiv=graph (canonicalParts 0) := by
  have h : ∀ u v : Vertices (canonicalParts 0),
      SmallBoolean.K4.part (canonicalZeroEquiv u)≠SmallBoolean.K4.part (canonicalZeroEquiv v) ↔
        u.1.1≠v.1.1 := by decide
  ext u v
  exact h u v

theorem canonicalOne_graph : SmallBoolean.K1112.graph.comap canonicalOneEquiv=graph (canonicalParts 1) := by
  have h : ∀ u v : Vertices (canonicalParts 1),
      SmallBoolean.K1112.part (canonicalOneEquiv u)≠SmallBoolean.K1112.part (canonicalOneEquiv v) ↔
        u.1.1≠v.1.1 := by decide
  ext u v
  exact h u v

theorem canonicalTwo_graph : SmallBoolean.K1122.graph.comap canonicalTwoEquiv=graph (canonicalParts 2) := by
  have h : ∀ u v : Vertices (canonicalParts 2),
      SmallBoolean.K1122.part (canonicalTwoEquiv u)≠SmallBoolean.K1122.part (canonicalTwoEquiv v) ↔
        u.1.1≠v.1.1 := by decide
  ext u v
  exact h u v

theorem canonicalThree_graph : (DoubledParts.singletonGraph (0 : Fin 4)).comap canonicalThreeEquiv=
    graph (canonicalParts 3) := by
  ext u v
  rfl

theorem canonicalFour_graph : (DoubledParts.graph (Fin 4)).comap canonicalFourEquiv=
    graph (canonicalParts 4) := by
  ext u v
  rfl

def canonicalPair (d : ℕ) (hd : d≤4) : BooleanPairData (graph (canonicalParts d)) := by
  interval_cases d
  · simpa only [canonicalZero_graph] using SmallBoolean.K4.pairData.relabel canonicalZeroEquiv
  · simpa only [canonicalOne_graph] using SmallBoolean.K1112.pairData.relabel canonicalOneEquiv
  · simpa only [canonicalTwo_graph] using SmallBoolean.K1122.pairData.relabel canonicalTwoEquiv
  · simpa only [canonicalThree_graph] using
      (DoubledParts.singletonPairData (I := Fin 4) (by decide) 0).relabel canonicalThreeEquiv
  · simpa only [canonicalFour_graph] using
      (DoubledParts.doubledPairData (I := Fin 4) (by decide)).relabel canonicalFourEquiv

def permuteParts {s t : Finset (Fin 4)} (σ : Equiv.Perm (Fin 4))
    (hσ : s.map σ.toEmbedding=t) : Vertices s ≃ Vertices t :=
  (σ.prodCongr (Equiv.refl (Fin 2))).subtypeEquiv (by
    intro v
    rw [← hσ]
    simp)

theorem graph_permuteParts {s t : Finset (Fin 4)} (σ : Equiv.Perm (Fin 4))
    (hσ : s.map σ.toEmbedding=t) : (graph t).comap (permuteParts σ hσ)=graph s := by
  ext u v
  change (σ u.1.1≠σ v.1.1) ↔ (u.1.1≠v.1.1)
  exact not_congr σ.injective.eq_iff

/-- Every one of the sixteen part patterns is covered. The reduction uses an
actual permutation of the four parts and an equivalence of all real cones. -/
def pairData (s : Finset (Fin 4)) : BooleanPairData (graph s) := by
  have hd : s.card≤4 := by simpa using card_le_card (subset_univ s)
  have hex := Equiv.Perm.exists_map_finset_eq s (canonicalParts s.card)
    (canonicalParts_card hd).symm
  let σ := Classical.choose hex
  have hσ := Classical.choose_spec hex
  simpa only [graph_permuteParts] using (canonicalPair s.card hd).relabel (permuteParts σ hσ)

def doubledParts (a : Fin 4 → ℕ) : Finset (Fin 4) := univ.filter fun i => a i=2

def partSizeEquiv (a : Fin 4 → ℕ) (ha : ∀ i,a i=1 ∨ a i=2) :
    (Σ i : Fin 4,Fin (a i)) ≃ Vertices (doubledParts a) where
  toFun v := ⟨(v.1,⟨v.2.val,by rcases ha v.1 with h | h <;> have hv := v.2.isLt <;> omega⟩),by
    rcases ha v.1 with h | h
    · left
      apply Fin.ext
      change v.2.val=0
      have hv := v.2.isLt
      omega
    · right
      simp [doubledParts,h]⟩
  invFun v := ⟨v.1.1,⟨v.1.2.val,by
    rcases ha v.1.1 with h | h
    · have hb : v.1.2=0 := by
        rcases v.2 with hb | hm
        · exact hb
        · have hm' : a v.1.1=2 := by simpa [doubledParts] using hm
          omega
      simp [h,hb]
    · have hb := v.1.2.isLt
      omega⟩⟩
  left_inv v := by
    rcases v with ⟨i,b⟩
    congr 1
  right_inv v := by
    apply Subtype.ext
    exact Prod.ext rfl (Fin.ext rfl)

theorem graph_partSizeEquiv (a : Fin 4 → ℕ) (ha : ∀ i,a i=1 ∨ a i=2) :
    (graph (doubledParts a)).comap (partSizeEquiv a ha)=fourPartite a := by
  ext u v
  rfl

theorem fourPartite_connected (a : Fin 4 → ℕ) (ha : ∀ i,0<a i) :
    (fourPartite a).Connected := by
  letI : Nonempty (Σ i : Fin 4,Fin (a i)) := ⟨⟨0,⟨0,ha 0⟩⟩⟩
  refine ⟨?_⟩
  intro u v
  by_cases huv : u.1≠v.1
  · exact SimpleGraph.Adj.reachable huv
  · have he : u.1=v.1 := not_not.mp huv
    let i : Fin 4 := if u.1=0 then 1 else 0
    have hi : i≠u.1 := by
      dsimp [i]
      split_ifs with h
      · simp [h]
      · exact Ne.symm h
    let w : Σ i : Fin 4,Fin (a i) := ⟨i,⟨0,ha i⟩⟩
    exact (SimpleGraph.Adj.reachable (show (fourPartite a).Adj u w from Ne.symm hi)).trans
      (SimpleGraph.Adj.reachable (show (fourPartite a).Adj w v from by change i≠v.1; rwa [← he]))

/-- Corollary9.11, with its original arbitrary four part sizes and actual
Minkowski equality in the standard integer coordinate lattice. -/
theorem four_small_parts_decomposition : Targets.FourSmallPartsDecomposition := by
  intro a ha
  have hconn := fourPartite_connected a (fun i => by rcases ha i with h | h <;> omega)
  let D : BooleanPairData (fourPartite a) := by
    simpa only [graph_partSizeEquiv] using (pairData (doubledParts a)).relabel (partSizeEquiv a ha)
  exact ⟨basePolytope D.left,basePolytope D.right,D.geometric_pair hconn⟩

end FourSmallParts
end GraphicalZonotopes
