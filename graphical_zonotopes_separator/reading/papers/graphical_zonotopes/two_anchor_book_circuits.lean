module

public import Papers.GraphicalZonotopes.TwoAnchorBlockData
public import Papers.GraphicalZonotopes.AnchoredWeightedCircuits
public import Papers.GraphicalZonotopes.BookBlockCounts

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise

/-- The complete two-threshold construction, uniformly in the ambient hub
set and every admissible intermediate sum of local block ranks. -/
theorem two_threshold_book_interval {s k : ℕ} (hs : 3≤s)
    (T : OrderedTriple (Fin s))
    (hklo : (∑ C : BookBlock (Fin s),T.lowerRank C)+2≤k)
    (hkhi : k≤(∑ C : BookBlock (Fin s),T.upperRank C)+2) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(((2*k : ℕ) : ℝ)) • graphicalZonotope (cliqueBook s k) := by
  classical
  obtain ⟨r,hr,hrsum⟩ := interval_sum_composition T.lowerRank T.upperRank T.lowerRank_le_upperRank
    (n:=k-2) (by omega) (by omega)
  let P := fun C => Classical.choice (T.omittedBlock_exists C (hr C).1 (hr C).2)
  have hF : ∀ C j,∃ F : SetFunction (Fin s),IsMonotoneBoolean F ∧
      (∀ a,a∈C.1 → Essential F a) ∧
      (∀ a,a∉C.1 → ∀ X,F (insert a X)=F X) ∧
      responseClass F=blockClass C.1 ((P C).column j) := fun C j => (P C).realizable j
  choose F hFb hFe hFi hFc using hF
  let J := Σ C : BookBlock (Fin s),Fin (r C)
  let G : J → SetFunction (Fin s) := fun j => F j.1 j.2
  let w : J → ℤ := fun j => (P j.1).weight j.2
  have hG : ∀ j,IsMonotoneBoolean (G j) := fun j => hFb j.1 j.2
  have hGc : ∀ j : J,responseClass (G j)=blockClass j.1.1 ((P j.1).column j.2) :=
    fun j => hFc j.1 j.2
  have hess : ∀ j,∃ a,Essential (G j) a := by
    intro j
    obtain ⟨a,ha⟩ := card_pos.mp (show 0<j.1.1.card by
      have h := (mem_largeBlocks.mp j.1.2).2
      omega)
    exact ⟨a,hFe j.1 j.2 a ha⟩
  have hpair : ∀ C : BookBlock (Fin s),∃ p : PairIn C.1,True := by
    intro C
    obtain ⟨p,hp⟩ := cliquePairs_nonempty C.1 C.1 (Subset.refl _)
      (by have h := (mem_largeBlocks.mp C.2).2; omega)
    exact ⟨p,trivial⟩
  have hind : LinearIndependent ℝ (fun j => responseClass (G j)) := by
    simp_rw [hGc]
    exact block_families_independent Subtype.val Subtype.val_injective
      (fun C => (hpair C).choose) (fun C => (P C).column) (fun C => (P C).independent)
  have hRest : LinearIndependent ℝ
      (fun j => responseClass (anchoredFamily (thresholdStar T.b) G j)) :=
    second_threshold_and_pure_independent T.a T.b (fun j : J => j.1.1)
      (fun j => (P j.1).column j.2) G hGc hind T.firstRow T.secondRow T.row_index_eq
      T.threshold_a_first T.threshold_a_second T.threshold_b_first T.threshold_b_second
      (fun j => ((P j.1).first_zero j.2).trans ((P j.1).second_zero j.2).symm)
  have hanchors : responseClass (thresholdStar T.a)+responseClass (thresholdStar T.b)=
      ∑ C : BookBlock (Fin s),(-1 : ℝ)^(C.1.card-3) •
        blockClass C.1 (starVector C.1 T.a+starVector C.1 T.b) := by
    rw [threshold_response_largeBlocks,threshold_response_largeBlocks,← sum_add_distrib]
    apply sum_congr rfl
    intro C hC
    simp only [map_add,smul_add]
  have hpures : (∑ j : J,(w j : ℝ) • responseClass (G j))=
      ∑ C : BookBlock (Fin s),twoAnchorTarget C.1 T.a T.b := by
    rw [Fintype.sum_sigma]
    apply sum_congr rfl
    intro C hC
    simpa only [w,hGc] using (P C).weighted_sum
  have hsum : responseClass (thresholdStar T.a)+
      ∑ j : Option J,(anchoredWeights w j : ℝ) •
        responseClass (anchoredFamily (thresholdStar T.b) G j)=0 := by
    rw [Fintype.sum_option]
    simp only [anchoredWeights,Int.cast_one,anchoredFamily,one_smul]
    rw [← add_assoc,hpures,hanchors]
    simp only [twoAnchorTarget,sum_neg_distrib,add_neg_cancel]
  have hRestB : ∀ j,IsMonotoneBoolean (anchoredFamily (thresholdStar T.b) G j) := by
    intro j
    cases j with
    | none => exact thresholdStar_boolean T.b
    | some j => exact hG j
  have hRestE : ∀ j,∃ a,Essential (anchoredFamily (thresholdStar T.b) G j) a := by
    intro j
    cases j with
    | none => exact ⟨T.b,thresholdStar_essential (by simpa using hs) T.b T.b⟩
    | some j => exact hess j
  have hw : ∀ j,0<anchoredWeights w j := by
    intro j
    cases j with
    | none => norm_num [anchoredWeights]
    | some j => exact (P j.1).positive j.2
  have hb : ∀ j,anchoredWeights w j≤2 := by
    intro j
    cases j with
    | none => norm_num [anchoredWeights]
    | some j => exact (P j.1).bounded j.2
  have hcard : Fintype.card (Option J)+1=k := by
    rw [Fintype.card_option,Fintype.card_sigma]
    simp only [Fintype.card_fin,hrsum]
    omega
  obtain ⟨f,hfn,hfi,hfe,hfg,hfd,hfm,hfl,R,hRl,hRn,hR⟩ :=
    lattice_book_of_anchored_weighted_circuit (by omega) (thresholdStar T.a)
      (anchoredFamily (thresholdStar T.b) G) (thresholdStar_boolean T.a) hRestB
      (thresholdStar_essential (by simpa using hs) T.a) hRestE
      (anchoredWeights w) hw 2 (by norm_num) hb hRest hsum hcard
  exact ⟨f,hfn,hfi,hfe,hfg,hfd,hfm,hfl,R,hRl,hRn,by simpa only [Int.cast_mul,
    Int.cast_ofNat,Int.cast_natCast,Nat.cast_mul,Nat.cast_ofNat] using hR⟩

def initialTriple {s : ℕ} (hs : 3≤s) : OrderedTriple (Fin s) where
  a := ⟨0,by omega⟩
  b := ⟨1,by omega⟩
  c := ⟨2,by omega⟩
  ab := by change (0 : ℕ)<1; omega
  bc := by change (1 : ℕ)<2; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem two_threshold_four_counts :
    (∑ C : BookBlock (Fin 4),(initialTriple (by decide : 3≤4)).lowerRank C)=10 ∧
    (∑ C : BookBlock (Fin 4),(initialTriple (by decide : 3≤4)).upperRank C)=12 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem two_threshold_five_counts :
    (∑ C : BookBlock (Fin 5),(initialTriple (by decide : 3≤5)).lowerRank C)=37 ∧
    (∑ C : BookBlock (Fin 5),(initialTriple (by decide : 3≤5)).upperRank C)=51 := by
  decide

/-- The four-hub overlap bridge of Lemma 7.9, including both endpoint sizes. -/
theorem two_threshold_four_bridge {k : ℕ} (hklo : 12≤k) (hkhi : k≤14) :
    ∃ f : SetFunction (Fin 4⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook 4 k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin 4⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(((2*k : ℕ) : ℝ)) • graphicalZonotope (cliqueBook 4 k) := by
  apply two_threshold_book_interval (by decide) (initialTriple (by decide))
  · rw [two_threshold_four_counts.1]
    exact hklo
  · rw [two_threshold_four_counts.2]
    exact hkhi

/-- The five-hub overlap bridge of Lemma 7.9, with every count 39 through 53. -/
theorem two_threshold_five_bridge {k : ℕ} (hklo : 39≤k) (hkhi : k≤53) :
    ∃ f : SetFunction (Fin 5⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook 5 k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin 5⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(((2*k : ℕ) : ℝ)) • graphicalZonotope (cliqueBook 5 k) := by
  apply two_threshold_book_interval (by decide) (initialTriple (by decide))
  · rw [two_threshold_five_counts.1]
    exact hklo
  · rw [two_threshold_five_counts.2]
    exact hkhi

end BooleanModule
end GraphicalZonotopes
