module

public import Papers.GraphicalZonotopes.NegativeStarInterpolation
public import Papers.GraphicalZonotopes.BlockFamilies
public import Papers.GraphicalZonotopes.AnchoredBooleanCircuits
public import Papers.GraphicalZonotopes.AnchorBlockCounts
public import Papers.GraphicalZonotopes.ThresholdResponse

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H : Type*} [Fintype H] [LinearOrder H]

abbrev AnchorBlock (a : H) := ↥(anchorBlocks (univ : Finset H) a)

def anchorSignedClass (a : H) (C : AnchorBlock a) : ResponseQuotient H :=
  (-1 : ℝ)^(C.1.card-3) • blockClass C.1 (starVector C.1 a)

/-- The threshold response is the sum of its signed stars over every clique
block containing the anchor, with all other actual rows zero. -/
theorem threshold_response_block_sum (a : H) :
    responseClass (thresholdStar a)=∑ C : AnchorBlock a,anchorSignedClass a C := by
  have hcoord : thresholdSignedStar a=
      ∑ C : AnchorBlock a,(-1 : ℝ)^(C.1.card-3) •
        blockCoordinates C.1 (starVector C.1 a) := by
    funext r
    rw [Finset.sum_apply]
    by_cases hr : rowClique r∈anchorBlocks (univ : Finset H) a
    · let C₀ : AnchorBlock a := ⟨rowClique r,hr⟩
      rw [sum_eq_single C₀]
      · change thresholdSignedStar a r=
          (-1 : ℝ)^((rowClique r).card-3)*
            blockCoordinates (rowClique r) (starVector (rowClique r) a) r
        have he : blockCoordinates (rowClique r) (starVector (rowClique r) a) r=
            starVector (rowClique r) a (pairAtRow (rowClique r) r rfl) := by
          change (if h : rowClique r=rowClique r then
            starVector (rowClique r) a (pairAtRow (rowClique r) r h) else 0)=_
          rw [dite_eq_left rfl]
        rw [he,starVector_eq]
        have hsize := (mem_anchorBlocks.mp hr).2.2
        change (if 3≤(rowClique r).card ∧ (a=r.1.1.1 ∨ a=r.1.1.2) then
          (-1 : ℝ)^((rowClique r).card-3) else 0)=
          (-1 : ℝ)^((rowClique r).card-3)*(if a=r.1.1.1 ∨ a=r.1.1.2 then 1 else 0)
        by_cases h : a=r.1.1.1 ∨ a=r.1.1.2 <;> simp [hsize,h]
      · intro C hC hne
        have hrow : rowClique r≠C.1 := fun h => hne (Subtype.ext h.symm)
        change (-1 : ℝ)^(C.1.card-3)*
          (if h : rowClique r=C.1 then starVector C.1 a (pairAtRow C.1 r h) else 0)=0
        rw [dite_eq_right hrow,mul_zero]
      · simp
    · have hterms : ∀ C : AnchorBlock a,
          ((-1 : ℝ)^(C.1.card-3) • blockCoordinates C.1 (starVector C.1 a)) r=0 := by
        intro C
        have hrow : rowClique r≠C.1 := fun h => hr (h.symm ▸ C.2)
        change (-1 : ℝ)^(C.1.card-3)*
          (if h : rowClique r=C.1 then starVector C.1 a (pairAtRow C.1 r h) else 0)=0
        rw [dite_eq_right hrow,mul_zero]
      rw [sum_eq_zero (fun C _ => hterms C)]
      have hn : ¬(3≤(rowClique r).card ∧ (a=r.1.1.1 ∨ a=r.1.1.2)) := by
        rintro ⟨hc,ha⟩
        apply hr
        apply mem_anchorBlocks.mpr
        refine ⟨subset_univ _,?_,hc⟩
        rcases ha with h | h <;> simp [rowClique,h]
      exact ite_eq_right hn
  rw [thresholdStar_response_class,hcoord,map_sum]
  apply sum_congr rfl
  intro C hC
  rw [map_smul]
  rfl

theorem anchor_cancellation_decomposition (a : H) (C : AnchorBlock a)
    {k : ℕ} (hk : 1≤k) (hkC : k≤C.1.card.choose 2-1) :
    Nonempty (PureDecomposition C.1 (-anchorSignedClass a C) k) := by
  have hsize := (mem_anchorBlocks.mp C.2).2.2
  have ha := (mem_anchorBlocks.mp C.2).2.1
  rcases neg_one_pow_eq_or ℝ (C.1.card-3) with h | h
  · simpa only [anchorSignedClass,h,one_smul] using
      negative_star_interpolation C.1 hsize a ha hk hkC
  · simpa only [anchorSignedClass,h,neg_one_smul,neg_neg] using
      positive_star_interpolation C.1 hsize a ha hk hkC

/-- The whole single-threshold interval of Lemma 7.8. The upper endpoint is
written as the equivalent difference of complete response capacities. Every
ambient parameter is arbitrary, and the witness has an integral complement
in exactly `k` times the original graphical zonotope. -/
theorem threshold_book_interval {s k : ℕ} (hs : 3≤s)
    (hklo : 2^(s-1)-s+1≤k)
    (hkhi : k≤cliqueCapacity s-cliqueCapacity (s-1)+1) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(k : ℝ) • graphicalZonotope (cliqueBook s k) := by
  classical
  let a : Fin s := ⟨0,by omega⟩
  let d : AnchorBlock a → ℕ := fun C => C.1.card.choose 2-1
  have hd : ∀ C,1≤d C := by
    intro C
    have h := Nat.choose_le_choose 2 (mem_anchorBlocks.mp C.2).2.2
    norm_num [Nat.choose] at h
    change 1≤C.1.card.choose 2-1
    omega
  have hcard : Fintype.card (AnchorBlock a)=2^(s-1)-s := by
    simpa only [AnchorBlock,Fintype.card_coe,card_univ,Fintype.card_fin] using
      anchorBlocks_card (univ : Finset (Fin s)) a (mem_univ a)
  have hsumd : (∑ C : AnchorBlock a,d C)=cliqueCapacity s-cliqueCapacity (s-1) := by
    change (∑ C : ↥(anchorBlocks (univ : Finset (Fin s)) a),(C.1.card.choose 2-1))=_
    rw [sum_coe_sort (anchorBlocks (univ : Finset (Fin s)) a)
      (fun C : Finset (Fin s) => C.card.choose 2-1)]
    simpa only [card_univ,Fintype.card_fin] using
      anchorBlocks_dimension_sum (univ : Finset (Fin s)) a (mem_univ a)
  have hkpos : 0<k := by omega
  obtain ⟨r,hr,hrsum⟩ := positive_sum_composition d hd (n:=k-1)
    (by rw [hcard]; omega) (by rw [hsumd]; omega)
  have hP : ∀ C : AnchorBlock a,Nonempty
      (PureDecomposition C.1 (-anchorSignedClass a C) (r C)) :=
    fun C => anchor_cancellation_decomposition a C (hr C).1 (hr C).2
  let P := fun C => Classical.choice (hP C)
  let F : (Σ C : AnchorBlock a,Fin (r C)) → SetFunction (Fin s) :=
    fun j => (P j.1).functions j.2
  have hind : LinearIndependent ℝ (fun j => responseClass (F j)) :=
    pureDecompositions_independent Subtype.val Subtype.val_injective
      (fun C => by have h := (mem_anchorBlocks.mp C.2).2.2; omega)
      (fun C => -anchorSignedClass a C) r P
  have hsum : responseClass (thresholdStar a)+∑ j,responseClass (F j)=0 := by
    rw [Fintype.sum_sigma]
    have hp : ∀ C : AnchorBlock a,(∑ j : Fin (r C),responseClass (F ⟨C,j⟩))=
        -anchorSignedClass a C := fun C => (P C).sum_eq
    simp_rw [hp]
    rw [sum_neg_distrib,← threshold_response_block_sum]
    exact add_neg_cancel _
  apply lattice_book_of_anchored_circuit (by omega) (thresholdStar a) F
    (thresholdStar_boolean a) (fun j => (P j.1).monotone_boolean j.2)
    (thresholdStar_essential (by simpa using hs) a)
    (fun j => ⟨a,(P j.1).essential j.2 a (mem_anchorBlocks.mp j.1.2).2.1⟩)
    hind hsum
  simp only [Fintype.card_sigma,Fintype.card_fin,hrsum]
  omega

end BooleanModule
end GraphicalZonotopes
