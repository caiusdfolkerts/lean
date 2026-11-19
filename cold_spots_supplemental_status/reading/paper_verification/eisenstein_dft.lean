module
public import PaperVerification.EisensteinArithmetic
public import Mathlib.Tactic.Abel
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def eisDFTNum (v : Fin 3 → EisInt) : Fin 3 → EisInt :=
  ![v 0 + v 1 + v 2,
    v 0 + eisOmega (v 1) + eisOmega (eisOmega (v 2)),
    v 0 + eisOmega (eisOmega (v 1)) + eisOmega (v 2)]

theorem eisDFTNum_residue (v : Fin 3 → EisInt) (i : Fin 3) :
    eisResidue (eisDFTNum v i) = eisResidue (∑ j, v j) := by
  fin_cases i <;>
    simp [eisDFTNum, Fin.sum_univ_three, map_add, eisResidue_omega, add_assoc]

theorem eisDFTNum_sum (v : Fin 3 → EisInt) :
    (∑ i, eisDFTNum v i) = (3 : ℤ) • v 0 := by
  ext <;> simp [eisDFTNum, eisOmega, Fin.sum_univ_succ, zsmul_eq_mul] <;> ring

theorem triDFT_embed (v : Fin 3 → EisInt) (i : Fin 3) :
    triDFT (fun j ↦ eisEmbed (v j)) i = triThetaInv (eisEmbed (eisDFTNum v i)) := by
  fin_cases i <;> simp [triDFT, eisDFTNum, map_add]

lemma triTheta_add (x y : TriPoint) : triTheta (x + y) = triTheta x + triTheta y := by
  ext <;> dsimp [triTheta] <;> ring

lemma triTheta_smul (a : ℝ) (x : TriPoint) : triTheta (a • x) = a • triTheta x := by
  ext <;> dsimp [triTheta] <;> ring

lemma eisEmbed_zsmul (a : ℤ) (x : EisInt) : eisEmbed (a • x) = (a : ℝ) • eisEmbed x := by
  ext <;> simp [eisEmbed, zsmul_eq_mul]

abbrev TriZeroSum := {h : Fin 3 → EisInt // eisResidue (∑ i, h i) = 0}
abbrev TriGlueIndex := ZMod 3 × TriZeroSum

def triGluePoint (g : TriGlueIndex) : Fin 3 → TriPoint :=
  fun i ↦ eisEmbed (g.2.val i) + (g.1.val : ℝ) • triC

theorem triGluePoint_injective : Function.Injective triGluePoint := by
  intro g h heq
  have h0 := congrArg Prod.fst (congrFun heq 0)
  change ((g.2.val 0).1 : ℝ) + (g.1.val : ℝ) * (1 / 3) =
    ((h.2.val 0).1 : ℝ) + (h.1.val : ℝ) * (1 / 3) at h0
  have hint : (3 : ℤ) * ((g.2.val 0).1 - (h.2.val 0).1) =
      (h.1.val : ℤ) - (g.1.val : ℤ) := by
    apply Int.cast_injective (α := ℝ)
    push_cast
    linarith
  have hmod := congrArg (fun k : ℤ ↦ (k : ZMod 3)) hint
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_sub, Int.cast_natCast,
    ZMod.natCast_zmod_val, zmodThree_three_eq_zero, zero_mul] at hmod
  have hr : g.1 = h.1 := by linear_combination hmod
  have hh : g.2 = h.2 := by
    apply Subtype.ext
    funext i
    apply eisEmbed_injective
    have hi := congrFun heq i
    change eisEmbed (g.2.val i) + (g.1.val : ℝ) • triC =
      eisEmbed (h.2.val i) + (h.1.val : ℝ) • triC at hi
    rw [hr] at hi
    exact add_right_cancel hi
  exact Prod.ext hr hh

/-- The transformed integer lattice has exactly the three common cosets and
the single theta-residue condition used in the cubic identity. -/
theorem exists_triGlue_of_eis (v : Fin 3 → EisInt) :
    ∃ g : TriGlueIndex, triDFT (fun i ↦ eisEmbed (v i)) = triGluePoint g := by
  let r : ZMod 3 := -eisResidue (∑ i, v i)
  let d : EisInt := ((r.val : ℤ), (r.val : ℤ))
  have hd : eisResidue d = 2 * r := by
    simp [d, eisResidue, two_mul]
  have hz (i : Fin 3) : eisResidue (eisDFTNum v i - d) = 0 := by
    rw [map_sub, eisDFTNum_residue, hd]
    dsimp [r]
    have h3 : (3 : ZMod 3) = 0 := by decide
    linear_combination eisResidue (∑ j, v j) * h3
  let h : Fin 3 → EisInt := fun i ↦ eisThetaDiv (eisDFTNum v i - d) (hz i)
  have ht (i : Fin 3) : eisTheta (h i) = eisDFTNum v i - d := eisTheta_div _ (hz i)
  have hsum : (∑ i, h i) = eisTheta (d - v 0) := by
    apply eisTheta_injective
    rw [map_sum]
    simp only [ht, Finset.sum_sub_distrib, eisDFTNum_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    rw [eisTheta_sq]
    ext <;> simp [zsmul_eq_mul, nsmul_eq_mul] <;> ring
  have hzero : eisResidue (∑ i, h i) = 0 := by rw [hsum, eisResidue_theta]
  refine ⟨(r, ⟨h, hzero⟩), ?_⟩
  funext i
  apply triTheta_injective
  rw [triDFT_embed, triTheta_inv]
  change eisEmbed (eisDFTNum v i) = triTheta (eisEmbed (h i) + (r.val : ℝ) • triC)
  rw [triTheta_add, triTheta_smul, triTheta_embed, triTheta_c, ht, map_sub]
  have he : (r.val : ℝ) • eisEmbed (1, 1) = eisEmbed d := by
    ext <;> simp [d, eisEmbed]
  rw [he, sub_add_cancel]

def eisInverseNum (g : TriGlueIndex) : Fin 3 → EisInt :=
  ![(∑ i, g.2.val i) + ((g.1.val : ℤ), -(g.1.val : ℤ)),
    g.2.val 0 + eisOmega (eisOmega (g.2.val 1)) + eisOmega (g.2.val 2),
    g.2.val 0 + eisOmega (g.2.val 1) + eisOmega (eisOmega (g.2.val 2))]

theorem eisInverseNum_residue (g : TriGlueIndex) (i : Fin 3) :
    eisResidue (eisInverseNum g i) = 0 := by
  have h := g.2.property
  have hs : eisResidue (g.2.val 0) + eisResidue (g.2.val 1) + eisResidue (g.2.val 2) = 0 := by
    simpa [Fin.sum_univ_succ, map_add, add_assoc] using h
  fin_cases i
  · change eisResidue ((∑ i, g.2.val i) +
        ((g.1.val : ℤ), -(g.1.val : ℤ))) = 0
    rw [map_add, h, zero_add]
    simp [eisResidue]
  · simpa [eisInverseNum, map_add] using hs
  · simpa [eisInverseNum, map_add] using hs

theorem triDFTInv_glue (g : TriGlueIndex) (i : Fin 3) :
    triDFTInv (triGluePoint g) i = -triThetaInv (eisEmbed (eisInverseNum g i)) := by
  fin_cases i <;> ext <;>
    simp [triDFTInv, triGluePoint, eisInverseNum, Fin.sum_univ_succ,
      triThetaInv, triOmega, triC, eisEmbed, eisOmega] <;> ring

theorem exists_eis_of_triGlue (g : TriGlueIndex) :
    ∃ v : Fin 3 → EisInt, triDFT (fun i ↦ eisEmbed (v i)) = triGluePoint g := by
  let v : Fin 3 → EisInt := fun i ↦ -eisThetaDiv (eisInverseNum g i) (eisInverseNum_residue g i)
  have hv : (fun i ↦ eisEmbed (v i)) = triDFTInv (triGluePoint g) := by
    funext i
    rw [triDFTInv_glue, triThetaInv_embed_integral _ (eisInverseNum_residue g i)]
    exact map_neg eisEmbed _
  exact ⟨v, by rw [hv, triDFT_right_inv]⟩

def triGlueOfEis (v : Fin 3 → EisInt) : TriGlueIndex := Classical.choose (exists_triGlue_of_eis v)

lemma triGlueOfEis_spec (v : Fin 3 → EisInt) :
    triDFT (fun i ↦ eisEmbed (v i)) = triGluePoint (triGlueOfEis v) :=
  Classical.choose_spec (exists_triGlue_of_eis v)

theorem triGlueOfEis_bijective : Function.Bijective triGlueOfEis := by
  constructor
  · intro v w h
    have hT : triDFT (fun i ↦ eisEmbed (v i)) = triDFT (fun i ↦ eisEmbed (w i)) := by
      rw [triGlueOfEis_spec, triGlueOfEis_spec, h]
    have he := triDFT_injective hT
    funext i
    exact eisEmbed_injective (congrFun he i)
  · intro g
    obtain ⟨v, hv⟩ := exists_eis_of_triGlue g
    refine ⟨v, triGluePoint_injective ?_⟩
    exact (triGlueOfEis_spec v).symm.trans hv

def triDFTIntegerEquiv : (Fin 3 → EisInt) ≃ TriGlueIndex :=
  Equiv.ofBijective triGlueOfEis triGlueOfEis_bijective

@[simp] theorem triDFTIntegerEquiv_apply (v : Fin 3 → EisInt) :
    triDFTIntegerEquiv v = triGlueOfEis v := rfl

theorem triDFT_lattice_distance (v : Fin 3 → EisInt) (z : TriPoint) :
    (∑ i, triQ (eisEmbed (v i) - (![z, z + triC, z - triC] : Fin 3 → TriPoint) i)) =
      ∑ i, triQ (triGluePoint (triDFTIntegerEquiv v) i -
        (![-triTheta z, triC, -triC] : Fin 3 → TriPoint) i) := by
  have h := triDFT_preserves_norm
    ((fun i ↦ eisEmbed (v i)) - ![z, z + triC, z - triC])
  rw [triDFT_sub, triDFT_centers, triGlueOfEis_spec] at h
  simpa only [Pi.sub_apply, triDFTIntegerEquiv_apply] using h.symm

end PaperVerification.ColdSpots
