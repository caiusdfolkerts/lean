module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Elab.Tactic.Omega
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Order.Compact
public import paper_verification.lattice003
public import paper_verification.lattice004

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.BWHoles
section Source_BWHoles

-- original header: module
-- original header: public import PaperVerification.BWEligibility
-- original header: @[expose] public section
/-! # The full Barnes–Wall deep-hole equality criterion

An explicit real point attains squared depth 3/2.  The proof then identifies all
points attaining it with exactly the same coset condition as sharp Gaussian
 gluing.  The argument applies to every point of R¹⁶.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def bwQuarterPoint : Fin 8 → ℝ := fun _ => 1 / 4

def BWGluingCondition (x y : Fin 8 → ℝ) : Prop :=
  squaredDepth bwMSet x = 1 / 2 ∧ squaredDepth bwMSet y = 1 / 2 ∧
    ∀ q : BWQuotient, bwDepthProfile x q = 1 ∨ bwDepthProfile y q = 1

theorem e8FirstVector_eq_intVec : e8FirstVector = intVec (bitUnit 1) := by
  funext i
  simp [e8FirstVector, intVec, bitUnit]

theorem e8FirstVector_mem_bwM : e8FirstVector ∈ bwMSet := by
  rw [e8FirstVector_eq_intVec]
  exact intVec_mem_bwM _

theorem roundedInt_add_intVec {n : ℕ} (x : Fin n → ℝ) (m : Fin n → ℤ) :
    roundedInt (x + intVec m) = roundedInt x + m := by
  funext i
  simp only [roundedInt, Pi.add_apply, intVec, round_add_intCast]

theorem quarter_hole_or_unit_translate {x : Fin 8 → ℝ}
    (hx : QuarterGrid8 x) (hs : IntegerSum8 x) :
    E8FoldedHole x ∨ E8FoldedHole (x + e8FirstVector) := by
  have hp := quarter_parities_equiv hx hs
  by_cases he : Even (∑ i, roundedInt x i)
  · right
    have hg : -e8FirstVector ∈ bwMSet := bwMSet_neg e8FirstVector_mem_bwM
    have hx' : QuarterGrid8 (x + e8FirstVector) := by
      simpa only [sub_neg_eq_add] using quarterGrid_sub_bwM hx hg
    have hs' : IntegerSum8 (x + e8FirstVector) := by
      simpa only [sub_neg_eq_add] using integerSum_sub hs (bwM_integerSum hg)
    have hne : ¬Even (∑ i, roundedInt (x + e8FirstVector) i) := by
      rw [e8FirstVector_eq_intVec, roundedInt_add_intVec]
      simp only [Pi.add_apply, Finset.sum_add_distrib, sum_bitUnit, ZMod.val_one, Nat.cast_one]
      simpa only [Int.even_add_one, not_not] using he
    exact Or.inr (Or.inr (Or.inr ⟨(quarterGrid_iff_folded _).mp hx', hne,
      fun h => hne ((quarter_parities_equiv hx' hs').mpr h)⟩))
  · left
    exact Or.inr (Or.inr (Or.inr ⟨(quarterGrid_iff_folded _).mp hx, he,
      fun h => he (hp.mpr h)⟩))

theorem bwQuarterPoint_quarterGrid : QuarterGrid8 bwQuarterPoint := by
  intro i
  exact ⟨0, by norm_num [bwQuarterPoint]⟩

theorem bwQuarterPoint_integerSum : IntegerSum8 bwQuarterPoint := by
  exact ⟨2, by norm_num [bwQuarterPoint]⟩

/-- Every half-integer coordinate is at least one quarter from the witness. -/
theorem quarter_half_integer_sq_lower (k : ℤ) :
    (1 / 16 : ℝ) ≤ (1 / 4 - (k : ℝ) / 2) ^ 2 := by
  have hk : k ≤ 0 ∨ 1 ≤ k := by omega
  rcases hk with hk | hk
  · have h : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    nlinarith [sq_nonneg ((k : ℝ) / 2)]
  · have h : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hs := sq_nonneg (((k : ℝ) - 1) / 2)
    nlinarith

theorem squaredDepth_bwM_quarter : squaredDepth bwMSet bwQuarterPoint = 1 / 2 := by
  apply le_antisymm (squaredDepth_bwM_le _)
  apply le_csInf ((show bwMSet.Nonempty from ⟨0, bwMSet_zero⟩).image (fun z => sqDist bwQuarterPoint z))
  rintro r ⟨z, ⟨w, hw, rfl⟩, rfl⟩
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 8)))
    (fun i _ => quarter_half_integer_sq_lower (w i))
  norm_num [sqDist, bwQuarterPoint] at h ⊢
  exact h

theorem squaredDepth_bwM_quarter_unit :
    squaredDepth bwMSet (bwQuarterPoint + e8FirstVector) = 1 / 2 := by
  change squaredDepth (bwMAddSubgroup : Set (Fin 8 → ℝ))
    (bwQuarterPoint + e8FirstVector) = 1 / 2
  rw [squaredDepth_add_of_subgroup bwMAddSubgroup _ _ e8FirstVector_mem_bwM]
  exact squaredDepth_bwM_quarter

/-- The two witness profiles complement one another in every quotient coset. -/
theorem bw_witness_gluing : BWGluingCondition (bwQuarterPoint + e8FirstVector) bwQuarterPoint := by
  refine ⟨squaredDepth_bwM_quarter_unit, squaredDepth_bwM_quarter, ?_⟩
  intro q
  have hqM := bwRepresentative_mem q
  have h := quarter_hole_or_unit_translate (quarterGrid_sub_bwM bwQuarterPoint_quarterGrid hqM)
    (integerSum_sub bwQuarterPoint_integerSum (bwM_integerSum hqM))
  have heq : bwQuarterPoint - bwRepresentative q + e8FirstVector =
      bwQuarterPoint + e8FirstVector - bwRepresentative q := by abel
  rcases h with h | h
  · right
    exact (squaredDepth_E8_eq_one_iff _).mpr h
  · left
    rw [heq] at h
    exact (squaredDepth_E8_eq_one_iff _).mpr h

/-- The gluing equality condition always gives a deepest point. -/
theorem squaredDepth_bwGamma_of_gluing {x y : Fin 8 → ℝ} (h : BWGluingCondition x y) :
    squaredDepth bwGammaSet (Fin.append x y) = 3 / 2 := by
  apply le_antisymm (squaredDepth_bwGamma_le _)
  apply (le_squaredDepth_bwGamma_iff x y _).mpr
  intro q
  have hx := squaredDepth_bwM_le_profile x q
  have hy := squaredDepth_bwM_le_profile y q
  rw [h.1] at hx
  rw [h.2.1] at hy
  rcases h.2.2 q with he | he <;> rw [he] <;> linarith

theorem squaredDepth_bwGamma_witness :
    squaredDepth bwGammaSet (Fin.append (bwQuarterPoint + e8FirstVector) bwQuarterPoint) = 3 / 2 :=
  squaredDepth_bwGamma_of_gluing bw_witness_gluing

/-- Equality in the radius estimate forces both marginal blocks to be M-deep. -/
theorem bwGamma_deep_marginals {x y : Fin 8 → ℝ}
    (h : squaredDepth bwGammaSet (Fin.append x y) = 3 / 2) :
    squaredDepth bwMSet x = 1 / 2 ∧ squaredDepth bwMSet y = 1 / 2 := by
  obtain ⟨q, hq, _⟩ := exists_min_bwDepthProfile x
  obtain ⟨r, hr, _⟩ := exists_min_bwDepthProfile y
  have hqsum := squaredDepth_bwGamma_le_profile x y q
  have hrsum := squaredDepth_bwGamma_le_profile x y r
  rw [h, hq] at hqsum
  rw [h, hr] at hrsum
  constructor
  · linarith [squaredDepth_bwM_le x, bwDepthProfile_le_one y q]
  · linarith [squaredDepth_bwM_le y, bwDepthProfile_le_one x r]

/-- Every deepest block is eligible; this is deduced rather than imposed. -/
theorem bwGamma_deep_eligible {x y : Fin 8 → ℝ}
    (h : squaredDepth bwGammaSet (Fin.append x y) = 3 / 2) : BWEligible x ∧ BWEligible y := by
  obtain ⟨hx, hy⟩ := bwGamma_deep_marginals h
  obtain ⟨q, hq, _⟩ := exists_min_bwDepthProfile x
  obtain ⟨r, hr, _⟩ := exists_min_bwDepthProfile y
  have hqsum := squaredDepth_bwGamma_le_profile x y q
  have hrsum := squaredDepth_bwGamma_le_profile x y r
  rw [h, hq, hx] at hqsum
  rw [h, hr, hy] at hrsum
  refine ⟨⟨hx, r, ?_⟩, ⟨hy, q, ?_⟩⟩
  · linarith [bwDepthProfile_le_one x r]
  · linarith [bwDepthProfile_le_one y q]

/-- Complete radius equality, for all real points, in exactly the gluing form. -/
theorem squaredDepth_bwGamma_eq_iff (x y : Fin 8 → ℝ) :
    squaredDepth bwGammaSet (Fin.append x y) = 3 / 2 ↔ BWGluingCondition x y := by
  constructor
  · intro h
    obtain ⟨hx, hy⟩ := bwGamma_deep_eligible h
    refine ⟨hx.1, hy.1, ?_⟩
    intro q
    have hs := squaredDepth_bwGamma_le_profile x y q
    rw [h] at hs
    rcases bwEligible_profile_two_depths hx q with hqx | hqx
    · rcases bwEligible_profile_two_depths hy q with hqy | hqy
      · rw [hqx, hqy] at hs
        norm_num at hs
      · exact Or.inr hqy
    · exact Or.inl hqx
  · exact squaredDepth_bwGamma_of_gluing

theorem isDeepHole_bwGamma_iff_depth (z : Fin 16 → ℝ) :
    IsDeepHole bwGammaSet z ↔ squaredDepth bwGammaSet z = 3 / 2 := by
  constructor
  · intro h
    have hbound := h (Fin.append (bwQuarterPoint + e8FirstVector) bwQuarterPoint)
    rw [squaredDepth_bwGamma_witness] at hbound
    exact le_antisymm (squaredDepth_bwGamma_le z) hbound
  · intro hz y
    rw [hz]
    exact squaredDepth_bwGamma_le y

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.squaredDepth_bwGamma_eq_iff
#print axioms PaperVerification.ColdSpots.squaredDepth_bwGamma_witness
end
end Source_BWHoles
-- END ORIGINAL PaperVerification.BWHoles


-- BEGIN ORIGINAL PaperVerification.BWTheorems
section Source_BWTheorems

-- original header: module
-- original header: public import PaperVerification.BWHoles
-- original header: public import PaperVerification.E8Theorems
-- original header: @[expose] public section
/-! # Universal cold spots of the diagonal Barnes–Wall lattice

All analytic inputs are the proved E8 theorem at α and α/2.  The actual finite
coset factorization and the complete geometric equality criterion give the result
for every real point and every positive parameter.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def bwK (α : ℝ) : ℝ := (gaussian α 0 * gaussian α (1 / 2)) ^ 4
def bwS (α : ℝ) : ℝ := bwK (α / 2)
def bwGammaMinimum (α : ℝ) : ℝ := 2 * bwK α * bwS α - 16 * bwK α ^ 2

theorem bwK_pos {α : ℝ} (hα : 0 < α) : 0 < bwK α :=
  pow_pos (mul_pos (gaussian_pos hα _) (gaussian_pos hα _)) _

theorem bwThetaProfile_lower {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) (q : BWQuotient) :
    bwK α ≤ bwThetaProfile α x q := by
  rw [bwThetaProfile, setGaussian_dPlus_eq (by decide : 0 < 8) hα]
  exact dPlusGaussian_eight_lower hα _

theorem bwThetaProfile_eq_iff {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) (q : BWQuotient) :
    bwThetaProfile α x q = bwK α ↔ bwDepthProfile x q = 1 := by
  rw [bwThetaProfile, bwK, setGaussian_dPlus_eq (by decide : 0 < 8) hα,
    dPlusGaussian_eight_eq_min_iff hα, bwDepthProfile, squaredDepth_E8_eq_one_iff]

theorem bwThetaProfile_sum_lower {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    bwS α ≤ ∑ q : BWQuotient, bwThetaProfile α x q := by
  rw [← setGaussian_bwM_eq_sum_profiles hα, setGaussian_bwM,
    setGaussian_dPlus_eq (by decide : 0 < 8) (by positivity : 0 < α / 2)]
  exact dPlusGaussian_eight_lower (by positivity) _

theorem bwThetaProfile_sum_eq_iff {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    (∑ q : BWQuotient, bwThetaProfile α x q) = bwS α ↔ squaredDepth bwMSet x = 1 / 2 := by
  rw [← setGaussian_bwM_eq_sum_profiles hα, setGaussian_bwM,
    setGaussian_dPlus_eq (by decide : 0 < 8) (by positivity : 0 < α / 2)]
  change dPlusGaussian (α / 2) (fun i => 2 * halfHadamard x i) = bwK (α / 2) ↔ _
  rw [bwK, dPlusGaussian_eight_eq_min_iff (by positivity : 0 < α / 2),
    ← squaredDepth_E8_eq_one_iff, squaredDepth_bwM]
  constructor <;> intro h <;> linarith

/-- The sharp global bound for the actual diagonal lattice. -/
theorem setGaussian_bwGamma_lower {α : ℝ} (hα : 0 < α) (z : Fin 16 → ℝ) :
    bwGammaMinimum α ≤ setGaussian bwGammaSet α z := by
  rw [← append_bw_blocks z, setGaussian_bwGamma_eq_sum_profiles hα]
  have h := PaperVerification.Lattice.diagonal_gluing_bound Finset.univ
    (bwThetaProfile α (bwLeft z)) (bwThetaProfile α (bwRight z)) (bwK α) (bwS α)
    (bwK_pos hα).le (fun q _ => bwThetaProfile_lower hα _ q)
    (fun q _ => bwThetaProfile_lower hα _ q) (bwThetaProfile_sum_lower hα _)
    (bwThetaProfile_sum_lower hα _)
  simpa only [Finset.card_univ, card_bwQuotient, Nat.cast_ofNat, bwGammaMinimum] using h

/-- Exact Gaussian equality is the complete geometric gluing condition. -/
theorem setGaussian_bwGamma_eq_min_iff {α : ℝ} (hα : 0 < α) (x y : Fin 8 → ℝ) :
    setGaussian bwGammaSet α (Fin.append x y) = bwGammaMinimum α ↔ BWGluingCondition x y := by
  rw [setGaussian_bwGamma_eq_sum_profiles hα]
  have h := PaperVerification.Lattice.diagonal_gluing_eq_iff Finset.univ
    (bwThetaProfile α x) (bwThetaProfile α y) (bwK α) (bwS α)
    (bwK_pos hα) (fun q _ => bwThetaProfile_lower hα _ q)
    (fun q _ => bwThetaProfile_lower hα _ q) (bwThetaProfile_sum_lower hα _)
    (bwThetaProfile_sum_lower hα _)
  simpa only [Finset.card_univ, card_bwQuotient, Nat.cast_ofNat, Finset.mem_univ,
    forall_const, bwGammaMinimum, BWGluingCondition, bwThetaProfile_sum_eq_iff hα,
    bwThetaProfile_eq_iff hα] using h

theorem setGaussian_bwGamma_witness {α : ℝ} (hα : 0 < α) :
    setGaussian bwGammaSet α (Fin.append (bwQuarterPoint + e8FirstVector) bwQuarterPoint) =
      bwGammaMinimum α :=
  (setGaussian_bwGamma_eq_min_iff hα _ _).mpr bw_witness_gluing

theorem isColdSpot_bwGamma_iff_value {α : ℝ} (hα : 0 < α) (z : Fin 16 → ℝ) :
    IsColdSpot bwGammaSet α z ↔ setGaussian bwGammaSet α z = bwGammaMinimum α := by
  constructor
  · intro h
    have hw := h (Fin.append (bwQuarterPoint + e8FirstVector) bwQuarterPoint)
    rw [setGaussian_bwGamma_witness hα] at hw
    exact le_antisymm hw (setGaussian_bwGamma_lower hα z)
  · intro hz y
    rw [hz]
    exact setGaussian_bwGamma_lower hα y

/-- Theorem 1.1 for Γ, with every parameter and ambient coordinate unrestricted. -/
theorem coldSpot_bwGamma_iff_deepHole {α : ℝ} (hα : 0 < α) (z : Fin 16 → ℝ) :
    IsColdSpot bwGammaSet α z ↔ IsDeepHole bwGammaSet z := by
  rw [isColdSpot_bwGamma_iff_value hα, isDeepHole_bwGamma_iff_depth,
    ← append_bw_blocks z, setGaussian_bwGamma_eq_min_iff hα, squaredDepth_bwGamma_eq_iff]

/-- The sharp value is attained and is a lower bound at every real point. -/
theorem bwGamma_gaussian_minimum {α : ℝ} (hα : 0 < α) :
    (∀ z : Fin 16 → ℝ, bwGammaMinimum α ≤ setGaussian bwGammaSet α z) ∧
      ∃ z, setGaussian bwGammaSet α z = bwGammaMinimum α :=
  ⟨setGaussian_bwGamma_lower hα,
    ⟨Fin.append (bwQuarterPoint + e8FirstVector) bwQuarterPoint, setGaussian_bwGamma_witness hα⟩⟩

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.coldSpot_bwGamma_iff_deepHole
#print axioms PaperVerification.ColdSpots.bwGamma_gaussian_minimum
end
end Source_BWTheorems
-- END ORIGINAL PaperVerification.BWTheorems


-- BEGIN ORIGINAL PaperVerification.EisensteinArithmetic
section Source_EisensteinArithmetic

-- original header: module
-- original header: public import Mathlib.Data.ZMod.Basic
-- original header: public import Mathlib.Analysis.Complex.Basic
-- original header: public import Mathlib.Analysis.SpecialFunctions.Sqrt
-- original header: public import Mathlib.Data.Fin.Tuple.Basic
-- original header: public import Mathlib.Algebra.BigOperators.Fin
-- original header: public import Mathlib.Tactic.Ring
-- original header: public import Mathlib.Tactic.NormNum
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.FinCases
-- original header: public import Mathlib.Tactic.LinearCombination
-- original header: public import Mathlib.Tactic.Positivity
-- original header: public import Lean.Elab.Tactic.Omega
-- original header: @[expose] public section
/-!
# Exact Eisenstein coordinates

`(u,v)` denotes the physical complex number `u+v*ω`, with
`ω=(-1+i*sqrt(3))/2`. The quadratic form is proved to be its actual squared
Euclidean norm. Integral coordinates therefore describe the literal triangular
lattice, rather than an abstract theta function with assumed identities.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

abbrev EisInt := ℤ × ℤ
abbrev TriPoint := ℝ × ℝ

@[simp] theorem zmodThree_three_eq_zero : (3 : ZMod 3) = 0 := by decide

@[simp] theorem zmodThree_val_one : (1 : ZMod 3).val = 1 := by decide

@[simp] theorem zmodThree_val_two : (2 : ZMod 3).val = 2 := by decide

def eisEmbed : EisInt →+ TriPoint where
  toFun z := ((z.1 : ℝ), (z.2 : ℝ))
  map_zero' := by ext <;> simp
  map_add' := by intro z w; ext <;> simp

lemma eisEmbed_injective : Function.Injective eisEmbed := by
  intro z w h
  apply Prod.ext
  · exact Int.cast_injective (congrArg Prod.fst h)
  · exact Int.cast_injective (congrArg Prod.snd h)

def eisOmega : EisInt →+ EisInt where
  toFun z := (-z.2, z.1 - z.2)
  map_zero' := by ext <;> simp
  map_add' := by intro z w; ext <;> simp <;> ring

def eisTheta : EisInt →+ EisInt where
  toFun z := (z.1 - 2 * z.2, 2 * z.1 - z.2)
  map_zero' := by ext <;> simp
  map_add' := by intro z w; ext <;> simp <;> ring

def eisResidue : EisInt →+ ZMod 3 where
  toFun z := ((z.1 + z.2 : ℤ) : ZMod 3)
  map_zero' := by simp
  map_add' := by intro z w; simp; ring

lemma eisOmega_cube (z : EisInt) : eisOmega (eisOmega (eisOmega z)) = z := by
  ext <;> dsimp [eisOmega] <;> ring

lemma eisOmega_sum (z : EisInt) : z + eisOmega z + eisOmega (eisOmega z) = 0 := by
  ext <;> dsimp [eisOmega] <;> ring

lemma eisTheta_sq (z : EisInt) : eisTheta (eisTheta z) = (-3 : ℤ) • z := by
  ext <;> dsimp [eisTheta] <;> ring

lemma eisTheta_injective : Function.Injective eisTheta := by
  intro z w h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp [eisTheta] at h₁ h₂
  apply Prod.ext <;> omega

@[simp] lemma eisResidue_omega (z : EisInt) : eisResidue (eisOmega z) = eisResidue z := by
  change ((-z.2 + (z.1 - z.2) : ℤ) : ZMod 3) = ((z.1 + z.2 : ℤ) : ZMod 3)
  push_cast
  have h3 : (3 : ZMod 3) = 0 := by decide
  linear_combination -((z.2 : ℤ) : ZMod 3) * h3

@[simp] lemma eisResidue_theta (z : EisInt) : eisResidue (eisTheta z) = 0 := by
  change ((z.1 - 2 * z.2 + (2 * z.1 - z.2) : ℤ) : ZMod 3) = 0
  rw [show z.1 - 2 * z.2 + (2 * z.1 - z.2) = 3 * (z.1 - z.2) by ring]
  simp

theorem eisTheta_range_iff (z : EisInt) : (∃ w, eisTheta w = z) ↔ eisResidue z = 0 := by
  constructor
  · rintro ⟨w, rfl⟩
    exact eisResidue_theta w
  · intro hz
    have hd : (3 : ℤ) ∣ z.1 + z.2 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (z.1 + z.2) 3).mp hz
    obtain ⟨k, hk⟩ := hd
    refine ⟨(z.2 - k, k - z.1), ?_⟩
    ext <;> dsimp [eisTheta] <;> omega

def eisThetaDiv (z : EisInt) (hz : eisResidue z = 0) : EisInt :=
  Classical.choose ((eisTheta_range_iff z).mpr hz)

lemma eisTheta_div (z : EisInt) (hz : eisResidue z = 0) :
    eisTheta (eisThetaDiv z hz) = z := Classical.choose_spec ((eisTheta_range_iff z).mpr hz)

def triOmega (z : TriPoint) : TriPoint := (-z.2, z.1 - z.2)

def triTheta (z : TriPoint) : TriPoint := (z.1 - 2 * z.2, 2 * z.1 - z.2)

def triThetaInv (z : TriPoint) : TriPoint := ((-z.1 + 2 * z.2) / 3, (-2 * z.1 + z.2) / 3)

def triC : TriPoint := (1 / 3, -(1 / 3))

def triQ (z : TriPoint) : ℝ := z.1 ^ 2 - z.1 * z.2 + z.2 ^ 2

def triComplex (z : TriPoint) : ℂ :=
  ((z.1 - z.2 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 * z.2 / 2 : ℝ) : ℂ) * Complex.I

def eisensteinOmega : ℂ := triComplex (0, 1)

theorem triComplex_coordinates (z : TriPoint) :
    triComplex z = (z.1 : ℂ) + (z.2 : ℂ) * eisensteinOmega := by
  apply Complex.ext <;> simp [triComplex, eisensteinOmega] <;> ring

theorem triQ_eq_norm_sq (z : TriPoint) : triQ z = ‖triComplex z‖ ^ 2 := by
  rw [Complex.sq_norm]
  simp only [triComplex, Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add]
  have h3 : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  unfold triQ
  nlinarith only [congrArg (fun r : ℝ ↦ r * z.2 ^ 2) h3]

theorem triQ_lower (z : TriPoint) : (z.1 ^ 2 + z.2 ^ 2) / 2 ≤ triQ z := by
  unfold triQ
  nlinarith [sq_nonneg (z.1 - z.2)]

theorem triQ_nonneg (z : TriPoint) : 0 ≤ triQ z :=
  (by positivity : (0 : ℝ) ≤ (z.1 ^ 2 + z.2 ^ 2) / 2).trans (triQ_lower z)

theorem triQ_omega (z : TriPoint) : triQ (triOmega z) = triQ z := by
  dsimp [triOmega, triQ]
  ring

theorem triQ_theta (z : TriPoint) : triQ (triTheta z) = 3 * triQ z := by
  dsimp [triTheta, triQ]
  ring

@[simp] theorem triTheta_inv (z : TriPoint) : triTheta (triThetaInv z) = z := by
  ext <;> dsimp [triTheta, triThetaInv] <;> ring

@[simp] theorem triThetaInv_theta (z : TriPoint) : triThetaInv (triTheta z) = z := by
  ext <;> dsimp [triTheta, triThetaInv] <;> ring

theorem triTheta_injective : Function.Injective triTheta :=
  Function.LeftInverse.injective triThetaInv_theta

@[simp] theorem triTheta_embed (z : EisInt) : triTheta (eisEmbed z) = eisEmbed (eisTheta z) := by
  ext <;> simp [triTheta, eisEmbed, eisTheta]

@[simp] theorem triOmega_embed (z : EisInt) : triOmega (eisEmbed z) = eisEmbed (eisOmega z) := by
  ext <;> simp [triOmega, eisEmbed, eisOmega]

@[simp] theorem triTheta_c : triTheta triC = eisEmbed (1, 1) := by
  ext <;> norm_num [triTheta, triC, eisEmbed]

theorem triC_three : (3 : ℝ) • triC = eisEmbed (1, -1) := by
  ext <;> norm_num [triC, eisEmbed]

theorem triQ_c : triQ triC = 1 / 3 := by norm_num [triQ, triC]

theorem triThetaInv_embed_integral (z : EisInt) (hz : eisResidue z = 0) :
    triThetaInv (eisEmbed z) = eisEmbed (eisThetaDiv z hz) := by
  apply triTheta_injective
  rw [triTheta_inv, triTheta_embed, eisTheta_div]

def triIntegerLattice : Set TriPoint := Set.range eisEmbed

theorem triIntegerLattice_complex (z : TriPoint) : z ∈ triIntegerLattice ↔
    ∃ a b : ℤ, z = ((a : ℝ), (b : ℝ)) := by
  constructor
  · rintro ⟨⟨a,b⟩, rfl⟩
    exact ⟨a,b,rfl⟩
  · rintro ⟨a,b,rfl⟩
    exact ⟨(a,b),rfl⟩

def triDFT (v : Fin 3 → TriPoint) : Fin 3 → TriPoint :=
  ![triThetaInv (v 0 + v 1 + v 2),
    triThetaInv (v 0 + triOmega (v 1) + triOmega (triOmega (v 2))),
    triThetaInv (v 0 + triOmega (triOmega (v 1)) + triOmega (v 2))]

def triDFTInv (v : Fin 3 → TriPoint) : Fin 3 → TriPoint :=
  ![-triThetaInv (v 0 + v 1 + v 2),
    -triThetaInv (v 0 + triOmega (triOmega (v 1)) + triOmega (v 2)),
    -triThetaInv (v 0 + triOmega (v 1) + triOmega (triOmega (v 2)))]

theorem triDFT_left_inv (v : Fin 3 → TriPoint) : triDFTInv (triDFT v) = v := by
  ext i <;> fin_cases i <;> simp [triDFT, triDFTInv, triThetaInv, triOmega] <;> ring

theorem triDFT_right_inv (v : Fin 3 → TriPoint) : triDFT (triDFTInv v) = v := by
  ext i <;> fin_cases i <;> simp [triDFT, triDFTInv, triThetaInv, triOmega] <;> ring

theorem triDFT_injective : Function.Injective triDFT :=
  Function.LeftInverse.injective triDFT_left_inv

/-- The true Euclidean isometry of the three-point Eisenstein transform. -/
theorem triDFT_preserves_norm (v : Fin 3 → TriPoint) :
    (∑ i, triQ (triDFT v i)) = ∑ i, triQ (v i) := by
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Finset.univ_unique,
    Finset.sum_singleton, Fin.succ_zero_eq_one]
  norm_num [triDFT, triQ, triThetaInv, triOmega]
  ring

theorem triDFT_sub (v w : Fin 3 → TriPoint) : triDFT (v - w) = triDFT v - triDFT w := by
  ext i <;> fin_cases i <;> simp [triDFT, triThetaInv, triOmega] <;> ring

theorem triDFT_centers (z : TriPoint) :
    triDFT ![z, z + triC, z - triC] = ![-triTheta z, triC, -triC] := by
  ext i <;> fin_cases i <;> simp [triDFT, triThetaInv, triTheta, triOmega, triC] <;> ring

end PaperVerification.ColdSpots
end
end Source_EisensteinArithmetic
-- END ORIGINAL PaperVerification.EisensteinArithmetic


-- BEGIN ORIGINAL PaperVerification.EisensteinDFT
section Source_EisensteinDFT

-- original header: module
-- original header: public import PaperVerification.EisensteinArithmetic
-- original header: public import Mathlib.Tactic.Abel
-- original header: @[expose] public section
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
end
end Source_EisensteinDFT
-- END ORIGINAL PaperVerification.EisensteinDFT


-- BEGIN ORIGINAL PaperVerification.TriangularGaussian
section Source_TriangularGaussian

-- original header: module
-- original header: public import PaperVerification.EisensteinArithmetic
-- original header: public import PaperVerification.ThetaRelations
-- original header: public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def triangularGaussian (α : ℝ) (z : TriPoint) : ℝ :=
  ∑' m : EisInt, Real.exp (-α * triQ (eisEmbed m - z))

def triangularSplitEquiv : EisInt ⊕ EisInt ≃ EisInt where
  toFun
    | .inl p => (p.1 + p.2, 2 * p.2)
    | .inr p => (p.1 + p.2 + 1, 2 * p.2 + 1)
  invFun p := if Even p.2 then .inl (p.1 - p.2 / 2, p.2 / 2)
    else .inr (p.1 - p.2 / 2 - 1, p.2 / 2)
  left_inv := by
    intro p
    cases p with
    | inl p =>
      have he : Even (2 * p.2) := even_two_mul _
      change (if Even (2 * p.2) then
        Sum.inl (p.1 + p.2 - (2 * p.2) / 2, (2 * p.2) / 2)
        else Sum.inr (p.1 + p.2 - (2 * p.2) / 2 - 1, (2 * p.2) / 2)) = Sum.inl p
      rw [if_pos he]
      apply congrArg Sum.inl
      apply Prod.ext <;> dsimp <;> omega
    | inr p =>
      have he : ¬Even (2 * p.2 + 1) := by rw [Int.even_iff]; omega
      change (if Even (2 * p.2 + 1) then
        Sum.inl (p.1 + p.2 + 1 - (2 * p.2 + 1) / 2, (2 * p.2 + 1) / 2)
        else Sum.inr (p.1 + p.2 + 1 - (2 * p.2 + 1) / 2 - 1,
          (2 * p.2 + 1) / 2)) = Sum.inr p
      rw [if_neg he]
      apply congrArg Sum.inr
      apply Prod.ext <;> dsimp <;> omega
  right_inv := by
    intro p
    dsimp only
    split_ifs with he
    · rw [Int.even_iff] at he
      apply Prod.ext <;> dsimp <;> omega
    · rw [Int.even_iff] at he
      apply Prod.ext <;> dsimp <;> omega

lemma triangular_even_term (α : ℝ) (z : TriPoint) (p : EisInt) :
    Real.exp (-α * triQ (eisEmbed (triangularSplitEquiv (.inl p)) - z)) =
      Real.exp (-α * ((p.1 : ℝ) - (z.1 - z.2 / 2)) ^ 2) *
      Real.exp (-(3 * α) * ((p.2 : ℝ) - z.2 / 2) ^ 2) := by
  rw [← Real.exp_add]
  dsimp [triangularSplitEquiv, eisEmbed, triQ]
  push_cast
  congr 1
  ring

lemma triangular_odd_term (α : ℝ) (z : TriPoint) (p : EisInt) :
    Real.exp (-α * triQ (eisEmbed (triangularSplitEquiv (.inr p)) - z)) =
      Real.exp (-α * ((p.1 : ℝ) - (z.1 - z.2 / 2 - 1 / 2)) ^ 2) *
      Real.exp (-(3 * α) * ((p.2 : ℝ) - (z.2 / 2 - 1 / 2)) ^ 2) := by
  rw [← Real.exp_add]
  dsimp [triangularSplitEquiv, eisEmbed, triQ]
  push_cast
  congr 1
  ring

theorem hasSum_triangularGaussian {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    HasSum (fun m : EisInt ↦ Real.exp (-α * triQ (eisEmbed m - z)))
      (gaussian α (z.1 - z.2 / 2) * gaussian (3 * α) (z.2 / 2) +
       gaussian α (z.1 - z.2 / 2 - 1 / 2) * gaussian (3 * α) (z.2 / 2 - 1 / 2)) := by
  have h3 : 0 < 3 * α := by positivity
  have he : HasSum
      (fun p : EisInt ↦ Real.exp (-α * triQ (eisEmbed (triangularSplitEquiv (.inl p)) - z)))
      (gaussian α (z.1 - z.2 / 2) * gaussian (3 * α) (z.2 / 2)) := by
    simpa only [triangular_even_term] using hasSum_gaussian_pair hα h3
      (z.1 - z.2 / 2) (z.2 / 2)
  have ho : HasSum
      (fun p : EisInt ↦ Real.exp (-α * triQ (eisEmbed (triangularSplitEquiv (.inr p)) - z)))
      (gaussian α (z.1 - z.2 / 2 - 1 / 2) * gaussian (3 * α) (z.2 / 2 - 1 / 2)) := by
    simpa only [triangular_odd_term] using hasSum_gaussian_pair hα h3
      (z.1 - z.2 / 2 - 1 / 2) (z.2 / 2 - 1 / 2)
  exact (triangularSplitEquiv.hasSum_iff
    (f := fun m : EisInt ↦ Real.exp (-α * triQ (eisEmbed m - z)))).mp (he.sum ho)

theorem summable_triangularGaussian {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    Summable (fun m : EisInt ↦ Real.exp (-α * triQ (eisEmbed m - z))) :=
  (hasSum_triangularGaussian hα z).summable

theorem triangularGaussian_eq_products {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    triangularGaussian α z =
      gaussian α (z.1 - z.2 / 2) * gaussian (3 * α) (z.2 / 2) +
      gaussian α (z.1 - z.2 / 2 - 1 / 2) * gaussian (3 * α) (z.2 / 2 - 1 / 2) :=
  (hasSum_triangularGaussian hα z).tsum_eq

theorem triangularGaussian_pos {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    0 < triangularGaussian α z := by
  rw [triangularGaussian_eq_products hα]
  exact add_pos (mul_pos (gaussian_pos hα _) (gaussian_pos (by positivity) _))
    (mul_pos (gaussian_pos hα _) (gaussian_pos (by positivity) _))

theorem continuous_triangularGaussian {α : ℝ} (hα : 0 < α) :
    Continuous (triangularGaussian α) := by
  have heq : triangularGaussian α = fun z : TriPoint ↦
      gaussian α (z.1 - z.2 / 2) * gaussian (3 * α) (z.2 / 2) +
      gaussian α (z.1 - z.2 / 2 - 1 / 2) * gaussian (3 * α) (z.2 / 2 - 1 / 2) :=
    funext (triangularGaussian_eq_products hα)
  rw [heq]
  have ha := continuous_gaussian hα
  have hb := continuous_gaussian (show 0 < 3 * α by positivity)
  exact ((ha.comp (continuous_fst.sub (continuous_snd.div_const 2))).mul
      (hb.comp (continuous_snd.div_const 2))).add
    ((ha.comp ((continuous_fst.sub (continuous_snd.div_const 2)).sub continuous_const)).mul
      (hb.comp ((continuous_snd.div_const 2).sub continuous_const)))

theorem triangularGaussian_periodic (α : ℝ) (z : TriPoint) (w : EisInt) :
    triangularGaussian α (z + eisEmbed w) = triangularGaussian α z := by
  unfold triangularGaussian
  rw [← (Equiv.addRight w).tsum_eq]
  apply tsum_congr
  intro m
  simp only [Equiv.coe_addRight, map_add]
  apply congrArg (fun v : TriPoint => Real.exp (-α * triQ v))
  abel

lemma triQ_neg (z : TriPoint) : triQ (-z) = triQ z := by
  dsimp [triQ]
  ring

theorem triangularGaussian_even (α : ℝ) (z : TriPoint) :
    triangularGaussian α (-z) = triangularGaussian α z := by
  unfold triangularGaussian
  rw [← (Equiv.neg EisInt).tsum_eq]
  apply tsum_congr
  intro m
  simp only [Equiv.neg_apply, map_neg]
  rw [show -eisEmbed m - -z = -(eisEmbed m - z) by abel, triQ_neg]

def triangularResidueGaussian (α : ℝ) (z : TriPoint) (r : ZMod 3) : ℝ :=
  ∑' m : {m : EisInt // eisResidue m = r}, Real.exp (-α * triQ (eisEmbed m.val - z))

def eisRotateC : EisInt ≃ EisInt where
  toFun z := eisOmega z - (0, 1)
  invFun z := eisOmega (eisOmega (z + (0, 1)))
  left_inv := by
    intro z
    change eisOmega (eisOmega ((eisOmega z - (0, 1)) + (0, 1))) = z
    rw [sub_add_cancel, eisOmega_cube]
  right_inv := by
    intro z
    change eisOmega (eisOmega (eisOmega (z + (0, 1)))) - (0, 1) = z
    rw [eisOmega_cube, add_sub_cancel_right]

lemma eisResidue_rotateC (z : EisInt) : eisResidue (eisRotateC z) = eisResidue z - 1 := by
  change eisResidue (eisOmega z - (0, 1)) = _
  rw [map_sub, eisResidue_omega]
  rfl

lemma eisRotateC_distance (z : EisInt) :
    triQ (eisEmbed (eisRotateC z) - triC) = triQ (eisEmbed z - triC) := by
  have h : eisEmbed (eisRotateC z) - triC = triOmega (eisEmbed z - triC) := by
    ext <;> simp [eisRotateC, eisEmbed, eisOmega, triC, triOmega] <;> ring
  rw [h, triQ_omega]

def eisRotateResidue (r : ZMod 3) :
    {m : EisInt // eisResidue m = r} ≃ {m : EisInt // eisResidue m = r - 1} where
  toFun m := ⟨eisRotateC m.val, by rw [eisResidue_rotateC, m.property]⟩
  invFun m := ⟨eisRotateC.symm m.val, by
    have h := eisResidue_rotateC (eisRotateC.symm m.val)
    rw [eisRotateC.apply_symm_apply, m.property] at h
    exact sub_left_inj.mp h.symm⟩
  left_inv := by intro m; apply Subtype.ext; exact eisRotateC.symm_apply_apply m.val
  right_inv := by intro m; apply Subtype.ext; exact eisRotateC.apply_symm_apply m.val

theorem triangularResidueGaussian_rotate (α : ℝ) (r : ZMod 3) :
    triangularResidueGaussian α triC (r - 1) = triangularResidueGaussian α triC r := by
  unfold triangularResidueGaussian
  rw [← (eisRotateResidue r).tsum_eq]
  apply tsum_congr
  intro m
  exact congrArg (fun t : ℝ ↦ Real.exp (-α * t)) (eisRotateC_distance m.val)

theorem triangularResidueGaussian_sum {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    (∑ r : ZMod 3, triangularResidueGaussian α z r) = triangularGaussian α z := by
  have h := (summable_triangularGaussian hα z).hasSum
  have hs := ((Equiv.sigmaFiberEquiv eisResidue).hasSum_iff
    (f := fun m : EisInt ↦ Real.exp (-α * triQ (eisEmbed m - z)))).mpr h
  have hout := hs.sigma (fun r ↦ ((summable_triangularGaussian hα z).subtype
    (fun m ↦ eisResidue m = r)).hasSum)
  simpa only [triangularResidueGaussian, triangularGaussian,
    Function.comp_def, tsum_fintype] using hout.tsum_eq

/-- Each theta-residue class contributes exactly one third at a triangular hole. -/
theorem triangularResidueGaussian_at_c {α : ℝ} (hα : 0 < α) (r : ZMod 3) :
    triangularResidueGaussian α triC r = triangularGaussian α triC / 3 := by
  have h0 := triangularResidueGaussian_rotate α 0
  have h1 := triangularResidueGaussian_rotate α 1
  rw [show (0 : ZMod 3) - 1 = 2 by decide] at h0
  rw [sub_self] at h1
  have hall : ∀ s : ZMod 3, triangularResidueGaussian α triC s =
      triangularResidueGaussian α triC 0 := by
    intro s
    fin_cases s
    · rfl
    · exact h1.symm
    · exact h0
  have hs := triangularResidueGaussian_sum hα triC
  simp only [hall, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_ofNat] at hs
  rw [hall]
  linarith

end PaperVerification.ColdSpots
end
end Source_TriangularGaussian
-- END ORIGINAL PaperVerification.TriangularGaussian


-- BEGIN ORIGINAL PaperVerification.EisensteinConvolution
section Source_EisensteinConvolution

-- original header: module
-- original header: public import PaperVerification.EisensteinDFT
-- original header: public import PaperVerification.TriangularGaussian
-- original header: public import PaperVerification.GaussianProduct
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def eisZeroSumEquiv :
    (Σ a : EisInt, Σ b : EisInt, {c : EisInt // eisResidue c = -eisResidue a - eisResidue b}) ≃
      TriZeroSum where
  toFun p := ⟨![p.1, p.2.1, p.2.2.val], by
    simp only [Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, map_add]
    rw [p.2.2.property]
    abel⟩
  invFun h := ⟨h.val 0, h.val 1, ⟨h.val 2, by
    have hh := h.property
    simp only [Fin.sum_univ_three,
      map_add] at hh
    linear_combination hh⟩⟩
  left_inv := by rintro ⟨a,b,c⟩; rfl
  right_inv := by
    intro h
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl

def eisZeroSumSwap : TriZeroSum ≃ TriZeroSum where
  toFun h := ⟨![h.val 0, h.val 2, h.val 1], by
    have hh := h.property
    simp only [Fin.sum_univ_three, map_add] at hh
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, map_add]
    linear_combination hh⟩
  invFun h := ⟨![h.val 0, h.val 2, h.val 1], by
    have hh := h.property
    simp only [Fin.sum_univ_three, map_add] at hh
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, map_add]
    linear_combination hh⟩
  left_inv := by intro h; apply Subtype.ext; funext i; fin_cases i <;> rfl
  right_inv := by intro h; apply Subtype.ext; funext i; fin_cases i <;> rfl

theorem eis_convolution_uniform_third (f g h : EisInt → ℝ)
    (hf : Summable f) (hg : Summable g) (hh : Summable h) (C : ℝ)
    (hc : ∀ r : ZMod 3, (∑' c : {c : EisInt // eisResidue c = r}, h c.val) = C) :
    (∑' v : TriZeroSum, f (v.val 0) * g (v.val 1) * h (v.val 2)) =
      (∑' a, f a) * (∑' b, g b) * C := by
  have hall : Summable (fun v : Fin 3 → EisInt ↦ f (v 0) * g (v 1) * h (v 2)) := by
    have ht := summable_fin_product 3 (![f,g,h]) (by
      intro i; fin_cases i <;> assumption)
    simpa [Fin.prod_univ_succ, mul_assoc] using ht
  have hz := hall.subtype (fun v ↦ eisResidue (∑ i, v i) = 0)
  have hs := eisZeroSumEquiv.summable_iff.mpr hz
  change Summable (fun p : (Σ a : EisInt, Σ b : EisInt,
    {c : EisInt // eisResidue c = -eisResidue a - eisResidue b}) ↦
    f p.1 * g p.2.1 * h p.2.2.val) at hs
  rw [← eisZeroSumEquiv.tsum_eq]
  change (∑' p : (Σ a : EisInt, Σ b : EisInt,
    {c : EisInt // eisResidue c = -eisResidue a - eisResidue b}),
    f p.1 * g p.2.1 * h p.2.2.val) = _
  rw [hs.tsum_sigma]
  calc
    (∑' a, ∑' b : (Σ b : EisInt, {c : EisInt //
        eisResidue c = -eisResidue a - eisResidue b}),
        f a * g b.1 * h b.2.val) =
        ∑' a, ∑' b, f a * g b * C := by
      apply tsum_congr
      intro a
      rw [(hs.sigma_factor a).tsum_sigma]
      apply tsum_congr
      intro b
      change (∑' c : {c : EisInt // eisResidue c = -eisResidue a - eisResidue b},
        (f a * g b) * h c.val) = f a * g b * C
      rw [tsum_mul_left, hc]
    _ = (∑' a, f a) * (∑' b, g b) * C := by
      calc
        (∑' a, ∑' b, f a * g b * C) =
            ∑' a, (f a * (∑' b, g b)) * C := by
          apply tsum_congr
          intro a
          rw [tsum_mul_right, tsum_mul_left]
        _ = _ := by rw [tsum_mul_right, tsum_mul_right]

theorem eis_convolution_uniform_second (f g h : EisInt → ℝ)
    (hf : Summable f) (hg : Summable g) (hh : Summable h) (C : ℝ)
    (hc : ∀ r : ZMod 3, (∑' c : {c : EisInt // eisResidue c = r}, g c.val) = C) :
    (∑' v : TriZeroSum, f (v.val 0) * g (v.val 1) * h (v.val 2)) =
      (∑' a, f a) * (∑' b, h b) * C := by
  rw [← eisZeroSumSwap.tsum_eq]
  have he : (fun v : TriZeroSum ↦
      f ((eisZeroSumSwap v).val 0) * g ((eisZeroSumSwap v).val 1) *
        h ((eisZeroSumSwap v).val 2)) =
      fun v : TriZeroSum ↦ f (v.val 0) * h (v.val 1) * g (v.val 2) := by
    funext v
    dsimp [eisZeroSumSwap]
    ring
  rw [he]
  exact eis_convolution_uniform_third f h g hf hh hg C hc

def eisResidueNeg (r : ZMod 3) :
    {m : EisInt // eisResidue m = r} ≃ {m : EisInt // eisResidue m = -r} where
  toFun m := ⟨-m.val, by rw [map_neg, m.property]⟩
  invFun m := ⟨-m.val, by rw [map_neg, m.property, neg_neg]⟩
  left_inv := by intro m; apply Subtype.ext; exact neg_neg _
  right_inv := by intro m; apply Subtype.ext; exact neg_neg _

theorem triangularResidueGaussian_neg (α : ℝ) (z : TriPoint) (r : ZMod 3) :
    triangularResidueGaussian α (-z) (-r) = triangularResidueGaussian α z r := by
  unfold triangularResidueGaussian
  rw [← (eisResidueNeg r).tsum_eq]
  apply tsum_congr
  intro m
  change Real.exp (-α * triQ (eisEmbed (-m.val) - -z)) = _
  rw [map_neg, show -eisEmbed m.val - -z = -(eisEmbed m.val - z) by abel, triQ_neg]

def eisResidueAdd (w : EisInt) (r : ZMod 3) :
    {m : EisInt // eisResidue m = r} ≃
      {m : EisInt // eisResidue m = r + eisResidue w} where
  toFun m := ⟨m.val + w, by rw [map_add, m.property]⟩
  invFun m := ⟨m.val - w, by rw [map_sub, m.property, add_sub_cancel_right]⟩
  left_inv := by intro m; apply Subtype.ext; exact add_sub_cancel_right _ _
  right_inv := by intro m; apply Subtype.ext; exact sub_add_cancel _ _

theorem triangularResidueGaussian_add (α : ℝ) (z : TriPoint) (w : EisInt) (r : ZMod 3) :
    triangularResidueGaussian α (z + eisEmbed w) (r + eisResidue w) =
      triangularResidueGaussian α z r := by
  unfold triangularResidueGaussian
  rw [← (eisResidueAdd w r).tsum_eq]
  apply tsum_congr
  intro m
  change Real.exp (-α * triQ (eisEmbed (m.val + w) - (z + eisEmbed w))) = _
  rw [map_add, add_sub_add_right_eq_sub]

lemma triangularResidueGaussian_at_neg_c {α : ℝ} (hα : 0 < α) (r : ZMod 3) :
    triangularResidueGaussian α (-triC) r = triangularGaussian α triC / 3 := by
  rw [← neg_neg r, triangularResidueGaussian_neg]
  exact triangularResidueGaussian_at_c hα (-r)

lemma triangularResidueGaussian_at_neg_two_c {α : ℝ} (hα : 0 < α) (r : ZMod 3) :
    triangularResidueGaussian α (-(2 : ℝ) • triC) r = triangularGaussian α triC / 3 := by
  have hz : -(2 : ℝ) • triC = triC + eisEmbed (-1,1) := by
    ext <;> norm_num [triC, eisEmbed]
  have hr : eisResidue (-1,1) = 0 := by norm_num [eisResidue]
  rw [hz, ← add_zero r, ← hr, triangularResidueGaussian_add]
  exact triangularResidueGaussian_at_c hα r

end PaperVerification.ColdSpots
end
end Source_EisensteinConvolution
-- END ORIGINAL PaperVerification.EisensteinConvolution


-- BEGIN ORIGINAL PaperVerification.TriangularCubic
section Source_TriangularCubic

-- original header: module
-- original header: public import PaperVerification.EisensteinConvolution
-- original header: public import Mathlib.Tactic.Module
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def triangularProduct (α : ℝ) (z : TriPoint) : ℝ :=
  triangularGaussian α z * triangularGaussian α (z + triC) *
    triangularGaussian α (z - triC)

def triangularConstrained (α : ℝ) (z w u : TriPoint) : ℝ :=
  ∑' h : TriZeroSum,
    Real.exp (-α * triQ (eisEmbed (h.val 0) - z)) *
      Real.exp (-α * triQ (eisEmbed (h.val 1) - w)) *
      Real.exp (-α * triQ (eisEmbed (h.val 2) - u))

lemma triangularConstrained_third {α : ℝ} (hα : 0 < α) (z w u : TriPoint)
    (C : ℝ) (hu : ∀ r, triangularResidueGaussian α u r = C) :
    triangularConstrained α z w u = triangularGaussian α z * triangularGaussian α w * C :=
  eis_convolution_uniform_third _ _ _ (summable_triangularGaussian hα z)
    (summable_triangularGaussian hα w) (summable_triangularGaussian hα u) C hu

lemma triangularConstrained_second {α : ℝ} (hα : 0 < α) (z w u : TriPoint)
    (C : ℝ) (hw : ∀ r, triangularResidueGaussian α w r = C) :
    triangularConstrained α z w u = triangularGaussian α z * triangularGaussian α u * C :=
  eis_convolution_uniform_second _ _ _ (summable_triangularGaussian hα z)
    (summable_triangularGaussian hα w) (summable_triangularGaussian hα u) C hw

set_option maxHeartbeats 0 in
lemma triangularProduct_glue {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    triangularProduct α z = ∑ r : ZMod 3,
      triangularConstrained α (-triTheta z - (r.val : ℝ) • triC)
        (triC - (r.val : ℝ) • triC) (-triC - (r.val : ℝ) • triC) := by
  let f : (Fin 3 → EisInt) → ℝ := fun v ↦
    ∏ i, Real.exp (-α * triQ (eisEmbed (v i) - (![z,z+triC,z-triC] : Fin 3 → TriPoint) i))
  let g : TriGlueIndex → ℝ := fun p ↦
    ∏ i, Real.exp (-α * triQ (triGluePoint p i -
      (![-triTheta z,triC,-triC] : Fin 3 → TriPoint) i))
  have hf : Summable f := by
    dsimp only [f]
    exact summable_fin_product 3
      (fun i m ↦ Real.exp (-α * triQ
        (eisEmbed m - (![z,z+triC,z-triC] : Fin 3 → TriPoint) i)))
      (fun i ↦ summable_triangularGaussian hα _)
  have he (v : Fin 3 → EisInt) : f v = g (triDFTIntegerEquiv v) := by
    dsimp [f,g]
    rw [← Real.exp_sum, ← Real.exp_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      triDFT_lattice_distance, triDFTIntegerEquiv_apply]
  have hg : Summable g := triDFTIntegerEquiv.summable_iff.mp (hf.congr he)
  have hP : triangularProduct α z = ∑' v, f v := by
    dsimp only [f]
    rw [tsum_fin_product 3
      (fun i (m : EisInt) ↦ Real.exp (-α * triQ
        (eisEmbed m - (![z,z+triC,z-triC] : Fin 3 → TriPoint) i)))
      (fun i ↦ summable_triangularGaussian hα _)]
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, triangularProduct, triangularGaussian]
  rw [hP]
  calc
    (∑' v, f v) = ∑' p, g p := by
      simp_rw [he]
      exact triDFTIntegerEquiv.tsum_eq _
    _ = ∑ r : ZMod 3, ∑' h : TriZeroSum, g (r,h) := by
      rw [hg.tsum_prod, tsum_fintype]
    _ = ∑ r : ZMod 3,
        triangularConstrained α (-triTheta z - (r.val : ℝ) • triC)
          (triC - (r.val : ℝ) • triC) (-triC - (r.val : ℝ) • triC) := by
      apply Finset.sum_congr rfl
      intro r hr
      apply tsum_congr
      intro h
      dsimp [g, triangularConstrained]
      simp only [Fin.prod_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_one,
        triGluePoint]
      have hshift (a b d : TriPoint) : a + d - b = a - (b - d) := by abel
      simp only [hshift, mul_assoc]

lemma triangularGaussian_neg_three_c (α : ℝ) :
    triangularGaussian α (-(3 : ℝ) • triC) = triangularGaussian α 0 := by
  have he : -(3 : ℝ) • triC = (0 : TriPoint) + eisEmbed (-1,1) := by
    ext <;> norm_num [triC,eisEmbed]
  rw [he, triangularGaussian_periodic]

lemma triangularGaussian_two_c (α : ℝ) (z : TriPoint) :
    triangularGaussian α (z + (2 : ℝ) • triC) = triangularGaussian α (z - triC) := by
  have he : z + (2 : ℝ) • triC = (z - triC) + eisEmbed (1,-1) := by
    ext <;> dsimp [triC,eisEmbed] <;> ring
  rw [he, triangularGaussian_periodic]

/-- Proposition 8.1, equation (30), proved directly from the physical lattice
by an exact three-coset isometry and absolutely convergent residue sums. -/
theorem triangular_cubic_identity {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    triangularProduct α z = triangularGaussian α triC / 3 *
      (triangularGaussian α 0 *
          (triangularGaussian α (triTheta z + triC) +
            triangularGaussian α (triTheta z - triC)) +
        triangularGaussian α triC * triangularGaussian α (triTheta z)) := by
  rw [triangularProduct_glue hα]
  have hs : (Finset.univ : Finset (ZMod 3)) = {0,1,2} := by decide
  rw [hs]
  rw [Finset.sum_insert (show (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3)) by decide),
    Finset.sum_insert (show (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3)) by decide),
    Finset.sum_singleton]
  simp only [ZMod.val_zero, zmodThree_val_one, zmodThree_val_two, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, zero_smul, one_smul, sub_zero, sub_self]
  have h0 := triangularConstrained_third hα (-triTheta z) triC (-triC)
    (triangularGaussian α triC / 3) (triangularResidueGaussian_at_neg_c hα)
  have h1 := triangularConstrained_third hα (-triTheta z - triC) 0 (-(2 : ℝ) • triC)
    (triangularGaussian α triC / 3) (triangularResidueGaussian_at_neg_two_c hα)
  have h2 := triangularConstrained_second hα (-triTheta z - (2 : ℝ) • triC)
    (-triC) (-(3 : ℝ) • triC) (triangularGaussian α triC / 3)
    (triangularResidueGaussian_at_neg_c hα)
  have e1 : -triC - triC = -(2 : ℝ) • triC := by module
  have e2 : triC - (2 : ℝ) • triC = -triC := by module
  have e3 : -triC - (2 : ℝ) • triC = -(3 : ℝ) • triC := by module
  rw [e1,e2,e3,h0,h1,h2,triangularGaussian_even,triangularGaussian_neg_three_c]
  rw [show -triTheta z - triC = -(triTheta z + triC) by abel,
    show -triTheta z - (2 : ℝ) • triC = -(triTheta z + (2 : ℝ) • triC) by module,
    triangularGaussian_even,triangularGaussian_even,triangularGaussian_two_c]
  ring

end PaperVerification.ColdSpots
end
end Source_TriangularCubic
-- END ORIGINAL PaperVerification.TriangularCubic


-- BEGIN ORIGINAL PaperVerification.TriangularPhases
section Source_TriangularPhases

-- original header: module
-- original header: public import PaperVerification.TriangularCubic
-- original header: public import Mathlib.Algebra.Order.Floor.Ring
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

def TriPhase (z : TriPoint) : Prop :=
  ∃ r : ZMod 3, ∃ m : EisInt, z = eisEmbed m + (r.val : ℝ) • triC

theorem triPhase_iff_theta_integral (z : TriPoint) :
    TriPhase z ↔ triTheta z ∈ triIntegerLattice := by
  constructor
  · rintro ⟨r,m,rfl⟩
    refine ⟨eisTheta m + ((r.val : ℤ),(r.val : ℤ)), ?_⟩
    rw [map_add, triTheta_add, triTheta_embed, triTheta_smul, triTheta_c]
    congr 1
    ext <;> simp [eisEmbed]
  · rintro ⟨m,hm⟩
    let r : ZMod 3 := -eisResidue m
    let d : EisInt := ((r.val : ℤ),(r.val : ℤ))
    have hd : eisResidue d = 2*r := by simp [d,eisResidue,two_mul]
    have hz : eisResidue (m-d) = 0 := by
      rw [map_sub,hd]
      dsimp [r]
      have h3 : (3 : ZMod 3) = 0 := by decide
      linear_combination eisResidue m * h3
    refine ⟨r,eisThetaDiv (m-d) hz, ?_⟩
    apply triTheta_injective
    rw [← hm,triTheta_add,triTheta_embed,triTheta_smul,triTheta_c,eisTheta_div,map_sub]
    have he : (r.val : ℝ) • eisEmbed (1,1) = eisEmbed d := by ext <;> simp [d,eisEmbed]
    rw [he,sub_add_cancel]

theorem triPhase_iff_integer_multiple (z : TriPoint) :
    TriPhase z ↔ ∃ m : EisInt, ∃ k : ℤ, z = eisEmbed m + (k : ℝ) • triC := by
  constructor
  · rintro ⟨r,m,h⟩
    exact ⟨m,(r.val : ℤ),by simpa using h⟩
  · rintro ⟨m,k,rfl⟩
    rw [triPhase_iff_theta_integral]
    refine ⟨eisTheta m + (k,k), ?_⟩
    rw [map_add,triTheta_add,triTheta_embed,triTheta_smul,triTheta_c]
    congr 1
    ext <;> simp [eisEmbed]

theorem triangularProduct_periodic (α : ℝ) (z : TriPoint) (m : EisInt) :
    triangularProduct α (z + eisEmbed m) = triangularProduct α z := by
  unfold triangularProduct
  rw [show z + eisEmbed m + triC = (z+triC)+eisEmbed m by abel,
    show z + eisEmbed m - triC = (z-triC)+eisEmbed m by abel]
  simp only [triangularGaussian_periodic]

theorem triangularProduct_c_periodic (α : ℝ) (z : TriPoint) :
    triangularProduct α (z+triC) = triangularProduct α z := by
  unfold triangularProduct
  rw [show z+triC+triC = z+(2:ℝ)•triC by module,
    triangularGaussian_two_c,add_sub_cancel_right]
  ring

theorem triangularProduct_zero (α : ℝ) :
    triangularProduct α 0 = triangularGaussian α 0 * triangularGaussian α triC ^ 2 := by
  simp only [triangularProduct,zero_add,zero_sub,triangularGaussian_even]
  ring

theorem triangularProduct_phase (α : ℝ) {z : TriPoint} (hz : TriPhase z) :
    triangularProduct α z = triangularGaussian α 0 * triangularGaussian α triC ^ 2 := by
  obtain ⟨r,m,rfl⟩ := hz
  rw [add_comm,triangularProduct_periodic]
  rcases (show ∀ r : ZMod 3, r = 0 ∨ r = 1 ∨ r = 2 by decide) r with
    rfl | rfl | rfl
  · change triangularProduct α (((0 : ZMod 3).val : ℝ) • triC) = _
    rw [ZMod.val_zero]
    simpa only [Nat.cast_zero, zero_smul] using triangularProduct_zero α
  · change triangularProduct α (((1 : ZMod 3).val : ℝ) • triC) = _
    rw [zmodThree_val_one]
    have h := (triangularProduct_c_periodic α 0).trans (triangularProduct_zero α)
    simpa only [Nat.cast_one, one_smul, zero_add] using h
  · change triangularProduct α (((2 : ZMod 3).val : ℝ) • triC) = _
    rw [zmodThree_val_two]
    have h1 : triangularProduct α triC =
        triangularGaussian α 0 * triangularGaussian α triC ^ 2 := by
      simpa only [zero_add] using
        (triangularProduct_c_periodic α 0).trans (triangularProduct_zero α)
    have he : (2:ℝ)•triC = triC+triC := by module
    simpa only [Nat.cast_ofNat, he] using (triangularProduct_c_periodic α triC).trans h1

def triFraction (z : TriPoint) : TriPoint := (Int.fract z.1,Int.fract z.2)

def triFloor (z : TriPoint) : EisInt := (⌊z.1⌋,⌊z.2⌋)

theorem triFraction_add_floor (z : TriPoint) : triFraction z + eisEmbed (triFloor z) = z := by
  apply Prod.ext
  · change Int.fract z.1 + (⌊z.1⌋ : ℝ) = z.1
    exact Int.fract_add_floor z.1
  · change Int.fract z.2 + (⌊z.2⌋ : ℝ) = z.2
    exact Int.fract_add_floor z.2

theorem triFraction_mem (z : TriPoint) :
    triFraction z ∈ (Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc (0:ℝ) 1) :=
  ⟨⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩,
    ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩⟩

end PaperVerification.ColdSpots
end
end Source_TriangularPhases
-- END ORIGINAL PaperVerification.TriangularPhases


-- BEGIN ORIGINAL PaperVerification.TriangularGeometry
section Source_TriangularGeometry

-- original header: module
-- original header: public import PaperVerification.TriangularPhases
-- original header: public import Mathlib.Order.ConditionallyCompleteLattice.Basic
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

def triangularDepth (z : TriPoint) : ℝ := sInf (Set.range fun m : EisInt ↦ triQ (eisEmbed m-z))

lemma triangularDepth_bdd (z : TriPoint) :
    BddBelow (Set.range fun m : EisInt ↦ triQ (eisEmbed m-z)) :=
  ⟨0,by rintro t ⟨m,rfl⟩; exact triQ_nonneg _⟩

lemma triangularDepth_nonneg (z : TriPoint) : 0 ≤ triangularDepth z := by
  apply le_csInf (Set.range_nonempty _)
  rintro t ⟨m,rfl⟩
  exact triQ_nonneg _

lemma triangularDepth_le (z : TriPoint) (m : EisInt) :
    triangularDepth z ≤ triQ (eisEmbed m-z) :=
  csInf_le (triangularDepth_bdd z) (Set.mem_range_self m)

theorem triangularDepth_periodic (z : TriPoint) (w : EisInt) :
    triangularDepth (z+eisEmbed w) = triangularDepth z := by
  unfold triangularDepth
  congr 1
  ext t
  constructor
  · rintro ⟨m,rfl⟩
    refine ⟨m-w,?_⟩
    change triQ (eisEmbed (m-w)-z) = triQ (eisEmbed m-(z+eisEmbed w))
    rw [map_sub]
    congr 1
    abel
  · rintro ⟨m,rfl⟩
    refine ⟨m+w,?_⟩
    change triQ (eisEmbed (m+w)-(z+eisEmbed w)) = triQ (eisEmbed m-z)
    rw [map_add,add_sub_add_right_eq_sub]

theorem triangularDepth_even (z : TriPoint) : triangularDepth (-z) = triangularDepth z := by
  unfold triangularDepth
  congr 1
  ext t
  constructor <;> rintro ⟨m,rfl⟩ <;> refine ⟨-m,?_⟩
  · change triQ (eisEmbed (-m)-z) = triQ (eisEmbed m- -z)
    rw [map_neg,show -eisEmbed m-z = -(eisEmbed m- -z) by abel,triQ_neg]
  · change triQ (eisEmbed (-m)- -z) = triQ (eisEmbed m-z)
    rw [map_neg,show -eisEmbed m- -z = -(eisEmbed m-z) by abel,triQ_neg]

theorem triangularDepth_zero : triangularDepth 0 = 0 := by
  apply le_antisymm
  · simpa [eisEmbed,triQ] using triangularDepth_le 0 (0,0)
  · exact triangularDepth_nonneg _

lemma triQ_at_c_integer (m : EisInt) :
    triQ (eisEmbed m-triC) =
      ((m.1^2-m.1*m.2+m.2^2-m.1+m.2 : ℤ) : ℝ) + 1/3 := by
  dsimp [triQ,eisEmbed,triC]
  push_cast
  ring

theorem triangularDepth_c : triangularDepth triC = 1/3 := by
  apply le_antisymm
  · have h := triangularDepth_le triC (0,0)
    norm_num [eisEmbed,triQ,triC] at h ⊢
    exact h
  · apply le_csInf (Set.range_nonempty _)
    rintro t ⟨m,rfl⟩
    change 1/3 ≤ triQ (eisEmbed m-triC)
    rw [triQ_at_c_integer]
    let k : ℤ := m.1^2-m.1*m.2+m.2^2-m.1+m.2
    have hn := triQ_nonneg (eisEmbed m-triC)
    rw [triQ_at_c_integer] at hn
    have hk : 0 ≤ k := by
      by_contra hh
      have hi : k ≤ -1 := by omega
      have hr : (k : ℝ) ≤ -1 := by exact_mod_cast hi
      dsimp [k] at hr
      linarith
    have hr : (0:ℝ) ≤ k := by exact_mod_cast hk
    dsimp [k] at hr
    linarith

private lemma triangle_depth_first (u v d : ℝ) (hv : 0 ≤ v) (hvu : v ≤ u) (hu : u ≤ 1)
    (h0 : d ≤ triQ ((0,0)-(u,v))) (h1 : d ≤ triQ ((1,0)-(u,v)))
    (h2 : d ≤ triQ ((1,1)-(u,v))) :
    d ≤ 1/3-triQ ((u,v)-((2/3:ℝ),1/3)) := by
  have hA := mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr h0)
  have hB := mul_nonneg (sub_nonneg.mpr hvu) (sub_nonneg.mpr h1)
  have hC := mul_nonneg hv (sub_nonneg.mpr h2)
  have he : (1-u)*(triQ ((0,0)-(u,v))-d)+(u-v)*(triQ ((1,0)-(u,v))-d)+
      v*(triQ ((1,1)-(u,v))-d) = 1/3-triQ ((u,v)-((2/3:ℝ),1/3))-d := by
    dsimp [triQ]
    ring
  linarith

private lemma triangle_depth_second (u v d : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1)
    (h0 : d ≤ triQ ((0,0)-(u,v))) (h1 : d ≤ triQ ((0,1)-(u,v)))
    (h2 : d ≤ triQ ((1,1)-(u,v))) :
    d ≤ 1/3-triQ ((u,v)-((1/3:ℝ),2/3)) := by
  have hA := mul_nonneg (sub_nonneg.mpr hv) (sub_nonneg.mpr h0)
  have hB := mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr h1)
  have hC := mul_nonneg hu (sub_nonneg.mpr h2)
  have he : (1-v)*(triQ ((0,0)-(u,v))-d)+(v-u)*(triQ ((0,1)-(u,v))-d)+
      u*(triQ ((1,1)-(u,v))-d) = 1/3-triQ ((u,v)-((1/3:ℝ),2/3))-d := by
    dsimp [triQ]
    ring
  linarith

theorem triangularDepth_fundamental (z : TriPoint)
    (hz : z ∈ (Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc (0:ℝ) 1)) :
    triangularDepth z ≤ 1/3 ∧
      (triangularDepth z = 1/3 → z=((2/3:ℝ),1/3) ∨ z=((1/3:ℝ),2/3)) := by
  have h0 : triangularDepth z ≤ triQ ((0,0)-(z.1,z.2)) := by
    simpa [eisEmbed] using triangularDepth_le z (0,0)
  have h11 : triangularDepth z ≤ triQ ((1,1)-(z.1,z.2)) := by
    simpa [eisEmbed] using triangularDepth_le z (1,1)
  rcases le_total z.2 z.1 with h | h
  · have h10 : triangularDepth z ≤ triQ ((1,0)-(z.1,z.2)) := by
      simpa [eisEmbed] using triangularDepth_le z (1,0)
    have hd := triangle_depth_first z.1 z.2 (triangularDepth z) hz.2.1 h hz.1.2 h0 h10 h11
    have hq := triQ_nonneg (z-((2/3:ℝ),1/3))
    refine ⟨by linarith,?_⟩
    intro he
    left
    have hl := triQ_lower (z-((2/3:ℝ),1/3))
    have hzq : triQ (z-((2/3:ℝ),1/3))=0 := by linarith
    rw [hzq] at hl
    apply Prod.ext <;> dsimp at hl ⊢ <;>
      nlinarith [sq_nonneg (z.1-2/3),sq_nonneg (z.2-1/3)]
  · have h01 : triangularDepth z ≤ triQ ((0,1)-(z.1,z.2)) := by
      simpa [eisEmbed] using triangularDepth_le z (0,1)
    have hd := triangle_depth_second z.1 z.2 (triangularDepth z) hz.1.1 h hz.2.2 h0 h01 h11
    have hq := triQ_nonneg (z-((1/3:ℝ),2/3))
    refine ⟨by linarith,?_⟩
    intro he
    right
    have hl := triQ_lower (z-((1/3:ℝ),2/3))
    have hzq : triQ (z-((1/3:ℝ),2/3))=0 := by linarith
    rw [hzq] at hl
    apply Prod.ext <;> dsimp at hl ⊢ <;>
      nlinarith [sq_nonneg (z.1-1/3),sq_nonneg (z.2-2/3)]

theorem triangularDepth_le_third (z : TriPoint) : triangularDepth z ≤ 1/3 := by
  rw [← triFraction_add_floor z,triangularDepth_periodic]
  exact (triangularDepth_fundamental _ (triFraction_mem z)).1

def TriHole (z : TriPoint) : Prop :=
  (∃ m : EisInt, z=eisEmbed m+triC) ∨ (∃ m : EisInt, z=eisEmbed m-triC)

theorem triangularDepth_eq_third_iff (z : TriPoint) : triangularDepth z=1/3 ↔ TriHole z := by
  constructor
  · intro hz
    have hf : triangularDepth (triFraction z)=1/3 := by
      rw [← triangularDepth_periodic _ (triFloor z),triFraction_add_floor]
      exact hz
    rcases (triangularDepth_fundamental _ (triFraction_mem z)).2 hf with h | h
    · right
      refine ⟨triFloor z+(1,0),?_⟩
      conv_lhs => rw [← triFraction_add_floor z,h]
      rw [map_add]
      ext <;> dsimp [eisEmbed,triC] <;> ring
    · left
      refine ⟨triFloor z+(0,1),?_⟩
      conv_lhs => rw [← triFraction_add_floor z,h]
      rw [map_add]
      ext <;> dsimp [eisEmbed,triC] <;> ring
  · rintro (⟨m,rfl⟩|⟨m,rfl⟩)
    · rw [add_comm,triangularDepth_periodic,triangularDepth_c]
    · rw [sub_eq_add_neg,add_comm,triangularDepth_periodic,triangularDepth_even,triangularDepth_c]

theorem triHole_both_iff (z : TriPoint) :
    TriHole (z+triC) ∧ TriHole (z-triC) ↔ z ∈ triIntegerLattice := by
  constructor
  · rintro ⟨h1,h2⟩
    rcases h1 with ⟨m,hm⟩|⟨m,hm⟩
    · exact ⟨m,(add_right_cancel hm).symm⟩
    rcases h2 with ⟨n,hn⟩|⟨n,hn⟩
    · have h := congrArg Prod.fst hm
      have h' := congrArg Prod.fst hn
      dsimp [eisEmbed,triC] at h h'
      have hh : (3:ℤ)*(m.1-n.1)=4 := by
        apply Int.cast_injective (α:=ℝ)
        push_cast
        linarith
      omega
    · exact ⟨n,(sub_left_inj.mp hn).symm⟩
  · rintro ⟨m,rfl⟩
    exact ⟨Or.inl ⟨m,rfl⟩,Or.inr ⟨m,rfl⟩⟩

/-- Every residue class has a nearest representative at a triangular hole. -/
theorem exists_nearest_c_residue (r : ZMod 3) :
    ∃ m : EisInt, eisResidue m=r ∧ triQ (eisEmbed m-triC)=1/3 := by
  fin_cases r
  · refine ⟨(0,0),?_,by norm_num [eisEmbed,triQ,triC]⟩
    change eisResidue (0,0) = (0 : ZMod 3)
    norm_num [eisResidue] <;> decide
  · refine ⟨(1,0),?_,by norm_num [eisEmbed,triQ,triC]⟩
    change eisResidue (1,0) = (1 : ZMod 3)
    norm_num [eisResidue] <;> decide
  · refine ⟨(0,-1),?_,by norm_num [eisEmbed,triQ,triC]⟩
    change eisResidue (0,-1) = (2 : ZMod 3)
    norm_num [eisResidue] <;> decide

end PaperVerification.ColdSpots
end
end Source_TriangularGeometry
-- END ORIGINAL PaperVerification.TriangularGeometry


-- BEGIN ORIGINAL PaperVerification.TriangularDepthSum
section Source_TriangularDepthSum

-- original header: module
-- original header: public import PaperVerification.TriangularGeometry
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def triangularDepthSum (z : TriPoint) : ℝ :=
  triangularDepth z+triangularDepth (z+triC)+triangularDepth (z-triC)

lemma triangularDepthSum_le_integer (z : TriPoint) (v : Fin 3 → EisInt) :
    triangularDepthSum z ≤
      ∑ i, triQ (eisEmbed (v i)-(![z,z+triC,z-triC] : Fin 3 → TriPoint) i) := by
  have h0 := triangularDepth_le z (v 0)
  have h1 := triangularDepth_le (z+triC) (v 1)
  have h2 := triangularDepth_le (z-triC) (v 2)
  simp only [Fin.sum_univ_three,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  unfold triangularDepthSum
  linarith

lemma triangularDepthSum_le_glue (z : TriPoint) (g : TriGlueIndex) :
    triangularDepthSum z ≤ ∑ i, triQ (triGluePoint g i-
      (![-triTheta z,triC,-triC] : Fin 3 → TriPoint) i) := by
  have h := triangularDepthSum_le_integer z (triDFTIntegerEquiv.symm g)
  rw [triDFT_lattice_distance,triDFTIntegerEquiv.apply_symm_apply] at h
  exact h

lemma nearest_neg_c_residue (r : ZMod 3) :
    ∃ m : EisInt, eisResidue m=r ∧ triQ (eisEmbed m- -triC)=1/3 := by
  obtain ⟨m,hm,hd⟩ := exists_nearest_c_residue (-r)
  refine ⟨-m,by rw [map_neg,hm,neg_neg],?_⟩
  rw [map_neg,show -eisEmbed m- -triC = -(eisEmbed m-triC) by abel,triQ_neg,hd]

lemma nearest_neg_two_c_residue (r : ZMod 3) :
    ∃ m : EisInt, eisResidue m=r ∧ triQ (eisEmbed m- (-(2:ℝ)•triC))=1/3 := by
  obtain ⟨m,hm,hd⟩ := exists_nearest_c_residue r
  refine ⟨m+(-1,1),by simpa [map_add,eisResidue] using hm,?_⟩
  have he : eisEmbed (m+(-1,1))- (-(2:ℝ)•triC) = eisEmbed m-triC := by
    rw [map_add]
    ext <;> dsimp [eisEmbed,triC] <;> ring
  rw [he,hd]

lemma triangularDepthSum_upper_plus (z : TriPoint) :
    triangularDepthSum z ≤ 1/3+triangularDepth (triTheta z+triC) := by
  have hall (m : EisInt) : triangularDepthSum z-1/3 ≤
      triQ (eisEmbed m-(-triTheta z-triC)) := by
    obtain ⟨u,hu,hdu⟩ := nearest_neg_two_c_residue (-eisResidue m)
    let h : TriZeroSum := ⟨![m,0,u],by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, map_add, map_zero, add_zero, hu, add_neg_cancel]⟩
    have hb := triangularDepthSum_le_glue z ((1:ZMod 3),h)
    have he : (∑ i, triQ (triGluePoint ((1:ZMod 3),h) i-
        (![-triTheta z,triC,-triC] : Fin 3 → TriPoint) i)) =
        triQ (eisEmbed m-(-triTheta z-triC))+1/3 := by
      simp only [Fin.sum_univ_three,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,triGluePoint,
        h,zmodThree_val_one,Nat.cast_one,one_smul,map_zero,zero_add,sub_self]
      have hm' : eisEmbed m+triC- -triTheta z =
          eisEmbed m-(-triTheta z-triC) := by abel
      have hu' : eisEmbed u+triC- -triC = eisEmbed u-(-(2:ℝ)•triC) := by module
      rw [hm',hu',hdu]
      norm_num [triQ]
    rw [he] at hb
    linarith
  have hd : triangularDepthSum z-1/3 ≤ triangularDepth (-triTheta z-triC) := by
    apply le_csInf (Set.range_nonempty _)
    rintro t ⟨m,rfl⟩
    exact hall m
  rw [show -triTheta z-triC = -(triTheta z+triC) by abel,triangularDepth_even] at hd
  linarith

lemma triangularDepthSum_upper_minus (z : TriPoint) :
    triangularDepthSum z ≤ 1/3+triangularDepth (triTheta z-triC) := by
  have hall (m : EisInt) : triangularDepthSum z-1/3 ≤
      triQ (eisEmbed m-(-triTheta z-(2:ℝ)•triC)) := by
    obtain ⟨u,hu,hdu⟩ := nearest_neg_c_residue (-eisResidue m)
    let h : TriZeroSum := ⟨![m,u,(-1,1)],by
      have hr : eisResidue (-1, 1) = 0 := by norm_num [eisResidue]
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, map_add, hu, hr, add_neg_cancel, zero_add]⟩
    have hb := triangularDepthSum_le_glue z ((2:ZMod 3),h)
    have he : (∑ i, triQ (triGluePoint ((2:ZMod 3),h) i-
        (![-triTheta z,triC,-triC] : Fin 3 → TriPoint) i)) =
        triQ (eisEmbed m-(-triTheta z-(2:ℝ)•triC))+1/3 := by
      simp only [Fin.sum_univ_three,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,triGluePoint,
        h,zmodThree_val_two,Nat.cast_ofNat]
      have hm' : eisEmbed m+(2:ℝ)•triC- -triTheta z =
          eisEmbed m-(-triTheta z-(2:ℝ)•triC) := by abel
      have hu' : eisEmbed u+(2:ℝ)•triC-triC = eisEmbed u- -triC := by module
      have hz : eisEmbed (-1,1)+(2:ℝ)•triC- -triC = 0 := by
        ext <;> norm_num [eisEmbed,triC]
      rw [hm',hu',hdu,hz]
      norm_num [triQ]
    rw [he] at hb
    linarith
  have hd : triangularDepthSum z-1/3 ≤ triangularDepth (-triTheta z-(2:ℝ)•triC) := by
    apply le_csInf (Set.range_nonempty _)
    rintro t ⟨m,rfl⟩
    exact hall m
  have he : triTheta z+(2:ℝ)•triC = (triTheta z-triC)+eisEmbed (1,-1) := by
    ext <;> dsimp [triC,eisEmbed] <;> ring
  rw [show -triTheta z-(2:ℝ)•triC = -(triTheta z+(2:ℝ)•triC) by module,
    triangularDepth_even,he,triangularDepth_periodic] at hd
  linarith

theorem triangularDepthSum_upper (z : TriPoint) : triangularDepthSum z ≤ 2/3 := by
  have h := triangularDepthSum_upper_plus z
  have h' := triangularDepth_le_third (triTheta z+triC)
  linarith

theorem triangularDepthSum_periodic (z : TriPoint) (m : EisInt) :
    triangularDepthSum (z+eisEmbed m)=triangularDepthSum z := by
  unfold triangularDepthSum
  rw [show z+eisEmbed m+triC = (z+triC)+eisEmbed m by abel,
    show z+eisEmbed m-triC = (z-triC)+eisEmbed m by abel]
  simp only [triangularDepth_periodic]

theorem triangularDepthSum_c_periodic (z : TriPoint) :
    triangularDepthSum (z+triC)=triangularDepthSum z := by
  unfold triangularDepthSum
  have he : z+triC+triC = (z-triC)+eisEmbed (1,-1) := by
    ext <;> dsimp [triC,eisEmbed] <;> ring
  rw [he,triangularDepth_periodic,add_sub_cancel_right]
  ring

theorem triangularDepthSum_zero : triangularDepthSum 0=2/3 := by
  simp [triangularDepthSum,triangularDepth_zero,triangularDepth_c,triangularDepth_even]
  norm_num

/-- The scalar geometric equality is proved from explicit nearest residue
representatives and the same integral Fourier isometry, without a Laplace limit. -/
theorem triangularDepthSum_eq_iff (z : TriPoint) : triangularDepthSum z=2/3 ↔ TriPhase z := by
  constructor
  · intro hz
    have hp := triangularDepthSum_upper_plus z
    have hm := triangularDepthSum_upper_minus z
    have hp' := triangularDepth_le_third (triTheta z+triC)
    have hm' := triangularDepth_le_third (triTheta z-triC)
    have he1 : triangularDepth (triTheta z+triC)=1/3 := by linarith
    have he2 : triangularDepth (triTheta z-triC)=1/3 := by linarith
    exact (triPhase_iff_theta_integral z).mpr ((triHole_both_iff _).mp
      ⟨(triangularDepth_eq_third_iff _).mp he1,(triangularDepth_eq_third_iff _).mp he2⟩)
  · rintro ⟨r,m,rfl⟩
    rw [add_comm,triangularDepthSum_periodic]
    rcases (show ∀ r : ZMod 3, r = 0 ∨ r = 1 ∨ r = 2 by decide) r with
      rfl | rfl | rfl
    · change triangularDepthSum (((0 : ZMod 3).val : ℝ) • triC) = _
      rw [ZMod.val_zero]
      simpa only [Nat.cast_zero, zero_smul] using triangularDepthSum_zero
    · change triangularDepthSum (((1 : ZMod 3).val : ℝ) • triC) = _
      rw [zmodThree_val_one]
      have h := (triangularDepthSum_c_periodic 0).trans triangularDepthSum_zero
      simpa only [Nat.cast_one, one_smul, zero_add] using h
    · change triangularDepthSum (((2 : ZMod 3).val : ℝ) • triC) = _
      rw [zmodThree_val_two]
      have h1 : triangularDepthSum triC = 2 / 3 := by
        simpa only [zero_add] using
          (triangularDepthSum_c_periodic 0).trans triangularDepthSum_zero
      have he : (2:ℝ)•triC=triC+triC := by module
      simpa only [Nat.cast_ofNat, he] using (triangularDepthSum_c_periodic triC).trans h1

end PaperVerification.ColdSpots
end
end Source_TriangularDepthSum
-- END ORIGINAL PaperVerification.TriangularDepthSum


-- BEGIN ORIGINAL PaperVerification.ThreeTermAMGM
section Source_ThreeTermAMGM

-- original header: module
-- original header: public import Mathlib.Data.Real.Basic
-- original header: public import Mathlib.Tactic.Ring
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.Positivity
-- original header: @[expose] public section
namespace PaperVerification.ColdSpots

private theorem amgm3_at_minimum (x y z : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hxz : x ≤ z) :
    27 * (x * y * z) ≤ (x + y + z) ^ 3 ∧
      ((x + y + z) ^ 3 = 27 * (x * y * z) ↔ x = y ∧ y = z) := by
  let u := y - x
  let v := z - x
  have hu : 0 ≤ u := sub_nonneg.mpr hxy
  have hv : 0 ≤ v := sub_nonneg.mpr hxz
  have hq : 0 ≤ u ^ 2 - u * v + v ^ 2 := by
    nlinarith [sq_nonneg (u-v), sq_nonneg u, sq_nonneg v]
  have hp : 0 ≤ 9 * x * (u ^ 2 - u * v + v ^ 2) := by positivity
  have hc : 0 ≤ (u + v) ^ 3 := pow_nonneg (add_nonneg hu hv) _
  have hi : (x+y+z)^3 - 27*(x*y*z) =
      9*x*(u^2-u*v+v^2) + (u+v)^3 := by dsimp [u,v]; ring
  refine ⟨by linarith, ?_⟩
  constructor
  · intro h
    have hz : (u+v)^3 = 0 := by linarith
    have huv : u+v = 0 := eq_zero_of_pow_eq_zero hz
    dsimp [u,v] at huv hu hv
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl,rfl⟩
    ring

theorem three_term_amgm (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    27 * (x * y * z) ≤ (x + y + z) ^ 3 ∧
      ((x + y + z) ^ 3 = 27 * (x * y * z) ↔ x = y ∧ y = z) := by
  rcases le_total x y with hxy | hyx
  · rcases le_total x z with hxz | hzx
    · exact amgm3_at_minimum x y z hx hxy hxz
    · have h := amgm3_at_minimum z x y hz hzx (hzx.trans hxy)
      have he : (z=x ∧ x=y) ↔ (x=y ∧ y=z) := by constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith
      simpa [add_comm,add_left_comm,add_assoc,mul_comm,mul_left_comm,mul_assoc,he] using h
  · rcases le_total y z with hyz | hzy
    · have h := amgm3_at_minimum y x z hy hyx hyz
      have he : (y=x ∧ x=z) ↔ (x=y ∧ y=z) := by constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith
      simpa [add_comm,add_left_comm,add_assoc,mul_comm,mul_left_comm,mul_assoc,he] using h
    · have h := amgm3_at_minimum z x y hz (hzy.trans hyx) hzy
      have he : (z=x ∧ x=y) ↔ (x=y ∧ y=z) := by constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith
      simpa [add_comm,add_left_comm,add_assoc,mul_comm,mul_left_comm,mul_assoc,he] using h

end PaperVerification.ColdSpots
end Source_ThreeTermAMGM
-- END ORIGINAL PaperVerification.ThreeTermAMGM


-- BEGIN ORIGINAL PaperVerification.TriangularMaximum
section Source_TriangularMaximum

-- original header: module
-- original header: public import PaperVerification.TriangularGaussian
-- original header: public import Mathlib.Algebra.Ring.Int.Parity
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

lemma gaussian_pair_sum {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t + gaussian α (t - 1 / 2) = gaussian (α / 4) (2 * t) := by
  have h := gaussian_split (show 0 < α / 4 by positivity) (2 * t)
  rw [show 4 * (α / 4) = α by ring,
    show 2 * t / 2 = t by ring, show (2 * t - 1) / 2 = t - 1 / 2 by ring] at h
  exact h.symm

lemma gaussian_pair_sum_le {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t + gaussian α (t - 1 / 2) ≤ gaussian α 0 + gaussian α (1 / 2) := by
  have h0 := gaussian_pair_sum hα 0
  simp only [zero_sub, mul_zero, gaussian_even] at h0
  rw [gaussian_pair_sum hα, h0]
  exact gaussian_le_zero (by positivity) _

lemma gaussian_pair_sum_eq_iff {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t + gaussian α (t - 1 / 2) = gaussian α 0 + gaussian α (1 / 2) ↔
      ∃ m : ℤ, 2 * t = (m : ℝ) := by
  have h0 := gaussian_pair_sum hα 0
  simp only [zero_sub, mul_zero, gaussian_even] at h0
  rw [gaussian_pair_sum hα, h0]
  exact gaussian_maximum_iff (by positivity) _

lemma gaussian_zero_gt_half {α : ℝ} (hα : 0 < α) :
    gaussian α (1 / 2) < gaussian α 0 := by
  apply lt_of_le_of_ne (gaussian_le_zero hα _)
  intro heq
  obtain ⟨m, hm⟩ := (gaussian_maximum_iff hα (1 / 2)).mp heq
  have hm0 : (0 : ℤ) < m := by exact_mod_cast (show (0 : ℝ) < m by linarith)
  have hm1 : m < (1 : ℤ) := by exact_mod_cast (show (m : ℝ) < 1 by linarith)
  omega

lemma gaussian_pair_difference_abs_le {α : ℝ} (hα : 0 < α) (t : ℝ) :
    |gaussian α t - gaussian α (t - 1 / 2)| ≤ gaussian α 0 - gaussian α (1 / 2) := by
  have hp := gaussian_shift_product_min hα t
  have hs : gaussian α t ^ 2 + gaussian α (t - 1 / 2) ^ 2 ≤
      gaussian α 0 ^ 2 + gaussian α (1 / 2) ^ 2 := by
    have h0 := gaussian_diagonal_sum hα 0
    simp only [zero_sub, mul_zero, gaussian_even] at h0
    rw [gaussian_diagonal_sum hα, h0]
    exact mul_le_mul_of_nonneg_left (gaussian_le_zero (half_pos hα) _)
      (gaussian_pos (half_pos hα) _).le
  have hd := (gaussian_zero_gt_half hα).le
  apply (sq_le_sq₀ (abs_nonneg _) (sub_nonneg.mpr hd)).mp
  rw [sq_abs]
  nlinarith

lemma triangularGaussian_upper_algebra {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    triangularGaussian α z ≤ triangularGaussian α 0 ∧
      (triangularGaussian α z = triangularGaussian α 0 →
        (∃ p : ℤ, 2 * (z.1 - z.2 / 2) = (p : ℝ)) ∧
        (∃ q : ℤ, z.2 = (q : ℝ))) := by
  let s := z.1 - z.2 / 2
  let t := z.2 / 2
  let X := gaussian α s + gaussian α (s - 1 / 2)
  let Y := gaussian (3 * α) t + gaussian (3 * α) (t - 1 / 2)
  let A := gaussian α 0 + gaussian α (1 / 2)
  let B := gaussian (3 * α) 0 + gaussian (3 * α) (1 / 2)
  let d := gaussian α 0 - gaussian α (1 / 2)
  let e := gaussian (3 * α) 0 - gaussian (3 * α) (1 / 2)
  let D := gaussian α s - gaussian α (s - 1 / 2)
  let E := gaussian (3 * α) t - gaussian (3 * α) (t - 1 / 2)
  have h3 : 0 < 3 * α := by positivity
  have hX : 0 < X := add_pos (gaussian_pos hα _) (gaussian_pos hα _)
  have hY : 0 < Y := add_pos (gaussian_pos h3 _) (gaussian_pos h3 _)
  have hA : 0 < A := add_pos (gaussian_pos hα _) (gaussian_pos hα _)
  have hB : 0 < B := add_pos (gaussian_pos h3 _) (gaussian_pos h3 _)
  have hXA : X ≤ A := gaussian_pair_sum_le hα s
  have hYB : Y ≤ B := gaussian_pair_sum_le h3 t
  have hd : 0 < d := sub_pos.mpr (gaussian_zero_gt_half hα)
  have he : 0 < e := sub_pos.mpr (gaussian_zero_gt_half h3)
  have hD : |D| ≤ d := gaussian_pair_difference_abs_le hα s
  have hE : |E| ≤ e := gaussian_pair_difference_abs_le h3 t
  have hDE : D * E ≤ d * e := (le_abs_self _).trans (by
    rw [abs_mul]
    exact mul_le_mul hD hE (abs_nonneg E) hd.le)
  have hXY : X * Y ≤ A * B := mul_le_mul hXA hYB hY.le hA.le
  have hf : 2 * triangularGaussian α z = X * Y + D * E := by
    rw [triangularGaussian_eq_products hα]
    dsimp [X,Y,D,E,s,t]
    ring
  have hf0 : 2 * triangularGaussian α 0 = A * B + d * e := by
    rw [triangularGaussian_eq_products hα]
    norm_num only [Prod.fst_zero, Prod.snd_zero, zero_div, sub_self, zero_sub, gaussian_even]
    dsimp [A,B,d,e]
    ring
  refine ⟨by linarith, ?_⟩
  intro heq
  have hXYeq : X * Y = A * B := by rw [heq] at hf; linarith
  have hXeq : X = A := by
    apply le_antisymm hXA
    by_contra hn
    have hlt := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hB
    have hle := mul_le_mul_of_nonneg_left hYB hX.le
    nlinarith
  have hYeq : Y = B := by
    apply mul_left_cancel₀ hA.ne'
    simpa only [hXeq] using hXYeq
  refine ⟨(gaussian_pair_sum_eq_iff hα s).mp hXeq, ?_⟩
  obtain ⟨q,hq⟩ := (gaussian_pair_sum_eq_iff h3 t).mp hYeq
  exact ⟨q, by dsimp [t] at hq; linarith⟩

theorem triangularGaussian_le_zero {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    triangularGaussian α z ≤ triangularGaussian α 0 :=
  (triangularGaussian_upper_algebra hα z).1

lemma triangularGaussian_half_strict {α : ℝ} (hα : 0 < α) :
    triangularGaussian α ((1 / 2 : ℝ),0) < triangularGaussian α 0 := by
  rw [triangularGaussian_eq_products hα, triangularGaussian_eq_products hα]
  norm_num only [Prod.fst, Prod.snd, Prod.fst_zero, Prod.snd_zero, zero_div,
    sub_zero, sub_self, zero_sub, gaussian_even]
  have h := mul_pos (sub_pos.mpr (gaussian_zero_gt_half hα))
    (sub_pos.mpr (gaussian_zero_gt_half (show 0 < 3 * α by positivity)))
  nlinarith

/-- The maximum of the actual triangular Gaussian occurs precisely at its
integral Eisenstein lattice, with no use of a separate triangular minimum theorem. -/
theorem triangularGaussian_maximum_iff {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    triangularGaussian α z = triangularGaussian α 0 ↔ z ∈ triIntegerLattice := by
  constructor
  · intro hz
    obtain ⟨⟨p,hp⟩,⟨q,hq⟩⟩ := (triangularGaussian_upper_algebra hα z).2 hz
    have hu : z.1 = ((p : ℝ) + q) / 2 := by linarith
    rcases Int.even_or_odd (p + q) with he | ho
    · obtain ⟨k,hk⟩ := he
      refine ⟨(k,q), ?_⟩
      apply Prod.ext
      · change (k : ℝ) = z.1
        have hkr : (p : ℝ) + q = k + k := by exact_mod_cast hk
        linarith
      · exact hq.symm
    · obtain ⟨k,hk⟩ := ho
      have he : z = ((1 / 2 : ℝ),0) + eisEmbed (k,q) := by
        apply Prod.ext
        · change z.1 = 1 / 2 + (k : ℝ)
          have hkr : (p : ℝ) + q = 2 * k + 1 := by exact_mod_cast hk
          linarith
        · simpa [eisEmbed] using hq
      rw [he, triangularGaussian_periodic] at hz
      exact False.elim ((ne_of_lt (triangularGaussian_half_strict hα)) hz)
  · rintro ⟨m,rfl⟩
    simpa only [zero_add] using triangularGaussian_periodic α 0 m

theorem triangularGaussian_c_lt_zero {α : ℝ} (hα : 0 < α) :
    triangularGaussian α triC < triangularGaussian α 0 := by
  apply lt_of_le_of_ne (triangularGaussian_le_zero hα triC)
  intro heq
  obtain ⟨m, hm⟩ := (triangularGaussian_maximum_iff hα triC).mp heq
  have h := congrArg Prod.fst hm
  change (m.1 : ℝ) = 1 / 3 at h
  have h0 : (0 : ℤ) < m.1 := by exact_mod_cast (show (0 : ℝ) < m.1 by linarith)
  have h1 : m.1 < (1 : ℤ) := by exact_mod_cast (show (m.1 : ℝ) < 1 by linarith)
  omega

end PaperVerification.ColdSpots
end
end Source_TriangularMaximum
-- END ORIGINAL PaperVerification.TriangularMaximum


-- BEGIN ORIGINAL PaperVerification.TriangularMinimum
section Source_TriangularMinimum

-- original header: module
-- original header: public import PaperVerification.TriangularPhases
-- original header: public import PaperVerification.TriangularMaximum
-- original header: public import PaperVerification.ThreeTermAMGM
-- original header: public import Mathlib.Topology.Order.Compact
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

theorem triangularProduct_pos {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    0 < triangularProduct α z :=
  mul_pos (mul_pos (triangularGaussian_pos hα _) (triangularGaussian_pos hα _))
    (triangularGaussian_pos hα _)

theorem continuous_triangularProduct {α : ℝ} (hα : 0 < α) :
    Continuous (triangularProduct α) :=
  ((continuous_triangularGaussian hα).mul
    ((continuous_triangularGaussian hα).comp (continuous_id.add continuous_const))).mul
      ((continuous_triangularGaussian hα).comp (continuous_id.sub continuous_const))

theorem triangularProduct_attains_minimum {α : ℝ} (hα : 0 < α) :
    ∃ z : TriPoint, ∀ w, triangularProduct α z ≤ triangularProduct α w := by
  have hc := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1)).prod
    (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1))
  have hn : ((Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc (0:ℝ) 1)).Nonempty :=
    ⟨(0,0),by norm_num⟩
  obtain ⟨z,hz,hmin⟩ := hc.exists_isMinOn hn (continuous_triangularProduct hα).continuousOn
  refine ⟨z,fun w ↦ ?_⟩
  have h := hmin (triFraction_mem w)
  rw [← triFraction_add_floor w,triangularProduct_periodic]
  exact h

theorem triangularProduct_cubic_bound {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    (triangularGaussian α 0 * triangularGaussian α triC ^ 2)^2 *
      triangularProduct α (triTheta z) ≤ triangularProduct α z ^ 3 := by
  let a := triangularGaussian α 0
  let b := triangularGaussian α triC
  let x := a * triangularGaussian α (triTheta z+triC)
  let y := a * triangularGaussian α (triTheta z-triC)
  let w := b * triangularGaussian α (triTheta z)
  have ha : 0 < a := triangularGaussian_pos hα _
  have hb : 0 < b := triangularGaussian_pos hα _
  have hx : 0 < x := mul_pos ha (triangularGaussian_pos hα _)
  have hy : 0 < y := mul_pos ha (triangularGaussian_pos hα _)
  have hw : 0 < w := mul_pos hb (triangularGaussian_pos hα _)
  have h := (three_term_amgm x y w hx.le hy.le hw.le).1
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ b^3/27 by positivity)
  have he : triangularProduct α z = b/3*(x+y+w) := by
    rw [triangular_cubic_identity hα]
    dsimp [a,b,x,y,w]
    ring
  rw [he]
  dsimp [a,b,x,y,w,triangularProduct] at hm ⊢
  nlinarith only [hm]

/-- The sharp scalar lower bound in Proposition 8.1 for every physical point. -/
theorem triangularProduct_minimum {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    triangularGaussian α 0 * triangularGaussian α triC ^ 2 ≤ triangularProduct α z := by
  obtain ⟨w,hw⟩ := triangularProduct_attains_minimum hα
  let K := triangularGaussian α 0 * triangularGaussian α triC ^ 2
  have hK : 0 < K := mul_pos (triangularGaussian_pos hα _) (sq_pos_of_pos (triangularGaussian_pos hα _))
  have hm : 0 < triangularProduct α w := triangularProduct_pos hα _
  have h := triangularProduct_cubic_bound hα w
  have h' := hw (triTheta w)
  have hp := mul_le_mul_of_nonneg_left h' (sq_nonneg K)
  have hsq : K^2 ≤ triangularProduct α w ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right hm).mp
    calc
      K^2*triangularProduct α w ≤ K^2*triangularProduct α (triTheta w) := hp
      _ ≤ triangularProduct α w^3 := h
      _ = triangularProduct α w^2*triangularProduct α w := by ring
  have hle : K ≤ triangularProduct α w := (sq_le_sq₀ hK.le hm.le).mp hsq
  exact hle.trans (hw z)

theorem triangularProduct_equality_iff {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    triangularProduct α z = triangularGaussian α 0 * triangularGaussian α triC ^ 2 ↔
      TriPhase z := by
  constructor
  · intro heq
    let a := triangularGaussian α 0
    let b := triangularGaussian α triC
    let x := a * triangularGaussian α (triTheta z+triC)
    let y := a * triangularGaussian α (triTheta z-triC)
    let w := b * triangularGaussian α (triTheta z)
    have ha : 0 < a := triangularGaussian_pos hα _
    have hb : 0 < b := triangularGaussian_pos hα _
    have hx : 0 < x := mul_pos ha (triangularGaussian_pos hα _)
    have hy : 0 < y := mul_pos ha (triangularGaussian_pos hα _)
    have hw : 0 < w := mul_pos hb (triangularGaussian_pos hα _)
    have htheta : triangularProduct α (triTheta z) = a*b^2 := by
      apply le_antisymm
      · have h := triangularProduct_cubic_bound hα z
        rw [heq] at h
        apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos (mul_pos ha (sq_pos_of_pos hb)))).mp
        calc
          (a*b^2)^2*triangularProduct α (triTheta z) ≤ (a*b^2)^3 := h
          _ = (a*b^2)^2*(a*b^2) := by ring
      · exact triangularProduct_minimum hα _
    have hsum : x+y+w = 3*a*b := by
      have hc : triangularProduct α z=b/3*(x+y+w) := by
        rw [triangular_cubic_identity hα]
        dsimp [a,b,x,y,w]
        ring
      have he : a*b^2=b/3*(x+y+w) := heq.symm.trans hc
      apply mul_left_cancel₀ hb.ne'
      calc
        b*(x+y+w)=3*(b/3*(x+y+w)) := by ring
        _ = 3*(a*b^2) := congrArg (fun t : ℝ ↦ 3*t) he.symm
        _ = b*(3*a*b) := by ring
    have hprod : x*y*w = a^3*b^3 := by
      have hp : x*y*w = a^2*b*triangularProduct α (triTheta z) := by
        dsimp [x,y,w,triangularProduct]
        ring
      rw [hp,htheta]
      ring
    have he : (x+y+w)^3 = 27*(x*y*w) := by rw [hsum,hprod]; ring
    have hequal := (three_term_amgm x y w hx.le hy.le hw.le).2.mp he
    have hwval : w = a*b := by linarith
    have hF : triangularGaussian α (triTheta z) = a := by
      apply mul_left_cancel₀ hb.ne'
      calc
        b*triangularGaussian α (triTheta z)=w := rfl
        _ = a*b := hwval
        _ = b*a := mul_comm _ _
    exact (triPhase_iff_theta_integral z).mpr ((triangularGaussian_maximum_iff hα _).mp hF)
  · intro hz
    exact triangularProduct_phase α hz

end PaperVerification.ColdSpots
end
end Source_TriangularMinimum
-- END ORIGINAL PaperVerification.TriangularMinimum


-- BEGIN ORIGINAL PaperVerification.E6Coordinates
section Source_E6Coordinates

-- original header: module
-- original header: public import PaperVerification.TriangularMinimum
-- original header: public import PaperVerification.TriangularDepthSum
-- original header: public import Mathlib.Analysis.InnerProductSpace.PiL2
-- original header: public import Mathlib.Algebra.Order.Archimedean.Real.Basic
-- original header: public import Mathlib.Topology.Algebra.InfiniteSum.Real
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

abbrev TriTriple := Fin 3 → TriPoint
abbrev E6Index := ZMod 3 × (Fin 3 → EisInt)

def l6Point (p : E6Index) : TriTriple :=
  fun i ↦ eisEmbed (p.2 i)+(p.1.val : ℝ)•triC

def l6Set : Set TriTriple := Set.range l6Point

def triTripleSqDist (z w : TriTriple) : ℝ := ∑ i, triQ (z i-w i)

def l6Gaussian (α : ℝ) (z : TriTriple) : ℝ :=
  ∑' p : E6Index, Real.exp (-α*triTripleSqDist (l6Point p) z)

def l6Depth (z : TriTriple) : ℝ :=
  sInf (Set.range fun p : E6Index ↦ triTripleSqDist (l6Point p) z)

def IsL6ColdSpot (α : ℝ) (z : TriTriple) : Prop := ∀ w, l6Gaussian α z ≤ l6Gaussian α w

def IsL6DeepHole (z : TriTriple) : Prop := ∀ w, l6Depth w ≤ l6Depth z

theorem l6Point_injective : Function.Injective l6Point := by
  intro p q h
  have h0 := congrArg Prod.fst (congrFun h 0)
  change ((p.2 0).1 : ℝ)+(p.1.val : ℝ)*(1/3) =
    ((q.2 0).1 : ℝ)+(q.1.val : ℝ)*(1/3) at h0
  have hi : (3:ℤ)*((p.2 0).1-(q.2 0).1) = (q.1.val : ℤ)-(p.1.val : ℤ) := by
    apply Int.cast_injective (α:=ℝ)
    push_cast
    linarith
  have hr0 := congrArg (fun k : ℤ ↦ (k : ZMod 3)) hi
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_sub, Int.cast_natCast,
    ZMod.natCast_zmod_val, zmodThree_three_eq_zero, zero_mul] at hr0
  have hr : p.1=q.1 := by linear_combination hr0
  apply Prod.ext hr
  funext i
  apply eisEmbed_injective
  have hh := congrFun h i
  change eisEmbed (p.2 i)+(p.1.val : ℝ)•triC=eisEmbed (q.2 i)+(q.1.val : ℝ)•triC at hh
  rw [hr] at hh
  exact add_right_cancel hh

def l6Equiv : E6Index ≃ l6Set := Equiv.ofInjective l6Point l6Point_injective

theorem l6Set_iff_integer_glue (z : TriTriple) : z ∈ l6Set ↔
    ∃ m : Fin 3 → EisInt, ∃ k : ℤ, ∀ i, z i=eisEmbed (m i)+(k : ℝ)•triC := by
  constructor
  · rintro ⟨⟨r,m⟩,rfl⟩
    exact ⟨m,(r.val : ℤ),fun _ ↦ rfl⟩
  · rintro ⟨m,k,h⟩
    let r : ZMod 3 := k
    let q : ℤ := k/3
    have hk : k=(r.val : ℤ)+3*q := by
      have hr : (r.val : ℤ)=k%3 := by
        simpa [r] using (ZMod.val_intCast (n:=3) k)
      dsimp [q]
      omega
    refine ⟨(r,fun i ↦ m i+q•(1,-1)),?_⟩
    funext i
    rw [h i]
    dsimp [l6Point]
    rw [map_add]
    have hkr : (k:ℝ)=(r.val:ℝ)+3*(q:ℝ) := by exact_mod_cast hk
    ext <;> dsimp [triC,eisEmbed] <;> push_cast <;> rw [hkr] <;> ring

theorem l6Gaussian_actual_set (α : ℝ) (z : TriTriple) :
    l6Gaussian α z = ∑' p : l6Set, Real.exp (-α*triTripleSqDist p.val z) :=
  l6Equiv.tsum_eq (fun p : l6Set ↦ Real.exp (-α*triTripleSqDist p.val z))

theorem l6Depth_actual_set (z : TriTriple) :
    l6Depth z = sInf ((fun p ↦ triTripleSqDist p z) '' l6Set) := by
  unfold l6Depth l6Set
  exact congrArg sInf (Set.range_comp' (fun p : TriTriple ↦ triTripleSqDist p z) l6Point)

theorem l6_term_factor (α : ℝ) (z : TriTriple) (r : ZMod 3) (m : Fin 3 → EisInt) :
    Real.exp (-α*triTripleSqDist (l6Point (r,m)) z) =
      ∏ i, Real.exp (-α*triQ (eisEmbed (m i)-(z i-(r.val : ℝ)•triC))) := by
  unfold triTripleSqDist
  rw [Finset.mul_sum,Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  have hpoint : l6Point (r,m) i-z i =
      eisEmbed (m i)-(z i-(r.val : ℝ)•triC) := by
    dsimp only [l6Point]
    abel
  exact congrArg (fun v : TriPoint ↦ Real.exp (-α*triQ v)) hpoint

theorem summable_l6Gaussian {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    Summable (fun p : E6Index ↦ Real.exp (-α*triTripleSqDist (l6Point p) z)) := by
  apply (summable_prod_of_nonneg (fun _ ↦ (Real.exp_pos _).le)).mpr
  refine ⟨?_,Summable.of_finite⟩
  intro r
  simp only [l6_term_factor]
  exact summable_fin_product 3
    (fun i m ↦ Real.exp (-α*triQ (eisEmbed m-(z i-(r.val : ℝ)•triC))))
    (fun i ↦ summable_triangularGaussian hα (z i-(r.val : ℝ)•triC))

theorem l6Gaussian_cosets {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    l6Gaussian α z = ∑ r : ZMod 3, ∏ i, triangularGaussian α (z i-(r.val : ℝ)•triC) := by
  unfold l6Gaussian
  rw [(summable_l6Gaussian hα z).tsum_prod,tsum_fintype]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [l6_term_factor]
  exact tsum_fin_product 3
    (fun i m ↦ Real.exp (-α*triQ (eisEmbed m-(z i-(r.val : ℝ)•triC))))
    (fun i ↦ summable_triangularGaussian hα (z i-(r.val : ℝ)•triC))

theorem l6Depth_nonneg (z : TriTriple) : 0 ≤ l6Depth z := by
  apply le_csInf (Set.range_nonempty _)
  rintro t ⟨p,rfl⟩
  exact Finset.sum_nonneg (fun i hi ↦ triQ_nonneg _)

theorem l6Depth_le (z : TriTriple) (p : E6Index) :
    l6Depth z ≤ triTripleSqDist (l6Point p) z :=
  csInf_le ⟨0,by rintro t ⟨q,rfl⟩; exact Finset.sum_nonneg (fun i hi ↦ triQ_nonneg _)⟩
    (Set.mem_range_self p)

def l6CosetDepth (z : TriTriple) (r : ZMod 3) : ℝ :=
  ∑ i, triangularDepth (z i-(r.val : ℝ)•triC)

theorem l6Depth_le_cosetDepth (z : TriTriple) (r : ZMod 3) : l6Depth z ≤ l6CosetDepth z r := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have he : 0 < ε/3 := by positivity
  have hex (i : Fin 3) : ∃ m : EisInt,
      triQ (eisEmbed m-(z i-(r.val : ℝ)•triC)) < triangularDepth (z i-(r.val : ℝ)•triC)+ε/3 := by
    obtain ⟨a,⟨m,rfl⟩,hm⟩ := exists_lt_of_csInf_lt
      (Set.range_nonempty (fun m : EisInt ↦ triQ (eisEmbed m-(z i-(r.val : ℝ)•triC))))
      (lt_add_of_pos_right (triangularDepth (z i-(r.val : ℝ)•triC)) he)
    exact ⟨m,hm⟩
  choose m hm using hex
  have h := l6Depth_le z (r,m)
  have heq : triTripleSqDist (l6Point (r,m)) z =
      ∑ i, triQ (eisEmbed (m i)-(z i-(r.val : ℝ)•triC)) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    dsimp [l6Point]
    abel
  rw [heq] at h
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) ↦ (hm i).le)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul] at hs
  unfold l6CosetDepth
  linarith

end PaperVerification.ColdSpots
end
end Source_E6Coordinates
-- END ORIGINAL PaperVerification.E6Coordinates


-- BEGIN ORIGINAL PaperVerification.E6Phases
section Source_E6Phases

-- original header: module

-- original header: public import PaperVerification.E6Coordinates
-- original header: public import Mathlib.Data.Fintype.EquivFin

-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def triPhasePoint (r : ZMod 3) : TriPoint := (r.val : ℝ)•triC

lemma triPhase_difference_value (F : TriPoint → ℝ) (a b : ℝ)
    (h0 : F 0=a) (h1 : F triC=b) (hn1 : F (-triC)=b)
    (h2 : F ((2:ℝ)•triC)=b) (hn2 : F (-(2:ℝ)•triC)=b) (r s : ZMod 3) :
    F (triPhasePoint r-triPhasePoint s)=if r=s then a else b := by
  have hcases : ∀ x : ZMod 3, x=0 ∨ x=1 ∨ x=2 := by decide
  have h01 : (0 : ZMod 3) ≠ 1 := by decide
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  have hv0 : (0 : ZMod 3).val = 0 := by decide
  have hn2' : F (-((2 : ℝ) • triC)) = b := by simpa only [neg_smul] using hn2
  have hsub12 : triC - (2 : ℝ) • triC = -triC := by
    rw [two_smul]
    abel
  have hsub21 : (2 : ℝ) • triC - triC = triC := by
    rw [two_smul]
    abel
  rcases hcases r with rfl | rfl | rfl <;>
    rcases hcases s with rfl | rfl | rfl <;>
    norm_num [triPhasePoint, ← sub_smul, hv0, zmodThree_val_one,
      zmodThree_val_two, h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12,
      h0, h1, hn1, h2, hn2, hn2', hsub12, hsub21]

theorem triangularGaussian_phases {α : ℝ} (hα : 0 < α) (r s : ZMod 3) :
    triangularGaussian α (triPhasePoint r-triPhasePoint s)=
      if r=s then triangularGaussian α 0 else triangularGaussian α triC := by
  apply triPhase_difference_value _ _ _ rfl rfl
  · exact triangularGaussian_even _ _
  · have h := triangularGaussian_two_c α 0
    simpa only [zero_add,zero_sub,triangularGaussian_even] using h
  · rw [neg_smul,triangularGaussian_even]
    have h := triangularGaussian_two_c α 0
    simpa only [zero_add,zero_sub,triangularGaussian_even] using h

theorem triangularDepth_phases (r s : ZMod 3) :
    triangularDepth (triPhasePoint r-triPhasePoint s)=if r=s then 0 else 1/3 := by
  apply triPhase_difference_value _ _ _ triangularDepth_zero triangularDepth_c
  · rw [triangularDepth_even,triangularDepth_c]
  · have he : (2:ℝ)•triC = -triC+eisEmbed (1,-1) := by
      ext <;> norm_num [triC,eisEmbed]
    rw [he,triangularDepth_periodic,triangularDepth_even,triangularDepth_c]
  · rw [neg_smul,triangularDepth_even]
    have he : (2:ℝ)•triC = -triC+eisEmbed (1,-1) := by
      ext <;> norm_num [triC,eisEmbed]
    rw [he,triangularDepth_periodic,triangularDepth_even,triangularDepth_c]

def E6PhaseConfiguration (z : TriTriple) (r : Fin 3 → ZMod 3) : Prop :=
  ∃ m : Fin 3 → EisInt, ∀ i, z i=eisEmbed (m i)+triPhasePoint (r i)

def E6BalancedPhases (z : TriTriple) : Prop :=
  ∃ r : Fin 3 → ZMod 3, Function.Bijective r ∧ E6PhaseConfiguration z r

theorem exists_E6PhaseConfiguration_iff (z : TriTriple) :
    (∃ r, E6PhaseConfiguration z r) ↔ ∀ i, TriPhase (z i) := by
  constructor
  · rintro ⟨r,m,hm⟩ i
    exact ⟨r i,m i,hm i⟩
  · intro h
    choose r m hm using h
    exact ⟨r,m,hm⟩

def e6GaussianProfile (a b : ℝ) (r : Fin 3 → ZMod 3) (s : ZMod 3) : ℝ :=
  ∏ i, if r i=s then a else b

def e6DepthProfile (r : Fin 3 → ZMod 3) (s : ZMod 3) : ℝ :=
  ∑ i, if r i=s then (0:ℝ) else 1/3

theorem l6Gaussian_of_phases {α : ℝ} (hα : 0 < α) {z : TriTriple} {r : Fin 3 → ZMod 3}
    (hr : E6PhaseConfiguration z r) :
    l6Gaussian α z=∑ s : ZMod 3, e6GaussianProfile
      (triangularGaussian α 0) (triangularGaussian α triC) r s := by
  obtain ⟨m,hm⟩ := hr
  rw [l6Gaussian_cosets hα]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.prod_congr rfl
  intro i hi
  rw [hm i,show eisEmbed (m i)+triPhasePoint (r i)-(s.val:ℝ)•triC =
    (triPhasePoint (r i)-triPhasePoint s)+eisEmbed (m i) by dsimp [triPhasePoint]; abel,
    triangularGaussian_periodic,triangularGaussian_phases hα]

theorem l6CosetDepth_of_phases {z : TriTriple} {r : Fin 3 → ZMod 3}
    (hr : E6PhaseConfiguration z r) (s : ZMod 3) :
    l6CosetDepth z s=e6DepthProfile r s := by
  obtain ⟨m,hm⟩ := hr
  apply Finset.sum_congr rfl
  intro i hi
  rw [hm i,show eisEmbed (m i)+triPhasePoint (r i)-(s.val:ℝ)•triC =
    (triPhasePoint (r i)-triPhasePoint s)+eisEmbed (m i) by dsimp [triPhasePoint]; abel,
    triangularDepth_periodic,triangularDepth_phases]

lemma bijective_fin3_zmod3_iff (r : Fin 3 → ZMod 3) :
    Function.Bijective r ↔ r 0≠r 1 ∧ r 0≠r 2 ∧ r 1≠r 2 := by
  rw [Fintype.bijective_iff_injective_and_card]
  simp only [Fintype.card_fin,ZMod.card,eq_self_iff_true,true_and,and_true]
  constructor
  · intro h
    exact ⟨fun he ↦ by have := h he; norm_num at this,
      fun he ↦ by have := h he; norm_num at this,
      fun he ↦ by have := h he; norm_num at this⟩
  · rintro ⟨h01,h02,h12⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all

lemma e6GaussianProfile_eq_iff (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (r : Fin 3 → ZMod 3) :
    (e6GaussianProfile a b r 0=e6GaussianProfile a b r 1 ∧
      e6GaussianProfile a b r 1=e6GaussianProfile a b r 2) ↔ Function.Bijective r := by
  rw [bijective_fin3_zmod3_iff]
  have ha : 0 < a := hb.trans hab
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  have hb2 : 0 < b^2 := sq_pos_of_pos hb
  have hgap : 0 < a*b*(a-b) := by positivity
  have hgap2 : 0 < (a-b)*(a^2+a*b+b^2) := by positivity
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have habne : a ≠ b := ne_of_gt hab
  have hcases : ∀ x : ZMod 3, x=0 ∨ x=1 ∨ x=2 := by decide
  have h01 : (0 : ZMod 3) ≠ 1 := by decide
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  rcases hcases (r 0) with h0 | h0 | h0 <;>
    rcases hcases (r 1) with h1 | h1 | h1 <;>
    rcases hcases (r 2) with h2 | h2 | h2 <;>
    simp [e6GaussianProfile, Fin.prod_univ_three, h0, h1, h2,
      h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12,
      ha0, hb0, habne, Ne.symm habne,
      mul_comm, mul_left_comm, mul_assoc] <;>
    first | (rintro ⟨he, hf⟩; nlinarith) | (intros; nlinarith)

lemma e6DepthProfile_eq_iff (r : Fin 3 → ZMod 3) :
    (e6DepthProfile r 0=2/3 ∧ e6DepthProfile r 1=2/3 ∧ e6DepthProfile r 2=2/3) ↔
      Function.Bijective r := by
  rw [bijective_fin3_zmod3_iff]
  have hcases : ∀ x : ZMod 3, x=0 ∨ x=1 ∨ x=2 := by decide
  have h01 : (0 : ZMod 3) ≠ 1 := by decide
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  rcases hcases (r 0) with h0 | h0 | h0 <;>
    rcases hcases (r 1) with h1 | h1 | h1 <;>
    rcases hcases (r 2) with h2 | h2 | h2 <;>
    norm_num [e6DepthProfile, Fin.sum_univ_three, h0, h1, h2,
      h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12]

lemma e6GaussianProfile_bijective (a b : ℝ) {r : Fin 3 → ZMod 3}
    (hr : Function.Bijective r) (s : ZMod 3) : e6GaussianProfile a b r s=a*b^2 := by
  have h := (bijective_fin3_zmod3_iff r).mp hr
  have hcases : ∀ x : ZMod 3, x=0 ∨ x=1 ∨ x=2 := by decide
  have h01 : (0 : ZMod 3) ≠ 1 := by decide
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  rcases hcases (r 0) with h0 | h0 | h0 <;>
    rcases hcases (r 1) with h1 | h1 | h1 <;>
    rcases hcases (r 2) with h2 | h2 | h2 <;>
    rcases hcases s with rfl | rfl | rfl <;>
    simp_all [e6GaussianProfile, Fin.prod_univ_three, pow_two,
      h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12,
      mul_comm, mul_left_comm, mul_assoc]

end PaperVerification.ColdSpots
end
end Source_E6Phases
-- END ORIGINAL PaperVerification.E6Phases


-- BEGIN ORIGINAL PaperVerification.FiniteThree
section Source_FiniteThree

-- original header: module

-- original header: public import Mathlib.Data.ZMod.Basic
-- original header: public import Mathlib.Algebra.BigOperators.Fin
-- original header: public import Mathlib.Tactic.NormNum

-- original header: @[expose] public section
namespace PaperVerification.ColdSpots

open scoped BigOperators

theorem sum_zmod_three {M : Type*} [AddCommMonoid M] (f : ZMod 3 → M) :
    (∑ r, f r)=f 0+f 1+f 2 := by
  have h : (Finset.univ : Finset (ZMod 3))={0,1,2} := by decide
  have h0 : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3)) := by decide
  have h1 : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3)) := by decide
  rw [h, Finset.sum_insert h0, Finset.sum_insert h1, Finset.sum_singleton, add_assoc]

theorem prod_zmod_three {M : Type*} [CommMonoid M] (f : ZMod 3 → M) :
    (∏ r, f r)=f 0*f 1*f 2 := by
  have h : (Finset.univ : Finset (ZMod 3))={0,1,2} := by decide
  have h0 : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3)) := by decide
  have h1 : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3)) := by decide
  rw [h, Finset.prod_insert h0, Finset.prod_insert h1, Finset.prod_singleton, mul_assoc]

end PaperVerification.ColdSpots
end Source_FiniteThree
-- END ORIGINAL PaperVerification.FiniteThree


-- BEGIN ORIGINAL PaperVerification.E6Geometry
section Source_E6Geometry

-- original header: module

-- original header: public import PaperVerification.E6Phases
-- original header: public import PaperVerification.FiniteThree

-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

lemma triangularDepth_neg_two_shift (z : TriPoint) :
    triangularDepth (z-(2:ℝ)•triC)=triangularDepth (z+triC) := by
  have he : z-(2:ℝ)•triC=(z+triC)+eisEmbed (-1,1) := by
    ext <;> dsimp [triC,eisEmbed] <;> ring
  rw [he,triangularDepth_periodic]

theorem sum_triangular_depth_phases (z : TriPoint) :
    (∑ r : ZMod 3, triangularDepth (z-triPhasePoint r))=triangularDepthSum z := by
  rw [sum_zmod_three]
  norm_num [triPhasePoint,triangularDepth_neg_two_shift,triangularDepthSum,
    add_assoc,add_comm,add_left_comm]

theorem l6CosetDepth_sum (z : TriTriple) :
    l6CosetDepth z 0+l6CosetDepth z 1+l6CosetDepth z 2 =
      triangularDepthSum (z 0)+triangularDepthSum (z 1)+triangularDepthSum (z 2) := by
  rw [← sum_zmod_three]
  unfold l6CosetDepth
  rw [Finset.sum_comm]
  change (∑ i, ∑ r : ZMod 3, triangularDepth (z i-triPhasePoint r))=_
  simp only [sum_triangular_depth_phases]
  simp [Fin.sum_univ_succ,add_assoc]

theorem l6Depth_cosets (z : TriTriple) :
    l6Depth z=min (l6CosetDepth z 0) (min (l6CosetDepth z 1) (l6CosetDepth z 2)) := by
  apply le_antisymm
  · exact le_min (l6Depth_le_cosetDepth z 0)
      (le_min (l6Depth_le_cosetDepth z 1) (l6Depth_le_cosetDepth z 2))
  · apply le_csInf (Set.range_nonempty _)
    rintro t ⟨⟨r,m⟩,rfl⟩
    have hmin : min (l6CosetDepth z 0) (min (l6CosetDepth z 1) (l6CosetDepth z 2)) ≤
        l6CosetDepth z r := by
      fin_cases r
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (min_le_left _ _)
      · exact (min_le_right _ _).trans (min_le_right _ _)
    apply hmin.trans
    apply Finset.sum_le_sum
    intro i hi
    have h := triangularDepth_le (z i-(r.val:ℝ)•triC) (m i)
    convert h using 1
    congr 1
    dsimp [l6Point]
    abel

theorem l6Depth_upper (z : TriTriple) : l6Depth z ≤ 2/3 := by
  have h0 := l6Depth_le_cosetDepth z 0
  have h1 := l6Depth_le_cosetDepth z 1
  have h2 := l6Depth_le_cosetDepth z 2
  have hs := l6CosetDepth_sum z
  have h0' := triangularDepthSum_upper (z 0)
  have h1' := triangularDepthSum_upper (z 1)
  have h2' := triangularDepthSum_upper (z 2)
  linarith

theorem l6Depth_equality_iff (z : TriTriple) : l6Depth z=2/3 ↔ E6BalancedPhases z := by
  constructor
  · intro hz
    have h0 := l6Depth_le_cosetDepth z 0
    have h1 := l6Depth_le_cosetDepth z 1
    have h2 := l6Depth_le_cosetDepth z 2
    have hs := l6CosetDepth_sum z
    have h0' := triangularDepthSum_upper (z 0)
    have h1' := triangularDepthSum_upper (z 1)
    have h2' := triangularDepthSum_upper (z 2)
    have hp : ∀ i, TriPhase (z i) := by
      intro i
      apply (triangularDepthSum_eq_iff _).mp
      fin_cases i
      · change triangularDepthSum (z 0)=2/3
        linarith
      · change triangularDepthSum (z 1)=2/3
        linarith
      · change triangularDepthSum (z 2)=2/3
        linarith
    obtain ⟨r,hr⟩ := (exists_E6PhaseConfiguration_iff z).mpr hp
    have he : e6DepthProfile r 0=2/3 ∧ e6DepthProfile r 1=2/3 ∧ e6DepthProfile r 2=2/3 := by
      rw [← l6CosetDepth_of_phases hr 0,← l6CosetDepth_of_phases hr 1,
        ← l6CosetDepth_of_phases hr 2]
      exact ⟨by linarith,by linarith,by linarith⟩
    exact ⟨r,(e6DepthProfile_eq_iff r).mp he,hr⟩
  · rintro ⟨r,hr,hz⟩
    have he := (e6DepthProfile_eq_iff r).mpr hr
    rw [l6Depth_cosets,l6CosetDepth_of_phases hz 0,l6CosetDepth_of_phases hz 1,
      l6CosetDepth_of_phases hz 2,he.1,he.2.1,he.2.2,min_self,min_self]

def e6HoleWitness : TriTriple := ![0,triC,-triC]

theorem e6HoleWitness_balanced : E6BalancedPhases e6HoleWitness := by
  let r : Fin 3 → ZMod 3 := ![0,1,2]
  have hr : Function.Bijective r := by
    rw [bijective_fin3_zmod3_iff]
    change (0 : ZMod 3) ≠ 1 ∧ (0 : ZMod 3) ≠ 2 ∧ (1 : ZMod 3) ≠ 2
    decide
  refine ⟨r,hr,![0,0,(-1,1)],?_⟩
  intro i
  fin_cases i <;> ext <;> norm_num [e6HoleWitness,r,triPhasePoint,eisEmbed,triC]

theorem l6Depth_witness : l6Depth e6HoleWitness=2/3 :=
  (l6Depth_equality_iff _).mpr e6HoleWitness_balanced

theorem isL6DeepHole_iff (z : TriTriple) : IsL6DeepHole z ↔ E6BalancedPhases z := by
  rw [← l6Depth_equality_iff]
  constructor
  · intro h
    have hw := h e6HoleWitness
    rw [l6Depth_witness] at hw
    exact le_antisymm (l6Depth_upper z) hw
  · intro h w
    rw [h]
    exact l6Depth_upper w

end PaperVerification.ColdSpots
end
end Source_E6Geometry
-- END ORIGINAL PaperVerification.E6Geometry


-- BEGIN ORIGINAL PaperVerification.E6Polarization
section Source_E6Polarization

-- original header: module

-- original header: public import PaperVerification.E6Phases
-- original header: public import PaperVerification.FiniteThree

-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def l6GaussianTerm (α : ℝ) (z : TriTriple) (r : ZMod 3) : ℝ :=
  ∏ i, triangularGaussian α (z i-triPhasePoint r)

lemma l6GaussianTerm_pos {α : ℝ} (hα : 0 < α) (z : TriTriple) (r : ZMod 3) :
    0 < l6GaussianTerm α z r := Finset.prod_pos (fun i hi ↦ triangularGaussian_pos hα _)

lemma triangularGaussian_neg_two_shift (α : ℝ) (z : TriPoint) :
    triangularGaussian α (z-(2:ℝ)•triC)=triangularGaussian α (z+triC) := by
  have he : z-(2:ℝ)•triC=(z+triC)+eisEmbed (-1,1) := by
    ext <;> dsimp [triC,eisEmbed] <;> ring
  rw [he,triangularGaussian_periodic]

lemma prod_triangular_gaussian_phases (α : ℝ) (z : TriPoint) :
    (∏ r : ZMod 3, triangularGaussian α (z-triPhasePoint r))=triangularProduct α z := by
  rw [prod_zmod_three]
  norm_num [triPhasePoint,triangularGaussian_neg_two_shift,triangularProduct,mul_assoc,mul_comm,mul_left_comm]

theorem l6GaussianTerm_product (α : ℝ) (z : TriTriple) :
    l6GaussianTerm α z 0*l6GaussianTerm α z 1*l6GaussianTerm α z 2 =
      triangularProduct α (z 0)*triangularProduct α (z 1)*triangularProduct α (z 2) := by
  rw [← prod_zmod_three]
  unfold l6GaussianTerm
  rw [Finset.prod_comm]
  simp only [prod_triangular_gaussian_phases]
  simp [Fin.prod_univ_succ,mul_assoc]

theorem l6Gaussian_sum_terms {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    l6Gaussian α z=l6GaussianTerm α z 0+l6GaussianTerm α z 1+l6GaussianTerm α z 2 := by
  rw [l6Gaussian_cosets hα,sum_zmod_three]
  rfl

lemma three_product_lower (K x y z : ℝ) (hK : 0 < K) (hx : K ≤ x) (hy : K ≤ y) (hz : K ≤ z) :
    K^3 ≤ x*y*z := by
  have hxy : K*K ≤ x*y := mul_le_mul hx hy hK.le (hK.le.trans hx)
  have h := mul_le_mul hxy hz hK.le (mul_nonneg (hK.le.trans hx) (hK.le.trans hy))
  nlinarith only [h]

lemma three_product_equality (K x y z : ℝ) (hK : 0 < K)
    (hx : K ≤ x) (hy : K ≤ y) (hz : K ≤ z) (he : x*y*z=K^3) :
    x=K ∧ y=K ∧ z=K := by
  have hp : 0 < K*K := mul_pos hK hK
  have hX : x*K*K ≤ x*y*z := by
    have h := mul_le_mul_of_nonneg_left (mul_le_mul hy hz hK.le (hK.le.trans hy)) (hK.le.trans hx)
    simpa [mul_assoc] using h
  have hY : K*y*K ≤ x*y*z := by
    exact mul_le_mul (mul_le_mul_of_nonneg_right hx (hK.le.trans hy)) hz hK.le
      (mul_nonneg (hK.le.trans hx) (hK.le.trans hy))
  have hZ : K*K*z ≤ x*y*z := mul_le_mul_of_nonneg_right
    (mul_le_mul hx hy hK.le (hK.le.trans hx)) (hK.le.trans hz)
  refine ⟨le_antisymm ?_ hx,le_antisymm ?_ hy,le_antisymm ?_ hz⟩
  · apply (mul_le_mul_iff_of_pos_right hp).mp
    calc
      x*(K*K)=x*K*K := by ring
      _ ≤ x*y*z := hX
      _ = K^3 := he
      _ = K*(K*K) := by ring
  · apply (mul_le_mul_iff_of_pos_right hp).mp
    calc
      y*(K*K)=K*y*K := by ring
      _ ≤ x*y*z := hY
      _ = K^3 := he
      _ = K*(K*K) := by ring
  · apply (mul_le_mul_iff_of_pos_right hp).mp
    calc
      z*(K*K)=K*K*z := by ring
      _ ≤ x*y*z := hZ
      _ = K^3 := he
      _ = K*(K*K) := by ring

theorem l6Gaussian_lower {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    3*triangularGaussian α 0*triangularGaussian α triC^2 ≤ l6Gaussian α z := by
  let K := triangularGaussian α 0*triangularGaussian α triC^2
  have hK : 0 < K := mul_pos (triangularGaussian_pos hα _) (sq_pos_of_pos (triangularGaussian_pos hα _))
  have h0 := l6GaussianTerm_pos hα z 0
  have h1 := l6GaussianTerm_pos hα z 1
  have h2 := l6GaussianTerm_pos hα z 2
  have h := (three_term_amgm _ _ _ h0.le h1.le h2.le).1
  rw [l6GaussianTerm_product] at h
  have hp := three_product_lower K _ _ _ hK (triangularProduct_minimum hα (z 0))
    (triangularProduct_minimum hα (z 1)) (triangularProduct_minimum hα (z 2))
  rw [← l6Gaussian_sum_terms hα] at h
  have hs : 0 ≤ l6Gaussian α z := by rw [l6Gaussian_sum_terms hα]; positivity
  have hc : (3*K)^3 ≤ l6Gaussian α z^3 := by nlinarith only [h,hp]
  have hl : 3*K ≤ l6Gaussian α z := le_of_pow_le_pow_left₀ (by norm_num : (3:ℕ)≠0) hs hc
  dsimp [K] at hl
  nlinarith only [hl]

theorem l6Gaussian_equality_iff {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    l6Gaussian α z=3*triangularGaussian α 0*triangularGaussian α triC^2 ↔
      E6BalancedPhases z := by
  constructor
  · intro heq
    let a := triangularGaussian α 0
    let b := triangularGaussian α triC
    let K := a*b^2
    have ha : 0 < a := triangularGaussian_pos hα _
    have hb : 0 < b := triangularGaussian_pos hα _
    have hK : 0 < K := by dsimp [K]; positivity
    have h0 := l6GaussianTerm_pos hα z 0
    have h1 := l6GaussianTerm_pos hα z 1
    have h2 := l6GaussianTerm_pos hα z 2
    have ham := (three_term_amgm _ _ _ h0.le h1.le h2.le)
    have hp := three_product_lower K _ _ _ hK (triangularProduct_minimum hα (z 0))
      (triangularProduct_minimum hα (z 1)) (triangularProduct_minimum hα (z 2))
    have hsum : l6GaussianTerm α z 0+l6GaussianTerm α z 1+l6GaussianTerm α z 2=3*K := by
      rw [← l6Gaussian_sum_terms hα,heq]
      dsimp [K,a,b]
      ring
    have hprod : triangularProduct α (z 0)*triangularProduct α (z 1)*triangularProduct α (z 2)=K^3 := by
      have hh := ham.1
      rw [hsum,l6GaussianTerm_product] at hh
      nlinarith only [hh,hp]
    have heach := three_product_equality K _ _ _ hK (triangularProduct_minimum hα (z 0))
      (triangularProduct_minimum hα (z 1)) (triangularProduct_minimum hα (z 2)) hprod
    have hph : ∀ i, TriPhase (z i) := by
      intro i
      apply (triangularProduct_equality_iff hα _).mp
      fin_cases i
      · exact heach.1
      · exact heach.2.1
      · exact heach.2.2
    obtain ⟨r,hr⟩ := (exists_E6PhaseConfiguration_iff z).mpr hph
    have heterms : l6GaussianTerm α z 0=l6GaussianTerm α z 1 ∧
        l6GaussianTerm α z 1=l6GaussianTerm α z 2 := by
      apply ham.2.mp
      rw [hsum,l6GaussianTerm_product,hprod]
      ring
    have ht (s : ZMod 3) : l6GaussianTerm α z s=e6GaussianProfile a b r s := by
      obtain ⟨m,hm⟩ := hr
      apply Finset.prod_congr rfl
      intro i hi
      rw [hm i,show eisEmbed (m i)+triPhasePoint (r i)-triPhasePoint s =
        (triPhasePoint (r i)-triPhasePoint s)+eisEmbed (m i) by abel,
        triangularGaussian_periodic,triangularGaussian_phases hα]
    simp only [ht] at heterms
    exact ⟨r,(e6GaussianProfile_eq_iff a b hb (triangularGaussian_c_lt_zero hα) r).mp heterms,hr⟩
  · rintro ⟨r,hr,hz⟩
    rw [l6Gaussian_of_phases hα hz]
    simp only [e6GaussianProfile_bijective _ _ hr,Finset.sum_const,Finset.card_univ,
      ZMod.card,nsmul_eq_mul]
    ring

end PaperVerification.ColdSpots
end
end Source_E6Polarization
-- END ORIGINAL PaperVerification.E6Polarization


-- BEGIN ORIGINAL PaperVerification.E6UnscaledTheorems
section Source_E6UnscaledTheorems

-- original header: module

-- original header: public import PaperVerification.E6Geometry
-- original header: public import PaperVerification.E6Polarization

-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

theorem l6Gaussian_witness {α : ℝ} (hα : 0 < α) :
    l6Gaussian α e6HoleWitness=3*triangularGaussian α 0*triangularGaussian α triC^2 :=
  (l6Gaussian_equality_iff hα _).mpr e6HoleWitness_balanced

theorem isL6ColdSpot_iff {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    IsL6ColdSpot α z ↔ E6BalancedPhases z := by
  rw [← l6Gaussian_equality_iff hα]
  constructor
  · intro h
    have hw := h e6HoleWitness
    rw [l6Gaussian_witness hα] at hw
    exact le_antisymm hw (l6Gaussian_lower hα z)
  · intro h w
    rw [h]
    exact l6Gaussian_lower hα w

theorem coldSpot_L6_iff_deepHole {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    IsL6ColdSpot α z ↔ IsL6DeepHole z := by
  rw [isL6ColdSpot_iff hα,isL6DeepHole_iff]

end PaperVerification.ColdSpots
end
end Source_E6UnscaledTheorems
-- END ORIGINAL PaperVerification.E6UnscaledTheorems


-- BEGIN ORIGINAL PaperVerification.LatticeScaling
section Source_LatticeScaling

-- original header: module

-- original header: public import PaperVerification.LatticeTranslations

-- original header: @[expose] public section
/-! # Similarities of actual Gaussian lattice sums and depth

These lemmas work with arbitrary nonempty subsets of Euclidean coordinate space.
They justify the normalization changes without modifying the Gaussian parameter
or the geometric meaning silently.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

variable {n : ℕ}

def scaleVec (c : ℝ) (x : Fin n → ℝ) : Fin n → ℝ := fun i => c * x i

def scaledSet (c : ℝ) (L : Set (Fin n → ℝ)) : Set (Fin n → ℝ) := scaleVec c '' L

theorem scaleVec_inv (c : ℝ) (hc : c ≠ 0) (x : Fin n → ℝ) :
    scaleVec c (scaleVec c⁻¹ x) = x := by
  funext i
  simp [scaleVec, hc, mul_assoc]

theorem scaleVec_injective (c : ℝ) (hc : c ≠ 0) : Function.Injective (@scaleVec n c) := by
  intro x y h
  funext i
  exact mul_left_cancel₀ hc (congrFun h i)

theorem sqDist_scaleVec (c : ℝ) (x y : Fin n → ℝ) :
    sqDist (scaleVec c x) (scaleVec c y) = c ^ 2 * sqDist x y := by
  simp only [sqDist, scaleVec, ← mul_sub, mul_pow, Finset.mul_sum]

def scaledSetEquiv (c : ℝ) (hc : c ≠ 0) (L : Set (Fin n → ℝ)) : L ≃ scaledSet c L :=
  Equiv.ofBijective (fun z => ⟨scaleVec c z.val, z.val, z.property, rfl⟩)
    ⟨fun x y h => Subtype.ext (scaleVec_injective c hc (congrArg Subtype.val h)), by
      rintro ⟨z, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩⟩

theorem setGaussian_scaled (c : ℝ) (hc : c ≠ 0) (L : Set (Fin n → ℝ))
    (α : ℝ) (x : Fin n → ℝ) :
    setGaussian (scaledSet c L) α (scaleVec c x) = setGaussian L (α * c ^ 2) x := by
  calc
    _ = ∑' z : L, Real.exp (-α * sqDist (scaleVec c z.val) (scaleVec c x)) :=
      ((scaledSetEquiv c hc L).tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro z
      rw [sqDist_scaleVec]
      congr 1
      ring

theorem summable_scaled_iff (c : ℝ) (hc : c ≠ 0) (L : Set (Fin n → ℝ))
    (α : ℝ) (x : Fin n → ℝ) :
    Summable (fun z : scaledSet c L => Real.exp (-α * sqDist z.val (scaleVec c x))) ↔
      Summable (fun z : L => Real.exp (-(α * c ^ 2) * sqDist z.val x)) := by
  rw [← (scaledSetEquiv c hc L).summable_iff]
  have he : (fun z : L => Real.exp (-α * sqDist
      ((scaledSetEquiv c hc L) z).val (scaleVec c x))) =
      fun z : L => Real.exp (-(α * c ^ 2) * sqDist z.val x) := by
    funext z
    change Real.exp (-α * sqDist (scaleVec c z.val) (scaleVec c x)) = _
    rw [sqDist_scaleVec]
    congr 1
    ring
  dsimp only [Function.comp_def]
  rw [he]

theorem squaredDepth_scaled (c : ℝ) (hc : c ≠ 0) (L : Set (Fin n → ℝ))
    (hL : L.Nonempty) (x : Fin n → ℝ) :
    squaredDepth (scaledSet c L) (scaleVec c x) = c ^ 2 * squaredDepth L x := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  apply le_antisymm
  · have h : squaredDepth (scaledSet c L) (scaleVec c x) / c ^ 2 ≤ squaredDepth L x := by
      apply le_csInf (hL.image (fun z => sqDist x z))
      rintro r ⟨z, hz, rfl⟩
      apply (div_le_iff₀ hc2).mpr
      have hd := squaredDepth_le (scaleVec c x)
        (show scaleVec c z ∈ scaledSet c L from ⟨z, hz, rfl⟩)
      rw [sqDist_scaleVec] at hd
      simpa only [mul_comm] using hd
    have h' := (div_le_iff₀ hc2).mp h
    simpa only [mul_comm] using h'
  · apply le_csInf ((hL.image (scaleVec c)).image (fun z => sqDist (scaleVec c x) z))
    rintro r ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    change c ^ 2 * squaredDepth L x ≤ sqDist (scaleVec c x) (scaleVec c w)
    rw [sqDist_scaleVec]
    exact mul_le_mul_of_nonneg_left (squaredDepth_le x hw) hc2.le

theorem isColdSpot_scaled_iff (c : ℝ) (hc : c ≠ 0) (L : Set (Fin n → ℝ))
    (α : ℝ) (x : Fin n → ℝ) :
    IsColdSpot (scaledSet c L) α (scaleVec c x) ↔ IsColdSpot L (α * c ^ 2) x := by
  constructor
  · intro h y
    have hy := h (scaleVec c y)
    simpa only [setGaussian_scaled c hc] using hy
  · intro h y
    have hy := h (scaleVec c⁻¹ y)
    rw [← setGaussian_scaled c hc, ← setGaussian_scaled c hc, scaleVec_inv c hc y] at hy
    exact hy

theorem isDeepHole_scaled_iff (c : ℝ) (hc : c ≠ 0) (L : Set (Fin n → ℝ))
    (hL : L.Nonempty) (x : Fin n → ℝ) :
    IsDeepHole (scaledSet c L) (scaleVec c x) ↔ IsDeepHole L x := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  constructor
  · intro h y
    have hy := h (scaleVec c y)
    rw [squaredDepth_scaled c hc L hL, squaredDepth_scaled c hc L hL] at hy
    exact (mul_le_mul_iff_of_pos_left hc2).mp hy
  · intro h y
    have hy := mul_le_mul_of_nonneg_left (h (scaleVec c⁻¹ y)) hc2.le
    rw [← squaredDepth_scaled c hc L hL, ← squaredDepth_scaled c hc L hL,
      scaleVec_inv c hc y] at hy
    exact hy

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.setGaussian_scaled
#print axioms PaperVerification.ColdSpots.squaredDepth_scaled
end
end Source_LatticeScaling
-- END ORIGINAL PaperVerification.LatticeScaling


-- BEGIN ORIGINAL PaperVerification.E6Euclidean
section Source_E6Euclidean

-- original header: module

-- original header: public import PaperVerification.E6UnscaledTheorems
-- original header: public import PaperVerification.LatticeScaling
-- original header: public import Mathlib.Data.Fin.Basic

-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def triTripleFlatten (z : TriTriple) (j : Fin 6) : ℝ :=
  Fin.addCases (m:=3) (n:=3) (motive:=fun _ ↦ ℝ)
    (fun i : Fin 3 ↦ (z i).1-(z i).2/2)
    (fun i : Fin 3 ↦ Real.sqrt 3*(z i).2/2) j

def triTripleUnflatten (x : Fin 6 → ℝ) : TriTriple := fun i ↦
  (x (Fin.castAdd 3 i)+x (Fin.natAdd 3 i)/Real.sqrt 3,
    2*x (Fin.natAdd 3 i)/Real.sqrt 3)

theorem triTripleUnflatten_flatten (z : TriTriple) :
    triTripleUnflatten (triTripleFlatten z)=z := by
  have hs : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3)).ne'
  ext i <;> simp [triTripleUnflatten,triTripleFlatten,hs, -Fin.natAdd_eq_addNat] <;>
    field_simp <;> ring

theorem triTripleFlatten_unflatten (x : Fin 6 → ℝ) :
    triTripleFlatten (triTripleUnflatten x)=x := by
  have hs : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3)).ne'
  funext j
  refine Fin.addCases (m:=3) (n:=3) (fun i ↦ ?_) (fun i ↦ ?_) j
  all_goals
    simp [triTripleUnflatten,triTripleFlatten,hs, -Fin.natAdd_eq_addNat] <;>
      field_simp <;> ring

def triTripleEuclideanEquiv : TriTriple ≃ (Fin 6 → ℝ) where
  toFun := triTripleFlatten
  invFun := triTripleUnflatten
  left_inv := triTripleUnflatten_flatten
  right_inv := triTripleFlatten_unflatten

theorem triTripleFlatten_sqDist (z w : TriTriple) :
    sqDist (triTripleFlatten z) (triTripleFlatten w)=triTripleSqDist z w := by
  unfold sqDist triTripleSqDist
  rw [Fin.sum_univ_add (a:=3) (b:=3),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [triTripleFlatten,Fin.addCases_left,Fin.addCases_right]
  have h3 : Real.sqrt 3^2=(3:ℝ) := Real.sq_sqrt (by norm_num)
  dsimp [triQ]
  nlinarith only [congrArg (fun t : ℝ ↦ t*((z i).2-(w i).2)^2) h3]

def l6EuclideanSet : Set (Fin 6 → ℝ) := triTripleFlatten '' l6Set

theorem l6EuclideanSet_nonempty : l6EuclideanSet.Nonempty :=
  ⟨triTripleFlatten (l6Point (0,0)),l6Point (0,0),⟨(0,0),rfl⟩,rfl⟩

def l6EuclideanIndexEquiv : E6Index ≃ l6EuclideanSet :=
  Equiv.ofBijective (fun p ↦ ⟨triTripleFlatten (l6Point p),l6Point p,⟨p,rfl⟩,rfl⟩)
    ⟨fun p q h ↦ l6Point_injective (triTripleEuclideanEquiv.injective
      (congrArg Subtype.val h)),by
      rintro ⟨x,z,⟨p,rfl⟩,rfl⟩
      exact ⟨p,rfl⟩⟩

theorem setGaussian_l6Euclidean (α : ℝ) (z : TriTriple) :
    setGaussian l6EuclideanSet α (triTripleFlatten z)=l6Gaussian α z := by
  unfold setGaussian l6Gaussian
  rw [← l6EuclideanIndexEquiv.tsum_eq]
  apply tsum_congr
  intro p
  exact congrArg (fun t : ℝ ↦ Real.exp (-α*t)) (triTripleFlatten_sqDist (l6Point p) z)

theorem squaredDepth_l6Euclidean (z : TriTriple) :
    squaredDepth l6EuclideanSet (triTripleFlatten z)=l6Depth z := by
  unfold squaredDepth l6Depth
  congr 1
  ext t
  constructor
  · rintro ⟨x,⟨w,⟨p,rfl⟩,rfl⟩,rfl⟩
    refine ⟨p,?_⟩
    change triTripleSqDist (l6Point p) z =
      sqDist (triTripleFlatten z) (triTripleFlatten (l6Point p))
    rw [sqDist_comm,triTripleFlatten_sqDist]
  · rintro ⟨p,rfl⟩
    refine ⟨triTripleFlatten (l6Point p),⟨l6Point p,⟨p,rfl⟩,rfl⟩,?_⟩
    change sqDist (triTripleFlatten z) (triTripleFlatten (l6Point p)) =
      triTripleSqDist (l6Point p) z
    rw [sqDist_comm,triTripleFlatten_sqDist]

theorem isColdSpot_l6Euclidean_iff (α : ℝ) (z : TriTriple) :
    IsColdSpot l6EuclideanSet α (triTripleFlatten z) ↔ IsL6ColdSpot α z := by
  constructor
  · intro h w
    simpa only [setGaussian_l6Euclidean] using h (triTripleFlatten w)
  · intro h x
    obtain ⟨w,rfl⟩ := triTripleEuclideanEquiv.surjective x
    change setGaussian l6EuclideanSet α (triTripleFlatten z) ≤
      setGaussian l6EuclideanSet α (triTripleFlatten w)
    simpa only [setGaussian_l6Euclidean] using h w

theorem isDeepHole_l6Euclidean_iff (z : TriTriple) :
    IsDeepHole l6EuclideanSet (triTripleFlatten z) ↔ IsL6DeepHole z := by
  constructor
  · intro h w
    simpa only [squaredDepth_l6Euclidean] using h (triTripleFlatten w)
  · intro h x
    obtain ⟨w,rfl⟩ := triTripleEuclideanEquiv.surjective x
    change squaredDepth l6EuclideanSet (triTripleFlatten w) ≤
      squaredDepth l6EuclideanSet (triTripleFlatten z)
    simpa only [squaredDepth_l6Euclidean] using h w

/-- The root-normalized lattice √2(E³+ℤ(c,c,c)), in ordinary Euclidean R⁶. -/
def e6Set : Set (Fin 6 → ℝ) := scaledSet (Real.sqrt 2) l6EuclideanSet

def e6PhysicalPoint (z : TriTriple) : Fin 6 → ℝ := scaleVec (Real.sqrt 2) (triTripleFlatten z)

theorem e6PhysicalPoint_surjective : Function.Surjective e6PhysicalPoint := by
  intro x
  refine ⟨triTripleUnflatten (scaleVec (Real.sqrt 2)⁻¹ x),?_⟩
  rw [e6PhysicalPoint,triTripleFlatten_unflatten,scaleVec_inv _ (by positivity)]

theorem e6Gaussian_scale (α : ℝ) (z : TriTriple) :
    setGaussian e6Set α (e6PhysicalPoint z)=l6Gaussian (2*α) z := by
  unfold e6Set e6PhysicalPoint
  rw [setGaussian_scaled _ (by positivity),Real.sq_sqrt (by norm_num),setGaussian_l6Euclidean]
  congr 1
  ring

theorem e6Depth_scale (z : TriTriple) :
    squaredDepth e6Set (e6PhysicalPoint z)=2*l6Depth z := by
  unfold e6Set e6PhysicalPoint
  rw [squaredDepth_scaled _ (by positivity) _ l6EuclideanSet_nonempty,
    Real.sq_sqrt (by norm_num),squaredDepth_l6Euclidean]

theorem coldSpot_E6_iff_deepHole {α : ℝ} (hα : 0 < α) (x : Fin 6 → ℝ) :
    IsColdSpot e6Set α x ↔ IsDeepHole e6Set x := by
  obtain ⟨z,rfl⟩ := e6PhysicalPoint_surjective x
  unfold e6Set e6PhysicalPoint
  rw [isColdSpot_scaled_iff _ (by positivity),
    isDeepHole_scaled_iff _ (by positivity) _ l6EuclideanSet_nonempty,
    Real.sq_sqrt (by norm_num),isColdSpot_l6Euclidean_iff,isDeepHole_l6Euclidean_iff]
  exact coldSpot_L6_iff_deepHole (by positivity) z

theorem e6_covering_radius_squared (x : Fin 6 → ℝ) : squaredDepth e6Set x ≤ 4/3 := by
  obtain ⟨z,rfl⟩ := e6PhysicalPoint_surjective x
  rw [e6Depth_scale]
  have h := l6Depth_upper z
  linarith

theorem e6_covering_radius_attained :
    squaredDepth e6Set (e6PhysicalPoint e6HoleWitness)=4/3 := by
  rw [e6Depth_scale,l6Depth_witness]
  norm_num

theorem e6_gaussian_minimum {α : ℝ} (hα : 0 < α) :
    (∀ x, 3*triangularGaussian (2*α) 0*triangularGaussian (2*α) triC^2 ≤
      setGaussian e6Set α x) ∧
    setGaussian e6Set α (e6PhysicalPoint e6HoleWitness)=
      3*triangularGaussian (2*α) 0*triangularGaussian (2*α) triC^2 := by
  constructor
  · intro x
    obtain ⟨z,rfl⟩ := e6PhysicalPoint_surjective x
    rw [e6Gaussian_scale]
    exact l6Gaussian_lower (by positivity) z
  · rw [e6Gaussian_scale]
    exact l6Gaussian_witness (by positivity)

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.coldSpot_E6_iff_deepHole
#print axioms PaperVerification.ColdSpots.e6_gaussian_minimum
end
end Source_E6Euclidean
-- END ORIGINAL PaperVerification.E6Euclidean


-- BEGIN ORIGINAL PaperVerification.E6Roots
section Source_E6Roots

-- original header: module

-- original header: public import PaperVerification.E6Euclidean
-- original header: public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def l6SimpleRoot : Fin 6 → TriTriple :=
  ![(fun _ ↦ -triC),![(1,0),0,0],![(-1,-1),0,0],
    ![0,(1,0),0],![0,(-1,-1),0],![0,0,(1,0)]]

def e6SimpleRoot (j : Fin 6) : Fin 6 → ℝ := e6PhysicalPoint (l6SimpleRoot j)

def l6RootSum (t : Fin 6 → ℝ) : TriTriple := ∑ j,t j•l6SimpleRoot j

def l6RootCoordinates (z : TriTriple) : Fin 6 → ℝ :=
  ![3*(z 2).2,(z 0).1+2*(z 2).2-(z 0).2,(z 2).2-(z 0).2,
    (z 1).1+2*(z 2).2-(z 1).2,(z 2).2-(z 1).2,(z 2).1+(z 2).2]

theorem l6RootCoordinates_sum (t : Fin 6 → ℝ) : l6RootCoordinates (l6RootSum t)=t := by
  ext i
  fin_cases i <;> simp [l6RootCoordinates,l6RootSum,l6SimpleRoot,triC,Fin.sum_univ_succ] <;> ring

theorem l6RootSum_coordinates (z : TriTriple) : l6RootSum (l6RootCoordinates z)=z := by
  ext i <;> fin_cases i <;>
    simp [l6RootCoordinates,l6RootSum,l6SimpleRoot,triC,Fin.sum_univ_succ] <;> ring

theorem l6RootSum_injective : Function.Injective l6RootSum :=
  Function.LeftInverse.injective l6RootCoordinates_sum

def triDot (z w : TriPoint) : ℝ := z.1*w.1-(z.1*w.2+z.2*w.1)/2+z.2*w.2

theorem triTripleFlatten_dot (z w : TriTriple) :
    (∑ i, triTripleFlatten z i*triTripleFlatten w i)=∑ i, triDot (z i) (w i) := by
  rw [Fin.sum_univ_add (a:=3) (b:=3),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [triTripleFlatten,Fin.addCases_left,Fin.addCases_right]
  have h3 : Real.sqrt 3^2=(3:ℝ) := Real.sq_sqrt (by norm_num)
  dsimp [triDot]
  nlinarith only [congrArg (fun t : ℝ ↦ t*(z i).2*(w i).2) h3]

theorem e6PhysicalPoint_dot (z w : TriTriple) :
    (∑ i, e6PhysicalPoint z i*e6PhysicalPoint w i)=2*∑ i, triDot (z i) (w i) := by
  have hs : Real.sqrt 2^2=(2:ℝ) := Real.sq_sqrt (by norm_num)
  unfold e6PhysicalPoint scaleVec
  have he (i : Fin 6) : Real.sqrt 2*triTripleFlatten z i*(Real.sqrt 2*triTripleFlatten w i)=
      2*(triTripleFlatten z i*triTripleFlatten w i) := by
    have h := congrArg (fun t : ℝ ↦ t*(triTripleFlatten z i*triTripleFlatten w i)) hs
    nlinarith only [h]
  simp_rw [he]
  rw [← Finset.mul_sum,triTripleFlatten_dot]

def e6Cartan : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2,-1,0,-1,0,-1;
     -1,2,-1,0,0,0;
     0,-1,2,0,0,0;
     -1,0,0,2,-1,0;
     0,0,0,-1,2,0;
     -1,0,0,0,0,2]

/-- The displayed simple roots have exactly the E₆ Cartan Gram matrix,
with arms of lengths two, two, and one and root norm squared two. -/
theorem e6SimpleRoot_gram (i j : Fin 6) :
    (∑ k, e6SimpleRoot i k*e6SimpleRoot j k)=(e6Cartan i j : ℝ) := by
  rw [show e6SimpleRoot i=e6PhysicalPoint (l6SimpleRoot i) from rfl,
    show e6SimpleRoot j=e6PhysicalPoint (l6SimpleRoot j) from rfl,e6PhysicalPoint_dot]
  fin_cases i <;> fin_cases j <;>
    norm_num [l6SimpleRoot,e6Cartan,triDot,triC,Fin.sum_univ_succ]

theorem l6Set_simpleRoot_span (z : TriTriple) : z ∈ l6Set ↔
    ∃ t : Fin 6 → ℤ, z=∑ j, (t j : ℝ)•l6SimpleRoot j := by
  rw [l6Set_iff_integer_glue]
  constructor
  · rintro ⟨m,k,hm⟩
    let t : Fin 6 → ℤ := ![3*(m 2).2-k,
      (m 0).1+2*(m 2).2-(m 0).2,(m 2).2-(m 0).2,
      (m 1).1+2*(m 2).2-(m 1).2,(m 2).2-(m 1).2,(m 2).1+(m 2).2]
    refine ⟨t,?_⟩
    ext i <;> rw [hm i] <;> fin_cases i <;>
      simp [t,l6SimpleRoot,Fin.sum_univ_succ,triC,eisEmbed] <;> ring
  · rintro ⟨t,rfl⟩
    let m : Fin 3 → EisInt := ![(t 1-t 2,-t 2),(t 3-t 4,-t 4),(t 5,0)]
    refine ⟨m,-t 0,?_⟩
    intro i
    fin_cases i <;> ext <;> simp [m,l6SimpleRoot,Fin.sum_univ_succ,triC,eisEmbed] <;> ring

lemma e6PhysicalPoint_sum_smul (t : Fin 6 → ℤ) (v : Fin 6 → TriTriple) :
    e6PhysicalPoint (∑ j, (t j : ℝ)•v j)=∑ j, (t j : ℝ)•e6PhysicalPoint (v j) := by
  funext i
  refine Fin.addCases (m:=3) (n:=3) (fun k ↦ ?_) (fun k ↦ ?_) i
  · simp only [e6PhysicalPoint,scaleVec,triTripleFlatten,Finset.sum_apply,
      Pi.smul_apply,Fin.addCases_left,Prod.fst_sum,Prod.snd_sum,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    rw [Finset.sum_div,← Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · simp only [e6PhysicalPoint,scaleVec,triTripleFlatten,Finset.sum_apply,
      Pi.smul_apply,Fin.addCases_right,Prod.snd_sum,Prod.smul_snd,smul_eq_mul]
    rw [Finset.mul_sum,Finset.sum_div,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

/-- This identifies the coordinate lattice with the integer lattice generated
by the actual E₆ simple roots, not merely an isospectral construction. -/
theorem e6Set_simpleRoot_span (x : Fin 6 → ℝ) : x ∈ e6Set ↔
    ∃ t : Fin 6 → ℤ, x=∑ j, (t j : ℝ)•e6SimpleRoot j := by
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    obtain ⟨t,rfl⟩ := (l6Set_simpleRoot_span z).mp hz
    exact ⟨t,e6PhysicalPoint_sum_smul t l6SimpleRoot⟩
  · rintro ⟨t,rfl⟩
    refine ⟨triTripleFlatten (∑ j, (t j : ℝ)•l6SimpleRoot j),
      ⟨_,(l6Set_simpleRoot_span _).mpr ⟨t,rfl⟩,rfl⟩,?_⟩
    exact e6PhysicalPoint_sum_smul t l6SimpleRoot

end PaperVerification.ColdSpots
end
end Source_E6Roots
-- END ORIGINAL PaperVerification.E6Roots


-- BEGIN ORIGINAL PaperVerification.E6Normalization
section Source_E6Normalization

-- original header: module

-- original header: public import PaperVerification.E6Roots

-- original header: @[expose] public section

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

theorem triQ_integer_nonzero {m : EisInt} (hm : m≠0) : 1 ≤ triQ (eisEmbed m) := by
  let q : ℤ := m.1^2-m.1*m.2+m.2^2
  have hq : triQ (eisEmbed m)=(q:ℝ) := by dsimp [q,triQ,eisEmbed]; push_cast; ring
  have hp : 0 < triQ (eisEmbed m) := by
    apply lt_of_le_of_ne (triQ_nonneg _)
    intro hz
    have hl := triQ_lower (eisEmbed m)
    rw [← hz] at hl
    have h1 : (m.1:ℝ)=0 := by
      dsimp [eisEmbed] at hl
      nlinarith [sq_nonneg (m.1:ℝ),sq_nonneg (m.2:ℝ)]
    have h2 : (m.2:ℝ)=0 := by
      dsimp [eisEmbed] at hl
      nlinarith [sq_nonneg (m.1:ℝ),sq_nonneg (m.2:ℝ)]
    apply hm
    apply Prod.ext
    · exact_mod_cast h1
    · exact_mod_cast h2
  have hi : 0 < q := by rw [hq] at hp; exact_mod_cast hp
  have hi' : (1:ℤ) ≤ q := by omega
  rw [hq]
  exact_mod_cast hi'

theorem l6_minimal_squared_norm {z : TriTriple} (hz : z ∈ l6Set) (hne : z≠0) :
    1 ≤ triTripleSqDist z 0 := by
  obtain ⟨⟨r,m⟩,rfl⟩ := hz
  by_cases hr : r=0
  · subst r
    have hm : ∃ i, m i≠0 := by
      by_contra h
      push_neg at h
      apply hne
      funext i
      simp [l6Point,h i]
    obtain ⟨i,hi⟩ := hm
    have ht := triQ_integer_nonzero hi
    have hs : triQ (eisEmbed (m i)) ≤ ∑ j, triQ (eisEmbed (m j)) :=
      Finset.single_le_sum (fun j hj ↦ triQ_nonneg (eisEmbed (m j))) (Finset.mem_univ i)
    simpa [triTripleSqDist,l6Point] using ht.trans hs
  · have hb (i : Fin 3) : 1/3 ≤ triQ (l6Point (r,m) i) := by
      fin_cases r
      · exact (hr rfl).elim
      · have h := triangularDepth_le (-triC) (m i)
        rw [triangularDepth_even,triangularDepth_c] at h
        change 1/3 ≤ triQ (l6Point ((1 : ZMod 3),m) i)
        simp only [l6Point,zmodThree_val_one,Nat.cast_one,one_smul]
        simpa only [sub_neg_eq_add] using h
      · have he : eisEmbed (m i)+(2:ℝ)•triC=eisEmbed (m i+(1,-1))-triC := by
          rw [map_add]
          ext <;> dsimp [eisEmbed,triC] <;> ring
        have h := triangularDepth_le triC (m i+(1,-1))
        rw [triangularDepth_c] at h
        change 1/3 ≤ triQ (l6Point ((2 : ZMod 3),m) i)
        simp only [l6Point,zmodThree_val_two,Nat.cast_ofNat]
        rw [he]
        exact h
    have hs := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 3))) ↦ hb i)
    norm_num [triTripleSqDist] at hs ⊢
    exact hs

theorem e6PhysicalPoint_sqDist (z w : TriTriple) :
    sqDist (e6PhysicalPoint z) (e6PhysicalPoint w)=2*triTripleSqDist z w := by
  rw [e6PhysicalPoint,e6PhysicalPoint,sqDist_scaleVec,
    Real.sq_sqrt (by norm_num),triTripleFlatten_sqDist]

theorem e6PhysicalPoint_zero : e6PhysicalPoint 0=0 := by
  funext j
  refine Fin.addCases (m:=3) (n:=3) (fun i ↦ ?_) (fun i ↦ ?_) j <;>
    simp [e6PhysicalPoint,scaleVec,triTripleFlatten, -Fin.natAdd_eq_addNat]

/-- The lattice normalization in Theorem 1.1 has minimum squared norm exactly two. -/
theorem e6_minimal_squared_norm :
    (∀ x ∈ e6Set, x≠0 → 2 ≤ sqDist x 0) ∧
      e6SimpleRoot 1 ∈ e6Set ∧ sqDist (e6SimpleRoot 1) 0=2 := by
  constructor
  · rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩ hne
    have hzn : z≠0 := by intro h; subst z; exact hne e6PhysicalPoint_zero
    have h := l6_minimal_squared_norm hz hzn
    change 2 ≤ sqDist (e6PhysicalPoint z) 0
    rw [← e6PhysicalPoint_zero,e6PhysicalPoint_sqDist]
    linarith
  · constructor
    · apply (e6Set_simpleRoot_span _).mpr
      refine ⟨Pi.single 1 1,?_⟩
      simp [Pi.single_apply]
    · have h := e6SimpleRoot_gram 1 1
      simpa [sqDist,pow_two,e6Cartan] using h

end PaperVerification.ColdSpots
end
end Source_E6Normalization
-- END ORIGINAL PaperVerification.E6Normalization


-- BEGIN ORIGINAL PaperVerification.E6HoleDescription
section Source_E6HoleDescription

-- original header: module

-- original header: public import PaperVerification.E6Roots

-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

def phaseIndexEquiv : Fin 3 ≃ ZMod 3 :=
  Equiv.ofBijective (fun i : Fin 3 ↦ (i.val : ZMod 3)) (by decide)

def e6WitnessCorrection : Fin 3 → EisInt := ![0,0,(-1,1)]

theorem e6HoleWitness_phase (i : Fin 3) :
    e6HoleWitness i=eisEmbed (e6WitnessCorrection i)+triPhasePoint (phaseIndexEquiv i) := by
  fin_cases i <;> ext <;> norm_num [e6HoleWitness,e6WitnessCorrection,triPhasePoint,
    phaseIndexEquiv,eisEmbed,triC]

theorem triPhase_add_integer (r : ZMod 3) (k : ℤ) :
    ∃ m : EisInt, triPhasePoint r+(k:ℝ)•triC =
      eisEmbed m+triPhasePoint (r+(k:ZMod 3)) := by
  let s : ZMod 3 := r+(k:ZMod 3)
  let q : ℤ := ((r.val:ℤ)+k)/3
  have hs : (s.val:ℤ)=((r.val:ℤ)+k)%3 := by
    have h := ZMod.val_intCast (n:=3) ((r.val:ℤ)+k)
    simpa [s] using h
  have hk : (r.val:ℤ)+k=(s.val:ℤ)+3*q := by dsimp [q]; omega
  refine ⟨q•(1,-1),?_⟩
  rw [eisEmbed_zsmul]
  have hkr : (r.val:ℝ)+(k:ℝ)=(s.val:ℝ)+3*(q:ℝ) := by exact_mod_cast hk
  ext <;> dsimp [triPhasePoint,triC,eisEmbed] <;> nlinarith only [hkr]

def E6PaperHole (z : TriTriple) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), ∃ l : TriTriple, l ∈ l6Set ∧
    ∀ i, z i=e6HoleWitness (σ i)+l i

theorem e6BalancedPhases_iff_paper (z : TriTriple) : E6BalancedPhases z ↔ E6PaperHole z := by
  constructor
  · rintro ⟨r,hr,m,hm⟩
    let σ : Equiv.Perm (Fin 3) := (Equiv.ofBijective r hr).trans phaseIndexEquiv.symm
    have hσ (i : Fin 3) : phaseIndexEquiv (σ i)=r i := by simp [σ]
    let v : Fin 3 → EisInt := fun i ↦ m i-e6WitnessCorrection (σ i)
    refine ⟨σ,fun i ↦ eisEmbed (v i),?_,?_⟩
    · apply (l6Set_iff_integer_glue _).mpr
      exact ⟨v,0,by intro i; simp⟩
    · intro i
      rw [hm i,e6HoleWitness_phase,hσ]
      dsimp [v]
      rw [map_sub]
      abel
  · rintro ⟨σ,l,hl,hz⟩
    obtain ⟨m,k,hm⟩ := (l6Set_iff_integer_glue l).mp hl
    let r : Fin 3 → ZMod 3 := fun i ↦ phaseIndexEquiv (σ i)+(k:ZMod 3)
    have hr : Function.Bijective r :=
      (Equiv.addRight (k:ZMod 3)).bijective.comp (phaseIndexEquiv.bijective.comp σ.bijective)
    have hex (i : Fin 3) := triPhase_add_integer (phaseIndexEquiv (σ i)) k
    choose v hv using hex
    refine ⟨r,hr,fun i ↦ e6WitnessCorrection (σ i)+m i+v i,?_⟩
    intro i
    rw [hz i,hm i,e6HoleWitness_phase]
    rw [show eisEmbed (e6WitnessCorrection (σ i))+triPhasePoint (phaseIndexEquiv (σ i))+
      (eisEmbed (m i)+(k:ℝ)•triC) =
      eisEmbed (e6WitnessCorrection (σ i))+eisEmbed (m i)+
        (triPhasePoint (phaseIndexEquiv (σ i))+(k:ℝ)•triC) by abel,hv i]
    simp only [map_add]
    dsimp only [r]
    abel

theorem e6_cold_spot_description {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    IsColdSpot e6Set α (e6PhysicalPoint z) ↔ E6PaperHole z := by
  unfold e6Set e6PhysicalPoint
  rw [isColdSpot_scaled_iff _ (by positivity),Real.sq_sqrt (by norm_num),
    isColdSpot_l6Euclidean_iff,isL6ColdSpot_iff (by positivity),e6BalancedPhases_iff_paper]

theorem e6_deep_hole_description (z : TriTriple) :
    IsDeepHole e6Set (e6PhysicalPoint z) ↔ E6PaperHole z := by
  unfold e6Set e6PhysicalPoint
  rw [isDeepHole_scaled_iff _ (by positivity) _ l6EuclideanSet_nonempty,
    isDeepHole_l6Euclidean_iff,isL6DeepHole_iff,e6BalancedPhases_iff_paper]

end PaperVerification.ColdSpots
end
end Source_E6HoleDescription
-- END ORIGINAL PaperVerification.E6HoleDescription


-- BEGIN ORIGINAL PaperVerification.E6TranslationClasses
section Source_E6TranslationClasses

-- original header: module

-- original header: public import PaperVerification.E6HoleDescription
-- original header: public import Mathlib.GroupTheory.QuotientGroup.Basic

-- original header: @[expose] public section

noncomputable section

namespace PaperVerification.ColdSpots

def l6AddSubgroup : AddSubgroup TriTriple where
  carrier := l6Set
  zero_mem' := (l6Set_iff_integer_glue 0).mpr ⟨0,0,by intro i; simp⟩
  add_mem' := by
    intro z w hz hw
    obtain ⟨m,k,hm⟩ := (l6Set_iff_integer_glue z).mp hz
    obtain ⟨n,l,hn⟩ := (l6Set_iff_integer_glue w).mp hw
    apply (l6Set_iff_integer_glue (z+w)).mpr
    refine ⟨m+n,k+l,?_⟩
    intro i
    simp only [Pi.add_apply,hm,hn,map_add,Int.cast_add,add_smul]
    abel
  neg_mem' := by
    intro z hz
    obtain ⟨m,k,hm⟩ := (l6Set_iff_integer_glue z).mp hz
    apply (l6Set_iff_integer_glue (-z)).mpr
    refine ⟨-m,-k,?_⟩
    intro i
    simp only [Pi.neg_apply,hm,map_neg,Int.cast_neg,neg_smul]
    abel

theorem triPhase_rep_unique {m n : EisInt} {r s : ZMod 3}
    (h : eisEmbed m+triPhasePoint r=eisEmbed n+triPhasePoint s) : r=s := by
  have hh := congrArg Prod.fst h
  change (m.1:ℝ)+(r.val:ℝ)*(1/3)=(n.1:ℝ)+(s.val:ℝ)*(1/3) at hh
  have hi : (3:ℤ)*(m.1-n.1)=(s.val:ℤ)-(r.val:ℤ) := by
    apply Int.cast_injective (α:=ℝ)
    push_cast
    linarith
  have hm := congrArg (fun k : ℤ ↦ (k:ZMod 3)) hi
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_sub, Int.cast_natCast,
    ZMod.natCast_zmod_val, zmodThree_three_eq_zero, zero_mul] at hm
  linear_combination hm

theorem e6PhaseConfiguration_unique {z : TriTriple} {r s : Fin 3 → ZMod 3}
    (hr : E6PhaseConfiguration z r) (hs : E6PhaseConfiguration z s) : r=s := by
  obtain ⟨m,hm⟩ := hr
  obtain ⟨n,hn⟩ := hs
  funext i
  exact triPhase_rep_unique ((hm i).symm.trans (hn i))

theorem e6PhaseConfiguration_add_lattice {z l : TriTriple} {r : Fin 3 → ZMod 3}
    (hz : E6PhaseConfiguration z r) (hl : l ∈ l6Set) :
    ∃ q : ZMod 3, E6PhaseConfiguration (z+l) (fun i ↦ r i+q) := by
  obtain ⟨m,hm⟩ := hz
  obtain ⟨n,k,hn⟩ := (l6Set_iff_integer_glue l).mp hl
  choose v hv using (fun i ↦ triPhase_add_integer (r i) k)
  refine ⟨(k:ZMod 3),fun i ↦ m i+n i+v i,?_⟩
  intro i
  simp only [Pi.add_apply,hm,hn,map_add]
  rw [show eisEmbed (m i)+triPhasePoint (r i)+(eisEmbed (n i)+(k:ℝ)•triC)=
    eisEmbed (m i)+eisEmbed (n i)+(triPhasePoint (r i)+(k:ℝ)•triC) by abel,hv i]
  abel

theorem e6Phase_sub_mem_iff {z w : TriTriple} {r s : Fin 3 → ZMod 3}
    (hz : E6PhaseConfiguration z r) (hw : E6PhaseConfiguration w s) :
    z-w ∈ l6Set ↔ ∃ q : ZMod 3, ∀ i, r i=s i+q := by
  constructor
  · intro h
    obtain ⟨q,hq⟩ := e6PhaseConfiguration_add_lattice hw h
    have he : w+(z-w)=z := by abel
    rw [he] at hq
    have hr := e6PhaseConfiguration_unique hz hq
    exact ⟨q,fun i ↦ congrFun hr i⟩
  · rintro ⟨q,hq⟩
    obtain ⟨m,hm⟩ := hz
    obtain ⟨n,hn⟩ := hw
    choose v hv using (fun i ↦ triPhase_add_integer (s i) (q.val:ℤ))
    apply (l6Set_iff_integer_glue (z-w)).mpr
    refine ⟨fun i ↦ m i-n i-v i,(q.val:ℤ),?_⟩
    intro i
    have he := hv i
    simp only [Int.cast_natCast,ZMod.natCast_zmod_val] at he
    rw [← hq i] at he
    simp only [Pi.sub_apply,hm,hn,map_sub,Int.cast_natCast]
    rw [show triPhasePoint (r i)=triPhasePoint (s i)+(q.val:ℝ)•triC-eisEmbed (v i) by
      apply eq_sub_iff_add_eq.mpr
      simpa [add_comm] using he.symm]
    abel

theorem e6BalancedPhases_add_lattice {z l : TriTriple} (hz : E6BalancedPhases z)
    (hl : l ∈ l6Set) : E6BalancedPhases (z+l) := by
  obtain ⟨r,hr,hz⟩ := hz
  obtain ⟨q,hq⟩ := e6PhaseConfiguration_add_lattice hz hl
  exact ⟨fun i ↦ r i+q,(Equiv.addRight q).bijective.comp hr,hq⟩

def e6PositivePhases : Fin 3 → ZMod 3 := ![0,1,2]
def e6NegativePhases : Fin 3 → ZMod 3 := ![0,2,1]

theorem e6HoleWitness_positive_configuration :
    E6PhaseConfiguration e6HoleWitness e6PositivePhases := by
  refine ⟨e6WitnessCorrection,?_⟩
  intro i
  have hi : phaseIndexEquiv i = e6PositivePhases i := by
    fin_cases i <;> rfl
  simpa only [hi] using e6HoleWitness_phase i

theorem e6HoleWitness_negative_configuration :
    E6PhaseConfiguration (-e6HoleWitness) e6NegativePhases := by
  refine ⟨![0,(-1,1),0],?_⟩
  intro i
  fin_cases i <;> ext <;>
    norm_num [e6HoleWitness,e6NegativePhases,triPhasePoint,eisEmbed,triC]

lemma balanced_phase_two_classes (r : Fin 3 → ZMod 3) (hr : Function.Bijective r) :
    (∃ q, ∀ i, r i=e6PositivePhases i+q) ∨
      (∃ q, ∀ i, r i=e6NegativePhases i+q) := by
  have hall : ∀ a b c : ZMod 3, a ≠ b → a ≠ c → b ≠ c →
      (b = 1 + a ∧ c = 2 + a) ∨ (b = 2 + a ∧ c = 1 + a) := by
    have hcases : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
    intro a b c hab hac hbc
    rcases hcases a with rfl | rfl | rfl <;>
      rcases hcases b with rfl | rfl | rfl <;>
      rcases hcases c with rfl | rfl | rfl
    all_goals solve
      | exact (hab rfl).elim
      | exact (hac rfl).elim
      | exact (hbc rfl).elim
      | exact Or.inl ⟨by decide, by decide⟩
      | exact Or.inr ⟨by decide, by decide⟩
  obtain ⟨h01, h02, h12⟩ := (bijective_fin3_zmod3_iff r).mp hr
  rcases hall (r 0) (r 1) (r 2) h01 h02 h12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨r 0, ?_⟩
    intro i
    rcases (show ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 by decide) i with rfl | rfl | rfl
    · simp only [e6PositivePhases, Matrix.cons_val_zero, zero_add]
    · simpa only [e6PositivePhases, Matrix.cons_val_one, Matrix.cons_val_zero] using h1
    · simpa only [e6PositivePhases, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons] using h2
  · right
    refine ⟨r 0, ?_⟩
    intro i
    rcases (show ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 by decide) i with rfl | rfl | rfl
    · simp only [e6NegativePhases, Matrix.cons_val_zero, zero_add]
    · simpa only [e6NegativePhases, Matrix.cons_val_one, Matrix.cons_val_zero] using h1
    · simpa only [e6NegativePhases, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons] using h2

theorem e6_two_translation_classes {z : TriTriple} (hz : E6BalancedPhases z) :
    z-e6HoleWitness ∈ l6Set ∨ z-(-e6HoleWitness) ∈ l6Set := by
  obtain ⟨r,hr,hz⟩ := hz
  rcases balanced_phase_two_classes r hr with h | h
  · exact Or.inl ((e6Phase_sub_mem_iff hz e6HoleWitness_positive_configuration).mpr h)
  · exact Or.inr ((e6Phase_sub_mem_iff hz e6HoleWitness_negative_configuration).mpr h)

theorem e6_two_classes_distinct : e6HoleWitness-(-e6HoleWitness) ∉ l6Set := by
  rw [e6Phase_sub_mem_iff e6HoleWitness_positive_configuration e6HoleWitness_negative_configuration]
  rintro ⟨q,hq⟩
  have h0 := hq 0
  have h1 := hq 1
  norm_num [e6PositivePhases,e6NegativePhases] at h0 h1
  rw [← h0] at h1
  exact (show (1 : ZMod 3) ≠ 2 by decide) (by simpa only [add_zero] using h1)

/-- Both classes occur and are interchanged by negation. Together with the
preceding exhaustiveness and distinctness theorems this is the exact count two. -/
theorem e6NegativeWitness_balanced : E6BalancedPhases (-e6HoleWitness) := by
  refine ⟨e6NegativePhases,?_,e6HoleWitness_negative_configuration⟩
  apply (bijective_fin3_zmod3_iff e6NegativePhases).mpr
  change (0 : ZMod 3) ≠ 2 ∧ (0 : ZMod 3) ≠ 1 ∧ (2 : ZMod 3) ≠ 1
  decide

end PaperVerification.ColdSpots
end
end Source_E6TranslationClasses
-- END ORIGINAL PaperVerification.E6TranslationClasses


-- BEGIN ORIGINAL PaperVerification.E6ClassCount
section Source_E6ClassCount

-- original header: module

-- original header: public import PaperVerification.E6TranslationClasses
-- original header: public import PaperVerification.E6Normalization
-- original header: public import Mathlib.SetTheory.Cardinal.Finite


-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

theorem e6PhysicalPoint_add (z w : TriTriple) :
    e6PhysicalPoint (z+w)=e6PhysicalPoint z+e6PhysicalPoint w := by
  funext j
  refine Fin.addCases (m:=3) (n:=3) (fun i ↦ ?_) (fun i ↦ ?_) j <;>
    simp [e6PhysicalPoint,scaleVec,triTripleFlatten, -Fin.natAdd_eq_addNat] <;> ring

def e6PhysicalAddHom : TriTriple →+ (Fin 6 → ℝ) where
  toFun := e6PhysicalPoint
  map_zero' := e6PhysicalPoint_zero
  map_add' := e6PhysicalPoint_add

theorem e6PhysicalPoint_injective : Function.Injective e6PhysicalPoint :=
  (scaleVec_injective (Real.sqrt 2) (by positivity)).comp triTripleEuclideanEquiv.injective

def e6AddSubgroup : AddSubgroup (Fin 6 → ℝ) := l6AddSubgroup.map e6PhysicalAddHom

theorem e6AddSubgroup_coe : (e6AddSubgroup : Set (Fin 6 → ℝ))=e6Set := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨triTripleFlatten z,⟨z,hz,rfl⟩,rfl⟩
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨z,hz,rfl⟩

theorem e6Physical_difference_mem (z w : TriTriple) :
    e6PhysicalPoint z-e6PhysicalPoint w ∈ e6Set ↔ z-w ∈ l6Set := by
  rw [← e6AddSubgroup_coe]
  change e6PhysicalAddHom z-e6PhysicalAddHom w ∈ e6AddSubgroup ↔ z-w ∈ l6Set
  rw [← map_sub e6PhysicalAddHom]
  constructor
  · rintro ⟨l,hl,he⟩
    exact e6PhysicalPoint_injective he ▸ hl
  · intro h
    exact ⟨z-w,h,rfl⟩

def e6CanonicalHole (b : Bool) : Fin 6 → ℝ :=
  e6PhysicalPoint (if b then -e6HoleWitness else e6HoleWitness)

theorem e6CanonicalHole_deep (b : Bool) : IsDeepHole e6Set (e6CanonicalHole b) := by
  have h : E6BalancedPhases (if b then -e6HoleWitness else e6HoleWitness) := by
    cases b
    · exact e6HoleWitness_balanced
    · exact e6NegativeWitness_balanced
  exact (e6_deep_hole_description _).mpr ((e6BalancedPhases_iff_paper _).mp h)

theorem e6CanonicalHole_distinct (b c : Bool) :
    e6CanonicalHole b-e6CanonicalHole c ∈ e6Set ↔ b=c := by
  unfold e6CanonicalHole
  rw [e6Physical_difference_mem]
  cases b <;> cases c
  · simp [show (0:TriTriple)∈l6Set from l6AddSubgroup.zero_mem]
  · constructor
    · intro h
      exact (e6_two_classes_distinct h).elim
    · intro h
      cases h
  · have h : -e6HoleWitness-e6HoleWitness ∉ l6Set := by
      intro hm
      apply e6_two_classes_distinct
      have hn : -(-e6HoleWitness-e6HoleWitness) ∈ l6Set := l6AddSubgroup.neg_mem hm
      rwa [show -(-e6HoleWitness-e6HoleWitness) =
        e6HoleWitness-(-e6HoleWitness) by abel] at hn
    constructor
    · intro hm
      exact (h hm).elim
    · intro he
      cases he
  · simp [show (0:TriTriple)∈l6Set from l6AddSubgroup.zero_mem]

theorem e6DeepHole_class_coverage {x : Fin 6 → ℝ} (hx : IsDeepHole e6Set x) :
    ∃ b : Bool, x-e6CanonicalHole b ∈ e6Set := by
  obtain ⟨z,rfl⟩ := e6PhysicalPoint_surjective x
  have hz : E6BalancedPhases z :=
    (e6BalancedPhases_iff_paper z).mpr ((e6_deep_hole_description z).mp hx)
  rcases e6_two_translation_classes hz with h | h
  · exact ⟨false,(e6Physical_difference_mem _ _).mpr h⟩
  · exact ⟨true,(e6Physical_difference_mem _ _).mpr h⟩

def E6DeepTranslationClasses :=
  {C : (Fin 6 → ℝ) ⧸ e6AddSubgroup // ∃ x : Fin 6 → ℝ,
    IsDeepHole e6Set x ∧ (x : (Fin 6 → ℝ) ⧸ e6AddSubgroup)=C}

def e6DeepClassMap (b : Bool) : E6DeepTranslationClasses :=
  ⟨(e6CanonicalHole b : (Fin 6 → ℝ) ⧸ e6AddSubgroup),
    e6CanonicalHole b,e6CanonicalHole_deep b,rfl⟩

theorem e6DeepClassMap_bijective : Function.Bijective e6DeepClassMap := by
  constructor
  · intro b c h
    apply (e6CanonicalHole_distinct b c).mp
    rw [← e6AddSubgroup_coe]
    exact QuotientAddGroup.eq_iff_sub_mem.mp (congrArg Subtype.val h)
  · rintro ⟨C,x,hx,hC⟩
    obtain ⟨b,hb⟩ := e6DeepHole_class_coverage hx
    rw [← e6AddSubgroup_coe] at hb
    exact ⟨b,Subtype.ext ((QuotientAddGroup.eq_iff_sub_mem.mpr hb).symm.trans hC)⟩

def e6DeepClassEquiv : Bool ≃ E6DeepTranslationClasses :=
  Equiv.ofBijective e6DeepClassMap e6DeepClassMap_bijective

/-- Exactly two classes in the actual root-normalized E₆ lattice quotient. -/
theorem e6_deep_translation_class_count : Nat.card E6DeepTranslationClasses=2 := by
  rw [← Nat.card_congr e6DeepClassEquiv,Nat.card_eq_fintype_card]
  norm_num

end PaperVerification.ColdSpots
end
end Source_E6ClassCount
-- END ORIGINAL PaperVerification.E6ClassCount


-- BEGIN ORIGINAL PaperVerification.BWConstruction
section Source_BWConstruction

-- original header: module

-- original header: public import PaperVerification.BWHoles

-- original header: @[expose] public section
/-! # Identification with the literal RM(1,4) Barnes–Wall construction

The diagonal point set is proved equal to D₁₆ + ½ RM(1,4).  The four-dimensional
code is defined by evaluations of affine binary functions; its Plotkin form is
made explicit, rather than postulated as a lattice identification.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

abbrev AffineCoefficients4 := AffineCoefficients3 × Binary
abbrev BinaryWord16 := Fin 16 → Binary

def affineWord4 (a : AffineCoefficients4) : BinaryWord16 :=
  Fin.append (affineWord3 a.1) (fun i => affineWord3 a.1 i + a.2)

/-- The same codeword evaluated in the four binary coordinate digits. -/
def affineValue4 (a : AffineCoefficients4) (i : Fin 16) : Binary :=
  a.1 3 + (∑ j : Fin 3, a.1 j.castSucc * (((i.val / 2 ^ j.val) % 2 : ℕ) : Binary)) +
    a.2 * (((i.val / 8) % 2 : ℕ) : Binary)

set_option maxRecDepth 65536 in
theorem affineWord4_eq_evaluation : ∀ a : AffineCoefficients4, ∀ i : Fin 16,
    affineWord4 a i = affineValue4 a i := by decide

def InRM4 (c : BinaryWord16) : Prop := ∃ a : AffineCoefficients4, c = affineWord4 a

def halfWord16 (c : BinaryWord16) : Fin 16 → ℝ := fun i => ((c i).val : ℝ) / 2

@[simp] theorem halfWord16_zero : halfWord16 (0 : BinaryWord16) = 0 := by
  funext i
  simp only [halfWord16, Pi.zero_apply, ZMod.val_zero, Nat.cast_zero, zero_div]

/-- The literal Construction-D point set in the paper. -/
def bwRMConstruction : Set (Fin 16 → ℝ) :=
  {x | ∃ z : Fin 16 → ℤ, Even (∑ i, z i) ∧ ∃ c : BinaryWord16,
    InRM4 c ∧ x = intVec z + halfWord16 c}

theorem inRM4_plotkin (c : BinaryWord16) :
    InRM4 c ↔ ∃ u : BinaryWord8, InRM3 u ∧ ∃ η : Binary,
      c = Fin.append u (fun i => u i + η) := by
  constructor
  · rintro ⟨⟨a, η⟩, rfl⟩
    exact ⟨affineWord3 a, ⟨a, rfl⟩, η, rfl⟩
  · rintro ⟨u, ⟨a, rfl⟩, η, rfl⟩
    exact ⟨(a, η), rfl⟩

theorem sum_halfWord (c : BinaryWord8) : (∑ i, halfWord c i) = (binaryWeight c : ℝ) / 2 := by
  simp only [halfWord, ← Finset.sum_div, ← Nat.cast_sum, sum_binary_val]

theorem halfWord_even_integerSum {c : BinaryWord8} (hc : InRM3 c) :
    ∃ k : ℤ, Even k ∧ (∑ i, halfWord c i) = (k : ℝ) := by
  rw [sum_halfWord]
  rcases inRM3_weight c hc with h | h | h
  · exact ⟨0, by decide, by norm_num [h]⟩
  · exact ⟨2, by decide, by norm_num [h]⟩
  · exact ⟨4, by decide, by norm_num [h]⟩

theorem e8_even_integerSum {x : Fin 8 → ℝ} (hx : x ∈ dPlusSet 8) :
    ∃ k : ℤ, Even k ∧ (∑ i, x i) = (k : ℝ) := by
  rcases hx with ⟨z, hz, rfl | rfl⟩
  · exact ⟨∑ i, z i, hz, by simp [intVec]⟩
  · exact ⟨(∑ i, z i) + 4, hz.add (by decide), by norm_num [Finset.sum_add_distrib]⟩

theorem bwGamma_append_iff (x y : Fin 8 → ℝ) :
    Fin.append x y ∈ bwGammaSet ↔ x ∈ bwMSet ∧ y ∈ bwMSet ∧ x - y ∈ dPlusSet 8 := by
  constructor
  · rintro ⟨q, l, hl, k, hk, h⟩
    have hx : x = l + bwRepresentative q := by
      simpa only [bwLeft_append] using congrArg bwLeft h
    have hy : y = k + bwRepresentative q := by
      simpa only [bwRight_append] using congrArg bwRight h
    refine ⟨hx.symm ▸ bwMSet_add (dPlusSet_subset_bwM hl) (bwRepresentative_mem q),
      hy.symm ▸ bwMSet_add (dPlusSet_subset_bwM hk) (bwRepresentative_mem q), ?_⟩
    have heq : x - y = l - k := by rw [hx, hy]; abel
    rw [heq]
    exact dPlusSet_sub (by decide : Even 8) hl hk
  · rintro ⟨hx, hy, hxy⟩
    obtain ⟨q, l, hl, rfl⟩ := bw_coset_coverage hx
    obtain ⟨r, k, hk, rfl⟩ := bw_coset_coverage hy
    have hrep : bwRepresentative q - bwRepresentative r ∈ dPlusSet 8 := by
      have h := dPlusSet_sub (by decide : Even 8) hxy
        (dPlusSet_sub (by decide : Even 8) hl hk)
      convert h using 1 <;> abel
    have hqr := bwRepresentative_mod_e8_injective hrep
    subst r
    exact ⟨q, l, hl, k, hk, rfl⟩

theorem halfWord_difference_e8_words {m k : Fin 8 → ℤ} {c d : BinaryWord8}
    (h : (intVec m + halfWord c) - (intVec k + halfWord d) ∈ dPlusSet 8) :
    c = d ∨ d = fun i => c i + 1 := by
  rcases h with ⟨z, hz, he | he⟩
  · left
    funext i
    have hi := congrFun he i
    change (m i : ℝ) + ((c i).val : ℝ) / 2 -
      ((k i : ℝ) + ((d i).val : ℝ) / 2) = (z i : ℝ) at hi
    have hint : 2 * (m i - k i - z i) + ((c i).val : ℤ) - (d i).val = 0 := by
      exact_mod_cast (show 2 * ((m i : ℝ) - (k i : ℝ) - (z i : ℝ)) +
        ((c i).val : ℝ) - ((d i).val : ℝ) = 0 by linarith)
    have hb := congrArg (fun a : ℤ => (a : Binary)) hint
    exact sub_eq_zero.mp (by simpa using hb)
  · right
    funext i
    have hi := congrFun he i
    change (m i : ℝ) + ((c i).val : ℝ) / 2 -
      ((k i : ℝ) + ((d i).val : ℝ) / 2) = (z i : ℝ) + 1 / 2 at hi
    have hint : 2 * (m i - k i - z i) + ((c i).val : ℤ) - (d i).val = 1 := by
      exact_mod_cast (show 2 * ((m i : ℝ) - (k i : ℝ) - (z i : ℝ)) +
        ((c i).val : ℝ) - ((d i).val : ℝ) = 1 by linarith)
    have hb := congrArg (fun a : ℤ => (a : Binary)) hint
    have heq : c i - d i = 1 := by simpa using hb
    have hneg : (-1 : Binary) = 1 := by decide
    calc
      d i = c i - 1 := by linear_combination -heq
      _ = c i + 1 := by rw [sub_eq_add_neg, hneg]

theorem integerPart_even_total {m k : Fin 8 → ℤ} {c d : BinaryWord8}
    (hc : InRM3 c) (hd : InRM3 d)
    (h : (intVec m + halfWord c) - (intVec k + halfWord d) ∈ dPlusSet 8) :
    Even ((∑ i, m i) + ∑ i, k i) := by
  obtain ⟨a, ha, hca⟩ := halfWord_even_integerSum hc
  obtain ⟨b, hb, hdb⟩ := halfWord_even_integerSum hd
  obtain ⟨v, hv, hvsum⟩ := e8_even_integerSum h
  have heq : (∑ i, m i) - (∑ i, k i) = v - a + b := by
    have hre : ((∑ i, m i : ℤ) : ℝ) + (a : ℝ) -
        (((∑ i, k i : ℤ) : ℝ) + (b : ℝ)) = (v : ℝ) := by
      simpa only [Pi.sub_apply, Pi.add_apply, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, intVec, ← Int.cast_sum, hca, hdb] using hvsum
    exact_mod_cast (show ((∑ i, m i : ℤ) : ℝ) - ((∑ i, k i : ℤ) : ℝ) =
      (v : ℝ) - (a : ℝ) + (b : ℝ) by linarith)
  apply Int.even_add.mpr
  apply Int.even_sub.mp
  rw [heq]
  exact (hv.sub ha).add hb

theorem int_halfCode_difference_mem_e8 {m k : Fin 8 → ℤ} {c : BinaryWord8}
    (hc : InRM3 c) (η : Binary) (hp : Even ((∑ i, m i) + ∑ i, k i)) :
    (intVec m + halfWord c) - (intVec k + halfWord (fun i => c i + η)) ∈ dPlusSet 8 := by
  have hmk : Even ((∑ i, m i) - ∑ i, k i) := Int.even_sub.mpr (Int.even_add.mp hp)
  rcases binary_eq_zero_or_one η with hη | hη
  · subst η
    have heq : (intVec m + halfWord c) - (intVec k + halfWord (fun i => c i + 0)) =
        intVec (m - k) := by
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, halfWord, add_zero, intVec, Int.cast_sub]
      ring
    rw [heq]
    apply (intVec_mem_dPlus_iff (by decide : 0 < 8) _).mpr
    simpa only [Pi.sub_apply, Finset.sum_sub_distrib] using hmk
  · subst η
    have hcompl : halfWord (fun i => c i + 1) = fun i => 1 / 2 - halfWord c i := by
      simpa only [add_comm] using halfWord_complement c
    rw [hcompl]
    let z : Fin 8 → ℤ := fun i => m i - k i + (c i).val - 1
    have hcEven : Even ((binaryWeight c : ℕ) : ℤ) := (Int.even_coe_nat _).mpr (inRM3_even_weight hc)
    have hz : Even (∑ i, z i) := by
      simpa only [z, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Nat.cast_sum,
        sum_binary_val, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, Nat.cast_ofNat] using
          (hmk.add hcEven).sub (by decide : Even (8 : ℤ))
    refine ⟨z, hz, Or.inr ?_⟩
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, intVec, halfWord, z,
      Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one]
    ring

/-- The exact lattice identity in Section 7.1, retaining its actual RM code meaning. -/
theorem bwGammaSet_eq_RMConstruction : bwGammaSet = bwRMConstruction := by
  ext z
  rw [← append_bw_blocks z]
  constructor
  · intro hz
    obtain ⟨hx, hy, hxy⟩ := (bwGamma_append_iff _ _).mp hz
    obtain ⟨m, c, hc, hm⟩ := (bwMSet_iff_integer_halfCode _).mp hx
    obtain ⟨k, d, hd, hk⟩ := (bwMSet_iff_integer_halfCode _).mp hy
    rw [hm, hk] at hxy ⊢
    have hp := integerPart_even_total hc hd hxy
    have hcd := halfWord_difference_e8_words hxy
    refine ⟨Fin.append m k, ?_, Fin.append c d, ?_, ?_⟩
    · simpa only [Fin.sum_univ_add (a := 8) (b := 8),
        Fin.append_left, Fin.append_right] using hp
    · apply (inRM4_plotkin _).mpr
      rcases hcd with hcd | hcd
      · exact ⟨c, hc, 0, by rw [← hcd]; simp⟩
      · exact ⟨c, hc, 1, by rw [hcd]⟩
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [Fin.append_left, Fin.append_right, intVec, halfWord, halfWord16,
          Pi.add_apply]
  · rintro ⟨w, hw, c, hc, hz⟩
    obtain ⟨u, hu, η, rfl⟩ := (inRM4_plotkin c).mp hc
    let m : Fin 8 → ℤ := fun i => w (Fin.castAdd 8 i)
    let k : Fin 8 → ℤ := fun i => w (Fin.natAdd 8 i)
    have hx : bwLeft z = intVec m + halfWord u := by
      funext i
      have h := congrFun hz (Fin.castAdd 8 i)
      simpa only [Fin.append_left, Pi.add_apply, intVec, halfWord, halfWord16, m] using h
    have hy : bwRight z = intVec k + halfWord (fun i => u i + η) := by
      funext i
      have h := congrFun hz (Fin.natAdd 8 i)
      simpa only [Fin.append_right, Pi.add_apply, intVec, halfWord, halfWord16, k] using h
    have hp : Even ((∑ i, m i) + ∑ i, k i) := by
      simpa only [Fin.sum_univ_add (a := 8) (b := 8), m, k] using hw
    apply (bwGamma_append_iff _ _).mpr
    rw [hx, hy]
    refine ⟨bwMSet_add (intVec_mem_bwM m) (halfWord_mem_bwM hu), ?_,
      int_halfCode_difference_mem_e8 hu η hp⟩
    apply bwMSet_add (intVec_mem_bwM k) (halfWord_mem_bwM ?_)
    rcases binary_eq_zero_or_one η with h | h
    · simpa only [h, add_zero] using hu
    · simpa only [h] using inRM3_add hu inRM3_one

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.affineWord4_eq_evaluation
#print axioms PaperVerification.ColdSpots.bwGammaSet_eq_RMConstruction
end
end Source_BWConstruction
-- END ORIGINAL PaperVerification.BWConstruction


-- BEGIN ORIGINAL PaperVerification.BWNormalized
section Source_BWNormalized

-- original header: module

-- original header: public import PaperVerification.BWTheorems
-- original header: public import PaperVerification.BWConstruction
-- original header: public import PaperVerification.LatticeScaling

-- original header: @[expose] public section
/-! # The usual integral Barnes–Wall normalization

The set is the explicit √2 scaling of D₁₆+½RM(1,4).  Its squared covering radius
is three, and its universal Gaussian cold spots are exactly all its deep holes.
-/

noncomputable section

namespace PaperVerification.ColdSpots

def bw16Set : Set (Fin 16 → ℝ) := scaledSet (Real.sqrt 2) bwRMConstruction

theorem bw16Set_eq_scaledGamma : bw16Set = scaledSet (Real.sqrt 2) bwGammaSet := by
  rw [bw16Set, bwGammaSet_eq_RMConstruction]

theorem sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'

theorem setGaussian_bw16 (α : ℝ) (x : Fin 16 → ℝ) :
    setGaussian bw16Set α (scaleVec (Real.sqrt 2) x) = setGaussian bwGammaSet (2 * α) x := by
  rw [bw16Set_eq_scaledGamma, setGaussian_scaled _ sqrt_two_ne_zero,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), mul_comm α 2]

theorem summable_setGaussian_bw16 {α : ℝ} (hα : 0 < α) (z : Fin 16 → ℝ) :
    Summable (fun v : bw16Set => Real.exp (-α * sqDist v.val z)) := by
  rw [bw16Set_eq_scaledGamma]
  have h := (summable_scaled_iff (Real.sqrt 2) sqrt_two_ne_zero bwGammaSet α
    (scaleVec (Real.sqrt 2)⁻¹ z)).mpr (by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      exact summable_setGaussian_bwGamma (by positivity) _)
  simpa only [scaleVec_inv _ sqrt_two_ne_zero] using h

theorem squaredDepth_bw16 (x : Fin 16 → ℝ) :
    squaredDepth bw16Set (scaleVec (Real.sqrt 2) x) = 2 * squaredDepth bwGammaSet x := by
  rw [bw16Set_eq_scaledGamma, squaredDepth_scaled _ sqrt_two_ne_zero _ bwGamma_nonempty,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The Barnes–Wall assertion of Theorem 1.1 in its stated integral normalization. -/
theorem coldSpot_bw16_iff_deepHole {α : ℝ} (hα : 0 < α) (z : Fin 16 → ℝ) :
    IsColdSpot bw16Set α z ↔ IsDeepHole bw16Set z := by
  have hz := scaleVec_inv (Real.sqrt 2) sqrt_two_ne_zero z
  conv_lhs => arg 3; rw [← hz]
  conv_rhs => arg 2; rw [← hz]
  rw [bw16Set_eq_scaledGamma, isColdSpot_scaled_iff _ sqrt_two_ne_zero,
    isDeepHole_scaled_iff _ sqrt_two_ne_zero _ bwGamma_nonempty,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact coldSpot_bwGamma_iff_deepHole (by positivity) _

/-- Squared covering radius three, with a displayed attaining point. -/
theorem bw16_squared_covering_radius :
    (∀ z : Fin 16 → ℝ, squaredDepth bw16Set z ≤ 3) ∧
      ∃ z, squaredDepth bw16Set z = 3 := by
  constructor
  · intro z
    have h := squaredDepth_bwGamma_le (scaleVec (Real.sqrt 2)⁻¹ z)
    have hd := squaredDepth_bw16 (scaleVec (Real.sqrt 2)⁻¹ z)
    rw [scaleVec_inv _ sqrt_two_ne_zero] at hd
    linarith
  · refine ⟨scaleVec (Real.sqrt 2) (Fin.append (bwQuarterPoint + e8FirstVector) bwQuarterPoint), ?_⟩
    rw [squaredDepth_bw16, squaredDepth_bwGamma_witness]
    norm_num

/-- The exact attained Gaussian minimum for every positive parameter. -/
theorem bw16_gaussian_minimum {α : ℝ} (hα : 0 < α) :
    (∀ z : Fin 16 → ℝ, bwGammaMinimum (2 * α) ≤ setGaussian bw16Set α z) ∧
      ∃ z, setGaussian bw16Set α z = bwGammaMinimum (2 * α) := by
  constructor
  · intro z
    have h := setGaussian_bwGamma_lower (by positivity : 0 < 2 * α) (scaleVec (Real.sqrt 2)⁻¹ z)
    have hg := setGaussian_bw16 α (scaleVec (Real.sqrt 2)⁻¹ z)
    rw [scaleVec_inv _ sqrt_two_ne_zero] at hg
    exact hg.symm ▸ h
  · refine ⟨scaleVec (Real.sqrt 2) (Fin.append (bwQuarterPoint + e8FirstVector) bwQuarterPoint), ?_⟩
    rw [setGaussian_bw16]
    exact setGaussian_bwGamma_witness (by positivity)

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.coldSpot_bw16_iff_deepHole
#print axioms PaperVerification.ColdSpots.bw16_squared_covering_radius
#print axioms PaperVerification.ColdSpots.bw16_gaussian_minimum
end
end Source_BWNormalized
-- END ORIGINAL PaperVerification.BWNormalized


-- Kernel-environment audit: every mathematical source body precedes this command.
set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let kenv := env.checked.get
  let entries := kenv.constants.foldStage2
    (fun rows name ci => rows.push (name, ci)) (#[] : Array (Name × ConstantInfo))
  let kind : ConstantInfo → String := fun ci => match ci with
    | .axiomInfo _ => "axiom"
    | .defnInfo _ => "definition"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
    | .inductInfo _ => "inductive"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut rows : Array Json := #[]
  let mut failures : Array Json := #[]
  for (name, ci) in entries do
    if ci.isUnsafe then
      failures := failures.push (Json.mkObj [
        ("declaration", toJson name.toString),
        ("unsafe_declaration", toJson true)])
    let deps := ci.getUsedConstantsAsSet.toArray.qsort Name.lt
    let mut dependencyRows : Array Json := #[]
    for dep in deps do
      match kenv.find? dep with
      | none =>
        failures := failures.push (Json.mkObj [
          ("declaration", toJson name.toString),
          ("missing_dependency", toJson dep.toString)])
      | some info =>
        let origin := match env.getModuleIdxFor? dep with
          | some idx => env.header.moduleNames[idx]!.toString
          | none => env.mainModule.toString
        dependencyRows := dependencyRows.push (Json.mkObj [
          ("name", toJson dep.toString), ("kind", toJson (kind info)),
          ("module", toJson origin)])
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun ax => !allowed.contains ax)
    if !bad.isEmpty then
      failures := failures.push (Json.mkObj [
        ("declaration", toJson name.toString),
        ("unapproved_axioms", toJson (bad.map Name.toString))])
    rows := rows.push (Json.mkObj [
      ("name", toJson name.toString), ("kind", toJson (kind ci)),
      ("unsafe", toJson ci.isUnsafe),
      ("type", toJson (toString ci.type)),
      ("level_parameters", toJson (ci.levelParams.map Name.toString)),
      ("has_body", toJson (ci.value? (allowOpaque := true)).isSome),
      ("dependencies", Json.arr dependencyRows),
      ("axioms", toJson (axioms.map Name.toString))])
  let sourceHash ← IO.getEnv "PAPER_VERIFICATION_SOURCE_SHA256"
  let fingerprint ← IO.getEnv "PAPER_VERIFICATION_FINGERPRINT"
  let document := Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("module", toJson env.mainModule.toString),
    ("source_sha256", toJson sourceHash),
    ("fingerprint", toJson fingerprint),
    ("kernel_environment", toJson true),
    ("declarations", Json.arr rows),
    ("failures", Json.arr failures),
    ("passed", toJson failures.isEmpty)]
  let target := (← IO.getEnv "PAPER_VERIFICATION_AUDIT_PATH").getD ".lake/build/paper-audit/PaperVerification_Lattice005.json"
  let path : System.FilePath := target
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path (document.compress ++ "\n")
  if !failures.isEmpty then
    throwError "Kernel declaration audit rejected {failures.size} dependency/axiom findings; see {target}"
  logInfo m!"Kernel declaration audit passed for {rows.size} declarations; see {target}"
