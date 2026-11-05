module
public import PaperVerification.BWCosets
public import PaperVerification.E7Projection
public import PaperVerification.LatticeGluing
public import Mathlib.Topology.Algebra.InfiniteSum.Real
@[expose] public section
/-! # Exact Gaussian and distance gluing for the Barnes–Wall point set

The sums are over actual distinct points of the diagonal union of E8 cosets.
Bijections and absolute convergence justify every infinite rearrangement.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

/-- The sixteen-dimensional diagonal lattice in Section 7. -/
def bwGammaSet : Set (Fin 16 → ℝ) :=
  {z | ∃ q : BWQuotient, ∃ l ∈ dPlusSet 8, ∃ k ∈ dPlusSet 8,
    z = Fin.append (l + bwRepresentative q) (k + bwRepresentative q)}

def bwLeft (z : Fin 16 → ℝ) : Fin 8 → ℝ := fun i => z (Fin.castAdd 8 i)
def bwRight (z : Fin 16 → ℝ) : Fin 8 → ℝ := fun i => z (Fin.natAdd 8 i)

@[simp] theorem bwLeft_append (x y : Fin 8 → ℝ) : bwLeft (Fin.append x y) = x := by
  funext i
  exact Fin.append_left x y i

@[simp] theorem bwRight_append (x y : Fin 8 → ℝ) : bwRight (Fin.append x y) = y := by
  funext i
  exact Fin.append_right x y i

theorem append_bw_blocks (z : Fin 16 → ℝ) : Fin.append (bwLeft z) (bwRight z) = z := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact Fin.append_left (bwLeft z) (bwRight z) j
  · exact Fin.append_right (bwLeft z) (bwRight z) j

theorem sqDist_append (x y u v : Fin 8 → ℝ) :
    sqDist (Fin.append x y) (Fin.append u v) = sqDist x u + sqDist y v := by
  unfold sqDist
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

def bwGammaMap (v : BWQuotient × (dPlusSet 8 × dPlusSet 8)) : bwGammaSet :=
  ⟨Fin.append (v.2.1.val + bwRepresentative v.1) (v.2.2.val + bwRepresentative v.1),
    v.1, v.2.1.val, v.2.1.property, v.2.2.val, v.2.2.property, rfl⟩

theorem bwGammaMap_bijective : Function.Bijective bwGammaMap := by
  constructor
  · rintro ⟨q, l, k⟩ ⟨r, l', k'⟩ h
    have hv := congrArg Subtype.val h
    have hl : l.val + bwRepresentative q = l'.val + bwRepresentative r := by
      simpa only [bwGammaMap, bwLeft_append] using congrArg bwLeft hv
    have hcoset : bwCosetMap (q, l) = bwCosetMap (r, l') := Subtype.ext hl
    have hp := bwCosetMap_bijective.1 hcoset
    have hq := congrArg Prod.fst hp
    have hll := congrArg Prod.snd hp
    change q = r at hq
    change l = l' at hll
    subst r
    subst l'
    have hk : k.val + bwRepresentative q = k'.val + bwRepresentative q := by
      simpa only [bwGammaMap, bwRight_append] using congrArg bwRight hv
    have hkk : k = k' := Subtype.ext (add_right_cancel hk)
    subst k'
    rfl
  · rintro ⟨x, q, l, hl, k, hk, hx⟩
    exact ⟨(q, ⟨l, hl⟩, ⟨k, hk⟩), Subtype.ext hx.symm⟩

def bwGammaEquiv : BWQuotient × (dPlusSet 8 × dPlusSet 8) ≃ bwGammaSet :=
  Equiv.ofBijective bwGammaMap bwGammaMap_bijective

def bwThetaProfile (α : ℝ) (x : Fin 8 → ℝ) (q : BWQuotient) : ℝ :=
  setGaussian (dPlusSet 8) α (x - bwRepresentative q)

def bwDepthProfile (x : Fin 8 → ℝ) (q : BWQuotient) : ℝ :=
  squaredDepth (dPlusSet 8) (x - bwRepresentative q)

theorem bwThetaProfile_nonneg (α : ℝ) (x : Fin 8 → ℝ) (q : BWQuotient) :
    0 ≤ bwThetaProfile α x q := tsum_nonneg fun _ => (Real.exp_pos _).le

/-- The marginal Gaussian sum is exactly the sum of the sixteen coset profiles. -/
theorem setGaussian_bwM_eq_sum_profiles {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    setGaussian bwMSet α x = ∑ q : BWQuotient, bwThetaProfile α x q := by
  let f : BWQuotient × dPlusSet 8 → ℝ := fun v =>
    Real.exp (-α * sqDist (v.2.val + bwRepresentative v.1) x)
  have hfq (q : BWQuotient) : Summable (fun l : dPlusSet 8 => f (q, l)) := by
    simpa only [f, sqDist_add_left] using
      summable_setGaussian_dPlus (by decide : 0 < 8) hα (x - bwRepresentative q)
  have hf : Summable f := (summable_prod_of_nonneg (fun _ => (Real.exp_pos _).le)).mpr
    ⟨hfq, Summable.of_finite⟩
  calc
    _ = ∑' v, f v := (bwCosetEquiv.tsum_eq (fun z : bwMSet => Real.exp (-α * sqDist z.val x))).symm
    _ = ∑' q : BWQuotient, ∑' l : dPlusSet 8, f (q, l) := hf.tsum_prod
    _ = _ := by simp only [tsum_fintype, f, sqDist_add_left, bwThetaProfile, setGaussian]

/-- Convergent product of the two Gaussian series in one diagonal coset. -/
theorem hasSum_bw_coset_product {α : ℝ} (hα : 0 < α)
    (x y : Fin 8 → ℝ) (q : BWQuotient) :
    HasSum (fun v : dPlusSet 8 × dPlusSet 8 =>
      Real.exp (-α * sqDist (v.1.val + bwRepresentative q) x) *
      Real.exp (-α * sqDist (v.2.val + bwRepresentative q) y))
      (bwThetaProfile α x q * bwThetaProfile α y q) := by
  have hx : Summable (fun l : dPlusSet 8 => Real.exp (-α * sqDist (l.val + bwRepresentative q) x)) := by
    simpa only [sqDist_add_left] using
      summable_setGaussian_dPlus (by decide : 0 < 8) hα (x - bwRepresentative q)
  have hy : Summable (fun l : dPlusSet 8 => Real.exp (-α * sqDist (l.val + bwRepresentative q) y)) := by
    simpa only [sqDist_add_left] using
      summable_setGaussian_dPlus (by decide : 0 < 8) hα (y - bwRepresentative q)
  have hprod := Summable.mul_of_nonneg hx hy (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)
  have hs := hx.hasSum.mul hy.hasSum hprod
  simpa only [bwThetaProfile, setGaussian, sqDist_add_left] using hs

/-- The exact inner-product formula in Proposition 7.1 for the actual lattice. -/
theorem setGaussian_bwGamma_eq_sum_profiles {α : ℝ} (hα : 0 < α) (x y : Fin 8 → ℝ) :
    setGaussian bwGammaSet α (Fin.append x y) =
      ∑ q : BWQuotient, bwThetaProfile α x q * bwThetaProfile α y q := by
  let f : BWQuotient × (dPlusSet 8 × dPlusSet 8) → ℝ := fun v =>
    Real.exp (-α * sqDist (v.2.1.val + bwRepresentative v.1) x) *
    Real.exp (-α * sqDist (v.2.2.val + bwRepresentative v.1) y)
  have hq (q : BWQuotient) : HasSum (fun v => f (q, v))
      (bwThetaProfile α x q * bwThetaProfile α y q) := hasSum_bw_coset_product hα x y q
  have hf : Summable f := (summable_prod_of_nonneg (fun _ => mul_nonneg
    (Real.exp_pos _).le (Real.exp_pos _).le)).mpr ⟨fun q => (hq q).summable, Summable.of_finite⟩
  calc
    _ = ∑' v, Real.exp (-α * sqDist (bwGammaEquiv v).val (Fin.append x y)) :=
      (bwGammaEquiv.tsum_eq _).symm
    _ = ∑' v, f v := by
      apply tsum_congr
      rintro ⟨q, l, k⟩
      change Real.exp (-α * sqDist (Fin.append (l.val + bwRepresentative q)
        (k.val + bwRepresentative q)) (Fin.append x y)) = _
      rw [sqDist_append, mul_add, Real.exp_add]
    _ = ∑' q : BWQuotient, ∑' v : dPlusSet 8 × dPlusSet 8, f (q, v) := hf.tsum_prod
    _ = _ := by simp only [(hq _).tsum_eq, tsum_fintype]

/-- Absolute convergence for the actual diagonal point-set series. -/
theorem summable_setGaussian_bwGamma {α : ℝ} (hα : 0 < α) (z : Fin 16 → ℝ) :
    Summable (fun v : bwGammaSet => Real.exp (-α * sqDist v.val z)) := by
  let x := bwLeft z
  let y := bwRight z
  let f : BWQuotient × (dPlusSet 8 × dPlusSet 8) → ℝ := fun v =>
    Real.exp (-α * sqDist (v.2.1.val + bwRepresentative v.1) x) *
    Real.exp (-α * sqDist (v.2.2.val + bwRepresentative v.1) y)
  have hf : Summable f := (summable_prod_of_nonneg (fun _ => mul_nonneg
    (Real.exp_pos _).le (Real.exp_pos _).le)).mpr
      ⟨fun q => (hasSum_bw_coset_product hα x y q).summable, Summable.of_finite⟩
  apply (bwGammaEquiv.summable_iff (f := fun v : bwGammaSet => Real.exp (-α * sqDist v.val z))).mp
  convert hf using 1
  funext v
  change Real.exp (-α * sqDist (Fin.append (v.2.1.val + bwRepresentative v.1)
    (v.2.2.val + bwRepresentative v.1)) z) = _
  rw [← append_bw_blocks z, sqDist_append, mul_add, Real.exp_add]

/-- A profile value is attained by a point in that actual coset. -/
theorem bwDepthProfile_attained (x : Fin 8 → ℝ) (q : BWQuotient) :
    ∃ l ∈ dPlusSet 8, sqDist x (l + bwRepresentative q) = bwDepthProfile x q := by
  obtain ⟨l, hl, hd⟩ := exists_nearest_dPlus (by decide : 0 < 8) (x - bwRepresentative q)
  refine ⟨l, hl, ?_⟩
  rw [← sqDist_sub_left, hd]
  rfl

theorem bwDepthProfile_le_sqDist (x : Fin 8 → ℝ) (q : BWQuotient)
    {l : Fin 8 → ℝ} (hl : l ∈ dPlusSet 8) :
    bwDepthProfile x q ≤ sqDist x (l + bwRepresentative q) := by
  rw [← sqDist_sub_left]
  exact squaredDepth_le _ hl

/-- One of the sixteen profile distances is the exact distance to M. -/
theorem exists_min_bwDepthProfile (x : Fin 8 → ℝ) :
    ∃ q : BWQuotient, bwDepthProfile x q = squaredDepth bwMSet x ∧
      ∀ r, bwDepthProfile x q ≤ bwDepthProfile x r := by
  classical
  obtain ⟨q, _, hq⟩ := Finset.exists_min_image Finset.univ (bwDepthProfile x)
    (show (Finset.univ : Finset BWQuotient).Nonempty from ⟨(0, 0), Finset.mem_univ _⟩)
  have hmin : ∀ r, bwDepthProfile x q ≤ bwDepthProfile x r := fun r => hq r (Finset.mem_univ _)
  refine ⟨q, ?_, hmin⟩
  apply le_antisymm
  · apply le_csInf ((show bwMSet.Nonempty from ⟨0, bwMSet_zero⟩).image (fun z => sqDist x z))
    rintro v ⟨z, hz, rfl⟩
    obtain ⟨r, l, hl, rfl⟩ := bw_coset_coverage hz
    exact (hmin r).trans (bwDepthProfile_le_sqDist x r hl)
  · obtain ⟨l, hl, hdist⟩ := bwDepthProfile_attained x q
    rw [← hdist]
    exact squaredDepth_le x (bwMSet_add (dPlusSet_subset_bwM hl) (bwRepresentative_mem q))

theorem squaredDepth_bwM_le_profile (x : Fin 8 → ℝ) (q : BWQuotient) :
    squaredDepth bwMSet x ≤ bwDepthProfile x q := by
  obtain ⟨r, hr, hmin⟩ := exists_min_bwDepthProfile x
  rw [← hr]
  exact hmin q

theorem bwGamma_nonempty : bwGammaSet.Nonempty := by
  exact ⟨Fin.append (0 + bwRepresentative (0, 0)) (0 + bwRepresentative (0, 0)),
    (0, 0), 0, zero_mem_dPlusSet 8, 0, zero_mem_dPlusSet 8, rfl⟩

/-- Exact lower-bound characterization of the distance to the actual diagonal set. -/
theorem le_squaredDepth_bwGamma_iff (x y : Fin 8 → ℝ) (r : ℝ) :
    r ≤ squaredDepth bwGammaSet (Fin.append x y) ↔
      ∀ q : BWQuotient, r ≤ bwDepthProfile x q + bwDepthProfile y q := by
  constructor
  · intro hr q
    obtain ⟨l, hl, hx⟩ := bwDepthProfile_attained x q
    obtain ⟨k, hk, hy⟩ := bwDepthProfile_attained y q
    have hd := squaredDepth_le (Fin.append x y)
      (show Fin.append (l + bwRepresentative q) (k + bwRepresentative q) ∈ bwGammaSet from
        ⟨q, l, hl, k, hk, rfl⟩)
    rw [sqDist_append, hx, hy] at hd
    exact hr.trans hd
  · intro hr
    apply le_csInf (bwGamma_nonempty.image (fun z => sqDist (Fin.append x y) z))
    rintro v ⟨z, ⟨q, l, hl, k, hk, rfl⟩, rfl⟩
    dsimp only
    rw [sqDist_append]
    exact (hr q).trans (add_le_add (bwDepthProfile_le_sqDist x q hl)
      (bwDepthProfile_le_sqDist y q hk))

theorem squaredDepth_bwGamma_le_profile (x y : Fin 8 → ℝ) (q : BWQuotient) :
    squaredDepth bwGammaSet (Fin.append x y) ≤ bwDepthProfile x q + bwDepthProfile y q :=
  (le_squaredDepth_bwGamma_iff x y _).mp le_rfl q

theorem bwDepthProfile_le_one (x : Fin 8 → ℝ) (q : BWQuotient) : bwDepthProfile x q ≤ 1 := by
  have h := squaredDepth_dPlus_le (by decide : 8 ≤ 8) (x - bwRepresentative q)
  norm_num at h
  exact h

/-- The covering estimate is valid at every point of ordinary R¹⁶. -/
theorem squaredDepth_bwGamma_le (z : Fin 16 → ℝ) : squaredDepth bwGammaSet z ≤ 3 / 2 := by
  rw [← append_bw_blocks z]
  obtain ⟨q, hq, _⟩ := exists_min_bwDepthProfile (bwLeft z)
  have h := squaredDepth_bwGamma_le_profile (bwLeft z) (bwRight z) q
  rw [hq] at h
  linarith [squaredDepth_bwM_le (bwLeft z), bwDepthProfile_le_one (bwRight z) q]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.setGaussian_bwGamma_eq_sum_profiles
#print axioms PaperVerification.ColdSpots.le_squaredDepth_bwGamma_iff
#print axioms PaperVerification.ColdSpots.squaredDepth_bwGamma_le
