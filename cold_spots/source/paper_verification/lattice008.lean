module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Elab.Tactic.Omega
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import paper_verification.lattice003
public import paper_verification.lattice004

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.GaussianLaplace
section Source_GaussianLaplace

-- original header: module

-- original header: public import Mathlib.Analysis.SpecialFunctions.Log.Basic
-- original header: public import Mathlib.Analysis.Normed.Ring.InfiniteSum
-- original header: public import Mathlib.Topology.Algebra.InfiniteSum.Order
-- original header: public import Mathlib.Topology.Algebra.InfiniteSum.Real
-- original header: public import Mathlib.Topology.Algebra.Order.Field
-- original header: public import Mathlib.Order.ConditionallyCompleteLattice.Basic
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.FieldSimp
-- original header: public import Mathlib.Tactic.Positivity
-- original header: public import Mathlib.Tactic.Ring

-- original header: @[expose] public section

/-!
# The low-temperature limit of a discrete Gaussian sum

For any nonempty family of nonnegative energies, summability at a single
positive parameter suffices for the normalized negative logarithm of the
partition sum to converge to the infimum of the energies. The infimum need
not be attained and the index type is not assumed finite or countable.

This supplies the general limiting principle used in Sections 6 and 8 of
the cold-spots manuscript. The principal lattice proofs do not depend on
this additional module.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open Filter Set
open scoped BigOperators Topology

variable {ι κ : Type*}

def discreteGaussianSum (d : ι → ℝ) (α : ℝ) : ℝ :=
  ∑' i, Real.exp (-α * d i)

def discreteGroundEnergy (d : ι → ℝ) : ℝ := sInf (Set.range d)

lemma discreteGroundEnergy_le (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (i : ι) :
    discreteGroundEnergy d ≤ d i :=
  csInf_le ⟨0, by rintro x ⟨j,rfl⟩; exact hd j⟩ (Set.mem_range_self i)

lemma discreteGroundEnergy_nonneg [Nonempty ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) : 0 ≤ discreteGroundEnergy d := by
  apply le_csInf (Set.range_nonempty _)
  rintro x ⟨i,rfl⟩
  exact hd i

lemma summable_discreteGaussian_of_ge (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    {α₀ α : ℝ} (hs : Summable (fun i => Real.exp (-α₀ * d i)))
    (hα : α₀ ≤ α) : Summable (fun i => Real.exp (-α * d i)) := by
  apply hs.of_nonneg_of_le (fun i => (Real.exp_pos _).le)
  intro i
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_right hα (hd i)]

lemma discreteGaussianSum_pos [Nonempty ι] (d : ι → ℝ) {α : ℝ}
    (hs : Summable (fun i => Real.exp (-α * d i))) :
    0 < discreteGaussianSum d α := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact hs.tsum_pos (fun _ => (Real.exp_pos _).le) i (Real.exp_pos _)

lemma discreteGaussianTerm_le_sum (d : ι → ℝ) {α : ℝ}
    (hs : Summable (fun i => Real.exp (-α * d i))) (i : ι) :
    Real.exp (-α * d i) ≤ discreteGaussianSum d α :=
  hs.le_tsum i (fun _ _ => (Real.exp_pos _).le)

/-- Uniform exponential bound using only one convergent Gaussian sum. -/
theorem discreteGaussianSum_upper (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    {α₀ α : ℝ} (hs : Summable (fun i => Real.exp (-α₀ * d i)))
    (hα : α₀ ≤ α) :
    discreteGaussianSum d α ≤
      Real.exp (-(α - α₀) * discreteGroundEnergy d) * discreteGaussianSum d α₀ := by
  have hsα := summable_discreteGaussian_of_ge d hd hs hα
  have hterm (i : ι) : Real.exp (-α * d i) ≤
      Real.exp (-(α - α₀) * discreteGroundEnergy d) * Real.exp (-α₀ * d i) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_nonneg (sub_nonneg.mpr hα)
      (sub_nonneg.mpr (discreteGroundEnergy_le d hd i))
    nlinarith only [h]
  have h := hsα.tsum_le_tsum hterm
    (hs.mul_left (Real.exp (-(α - α₀) * discreteGroundEnergy d)))
  simpa only [tsum_mul_left, discreteGaussianSum] using h

lemma discreteGaussian_log_lower [Nonempty ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) {α₀ α : ℝ}
    (hs : Summable (fun i => Real.exp (-α₀ * d i))) (hα : α₀ ≤ α)
    (hpos : 0 < α) :
    discreteGroundEnergy d -
        (α₀ * discreteGroundEnergy d + Real.log (discreteGaussianSum d α₀)) / α ≤
      -Real.log (discreteGaussianSum d α) / α := by
  have hsα := summable_discreteGaussian_of_ge d hd hs hα
  have hp := discreteGaussianSum_pos d hsα
  have hp₀ := discreteGaussianSum_pos d hs
  have hlog := Real.log_le_log hp (discreteGaussianSum_upper d hd hs hα)
  rw [Real.log_mul (Real.exp_pos _).ne' hp₀.ne', Real.log_exp] at hlog
  have hmul :
      (discreteGroundEnergy d -
        (α₀ * discreteGroundEnergy d + Real.log (discreteGaussianSum d α₀)) / α) * α =
      (α - α₀) * discreteGroundEnergy d - Real.log (discreteGaussianSum d α₀) := by
    field_simp [hpos.ne'] <;> ring
  apply (le_div_iff₀ hpos).mpr
  rw [hmul]
  linarith

lemma discreteGaussian_log_upper (d : ι → ℝ) {α : ℝ}
    (hs : Summable (fun i => Real.exp (-α * d i))) (hα : 0 < α) (i : ι) :
    -Real.log (discreteGaussianSum d α) / α ≤ d i := by
  have hlog := Real.log_le_log (Real.exp_pos (-α * d i))
    (discreteGaussianTerm_le_sum d hs i)
  rw [Real.log_exp] at hlog
  apply (div_le_iff₀ hα).mpr
  linarith

lemma discreteGaussian_log_le_infimum [Nonempty ι] (d : ι → ℝ) {α : ℝ}
    (hs : Summable (fun i => Real.exp (-α * d i))) (hα : 0 < α) :
    -Real.log (discreteGaussianSum d α) / α ≤ discreteGroundEnergy d := by
  apply le_csInf (Set.range_nonempty d)
  rintro x ⟨i,rfl⟩
  exact discreteGaussian_log_upper d hs hα i

/-- The quantitative two-sided estimate behind the low-temperature limit. -/
theorem discreteGaussian_log_sandwich [Nonempty ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) {α₀ α : ℝ}
    (hs : Summable (fun i => Real.exp (-α₀ * d i))) (hα : α₀ ≤ α)
    (hpos : 0 < α) :
    (discreteGroundEnergy d -
        (α₀ * discreteGroundEnergy d + Real.log (discreteGaussianSum d α₀)) / α ≤
      -Real.log (discreteGaussianSum d α) / α) ∧
    (-Real.log (discreteGaussianSum d α) / α ≤ discreteGroundEnergy d) :=
  ⟨discreteGaussian_log_lower d hd hs hα hpos,
    discreteGaussian_log_le_infimum d (summable_discreteGaussian_of_ge d hd hs hα) hpos⟩

/-- The discrete Gaussian Laplace principle. There is no nearest-point
attainment hypothesis and no finiteness restriction on the index family. -/
theorem discreteGaussian_laplace_limit [Nonempty ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hs : Summable (fun i => Real.exp (-α₀ * d i))) :
    Tendsto (fun α : ℝ => -Real.log (discreteGaussianSum d α) / α)
      atTop (𝓝 (discreteGroundEnergy d)) := by
  have hlower : Tendsto (fun α : ℝ => discreteGroundEnergy d -
      (α₀ * discreteGroundEnergy d + Real.log (discreteGaussianSum d α₀)) / α)
      atTop (𝓝 (discreteGroundEnergy d)) := by
    have hzero : Tendsto (fun α : ℝ =>
        (α₀ * discreteGroundEnergy d + Real.log (discreteGaussianSum d α₀)) / α)
        atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds.div_atTop tendsto_id
    have hconst : Tendsto (fun _ : ℝ => discreteGroundEnergy d) atTop
        (𝓝 (discreteGroundEnergy d)) := tendsto_const_nhds
    simpa only [sub_zero] using hconst.sub hzero
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [(tendsto_order.mp hlower).1 b hb, eventually_ge_atTop α₀]
      with α hlt hα
    exact hlt.trans_le (discreteGaussian_log_lower d hd hs hα (hα₀.trans_le hα))
  · intro b hb
    filter_upwards [eventually_ge_atTop α₀] with α hα
    exact (discreteGaussian_log_le_infimum d
      (summable_discreteGaussian_of_ge d hd hs hα) (hα₀.trans_le hα)).trans_lt hb

/-- Eventual equality of Gaussian sums determines the infimum of the
underlying squared-distance families. -/
theorem gaussian_infimum_eq_of_eventually_equal_sums [Nonempty ι] [Nonempty κ]
    (d : ι → ℝ) (e : κ → ℝ) (hd : ∀ i, 0 ≤ d i) (he : ∀ j, 0 ≤ e j)
    {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hsd : Summable (fun i => Real.exp (-α₀ * d i)))
    (hse : Summable (fun j => Real.exp (-α₀ * e j)))
    (hEq : (fun α : ℝ => ∑' i, Real.exp (-α * d i)) =ᶠ[atTop]
      fun α => ∑' j, Real.exp (-α * e j)) :
    sInf (Set.range d) = sInf (Set.range e) := by
  have hdlim := discreteGaussian_laplace_limit d hd hα₀ hsd
  have helim := discreteGaussian_laplace_limit e he hα₀ hse
  have hlog : (fun α : ℝ => -Real.log (discreteGaussianSum d α) / α) =ᶠ[atTop]
      fun α => -Real.log (discreteGaussianSum e α) / α := by
    filter_upwards [hEq] with α hα
    simp only [discreteGaussianSum, hα]
  exact tendsto_nhds_unique (hdlim.congr' hlog) helim

/-- The exact all-positive-parameter form used in the projection transfer
argument of Section 6. -/
theorem gaussian_infimum_eq_of_equal_sums [Nonempty ι] [Nonempty κ]
    (d : ι → ℝ) (e : κ → ℝ) (hd : ∀ i, 0 ≤ d i) (he : ∀ j, 0 ≤ e j)
    {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hsd : Summable (fun i => Real.exp (-α₀ * d i)))
    (hse : Summable (fun j => Real.exp (-α₀ * e j)))
    (hEq : ∀ α : ℝ, 0 < α → (∑' i, Real.exp (-α * d i)) =
      ∑' j, Real.exp (-α * e j)) :
    sInf (Set.range d) = sInf (Set.range e) := by
  apply gaussian_infimum_eq_of_eventually_equal_sums d e hd he hα₀ hsd hse
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with α hα
  exact hEq α hα

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.discreteGaussian_laplace_limit
#print axioms PaperVerification.ColdSpots.gaussian_infimum_eq_of_equal_sums
end
end Source_GaussianLaplace
-- END ORIGINAL PaperVerification.GaussianLaplace


-- BEGIN ORIGINAL PaperVerification.FiniteProjection
section Source_FiniteProjection

-- original header: module

-- original header: public import PaperVerification.DnGaussian
-- original header: public import Mathlib.Data.Set.Lattice.Disjoint
-- original header: public import Mathlib.Topology.Algebra.InfiniteSum.Real

-- original header: @[expose] public section

/-!
# Projection through finitely many orthogonal fibres

The point set is an actual disjoint union of products of sets in complementary
coordinate blocks. The Gaussian factorization is proved from a bijection of
point sets and summability. The minimizing-set transfer assumes exactly that the
fixed slice meets the global minimum set. It does not assume the projected
minimum, nor define a lattice by its desired minimizers.

This general analytic statement applies to the finite coset decomposition in
Proposition 6.1. Convergence hypotheses are explicit; the E7 application in
E7Projection discharges them for its concrete lattices.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

variable {h w : ℕ} {G : Type*}

/-- The literal union of orthogonal products in the finite glue decomposition. -/
def orthogonalGlue (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ)) :
    Set (Fin (h + w) → ℝ) :=
  {z | ∃ g : G, ∃ x ∈ C g, ∃ y ∈ D g, z = Fin.append x y}

theorem sqDist_append_blocks (x x' : Fin h → ℝ) (y y' : Fin w → ℝ) :
    sqDist (Fin.append x y) (Fin.append x' y') = sqDist x x' + sqDist y y' := by
  unfold sqDist
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem append_blocks_left_injective {x x' : Fin h → ℝ} {y y' : Fin w → ℝ}
    (heq : Fin.append x y = Fin.append x' y') : x = x' := by
  funext i
  simpa only [Fin.append_left] using congrFun heq (Fin.castAdd w i)

theorem append_blocks_right_injective {x x' : Fin h → ℝ} {y y' : Fin w → ℝ}
    (heq : Fin.append x y = Fin.append x' y') : y = y' := by
  funext i
  simpa only [Fin.append_right] using congrFun heq (Fin.natAdd h i)

def orthogonalGlueMap (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (v : Σ g : G, C g × D g) : orthogonalGlue C D :=
  ⟨Fin.append v.2.1.val v.2.2.val, v.1, v.2.1.val, v.2.1.property,
    v.2.2.val, v.2.2.property, rfl⟩

theorem orthogonalGlueMap_bijective
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g'))) :
    Function.Bijective (orthogonalGlueMap C D) := by
  constructor
  · rintro ⟨g, x, y⟩ ⟨g', x', y'⟩ heq
    have hv := congrArg Subtype.val heq
    change Fin.append x.val y.val = Fin.append x'.val y'.val at hv
    have hx := append_blocks_left_injective hv
    have hg : g = g' := by
      by_contra hne
      have hmem : x.val ∈ C g ∩ C g' := ⟨x.property, hx.symm ▸ x'.property⟩
      exact (hdisj hne).le_bot hmem
    subst g'
    have hxx : x = x' := Subtype.ext hx
    have hyy : y = y' := Subtype.ext (append_blocks_right_injective hv)
    subst x'
    subst y'
    rfl
  · rintro ⟨z, g, x, hx, y, hy, rfl⟩
    exact ⟨⟨g, ⟨x, hx⟩, ⟨y, hy⟩⟩, rfl⟩

def orthogonalGlueEquiv
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g'))) :
    (Σ g : G, C g × D g) ≃ orthogonalGlue C D :=
  Equiv.ofBijective _ (orthogonalGlueMap_bijective C D hdisj)

/-- The series in a single product block, with no finite truncation. -/
theorem hasSum_orthogonal_gaussian_product
    (C : Set (Fin h → ℝ)) (D : Set (Fin w → ℝ))
    (α : ℝ) (x : Fin h → ℝ) (t : Fin w → ℝ)
    (hC : Summable (fun v : C => Real.exp (-α * sqDist v.val x)))
    (hD : Summable (fun v : D => Real.exp (-α * sqDist v.val t))) :
    HasSum (fun v : C × D =>
      Real.exp (-α * sqDist (Fin.append v.1.val v.2.val) (Fin.append x t)))
      (setGaussian C α x * setGaussian D α t) := by
  have hprod := Summable.mul_of_nonneg hC hD
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hs := hC.hasSum.mul hD.hasSum hprod
  unfold setGaussian
  convert hs using 1
  funext v
  rw [sqDist_append_blocks, mul_add, Real.exp_add]

/-- Summability of the actual projected union follows from the component series. -/
theorem summable_gaussian_disjoint_finite_union [Fintype G]
    (C : G → Set (Fin h → ℝ)) (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (α : ℝ) (x : Fin h → ℝ)
    (hC : ∀ g, Summable (fun v : C g => Real.exp (-α * sqDist v.val x))) :
    Summable (fun v : (⋃ g, C g) => Real.exp (-α * sqDist v.val x)) := by
  let e := (Set.unionEqSigmaOfDisjoint hdisj).symm
  have hs : Summable (fun v : Σ g : G, C g =>
      Real.exp (-α * sqDist v.2.val x)) :=
    (summable_sigma_of_nonneg (fun _ => (Real.exp_pos _).le)).mpr
      ⟨hC, Summable.of_finite⟩
  exact (e.summable_iff (f := fun v : (⋃ g, C g) =>
    Real.exp (-α * sqDist v.val x))).mp hs

theorem setGaussian_disjoint_finite_union [Fintype G]
    (C : G → Set (Fin h → ℝ)) (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (α : ℝ) (x : Fin h → ℝ)
    (hC : ∀ g, Summable (fun v : C g => Real.exp (-α * sqDist v.val x))) :
    setGaussian (⋃ g, C g) α x = ∑ g : G, setGaussian (C g) α x := by
  let e := (Set.unionEqSigmaOfDisjoint hdisj).symm
  have hs : Summable (fun v : Σ g : G, C g =>
      Real.exp (-α * sqDist v.2.val x)) :=
    (summable_sigma_of_nonneg (fun _ => (Real.exp_pos _).le)).mpr
      ⟨hC, Summable.of_finite⟩
  calc
    _ = ∑' v : Σ g : G, C g, Real.exp (-α * sqDist v.2.val x) :=
      (e.tsum_eq (fun v : (⋃ g, C g) => Real.exp (-α * sqDist v.val x))).symm
    _ = ∑' g : G, ∑' v : C g, Real.exp (-α * sqDist v.val x) := hs.tsum_sigma
    _ = _ := by simp only [tsum_fintype, setGaussian]

/-- Exact orthogonal finite-coset factorization, justified by convergent series. -/
theorem setGaussian_orthogonalGlue [Fintype G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (α : ℝ) (x : Fin h → ℝ) (t : Fin w → ℝ)
    (hC : ∀ g, Summable (fun v : C g => Real.exp (-α * sqDist v.val x)))
    (hD : ∀ g, Summable (fun v : D g => Real.exp (-α * sqDist v.val t))) :
    setGaussian (orthogonalGlue C D) α (Fin.append x t) =
      ∑ g : G, setGaussian (C g) α x * setGaussian (D g) α t := by
  let f : (Σ g : G, C g × D g) → ℝ := fun v =>
    Real.exp (-α * sqDist (Fin.append v.2.1.val v.2.2.val) (Fin.append x t))
  have hg (g : G) : HasSum (fun v : C g × D g => f ⟨g, v⟩)
      (setGaussian (C g) α x * setGaussian (D g) α t) :=
    hasSum_orthogonal_gaussian_product (C g) (D g) α x t (hC g) (hD g)
  have hs : Summable f :=
    (summable_sigma_of_nonneg (fun _ => (Real.exp_pos _).le)).mpr
      ⟨fun g => (hg g).summable, Summable.of_finite⟩
  calc
    _ = ∑' v, f v := ((orthogonalGlueEquiv C D hdisj).tsum_eq
      (fun v : orthogonalGlue C D =>
        Real.exp (-α * sqDist v.val (Fin.append x t)))).symm
    _ = ∑' g : G, ∑' v : C g × D g, f ⟨g, v⟩ := hs.tsum_sigma
    _ = _ := by simp only [(hg _).tsum_eq, tsum_fintype]

theorem summable_gaussian_orthogonalGlue [Fintype G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (α : ℝ) (x : Fin h → ℝ) (t : Fin w → ℝ)
    (hC : ∀ g, Summable (fun v : C g => Real.exp (-α * sqDist v.val x)))
    (hD : ∀ g, Summable (fun v : D g => Real.exp (-α * sqDist v.val t))) :
    Summable (fun v : orthogonalGlue C D =>
      Real.exp (-α * sqDist v.val (Fin.append x t))) := by
  let f : (Σ g : G, C g × D g) → ℝ := fun v =>
    Real.exp (-α * sqDist (Fin.append v.2.1.val v.2.2.val) (Fin.append x t))
  have hs : Summable f :=
    (summable_sigma_of_nonneg (fun _ => (Real.exp_pos _).le)).mpr
      ⟨fun g => (hasSum_orthogonal_gaussian_product (C g) (D g) α x t
        (hC g) (hD g)).summable, Summable.of_finite⟩
  exact ((orthogonalGlueEquiv C D hdisj).summable_iff
    (f := fun v : orthogonalGlue C D =>
      Real.exp (-α * sqDist v.val (Fin.append x t)))).mp hs

/-- Equation in the proof of Proposition 6.1 for arbitrary finite product fibres. -/
theorem projection_gaussian_factorization [Fintype G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (α c : ℝ) (x : Fin h → ℝ) (t₀ : Fin w → ℝ)
    (hC : ∀ g, Summable (fun v : C g => Real.exp (-α * sqDist v.val x)))
    (hD : ∀ g, Summable (fun v : D g => Real.exp (-α * sqDist v.val t₀)))
    (hfibre : ∀ g, setGaussian (D g) α t₀ = c) :
    setGaussian (orthogonalGlue C D) α (Fin.append x t₀) =
      c * setGaussian (⋃ g, C g) α x := by
  rw [setGaussian_orthogonalGlue C D hdisj α x t₀ hC hD,
    setGaussian_disjoint_finite_union C hdisj α x hC]
  simp_rw [hfibre]
  rw [← Finset.sum_mul]
  exact mul_comm _ _

/-- The full minimum-set transfer. Its slice hypothesis is the existence of an
actual global minimizer on that slice, not an assumption about the projection. -/
theorem projection_coldSpot_iff_slice [Fintype G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (α c : ℝ) (hc : 0 < c) (t₀ : Fin w → ℝ)
    (hC : ∀ x g, Summable (fun v : C g => Real.exp (-α * sqDist v.val x)))
    (hD : ∀ g, Summable (fun v : D g => Real.exp (-α * sqDist v.val t₀)))
    (hfibre : ∀ g, setGaussian (D g) α t₀ = c)
    (hmeet : ∃ x₀ : Fin h → ℝ,
      IsColdSpot (orthogonalGlue C D) α (Fin.append x₀ t₀))
    (x : Fin h → ℝ) :
    IsColdSpot (⋃ g, C g) α x ↔
      IsColdSpot (orthogonalGlue C D) α (Fin.append x t₀) := by
  have hfactor (y : Fin h → ℝ) :=
    projection_gaussian_factorization C D hdisj α c y t₀ (hC y) hD hfibre
  obtain ⟨x₀, hx₀⟩ := hmeet
  constructor
  · intro hx z
    have hle := mul_le_mul_of_nonneg_left (hx x₀) hc.le
    rw [← hfactor x, ← hfactor x₀] at hle
    exact hle.trans (hx₀ z)
  · intro hx y
    have hle := hx (Fin.append y t₀)
    rw [hfactor x, hfactor y] at hle
    exact (mul_le_mul_iff_of_pos_left hc).mp hle

/-- Positive-parameter uniformity and the prescribed universal equality locus. -/
theorem projection_universal_minimum_set [Fintype G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (c : ℝ → ℝ) (hc : ∀ α, 0 < α → 0 < c α) (t₀ : Fin w → ℝ)
    (hC : ∀ α, 0 < α → ∀ x g,
      Summable (fun v : C g => Real.exp (-α * sqDist v.val x)))
    (hD : ∀ α, 0 < α → ∀ g,
      Summable (fun v : D g => Real.exp (-α * sqDist v.val t₀)))
    (hfibre : ∀ α, 0 < α → ∀ g, setGaussian (D g) α t₀ = c α)
    (K : Set (Fin (h + w) → ℝ))
    (hK : ∀ α, 0 < α → ∀ z,
      IsColdSpot (orthogonalGlue C D) α z ↔ z ∈ K)
    (hmeet : ∃ x₀ : Fin h → ℝ, Fin.append x₀ t₀ ∈ K) :
    ∀ α, 0 < α → ∀ x : Fin h → ℝ,
      IsColdSpot (⋃ g, C g) α x ↔ Fin.append x t₀ ∈ K := by
  intro α hα x
  rw [projection_coldSpot_iff_slice C D hdisj α (c α) (hc α hα) t₀
    (hC α hα) (hD α hα) (hfibre α hα) (by
      obtain ⟨x₀, hx₀⟩ := hmeet
      exact ⟨x₀, (hK α hα _).mpr hx₀⟩), hK α hα]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.projection_gaussian_factorization
#print axioms PaperVerification.ColdSpots.projection_coldSpot_iff_slice
#print axioms PaperVerification.ColdSpots.projection_universal_minimum_set

end
end Source_FiniteProjection
-- END ORIGINAL PaperVerification.FiniteProjection


-- BEGIN ORIGINAL PaperVerification.FiniteProjectionGeometry
section Source_FiniteProjectionGeometry

-- original header: module

-- original header: public import PaperVerification.FiniteProjection
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.FieldSimp
-- original header: public import Mathlib.Tactic.Ring

-- original header: @[expose] public section

/-!
# Geometric projection transfer

The squared-distance factorization is proved directly from infima of actual
Euclidean squared distances; nearest-point attainment is not assumed. Together
with the equal-theta/equal-infimum theorem, this is the geometric argument in
Proposition 6.1.
-/

noncomputable section

namespace PaperVerification.ColdSpots

variable {h w : ℕ} {G : Type*}

theorem finite_projection_nonempty [Nonempty G]
    (C : G → Set (Fin h → ℝ)) (hC : ∀ g, (C g).Nonempty) :
    (⋃ g, C g).Nonempty := by
  let g : G := Classical.arbitrary G
  obtain ⟨x, hx⟩ := hC g
  exact ⟨x, Set.mem_iUnion.mpr ⟨g, hx⟩⟩

theorem orthogonalGlue_nonempty [Nonempty G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hC : ∀ g, (C g).Nonempty) (hD : ∀ g, (D g).Nonempty) :
    (orthogonalGlue C D).Nonempty := by
  let g : G := Classical.arbitrary G
  obtain ⟨x, hx⟩ := hC g
  obtain ⟨y, hy⟩ := hD g
  exact ⟨Fin.append x y, g, x, hx, y, hy, rfl⟩

/-- Common fibre depth gives the exact geometric identity on the whole slice.
This holds even when none of the relevant infima is attained. -/
theorem projection_depth_factorization [Nonempty G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hC : ∀ g, (C g).Nonempty) (hD : ∀ g, (D g).Nonempty)
    (t₀ : Fin w → ℝ) (ρ : ℝ)
    (hfibre : ∀ g, squaredDepth (D g) t₀ = ρ)
    (x : Fin h → ℝ) :
    squaredDepth (orthogonalGlue C D) (Fin.append x t₀) =
      squaredDepth (⋃ g, C g) x + ρ := by
  apply le_antisymm
  · have hle : squaredDepth (orthogonalGlue C D) (Fin.append x t₀) - ρ ≤
        squaredDepth (⋃ g, C g) x := by
      apply le_csInf ((finite_projection_nonempty C hC).image (fun z => sqDist x z))
      rintro r ⟨u, hu, rfl⟩
      obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hu
      have hinner : squaredDepth (orthogonalGlue C D) (Fin.append x t₀) -
          sqDist x u ≤ squaredDepth (D g) t₀ := by
        apply le_csInf ((hD g).image (fun z => sqDist t₀ z))
        rintro r ⟨v, hv, rfl⟩
        have hb := squaredDepth_le (Fin.append x t₀)
          (show Fin.append u v ∈ orthogonalGlue C D from ⟨g, u, hg, v, hv, rfl⟩)
        rw [sqDist_append_blocks] at hb
        linarith
      rw [hfibre g] at hinner
      linarith
    linarith
  · apply le_csInf ((orthogonalGlue_nonempty C D hC hD).image
      (fun z => sqDist (Fin.append x t₀) z))
    rintro r ⟨z, ⟨g, u, hu, v, hv, rfl⟩, rfl⟩
    change squaredDepth (⋃ g, C g) x + ρ ≤
      sqDist (Fin.append x t₀) (Fin.append u v)
    rw [sqDist_append_blocks]
    have hbase := squaredDepth_le x (Set.mem_iUnion.mpr ⟨g, hu⟩)
    have hdist := squaredDepth_le t₀ hv
    rw [hfibre g] at hdist
    linarith

/-- Exact deepest-point transfer when a deepest point lies on the fixed slice. -/
theorem projection_deepHole_iff_slice [Nonempty G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hC : ∀ g, (C g).Nonempty) (hD : ∀ g, (D g).Nonempty)
    (t₀ : Fin w → ℝ) (ρ : ℝ)
    (hfibre : ∀ g, squaredDepth (D g) t₀ = ρ)
    (hmeet : ∃ x₀ : Fin h → ℝ,
      IsDeepHole (orthogonalGlue C D) (Fin.append x₀ t₀))
    (x : Fin h → ℝ) :
    IsDeepHole (⋃ g, C g) x ↔
      IsDeepHole (orthogonalGlue C D) (Fin.append x t₀) := by
  have hfactor (y : Fin h → ℝ) :=
    projection_depth_factorization C D hC hD t₀ ρ hfibre y
  obtain ⟨x₀, hx₀⟩ := hmeet
  constructor
  · intro hx z
    have hle : squaredDepth (orthogonalGlue C D) (Fin.append x₀ t₀) ≤
        squaredDepth (orthogonalGlue C D) (Fin.append x t₀) := by
      rw [hfactor x₀, hfactor x]
      simpa only [add_comm] using add_le_add_right (hx x₀) ρ
    exact (hx₀ z).trans hle
  · intro hx y
    have hle := hx (Fin.append y t₀)
    rw [hfactor x, hfactor y] at hle
    linarith

theorem sInf_gaussian_range_eq_of_coldSpot {n : ℕ}
    (L : Set (Fin n → ℝ)) (α : ℝ) {x : Fin n → ℝ}
    (hx : IsColdSpot L α x) :
    sInf (Set.range (setGaussian L α)) = setGaussian L α x := by
  have hb : BddBelow (Set.range (setGaussian L α)) :=
    ⟨setGaussian L α x, by rintro r ⟨y, rfl⟩; exact hx y⟩
  apply le_antisymm
  · exact csInf_le hb ⟨x, rfl⟩
  · exact le_csInf ⟨setGaussian L α x, x, rfl⟩ (by
      rintro r ⟨y, rfl⟩
      exact hx y)

/-- The literal quotient-of-minima formula in Proposition 6.1. -/
theorem projection_gaussian_minimum_value [Fintype G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (α c : ℝ) (hc : 0 < c) (t₀ : Fin w → ℝ)
    (hC : ∀ x g, Summable (fun v : C g => Real.exp (-α * sqDist v.val x)))
    (hD : ∀ g, Summable (fun v : D g => Real.exp (-α * sqDist v.val t₀)))
    (hfibre : ∀ g, setGaussian (D g) α t₀ = c)
    (hmeet : ∃ x₀ : Fin h → ℝ,
      IsColdSpot (orthogonalGlue C D) α (Fin.append x₀ t₀)) :
    sInf (Set.range (setGaussian (⋃ g, C g) α)) =
      sInf (Set.range (setGaussian (orthogonalGlue C D) α)) / c := by
  obtain ⟨x₀, hx₀⟩ := hmeet
  have hp : IsColdSpot (⋃ g, C g) α x₀ :=
    (projection_coldSpot_iff_slice C D hdisj α c hc t₀ hC hD hfibre
      ⟨x₀, hx₀⟩ x₀).mpr hx₀
  rw [sInf_gaussian_range_eq_of_coldSpot _ _ hp,
    sInf_gaussian_range_eq_of_coldSpot _ _ hx₀,
    projection_gaussian_factorization C D hdisj α c x₀ t₀ (hC x₀) hD hfibre]
  field_simp [hc.ne'] <;> ring

/-- The analytic and geometric transfers combine without assuming that the
projection already has the desired minimum set. -/
theorem projection_coldSpot_iff_deepHole [Fintype G] [Nonempty G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (hCne : ∀ g, (C g).Nonempty) (hDne : ∀ g, (D g).Nonempty)
    (α c ρ : ℝ) (hc : 0 < c) (t₀ : Fin w → ℝ)
    (hC : ∀ x g, Summable (fun v : C g => Real.exp (-α * sqDist v.val x)))
    (hD : ∀ g, Summable (fun v : D g => Real.exp (-α * sqDist v.val t₀)))
    (hGaussian : ∀ g, setGaussian (D g) α t₀ = c)
    (hDepth : ∀ g, squaredDepth (D g) t₀ = ρ)
    (hL : ∀ z, IsColdSpot (orthogonalGlue C D) α z ↔ IsDeepHole (orthogonalGlue C D) z)
    (hmeet : ∃ x₀ : Fin h → ℝ,
      IsDeepHole (orthogonalGlue C D) (Fin.append x₀ t₀))
    (x : Fin h → ℝ) :
    IsColdSpot (⋃ g, C g) α x ↔ IsDeepHole (⋃ g, C g) x := by
  have hmeetCold : ∃ x₀ : Fin h → ℝ,
      IsColdSpot (orthogonalGlue C D) α (Fin.append x₀ t₀) := by
    obtain ⟨x₀, hx₀⟩ := hmeet
    exact ⟨x₀, (hL _).mpr hx₀⟩
  rw [projection_coldSpot_iff_slice C D hdisj α c hc t₀ hC hD hGaussian hmeetCold,
    hL, projection_deepHole_iff_slice C D hCne hDne t₀ ρ hDepth hmeet]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.projection_depth_factorization
#print axioms PaperVerification.ColdSpots.projection_deepHole_iff_slice
#print axioms PaperVerification.ColdSpots.projection_gaussian_minimum_value
#print axioms PaperVerification.ColdSpots.projection_coldSpot_iff_deepHole

end
end Source_FiniteProjectionGeometry
-- END ORIGINAL PaperVerification.FiniteProjectionGeometry


-- BEGIN ORIGINAL PaperVerification.FiniteProjectionTransfer
section Source_FiniteProjectionTransfer

-- original header: module

-- original header: public import PaperVerification.FiniteProjectionGeometry
-- original header: public import PaperVerification.GaussianLaplace

-- original header: @[expose] public section

/-!
# The general finite-profile projection transfer

This file proves the statement of Proposition 6.1 at the level of actual finite
disjoint product decompositions. All point sets, Gaussian series, and squared
distances are the original geometric objects. Convergence is an explicit input
for the component series. No projected minimizer or fibre depth is assumed.

The final geometric implication uses the general discrete Laplace principle:
equal fibre theta functions for every positive parameter have equal infima of
their squared-distance families. It does not require nearest-point attainment.
-/

noncomputable section

namespace PaperVerification.ColdSpots

variable {h w : ℕ} {G : Type*}

theorem setGaussian_pos_of_nonempty {n : ℕ}
    (S : Set (Fin n → ℝ)) (α : ℝ) (x : Fin n → ℝ) (hS : S.Nonempty)
    (hs : Summable (fun z : S => Real.exp (-α * sqDist z.val x))) :
    0 < setGaussian S α x := by
  obtain ⟨z, hz⟩ := hS
  exact hs.tsum_pos (fun _ => (Real.exp_pos _).le) ⟨z, hz⟩ (Real.exp_pos _)

/-- The infimum in the geometric definition is the same infimum used in the
Laplace theorem. The order of the two points is reconciled by symmetry. -/
theorem squaredDepth_eq_subtype_sInf {n : ℕ}
    (S : Set (Fin n → ℝ)) (x : Fin n → ℝ) :
    squaredDepth S x = sInf (Set.range (fun z : S => sqDist z.val x)) := by
  unfold squaredDepth
  congr 1
  ext r
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, sqDist_comm z x⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z.val, z.property, sqDist_comm x z.val⟩

/-- Equality of the complete Gaussian functions determines the actual nearest
squared distance, even for nonclosed sets for which the infimum is not attained. -/
theorem squaredDepth_eq_of_gaussian_eq {n m : ℕ}
    (S : Set (Fin n → ℝ)) (T : Set (Fin m → ℝ))
    (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hS : S.Nonempty) (hT : T.Nonempty)
    {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hs : Summable (fun z : S => Real.exp (-α₀ * sqDist z.val x)))
    (ht : Summable (fun z : T => Real.exp (-α₀ * sqDist z.val y)))
    (heq : ∀ α : ℝ, 0 < α → setGaussian S α x = setGaussian T α y) :
    squaredDepth S x = squaredDepth T y := by
  letI : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  letI : Nonempty T := ⟨⟨hT.choose, hT.choose_spec⟩⟩
  rw [squaredDepth_eq_subtype_sInf, squaredDepth_eq_subtype_sInf]
  exact gaussian_infimum_eq_of_equal_sums
    (fun z : S => sqDist z.val x) (fun z : T => sqDist z.val y)
    (fun _ => sqDist_nonneg _ _) (fun _ => sqDist_nonneg _ _)
    hα₀ hs ht heq

/-- The common fibre depth is a conclusion of theta equality, not a hypothesis
added to the geometric part of the projection theorem. -/
theorem projection_common_fibre_depth [Nonempty G]
    (D : G → Set (Fin w → ℝ)) (hDne : ∀ g, (D g).Nonempty)
    (t₀ : Fin w → ℝ) (c : ℝ → ℝ)
    (hD : ∀ g, Summable (fun v : D g => Real.exp (-sqDist v.val t₀)))
    (hfibre : ∀ α : ℝ, 0 < α → ∀ g, setGaussian (D g) α t₀ = c α) :
    ∃ ρ : ℝ, ∀ g, squaredDepth (D g) t₀ = ρ := by
  let g₀ : G := Classical.arbitrary G
  refine ⟨squaredDepth (D g₀) t₀, fun g => ?_⟩
  apply squaredDepth_eq_of_gaussian_eq (D g) (D g₀) t₀ t₀ (hDne g) (hDne g₀)
    (α₀ := 1) (by norm_num)
  · simpa only [neg_mul, one_mul] using hD g
  · simpa only [neg_mul, one_mul] using hD g₀
  · intro α hα
    exact (hfibre α hα g).trans (hfibre α hα g₀).symm

/-- Proposition 6.1 for a finite disjoint orthogonal product decomposition,
with component convergence explicit. The result includes the exact universal
minimum set, the quotient of minimum values, and the full deep-hole assertion. -/
theorem finite_profile_projection_transfer [Fintype G] [Nonempty G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (hCne : ∀ g, (C g).Nonempty) (hDne : ∀ g, (D g).Nonempty)
    (t₀ : Fin w → ℝ) (c : ℝ → ℝ)
    (hC : ∀ α : ℝ, 0 < α → ∀ x g,
      Summable (fun v : C g => Real.exp (-α * sqDist v.val x)))
    (hD : ∀ α : ℝ, 0 < α → ∀ g,
      Summable (fun v : D g => Real.exp (-α * sqDist v.val t₀)))
    (hfibre : ∀ α : ℝ, 0 < α → ∀ g, setGaussian (D g) α t₀ = c α)
    (K : Set (Fin (h + w) → ℝ))
    (hK : ∀ α : ℝ, 0 < α → ∀ z,
      IsColdSpot (orthogonalGlue C D) α z ↔ z ∈ K)
    (hmeet : ∃ x₀ : Fin h → ℝ, Fin.append x₀ t₀ ∈ K) :
    (∀ α : ℝ, 0 < α → ∀ x : Fin h → ℝ,
      IsColdSpot (⋃ g, C g) α x ↔ Fin.append x t₀ ∈ K) ∧
    (∀ α : ℝ, 0 < α →
      sInf (Set.range (setGaussian (⋃ g, C g) α)) =
        sInf (Set.range (setGaussian (orthogonalGlue C D) α)) / c α) ∧
    ((∀ z, z ∈ K ↔ IsDeepHole (orthogonalGlue C D) z) →
      ∀ x : Fin h → ℝ,
        IsDeepHole (⋃ g, C g) x ↔ Fin.append x t₀ ∈ K) := by
  let g₀ : G := Classical.arbitrary G
  have hc (α : ℝ) (hα : 0 < α) : 0 < c α := by
    rw [← hfibre α hα g₀]
    exact setGaussian_pos_of_nonempty (D g₀) α t₀ (hDne g₀) (hD α hα g₀)
  refine ⟨projection_universal_minimum_set C D hdisj c hc t₀ hC hD hfibre K hK hmeet,
    ?_, ?_⟩
  · intro α hα
    apply projection_gaussian_minimum_value C D hdisj α (c α) (hc α hα) t₀
      (hC α hα) (hD α hα) (hfibre α hα)
    obtain ⟨x₀, hx₀⟩ := hmeet
    exact ⟨x₀, (hK α hα _).mpr hx₀⟩
  · intro hKdeep x
    obtain ⟨ρ, hρ⟩ := projection_common_fibre_depth D hDne t₀ c (by
      intro g
      simpa only [neg_mul, one_mul] using hD 1 (by norm_num) g) hfibre
    have hmeetDeep : ∃ x₀ : Fin h → ℝ,
        IsDeepHole (orthogonalGlue C D) (Fin.append x₀ t₀) := by
      obtain ⟨x₀, hx₀⟩ := hmeet
      exact ⟨x₀, (hKdeep _).mp hx₀⟩
    exact (projection_deepHole_iff_slice C D hCne hDne t₀ ρ hρ hmeetDeep x).trans
      (hKdeep _).symm

/-- The all-positive-parameter cold-spot/deep-hole equivalence on the projection.
Only the original lattice's equivalence and a slice intersection are assumed. -/
theorem projection_universal_coldSpot_iff_deepHole [Fintype G] [Nonempty G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (hCne : ∀ g, (C g).Nonempty) (hDne : ∀ g, (D g).Nonempty)
    (t₀ : Fin w → ℝ) (c : ℝ → ℝ)
    (hC : ∀ α : ℝ, 0 < α → ∀ x g,
      Summable (fun v : C g => Real.exp (-α * sqDist v.val x)))
    (hD : ∀ α : ℝ, 0 < α → ∀ g,
      Summable (fun v : D g => Real.exp (-α * sqDist v.val t₀)))
    (hfibre : ∀ α : ℝ, 0 < α → ∀ g, setGaussian (D g) α t₀ = c α)
    (hL : ∀ α : ℝ, 0 < α → ∀ z,
      IsColdSpot (orthogonalGlue C D) α z ↔ IsDeepHole (orthogonalGlue C D) z)
    (hmeet : ∃ x₀ : Fin h → ℝ,
      IsDeepHole (orthogonalGlue C D) (Fin.append x₀ t₀)) :
    ∀ α : ℝ, 0 < α → ∀ x : Fin h → ℝ,
      IsColdSpot (⋃ g, C g) α x ↔ IsDeepHole (⋃ g, C g) x := by
  have ht := finite_profile_projection_transfer C D hdisj hCne hDne t₀ c
    hC hD hfibre {z | IsDeepHole (orthogonalGlue C D) z} hL hmeet
  intro α hα x
  exact (ht.1 α hα x).trans (ht.2.2 (fun _ => Iff.rfl) x).symm

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.squaredDepth_eq_of_gaussian_eq
#print axioms PaperVerification.ColdSpots.projection_common_fibre_depth
#print axioms PaperVerification.ColdSpots.finite_profile_projection_transfer
#print axioms PaperVerification.ColdSpots.projection_universal_coldSpot_iff_deepHole

end
end Source_FiniteProjectionTransfer
-- END ORIGINAL PaperVerification.FiniteProjectionTransfer


-- BEGIN ORIGINAL PaperVerification.LatticeCosetProjection
section Source_LatticeCosetProjection

-- original header: module

-- original header: public import PaperVerification.FiniteProjectionTransfer
-- original header: public import Mathlib.Algebra.Module.ZLattice.Summable
-- original header: public import Mathlib.Analysis.Complex.Exponential
-- original header: public import Mathlib.Tactic.Abel
-- original header: public import Lean.Elab.Tactic.Omega
-- original header: public import Mathlib.Tactic.Ring

-- original header: @[expose] public section

/-!
# Gaussian convergence and projection for genuine lattice cosets

Convergence is derived from discreteness of the integer submodule. The proof
compares a Gaussian to a convergent inverse power series on the lattice; the
possible point of zero distance is a finite exceptional set. The final theorem
therefore has no analytic summability hypotheses.

The coordinate point sets use the Euclidean `WithLp 2` structure explicitly, so
the norm used in the convergence theorem is exactly the sum-of-squares metric
used in `sqDist` throughout the project.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open Filter

/-- A quantitative Gaussian tail estimate, obtained from a single term of the
exponential power series. -/
theorem gaussian_le_inverse_power (α t : ℝ) (hα : 0 < α) (ht : 0 < t) (m : ℕ) :
    Real.exp (-α * t ^ 2) ≤
      (Nat.factorial m : ℝ) / α ^ m * t⁻¹ ^ (2 * m) := by
  have hp := Real.pow_div_factorial_le_exp (x := α * t ^ 2)
    (mul_nonneg hα.le (sq_nonneg t)) m
  have hpos : 0 < (α * t ^ 2) ^ m / (Nat.factorial m : ℝ) := by positivity
  calc
    Real.exp (-α * t ^ 2) = (Real.exp (α * t ^ 2))⁻¹ := by
      rw [neg_mul, Real.exp_neg]
    _ ≤ ((α * t ^ 2) ^ m / (Nat.factorial m : ℝ))⁻¹ := inv_anti₀ hpos hp
    _ = (Nat.factorial m : ℝ) / α ^ m * t⁻¹ ^ (2 * m) := by
      simp only [inv_div, mul_pow, ← pow_mul, div_eq_mul_inv, mul_inv_rev, inv_pow, inv_inv]
      ring

/-- Every Gaussian series on a discrete integer submodule of a finite
real normed space converges. Full rank is unnecessary for convergence. -/
theorem summable_gaussian_zlattice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L]
    (α : ℝ) (hα : 0 < α) (x : E) :
    Summable (fun z : L => Real.exp (-α * ‖(z : E) - x‖ ^ 2)) := by
  let m : ℕ := Module.finrank ℤ L + 1
  have hm : Module.finrank ℤ L < 2 * m := by dsimp [m]; omega
  have hs := (ZLattice.summable_norm_sub_inv_pow L (2 * m) hm x).mul_left
    ((Nat.factorial m : ℝ) / α ^ m)
  apply Summable.of_norm_bounded_eventually hs
  have hfinite : {z : L | (z : E) = x}.Finite := Set.Subsingleton.finite (by
    intro a ha b hb
    exact Subtype.ext (ha.trans hb.symm))
  filter_upwards [hfinite.compl_mem_cofinite] with z hz
  have hz' : (z : E) ≠ x := hz
  have hnorm : 0 < ‖(z : E) - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz')
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact gaussian_le_inverse_power α ‖(z : E) - x‖ hα hnorm m

/-- A literal lattice coset, expressed in the coordinate convention used by the
paper. Its underlying lattice carries the Euclidean norm. -/
def euclideanLatticeCoset {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) : Set (Fin n → ℝ) :=
  {x | WithLp.toLp 2 x - a ∈ L}

def euclideanLatticeCosetEquiv {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) : L ≃ euclideanLatticeCoset L a where
  toFun z := ⟨WithLp.ofLp (z.val + a), by
    change WithLp.toLp 2 (WithLp.ofLp (z.val + a)) - a ∈ L
    simpa only [WithLp.toLp_ofLp, add_sub_cancel_right] using z.property⟩
  invFun x := ⟨WithLp.toLp 2 x.val - a, x.property⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem euclideanLatticeCoset_nonempty {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) : (euclideanLatticeCoset L a).Nonempty :=
  ⟨(euclideanLatticeCosetEquiv L a 0).val,
    (euclideanLatticeCosetEquiv L a 0).property⟩

theorem sqDist_euclideanLatticeCosetEquiv {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) (z : L) (x : Fin n → ℝ) :
    sqDist (euclideanLatticeCosetEquiv L a z).val x =
      ‖(z : EuclideanSpace ℝ (Fin n)) - (WithLp.toLp 2 x - a)‖ ^ 2 := by
  rw [sqDist_eq_euclidean_norm_sq]
  change ‖WithLp.toLp 2 (WithLp.ofLp (z.val + a)) - WithLp.toLp 2 x‖ ^ 2 = _
  rw [WithLp.toLp_ofLp]
  have heq : z.val + a - WithLp.toLp 2 x = z.val - (WithLp.toLp 2 x - a) := by abel
  rw [heq]

/-- Convergence on every actual Euclidean lattice coset, at every positive
parameter and every real point. -/
theorem summable_gaussian_euclideanLatticeCoset {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (a : EuclideanSpace ℝ (Fin n)) (α : ℝ) (hα : 0 < α) (x : Fin n → ℝ) :
    Summable (fun z : euclideanLatticeCoset L a => Real.exp (-α * sqDist z.val x)) := by
  let e := euclideanLatticeCosetEquiv L a
  have hs := summable_gaussian_zlattice L α hα (WithLp.toLp 2 x - a)
  have hs' : Summable (fun z : L => Real.exp (-α * sqDist (e z).val x)) := by
    simpa only [e, sqDist_euclideanLatticeCosetEquiv] using hs
  exact (e.summable_iff
    (f := fun z : euclideanLatticeCoset L a => Real.exp (-α * sqDist z.val x))).mp hs'

/-- Distinct cosets of an additive lattice are disjoint. -/
theorem euclideanLatticeCoset_pairwise_disjoint {n : ℕ} {G : Type*}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (a : G → EuclideanSpace ℝ (Fin n))
    (ha : Pairwise (fun g g' => a g - a g' ∉ L)) :
    Pairwise (fun g g' => Disjoint
      (euclideanLatticeCoset L (a g)) (euclideanLatticeCoset L (a g'))) := by
  intro g g' hne
  apply Set.disjoint_left.mpr
  intro x hx hx'
  apply ha hne
  have hm := L.sub_mem hx' hx
  convert hm using 1
  abel

/-- Projection transfer for genuine lattice cosets. Discreteness discharges all
series-convergence obligations. This is the full finite-glue form of Proposition
6.1 in orthogonal Euclidean coordinates, and includes both its minimum value and
its exact geometric equality set. -/
theorem lattice_coset_projection_transfer {h w : ℕ} {G : Type*}
    [Fintype G] [Nonempty G]
    (N : Submodule ℤ (EuclideanSpace ℝ (Fin h))) [DiscreteTopology N]
    (F : Submodule ℤ (EuclideanSpace ℝ (Fin w))) [DiscreteTopology F]
    (a : G → EuclideanSpace ℝ (Fin h)) (b : G → EuclideanSpace ℝ (Fin w))
    (ha : Pairwise (fun g g' => a g - a g' ∉ N))
    (t₀ : Fin w → ℝ) (c : ℝ → ℝ)
    (hfibre : ∀ α : ℝ, 0 < α → ∀ g,
      setGaussian (euclideanLatticeCoset F (b g)) α t₀ = c α)
    (K : Set (Fin (h + w) → ℝ))
    (hK : ∀ α : ℝ, 0 < α → ∀ z,
      IsColdSpot (orthogonalGlue (fun g => euclideanLatticeCoset N (a g))
        (fun g => euclideanLatticeCoset F (b g))) α z ↔ z ∈ K)
    (hmeet : ∃ x₀ : Fin h → ℝ, Fin.append x₀ t₀ ∈ K) :
    (∀ α : ℝ, 0 < α → ∀ x : Fin h → ℝ,
      IsColdSpot (⋃ g, euclideanLatticeCoset N (a g)) α x ↔ Fin.append x t₀ ∈ K) ∧
    (∀ α : ℝ, 0 < α →
      sInf (Set.range (setGaussian (⋃ g, euclideanLatticeCoset N (a g)) α)) =
        sInf (Set.range (setGaussian (orthogonalGlue
          (fun g => euclideanLatticeCoset N (a g))
          (fun g => euclideanLatticeCoset F (b g))) α)) / c α) ∧
    ((∀ z, z ∈ K ↔ IsDeepHole (orthogonalGlue
      (fun g => euclideanLatticeCoset N (a g))
      (fun g => euclideanLatticeCoset F (b g))) z) →
      ∀ x : Fin h → ℝ,
        IsDeepHole (⋃ g, euclideanLatticeCoset N (a g)) x ↔ Fin.append x t₀ ∈ K) := by
  apply finite_profile_projection_transfer
    (fun g => euclideanLatticeCoset N (a g)) (fun g => euclideanLatticeCoset F (b g))
    (euclideanLatticeCoset_pairwise_disjoint N a ha)
    (fun g => euclideanLatticeCoset_nonempty N (a g))
    (fun g => euclideanLatticeCoset_nonempty F (b g)) t₀ c
  · intro α hα x g
    exact summable_gaussian_euclideanLatticeCoset N (a g) α hα x
  · intro α hα g
    exact summable_gaussian_euclideanLatticeCoset F (b g) α hα t₀
  · exact hfibre
  · exact hK
  · exact hmeet

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.summable_gaussian_zlattice
#print axioms PaperVerification.ColdSpots.summable_gaussian_euclideanLatticeCoset
#print axioms PaperVerification.ColdSpots.lattice_coset_projection_transfer

end
end Source_LatticeCosetProjection
-- END ORIGINAL PaperVerification.LatticeCosetProjection


-- BEGIN ORIGINAL PaperVerification.LatticeDiagonalGluing
section Source_LatticeDiagonalGluing

-- original header: module

-- original header: public import PaperVerification.LatticeCosetProjection
-- original header: public import PaperVerification.LatticeGluing
-- original header: public import Mathlib.LinearAlgebra.Quotient.Basic

-- original header: @[expose] public section

/-!
# Diagonal gluing for arbitrary finite-index lattice inclusions

This file connects the general finite-profile inequality with actual lattice
Gaussian sums. The index set is the genuine quotient of `M` by `L`; its chosen
representatives are used only to write the profiles. The glued point set itself
is defined independently as pairs in `M` whose difference lies in `L`.

Convergence follows from lattice discreteness. The positivity of the smaller
lattice's minimum is proved from its attainment. The final theorem assumes only
the finite-index inclusion, a positive parameter, and the two attained minima
specified in Proposition 7.1; it does not assume any Gaussian factorization,
coset-coverage statement, or equality criterion.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

variable {n : ℕ}

/-- The actual quotient `M/L`, formed inside the subtype `M`. -/
abbrev LatticeGlueQuotient
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) :=
  M ⧸ L.comap M.subtype

/-- A representative chosen from the actual quotient class. -/
def latticeGlueRepresentative
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (q : LatticeGlueQuotient L M) : EuclideanSpace ℝ (Fin n) :=
  q.out.val

/-- Distinct quotient classes yield distinct lattice cosets. -/
theorem latticeGlueRepresentative_distinct
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) :
    Pairwise (fun q q' : LatticeGlueQuotient L M =>
      latticeGlueRepresentative L M q - latticeGlueRepresentative L M q' ∉ L) := by
  intro q q' hne hmem
  apply hne
  have hm : q.out - q'.out ∈ L.comap M.subtype := hmem
  have heq : (Submodule.Quotient.mk q.out : LatticeGlueQuotient L M) =
      Submodule.Quotient.mk q'.out := (Submodule.Quotient.eq _).mpr hm
  simpa only [Submodule.Quotient.mk_out] using heq

/-- The disjointness needed for reindexing is deduced from the quotient, not
assumed for a list of representatives. -/
theorem latticeGlueCosets_pairwise_disjoint
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) :
    Pairwise (fun q q' : LatticeGlueQuotient L M => Disjoint
      (euclideanLatticeCoset L (latticeGlueRepresentative L M q))
      (euclideanLatticeCoset L (latticeGlueRepresentative L M q'))) :=
  euclideanLatticeCoset_pairwise_disjoint L (latticeGlueRepresentative L M)
    (latticeGlueRepresentative_distinct L M)

/-- Exact coverage of the larger lattice by the genuine quotient cosets. -/
theorem latticeGlueCosets_union
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (hLM : L ≤ M) :
    (⋃ q : LatticeGlueQuotient L M,
      euclideanLatticeCoset L (latticeGlueRepresentative L M q)) =
        euclideanLatticeCoset M 0 := by
  ext x
  constructor
  · intro hx
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
    have hq' : WithLp.toLp 2 x - latticeGlueRepresentative L M q ∈ L := hq
    have hm := M.add_mem (hLM hq') q.out.property
    change WithLp.toLp 2 x - 0 ∈ M
    simpa only [sub_add_cancel, sub_zero, latticeGlueRepresentative] using hm
  · intro hx
    have hxM : WithLp.toLp 2 x ∈ M := by
      simpa only [euclideanLatticeCoset, Set.mem_setOf_eq, sub_zero] using hx
    let v : M := ⟨WithLp.toLp 2 x, hxM⟩
    let q : LatticeGlueQuotient L M := Submodule.Quotient.mk v
    refine Set.mem_iUnion.mpr ⟨q, ?_⟩
    change v - q.out ∈ L.comap M.subtype
    exact (Submodule.Quotient.eq _).mp (Submodule.Quotient.mk_out q).symm

/-- The glued lattice is the actual set of pairs in `M` congruent modulo `L`.
This definition contains no Gaussian or minimizing-set condition. -/
def diagonalLatticeGlue
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : Set (Fin (n + n) → ℝ) :=
  {z | ∃ x y : Fin n → ℝ, z = Fin.append x y ∧
    WithLp.toLp 2 x ∈ M ∧ WithLp.toLp 2 y ∈ M ∧
    WithLp.toLp 2 x - WithLp.toLp 2 y ∈ L}

/-- Equality with the literal diagonal coset union in Proposition 7.1. -/
theorem diagonalLatticeGlue_eq_orthogonalGlue
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (hLM : L ≤ M) :
    diagonalLatticeGlue L M =
      orthogonalGlue
        (fun q : LatticeGlueQuotient L M =>
          euclideanLatticeCoset L (latticeGlueRepresentative L M q))
        (fun q : LatticeGlueQuotient L M =>
          euclideanLatticeCoset L (latticeGlueRepresentative L M q)) := by
  ext z
  constructor
  · rintro ⟨x, y, hz, hxM, hyM, hxy⟩
    have hx : x ∈ euclideanLatticeCoset M 0 := by
      simpa only [euclideanLatticeCoset, Set.mem_setOf_eq, sub_zero] using hxM
    rw [← latticeGlueCosets_union L M hLM] at hx
    obtain ⟨q, hqx⟩ := Set.mem_iUnion.mp hx
    have hqy : y ∈ euclideanLatticeCoset L (latticeGlueRepresentative L M q) := by
      have hm := L.sub_mem hqx hxy
      change WithLp.toLp 2 y - latticeGlueRepresentative L M q ∈ L
      convert hm using 1
      abel
    exact ⟨q, x, hqx, y, hqy, hz⟩
  · rintro ⟨q, x, hx, y, hy, hz⟩
    have hxM : x ∈ euclideanLatticeCoset M 0 := by
      rw [← latticeGlueCosets_union L M hLM]
      exact Set.mem_iUnion.mpr ⟨q, hx⟩
    have hyM : y ∈ euclideanLatticeCoset M 0 := by
      rw [← latticeGlueCosets_union L M hLM]
      exact Set.mem_iUnion.mpr ⟨q, hy⟩
    refine ⟨x, y, hz, ?_, ?_, ?_⟩
    · simpa only [euclideanLatticeCoset, Set.mem_setOf_eq, sub_zero] using hxM
    · simpa only [euclideanLatticeCoset, Set.mem_setOf_eq, sub_zero] using hyM
    · have hm := L.sub_mem hx hy
      convert hm using 1
      abel

/-- Translation of the lattice coset is exactly translation of the argument.
The equality is obtained by bijective reindexing of actual point subtypes. -/
theorem euclideanLatticeCoset_gaussian_shift
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) (α : ℝ) (x : Fin n → ℝ) :
    setGaussian (euclideanLatticeCoset L a) α x =
      setGaussian (euclideanLatticeCoset L 0) α (x - WithLp.ofLp a) := by
  unfold setGaussian
  rw [← (euclideanLatticeCosetEquiv L a).tsum_eq
    (fun z : euclideanLatticeCoset L a => Real.exp (-α * sqDist z.val x)),
    ← (euclideanLatticeCosetEquiv L 0).tsum_eq
      (fun z : euclideanLatticeCoset L 0 =>
        Real.exp (-α * sqDist z.val (x - WithLp.ofLp a)))]
  apply tsum_congr
  intro z
  rw [sqDist_euclideanLatticeCosetEquiv, sqDist_euclideanLatticeCosetEquiv]
  simp only [WithLp.toLp_sub, WithLp.toLp_ofLp, sub_zero]

/-- Changing a representative within its coset leaves the point set unchanged. -/
theorem euclideanLatticeCoset_eq_of_sub_mem
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (a b : EuclideanSpace ℝ (Fin n)) (hab : a - b ∈ L) :
    euclideanLatticeCoset L a = euclideanLatticeCoset L b := by
  ext x
  constructor
  · intro hx
    have hm := L.add_mem hx hab
    change WithLp.toLp 2 x - b ∈ L
    convert hm using 1
    abel
  · intro hx
    have hm := L.sub_mem hx hab
    change WithLp.toLp 2 x - a ∈ L
    convert hm using 1
    abel

/-- In particular the shifted Gaussian profile is independent of representative. -/
theorem latticeGaussian_shift_eq_of_sub_mem
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (a b : EuclideanSpace ℝ (Fin n)) (hab : a - b ∈ L)
    (α : ℝ) (x : Fin n → ℝ) :
    setGaussian (euclideanLatticeCoset L 0) α (x - WithLp.ofLp a) =
      setGaussian (euclideanLatticeCoset L 0) α (x - WithLp.ofLp b) := by
  rw [← euclideanLatticeCoset_gaussian_shift, ← euclideanLatticeCoset_gaussian_shift,
    euclideanLatticeCoset_eq_of_sub_mem L a b hab]

/-- Convergence for the finite-index extension is derived from the smaller
lattice's convergence and the proved disjoint coset partition. -/
theorem summable_gaussian_lattice_extension
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hLM : L ≤ M) [Fintype (LatticeGlueQuotient L M)]
    (α : ℝ) (hα : 0 < α) (x : Fin n → ℝ) :
    Summable (fun z : euclideanLatticeCoset M 0 => Real.exp (-α * sqDist z.val x)) := by
  rw [← latticeGlueCosets_union L M hLM]
  exact summable_gaussian_disjoint_finite_union _ (latticeGlueCosets_pairwise_disjoint L M)
    α x (fun q => summable_gaussian_euclideanLatticeCoset L
      (latticeGlueRepresentative L M q) α hα x)

/-- The sum of the literal shifted `L` profiles is the ordinary `M` Gaussian. -/
theorem latticeGlue_profile_sum
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hLM : L ≤ M) [Fintype (LatticeGlueQuotient L M)]
    (α : ℝ) (hα : 0 < α) (x : Fin n → ℝ) :
    setGaussian (euclideanLatticeCoset M 0) α x =
      ∑ q : LatticeGlueQuotient L M,
        setGaussian (euclideanLatticeCoset L 0) α
          (x - WithLp.ofLp (latticeGlueRepresentative L M q)) := by
  rw [← latticeGlueCosets_union L M hLM,
    setGaussian_disjoint_finite_union _ (latticeGlueCosets_pairwise_disjoint L M)
      α x (fun q => summable_gaussian_euclideanLatticeCoset L
        (latticeGlueRepresentative L M q) α hα x)]
  apply Finset.sum_congr rfl
  intro q _
  exact euclideanLatticeCoset_gaussian_shift L (latticeGlueRepresentative L M q) α x

/-- Convergence of the actual glued Gaussian at every pair of real points. -/
theorem summable_gaussian_diagonalLatticeGlue
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hLM : L ≤ M) [Fintype (LatticeGlueQuotient L M)]
    (α : ℝ) (hα : 0 < α) (x y : Fin n → ℝ) :
    Summable (fun z : diagonalLatticeGlue L M =>
      Real.exp (-α * sqDist z.val (Fin.append x y))) := by
  rw [diagonalLatticeGlue_eq_orthogonalGlue L M hLM]
  exact summable_gaussian_orthogonalGlue _ _ (latticeGlueCosets_pairwise_disjoint L M)
    α x y
    (fun q => summable_gaussian_euclideanLatticeCoset L
      (latticeGlueRepresentative L M q) α hα x)
    (fun q => summable_gaussian_euclideanLatticeCoset L
      (latticeGlueRepresentative L M q) α hα y)

/-- Every ambient point has the two coordinate blocks used above. Thus the
convergence theorem covers the whole ambient Euclidean space. -/
theorem summable_gaussian_diagonalLatticeGlue_all
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hLM : L ≤ M) [Fintype (LatticeGlueQuotient L M)]
    (α : ℝ) (hα : 0 < α) (z : Fin (n + n) → ℝ) :
    Summable (fun v : diagonalLatticeGlue L M => Real.exp (-α * sqDist v.val z)) := by
  have hs := summable_gaussian_diagonalLatticeGlue L M hLM α hα
    (fun i => z (Fin.castAdd n i)) (fun i => z (Fin.natAdd n i))
  simpa only [Fin.append_castAdd_natAdd] using hs

/-- The displayed Gaussian factorization in the proof of Proposition 7.1. -/
theorem diagonalLatticeGlue_gaussian_factorization
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hLM : L ≤ M) [Fintype (LatticeGlueQuotient L M)]
    (α : ℝ) (hα : 0 < α) (x y : Fin n → ℝ) :
    setGaussian (diagonalLatticeGlue L M) α (Fin.append x y) =
      ∑ q : LatticeGlueQuotient L M,
        setGaussian (euclideanLatticeCoset L 0) α
          (x - WithLp.ofLp (latticeGlueRepresentative L M q)) *
        setGaussian (euclideanLatticeCoset L 0) α
          (y - WithLp.ofLp (latticeGlueRepresentative L M q)) := by
  rw [diagonalLatticeGlue_eq_orthogonalGlue L M hLM,
    setGaussian_orthogonalGlue _ _ (latticeGlueCosets_pairwise_disjoint L M)
      α x y
      (fun q => summable_gaussian_euclideanLatticeCoset L
        (latticeGlueRepresentative L M q) α hα x)
      (fun q => summable_gaussian_euclideanLatticeCoset L
        (latticeGlueRepresentative L M q) α hα y)]
  apply Finset.sum_congr rfl
  intro q _
  exact congrArg₂ (fun a b : ℝ => a * b)
    (euclideanLatticeCoset_gaussian_shift L (latticeGlueRepresentative L M q) α x)
    (euclideanLatticeCoset_gaussian_shift L (latticeGlueRepresentative L M q) α y)

/-- An attained lattice Gaussian minimum is strictly positive. -/
theorem latticeGaussian_minimum_pos
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (α : ℝ) (hα : 0 < α) (κ : ℝ)
    (hκ : IsLeast (Set.range (setGaussian (euclideanLatticeCoset L 0) α)) κ) :
    0 < κ := by
  obtain ⟨x, hx⟩ := hκ.1
  rw [← hx]
  exact setGaussian_pos_of_nonempty (euclideanLatticeCoset L 0) α x
    (euclideanLatticeCoset_nonempty L 0)
    (summable_gaussian_euclideanLatticeCoset L 0 α hα x)

/-- An attained least value identifies the full global minimum set. -/
theorem isColdSpot_iff_gaussian_eq_of_isLeast
    (S : Set (Fin n → ℝ)) (α κ : ℝ)
    (hκ : IsLeast (Set.range (setGaussian S α)) κ) (x : Fin n → ℝ) :
    IsColdSpot S α x ↔ setGaussian S α x = κ := by
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := hκ.1
    exact le_antisymm (by simpa only [hz] using hx z) (hκ.2 ⟨x, rfl⟩)
  · intro hx y
    rw [hx]
    exact hκ.2 ⟨y, rfl⟩

/-- Full arbitrary-finite-index diagonal gluing, Proposition 7.1. The index is
the cardinality of the actual quotient, the minima are actual attained Gaussian
minima, and the conclusion gives the exact global equality criterion. -/
theorem lattice_diagonal_gluing
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hLM : L ≤ M) [Finite (LatticeGlueQuotient L M)]
    (α : ℝ) (hα : 0 < α) (κ σ : ℝ)
    (hκ : IsLeast (Set.range (setGaussian (euclideanLatticeCoset L 0) α)) κ)
    (hσ : IsLeast (Set.range (setGaussian (euclideanLatticeCoset M 0) α)) σ)
    (x y : Fin n → ℝ) :
    (2 * κ * σ - (Nat.card (LatticeGlueQuotient L M) : ℝ) * κ ^ 2 ≤
      setGaussian (diagonalLatticeGlue L M) α (Fin.append x y)) ∧
    (setGaussian (diagonalLatticeGlue L M) α (Fin.append x y) =
        2 * κ * σ - (Nat.card (LatticeGlueQuotient L M) : ℝ) * κ ^ 2 ↔
      IsColdSpot (euclideanLatticeCoset M 0) α x ∧
      IsColdSpot (euclideanLatticeCoset M 0) α y ∧
      ∀ q : LatticeGlueQuotient L M,
        IsColdSpot (euclideanLatticeCoset L 0) α
          (x - WithLp.ofLp (latticeGlueRepresentative L M q)) ∨
        IsColdSpot (euclideanLatticeCoset L 0) α
          (y - WithLp.ofLp (latticeGlueRepresentative L M q))) := by
  classical
  letI : Fintype (LatticeGlueQuotient L M) := Fintype.ofFinite _
  let u (q : LatticeGlueQuotient L M) :=
    setGaussian (euclideanLatticeCoset L 0) α
      (x - WithLp.ofLp (latticeGlueRepresentative L M q))
  let v (q : LatticeGlueQuotient L M) :=
    setGaussian (euclideanLatticeCoset L 0) α
      (y - WithLp.ofLp (latticeGlueRepresentative L M q))
  have hκpos := latticeGaussian_minimum_pos L α hα κ hκ
  have hu (q : LatticeGlueQuotient L M) : κ ≤ u q := hκ.2 ⟨_, rfl⟩
  have hv (q : LatticeGlueQuotient L M) : κ ≤ v q := hκ.2 ⟨_, rfl⟩
  have hsumx : (∑ q, u q) = setGaussian (euclideanLatticeCoset M 0) α x :=
    (latticeGlue_profile_sum L M hLM α hα x).symm
  have hsumy : (∑ q, v q) = setGaussian (euclideanLatticeCoset M 0) α y :=
    (latticeGlue_profile_sum L M hLM α hα y).symm
  have hSu : σ ≤ ∑ q, u q := by rw [hsumx]; exact hσ.2 ⟨x, rfl⟩
  have hSv : σ ≤ ∑ q, v q := by rw [hsumy]; exact hσ.2 ⟨y, rfl⟩
  have hfactor : setGaussian (diagonalLatticeGlue L M) α (Fin.append x y) =
      ∑ q, u q * v q := diagonalLatticeGlue_gaussian_factorization L M hLM α hα x y
  constructor
  · rw [hfactor]
    simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using
      PaperVerification.Lattice.diagonal_gluing_bound Finset.univ u v κ σ hκpos.le
        (fun q _ => hu q) (fun q _ => hv q) hSu hSv
  · have heq : (∑ q, u q * v q) =
        2 * κ * σ - (Nat.card (LatticeGlueQuotient L M) : ℝ) * κ ^ 2 ↔
        (∑ q, u q) = σ ∧ (∑ q, v q) = σ ∧ ∀ q, u q = κ ∨ v q = κ := by
      simpa only [Finset.card_univ, Nat.card_eq_fintype_card,
        Finset.mem_univ, forall_true_left] using
        PaperVerification.Lattice.diagonal_gluing_eq_iff Finset.univ u v κ σ hκpos
          (fun q _ => hu q) (fun q _ => hv q) hSu hSv
    rw [hfactor, heq, hsumx, hsumy]
    simp_rw [isColdSpot_iff_gaussian_eq_of_isLeast _ α σ hσ,
      isColdSpot_iff_gaussian_eq_of_isLeast _ α κ hκ, u, v]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.latticeGlueCosets_union
#print axioms PaperVerification.ColdSpots.diagonalLatticeGlue_gaussian_factorization
#print axioms PaperVerification.ColdSpots.latticeGaussian_minimum_pos
#print axioms PaperVerification.ColdSpots.lattice_diagonal_gluing

end
end Source_LatticeDiagonalGluing
-- END ORIGINAL PaperVerification.LatticeDiagonalGluing


-- BEGIN ORIGINAL PaperVerification.OrthogonalLatticeProjection
section Source_OrthogonalLatticeProjection

-- original header: module

-- original header: public import PaperVerification.LatticeCosetProjection
-- original header: public import Mathlib.Analysis.InnerProductSpace.ProdL2
-- original header: public import Mathlib.Logic.Equiv.Fin.Basic
-- original header: public import Mathlib.Topology.MetricSpace.HausdorffDistance
-- original header: public import Mathlib.Tactic.Abel

-- original header: @[expose] public section

/-!
# Projection transfer in an arbitrary finite-dimensional Euclidean space

The finite-coset theorem is transported through orthonormal coordinates.
The ambient lattice, its intersections with the two actual subspaces, and
its orthogonal projection remain independent geometric objects.  The finite
glue decomposition is the displayed data of Proposition 6.1.  Gaussian
convergence and equality of fibre depths are derived in the imported theorems.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators InnerProductSpace

section MetricCoordinates

variable {E : Type*} [NormedAddCommGroup E] {n : ℕ}

def normSetGaussian (S : Set E) (α : ℝ) (x : E) : ℝ :=
  ∑' z : S, Real.exp (-α * ‖z.val - x‖ ^ 2)

def normSquaredDepth (S : Set E) (x : E) : ℝ :=
  sInf ((fun z : E => ‖x - z‖ ^ 2) '' S)

def NormColdSpot (S : Set E) (α : ℝ) (x : E) : Prop :=
  ∀ y : E, normSetGaussian S α x ≤ normSetGaussian S α y

def NormDeepHole (S : Set E) (x : E) : Prop :=
  ∀ y : E, normSquaredDepth S y ≤ normSquaredDepth S x

/-- The geometric definition is the square of the ordinary metric distance,
including sets for which a nearest point is not attained. -/
theorem normSquaredDepth_eq_infDist_sq (S : Set E) (hS : S.Nonempty) (x : E) :
    normSquaredDepth S x = Metric.infDist x S ^ 2 := by
  have hnonneg : 0 ≤ normSquaredDepth S x := by
    apply le_csInf (hS.image _)
    rintro r ⟨z, hz, rfl⟩
    exact sq_nonneg _
  have hbound (z : E) (hz : z ∈ S) : normSquaredDepth S x ≤ ‖x - z‖ ^ 2 :=
    csInf_le ⟨0, by rintro r ⟨v, hv, rfl⟩; exact sq_nonneg _⟩ ⟨z, hz, rfl⟩
  apply le_antisymm
  · have hsqrt : Real.sqrt (normSquaredDepth S x) ≤ Metric.infDist x S := by
      apply (Metric.le_infDist hS).mpr
      intro z hz
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) dist_nonneg).mp
      rw [Real.sq_sqrt hnonneg, dist_eq_norm]
      exact hbound z hz
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
    simpa only [Real.sq_sqrt hnonneg] using hs
  · apply le_csInf (hS.image _)
    rintro r ⟨z, hz, rfl⟩
    simpa only [dist_eq_norm] using
      pow_le_pow_left₀ Metric.infDist_nonneg (Metric.infDist_le_dist_of_mem hz) 2

theorem normDeepHole_iff_metric (S : Set E) (hS : S.Nonempty) (x : E) :
    NormDeepHole S x ↔ ∀ y : E, Metric.infDist y S ≤ Metric.infDist x S := by
  constructor
  · intro hx y
    have hy := hx y
    rw [normSquaredDepth_eq_infDist_sq S hS, normSquaredDepth_eq_infDist_sq S hS] at hy
    exact (sq_le_sq₀ Metric.infDist_nonneg Metric.infDist_nonneg).mp hy
  · intro hx y
    rw [normSquaredDepth_eq_infDist_sq S hS, normSquaredDepth_eq_infDist_sq S hS]
    exact pow_le_pow_left₀ Metric.infDist_nonneg (hx y) 2

def coordinateImageEquiv (e : E ≃ (Fin n → ℝ)) (S : Set E) : S ≃ e '' S where
  toFun z := ⟨e z.val, z.val, z.property, rfl⟩
  invFun z := ⟨e.symm z.val, by
    obtain ⟨x, hx, hxe⟩ := z.property
    simpa only [← hxe, e.symm_apply_apply] using hx⟩
  left_inv z := by apply Subtype.ext; exact e.symm_apply_apply z.val
  right_inv z := by apply Subtype.ext; exact e.apply_symm_apply z.val

theorem setGaussian_coordinate_image (e : E ≃ (Fin n → ℝ))
    (he : ∀ x y, sqDist (e x) (e y) = ‖x - y‖ ^ 2)
    (S : Set E) (α : ℝ) (x : E) :
    setGaussian (e '' S) α (e x) = normSetGaussian S α x := by
  unfold setGaussian normSetGaussian
  rw [← (coordinateImageEquiv e S).tsum_eq]
  apply tsum_congr
  intro z
  change Real.exp (-α * sqDist (e z.val) (e x)) = _
  rw [he]

theorem squaredDepth_coordinate_image (e : E ≃ (Fin n → ℝ))
    (he : ∀ x y, sqDist (e x) (e y) = ‖x - y‖ ^ 2)
    (S : Set E) (x : E) :
    squaredDepth (e '' S) (e x) = normSquaredDepth S x := by
  unfold squaredDepth normSquaredDepth
  congr 1
  ext r
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, (he x z).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨e z, ⟨z, hz, rfl⟩, he x z⟩

theorem coldSpot_coordinate_image (e : E ≃ (Fin n → ℝ))
    (he : ∀ x y, sqDist (e x) (e y) = ‖x - y‖ ^ 2)
    (S : Set E) (α : ℝ) (x : E) :
    IsColdSpot (e '' S) α (e x) ↔ NormColdSpot S α x := by
  constructor
  · intro hx y
    simpa only [setGaussian_coordinate_image e he] using hx (e y)
  · intro hx y
    obtain ⟨y, rfl⟩ := e.surjective y
    simpa only [setGaussian_coordinate_image e he] using hx y

theorem deepHole_coordinate_image (e : E ≃ (Fin n → ℝ))
    (he : ∀ x y, sqDist (e x) (e y) = ‖x - y‖ ^ 2)
    (S : Set E) (x : E) :
    IsDeepHole (e '' S) (e x) ↔ NormDeepHole S x := by
  constructor
  · intro hx y
    simpa only [squaredDepth_coordinate_image e he] using hx (e y)
  · intro hx y
    obtain ⟨y, rfl⟩ := e.surjective y
    simpa only [squaredDepth_coordinate_image e he] using hx y

theorem gaussian_range_coordinate_image (e : E ≃ (Fin n → ℝ))
    (he : ∀ x y, sqDist (e x) (e y) = ‖x - y‖ ^ 2)
    (S : Set E) (α : ℝ) :
    Set.range (setGaussian (e '' S) α) = Set.range (normSetGaussian S α) := by
  ext r
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨x, (setGaussian_coordinate_image e he S α x).symm.trans hy⟩
  · rintro ⟨x, hx⟩
    exact ⟨e x, (setGaussian_coordinate_image e he S α x).trans hx⟩

end MetricCoordinates

section OrthonormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Writing the second summand as `Hᗮ` loses no orthogonal decomposition:
every orthogonal complementary subspace is exactly this subspace. -/
theorem orthogonal_summand_eq (H W : Submodule ℝ E)
    (hspan : H ⊔ W = ⊤) (horth : W ≤ Hᗮ) : W = Hᗮ := by
  apply le_antisymm horth
  intro x hx
  have hxsum : x ∈ H ⊔ W := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hxsum
  have huorth : u ∈ Hᗮ := by
    have hsub := Hᗮ.sub_mem hx (horth hv)
    simpa only [← huv, add_sub_cancel_right] using hsub
  have hu0 : u = 0 := (Submodule.disjoint_def.mp H.orthogonal_disjoint) u hu huorth
  simpa only [← huv, hu0, zero_add] using hv

def isometricCoordinates {n : ℕ} (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    E ≃ (Fin n → ℝ) :=
  e.toEquiv.trans (WithLp.equiv 2 (Fin n → ℝ))

theorem sqDist_isometricCoordinates {n : ℕ}
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (x y : E) :
    sqDist (isometricCoordinates e x) (isometricCoordinates e y) = ‖x - y‖ ^ 2 := by
  rw [sqDist_eq_euclidean_norm_sq]
  change ‖e x - e y‖ ^ 2 = _
  rw [← map_sub, e.norm_map]

def orthogonalCoordinates (H : Submodule ℝ E) {h w : ℕ}
    (eH : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin h))
    (eW : Hᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin w)) : E ≃ (Fin (h + w) → ℝ) :=
  ((H.prodEquivOfIsCompl Hᗮ H.isCompl_orthogonal).symm.toEquiv.trans
    ((isometricCoordinates eH).prodCongr (isometricCoordinates eW))).trans
      (Fin.appendEquiv h w)

theorem orthogonalCoordinates_add (H : Submodule ℝ E) {h w : ℕ}
    (eH : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin h))
    (eW : Hᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin w)) (x : H) (t : Hᗮ) :
    orthogonalCoordinates H eH eW ((x : E) + (t : E)) =
      Fin.append (isometricCoordinates eH x) (isometricCoordinates eW t) := by
  change (Fin.appendEquiv h w)
    (((isometricCoordinates eH).prodCongr (isometricCoordinates eW))
      ((H.prodEquivOfIsCompl Hᗮ H.isCompl_orthogonal).symm
        ((H.prodEquivOfIsCompl Hᗮ H.isCompl_orthogonal) (x, t)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem sqDist_orthogonalCoordinates (H : Submodule ℝ E) {h w : ℕ}
    (eH : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin h))
    (eW : Hᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin w)) (x y : E) :
    sqDist (orthogonalCoordinates H eH eW x) (orthogonalCoordinates H eH eW y) =
      ‖x - y‖ ^ 2 := by
  obtain ⟨⟨xH, xW⟩, rfl⟩ := (H.prodEquivOfIsCompl Hᗮ H.isCompl_orthogonal).surjective x
  obtain ⟨⟨yH, yW⟩, rfl⟩ := (H.prodEquivOfIsCompl Hᗮ H.isCompl_orthogonal).surjective y
  change sqDist (orthogonalCoordinates H eH eW ((xH : E) + (xW : E)))
    (orthogonalCoordinates H eH eW ((yH : E) + (yW : E))) =
      ‖((xH : E) + (xW : E)) - ((yH : E) + (yW : E))‖ ^ 2
  rw [orthogonalCoordinates_add, orthogonalCoordinates_add, sqDist_append_blocks,
    sqDist_isometricCoordinates, sqDist_isometricCoordinates]
  have hsub : ((xH : E) + (xW : E)) - ((yH : E) + (yW : E)) =
      ((xH - yH : H) : E) + ((xW - yW : Hᗮ) : E) := by
    simp only [Submodule.coe_sub]
    abel
  have horth : ⟪((xH - yH : H) : E), ((xW - yW : Hᗮ) : E)⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K := H)
      (xH - yH).property (xW - yW).property
  rw [hsub]
  simpa only [pow_two, Submodule.norm_coe] using
    (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth).symm

def latticeIntersection (L : Submodule ℤ E) (H : Submodule ℝ E) : Submodule ℤ H :=
  ZLattice.comap ℝ L H.subtype

def latticeOrthogonalProjection (L : Submodule ℤ E) (H : Submodule ℝ E) :
    Submodule ℤ H :=
  L.map (H.orthogonalProjectionOnto.toLinearMap.restrictScalars ℤ)

def latticeCoset {V : Type*} [AddCommGroup V] (N : Submodule ℤ V) (a : V) : Set V :=
  {x | x - a ∈ N}

def coordinateLattice {n : ℕ} (N : Submodule ℤ E)
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
  ZLattice.comap ℝ N e.symm.toLinearMap

theorem coordinateLattice_coset_mem {n : ℕ} (N : Submodule ℤ E)
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (a x : E) :
    isometricCoordinates e x ∈ euclideanLatticeCoset (coordinateLattice N e) (e a) ↔
      x ∈ latticeCoset N a := by
  change e.symm (e x - e a) ∈ N ↔ x - a ∈ N
  rw [map_sub, e.symm_apply_apply, e.symm_apply_apply]

theorem coordinateLattice_coset_image {n : ℕ} (N : Submodule ℤ E)
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (a : E) :
    (isometricCoordinates e) '' latticeCoset N a =
      euclideanLatticeCoset (coordinateLattice N e) (e a) := by
  ext x
  obtain ⟨x, rfl⟩ := (isometricCoordinates e).surjective x
  rw [coordinateLattice_coset_mem]
  constructor
  · rintro ⟨y, hy, heq⟩
    exact (isometricCoordinates e).injective heq ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem orthogonal_projection_add (H : Submodule ℝ E) (x : H) (t : Hᗮ) :
    H.orthogonalProjectionOnto ((x : E) + (t : E)) = x := by
  rw [map_add, H.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (K := H) t.property, add_zero]

/-- Literal finite glue data in the orthogonal subspaces.  In particular the
underlying lattice is not defined by the desired Gaussian or deep-hole set. -/
def HasOrthogonalGlue (L : Submodule ℤ E) (H : Submodule ℝ E)
    {G : Type*} (a : G → H) (b : G → Hᗮ) : Prop :=
  ∀ z : E, z ∈ L ↔ ∃ g : G, ∃ x : H, ∃ t : Hᗮ,
    x ∈ latticeCoset (latticeIntersection L H) (a g) ∧
    t ∈ latticeCoset (latticeIntersection L Hᗮ) (b g) ∧ z = (x : E) + (t : E)

theorem orthogonalGlue_coordinate_image (L : Submodule ℤ E) (H : Submodule ℝ E)
    {G : Type*} (a : G → H) (b : G → Hᗮ) (hglue : HasOrthogonalGlue L H a b)
    {h w : ℕ} (eH : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin h))
    (eW : Hᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin w)) :
    (orthogonalCoordinates H eH eW) '' (L : Set E) =
      orthogonalGlue
        (fun g => euclideanLatticeCoset (coordinateLattice (latticeIntersection L H) eH) (eH (a g)))
        (fun g => euclideanLatticeCoset (coordinateLattice (latticeIntersection L Hᗮ) eW) (eW (b g))) := by
  ext z
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨g, x, t, hx, ht, rfl⟩ := (hglue z).mp hz
    exact ⟨g, isometricCoordinates eH x,
      (coordinateLattice_coset_mem _ _ _ _).mpr hx,
      isometricCoordinates eW t, (coordinateLattice_coset_mem _ _ _ _).mpr ht,
      orthogonalCoordinates_add H eH eW x t⟩
  · rintro ⟨g, x, hx, t, ht, rfl⟩
    obtain ⟨x, rfl⟩ := (isometricCoordinates eH).surjective x
    obtain ⟨t, rfl⟩ := (isometricCoordinates eW).surjective t
    exact ⟨(x : E) + (t : E), (hglue _).mpr ⟨g, x, t,
      (coordinateLattice_coset_mem _ _ _ _).mp hx,
      (coordinateLattice_coset_mem _ _ _ _).mp ht, rfl⟩,
      orthogonalCoordinates_add H eH eW x t⟩

theorem orthogonalProjection_coordinate_image (L : Submodule ℤ E) (H : Submodule ℝ E)
    {G : Type*} (a : G → H) (b : G → Hᗮ) (hglue : HasOrthogonalGlue L H a b)
    {h : ℕ} (eH : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin h)) :
    (isometricCoordinates eH) '' (latticeOrthogonalProjection L H : Set H) =
      ⋃ g, euclideanLatticeCoset (coordinateLattice (latticeIntersection L H) eH) (eH (a g)) := by
  ext x
  constructor
  · rintro ⟨x, ⟨z, hz, hzx⟩, rfl⟩
    obtain ⟨g, y, t, hy, ht, rfl⟩ := (hglue z).mp hz
    have hyx : y = x := (orthogonal_projection_add H y t).symm.trans hzx
    exact Set.mem_iUnion.mpr ⟨g,
      (coordinateLattice_coset_mem (latticeIntersection L H) eH (a g) x).mpr
        (hyx ▸ hy)⟩
  · obtain ⟨x, rfl⟩ := (isometricCoordinates eH).surjective x
    intro hx
    obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hx
    refine ⟨x, ?_, rfl⟩
    refine ⟨(x : E) + (b g : E), (hglue _).mpr ⟨g, x, b g,
      (coordinateLattice_coset_mem _ _ _ _).mp hg, ?_, rfl⟩,
      orthogonal_projection_add H x (b g)⟩
    change b g - b g ∈ latticeIntersection L Hᗮ
    simpa using (latticeIntersection L Hᗮ).zero_mem

/-- Proposition 6.1 in an arbitrary finite-dimensional real inner-product
space, with the paper's explicitly displayed finite glue decomposition.

`latticeIntersection` is the actual intersection, expressed as a submodule
of the subspace; `latticeOrthogonalProjection` is the actual orthogonal image.
There are no convergence, common-depth, or projected-minimum hypotheses.
The dimension of either summand is unrestricted, including zero. -/
theorem orthogonal_lattice_projection_transfer
    (L : Submodule ℤ E) [DiscreteTopology L] (H : Submodule ℝ E)
    {G : Type*} [Fintype G] (a : G → H) (b : G → Hᗮ)
    (hglue : HasOrthogonalGlue L H a b)
    (ha : Pairwise (fun g g' => a g - a g' ∉ latticeIntersection L H))
    (t₀ : Hᗮ) (c : ℝ → ℝ)
    (hfibre : ∀ α : ℝ, 0 < α → ∀ g,
      normSetGaussian (latticeCoset (latticeIntersection L Hᗮ) (b g)) α t₀ = c α)
    (K : Set E)
    (hK : ∀ α : ℝ, 0 < α → ∀ z : E,
      NormColdSpot (L : Set E) α z ↔ z ∈ K)
    (hmeet : ∃ x₀ : H, (x₀ : E) + (t₀ : E) ∈ K) :
    (∀ α : ℝ, 0 < α → ∀ x : H,
      NormColdSpot (latticeOrthogonalProjection L H : Set H) α x ↔
        (x : E) + (t₀ : E) ∈ K) ∧
    (∀ α : ℝ, 0 < α →
      sInf (Set.range (normSetGaussian (latticeOrthogonalProjection L H : Set H) α)) =
        sInf (Set.range (normSetGaussian (L : Set E) α)) / c α) ∧
    ((∀ z : E, z ∈ K ↔ NormDeepHole (L : Set E) z) → ∀ x : H,
      NormDeepHole (latticeOrthogonalProjection L H : Set H) x ↔
        (x : E) + (t₀ : E) ∈ K) := by
  letI : Nonempty G := by
    obtain ⟨g, _, _, _, _, _⟩ := (hglue 0).mp L.zero_mem
    exact ⟨g⟩
  let N := latticeIntersection L H
  let F := latticeIntersection L Hᗮ
  letI : DiscreteTopology N :=
    ZLattice.comap_discreteTopology ℝ L H.subtypeL.continuous H.subtype_injective
  letI : DiscreteTopology F :=
    ZLattice.comap_discreteTopology ℝ L Hᗮ.subtypeL.continuous Hᗮ.subtype_injective
  let eH := (stdOrthonormalBasis ℝ H).repr
  let eW := (stdOrthonormalBasis ℝ Hᗮ).repr
  let NC := coordinateLattice N eH
  let FC := coordinateLattice F eW
  letI : DiscreteTopology NC :=
    ZLattice.comap_discreteTopology ℝ N eH.symm.continuous eH.symm.injective
  letI : DiscreteTopology FC :=
    ZLattice.comap_discreteTopology ℝ F eW.symm.continuous eW.symm.injective
  let hc := isometricCoordinates eH
  let wc := isometricCoordinates eW
  let ec := orthogonalCoordinates H eH eW
  let C := fun g => euclideanLatticeCoset NC (eH (a g))
  let D := fun g => euclideanLatticeCoset FC (eW (b g))
  let Kc : Set (Fin (Module.finrank ℝ H + Module.finrank ℝ Hᗮ) → ℝ) :=
    {z | ec.symm z ∈ K}
  have hhc : ∀ x y, sqDist (hc x) (hc y) = ‖x - y‖ ^ 2 :=
    sqDist_isometricCoordinates eH
  have hec : ∀ x y, sqDist (ec x) (ec y) = ‖x - y‖ ^ 2 :=
    sqDist_orthogonalCoordinates H eH eW
  have hgluec : ec '' (L : Set E) = orthogonalGlue C D :=
    orthogonalGlue_coordinate_image L H a b hglue eH eW
  have hMc : hc '' (latticeOrthogonalProjection L H : Set H) = ⋃ g, C g :=
    orthogonalProjection_coordinate_image L H a b hglue eH
  have hac : Pairwise (fun g g' => eH (a g) - eH (a g') ∉ NC) := by
    intro g g' hne hm
    apply ha hne
    change eH.symm (eH (a g) - eH (a g')) ∈ N at hm
    simpa only [map_sub, eH.symm_apply_apply] using hm
  have hfibc : ∀ α : ℝ, 0 < α → ∀ g,
      setGaussian (D g) α (wc t₀) = c α := by
    intro α hα g
    calc
      setGaussian (D g) α (wc t₀) =
          normSetGaussian (latticeCoset F (b g)) α t₀ := by
        change setGaussian
          (euclideanLatticeCoset (coordinateLattice F eW) (eW (b g))) α
          (isometricCoordinates eW t₀) = _
        rw [← coordinateLattice_coset_image F eW (b g)]
        exact setGaussian_coordinate_image (isometricCoordinates eW)
          (sqDist_isometricCoordinates eW) _ _ _
      _ = c α := hfibre α hα g
  have hKc : ∀ α : ℝ, 0 < α → ∀ z,
      IsColdSpot (orthogonalGlue C D) α z ↔ z ∈ Kc := by
    intro α hα z
    obtain ⟨z, rfl⟩ := ec.surjective z
    rw [← hgluec, coldSpot_coordinate_image ec hec]
    simpa only [Kc, Set.mem_setOf_eq, ec.symm_apply_apply] using hK α hα z
  have hmeetc : ∃ x₀, Fin.append x₀ (wc t₀) ∈ Kc := by
    obtain ⟨x₀, hx₀⟩ := hmeet
    refine ⟨hc x₀, ?_⟩
    change ec.symm (Fin.append (hc x₀) (wc t₀)) ∈ K
    rw [← orthogonalCoordinates_add H eH eW]
    simpa only [ec, Equiv.symm_apply_apply] using hx₀
  have ht := lattice_coset_projection_transfer NC FC
    (fun g => eH (a g)) (fun g => eW (b g)) hac (wc t₀) c hfibc Kc hKc hmeetc
  refine ⟨?_, ?_, ?_⟩
  · intro α hα x
    have hx := ht.1 α hα (hc x)
    rw [← hMc, coldSpot_coordinate_image hc hhc] at hx
    change NormColdSpot (latticeOrthogonalProjection L H : Set H) α x ↔
      ec.symm (Fin.append (hc x) (wc t₀)) ∈ K at hx
    rw [← orthogonalCoordinates_add H eH eW] at hx
    simpa only [ec, Equiv.symm_apply_apply] using hx
  · intro α hα
    have hv := ht.2.1 α hα
    rw [← hMc, ← hgluec, gaussian_range_coordinate_image hc hhc,
      gaussian_range_coordinate_image ec hec] at hv
    exact hv
  · intro hdeep x
    have hdeepc : ∀ z, z ∈ Kc ↔ IsDeepHole (orthogonalGlue C D) z := by
      intro z
      obtain ⟨z, rfl⟩ := ec.surjective z
      rw [← hgluec, deepHole_coordinate_image ec hec]
      simpa only [Kc, Set.mem_setOf_eq, ec.symm_apply_apply] using hdeep z
    have hx := ht.2.2 hdeepc (hc x)
    rw [← hMc, deepHole_coordinate_image hc hhc] at hx
    change NormDeepHole (latticeOrthogonalProjection L H : Set H) x ↔
      ec.symm (Fin.append (hc x) (wc t₀)) ∈ K at hx
    rw [← orthogonalCoordinates_add H eH eW] at hx
    simpa only [ec, Equiv.symm_apply_apply] using hx

end OrthonormalCoordinates

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.orthogonal_lattice_projection_transfer
end
end Source_OrthogonalLatticeProjection
-- END ORIGINAL PaperVerification.OrthogonalLatticeProjection


-- BEGIN ORIGINAL PaperVerification.RationalLatticeGlue
section Source_RationalLatticeGlue

-- original header: module

-- original header: public import PaperVerification.OrthogonalLatticeProjection
-- original header: public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

-- original header: @[expose] public section

/-!
# Existence of the finite glue data for rational orthogonal subspaces

Rationality means that the lattice intersection spans the real subspace.
The sum of the two intersections is consequently a full lattice.  Its index
in the original lattice is finite, by the full-rank finite-quotient theorem
for finite free integer modules.  Coset representatives of this quotient
provide exactly the glue data in Proposition 6.1.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A subspace rational for a lattice is spanned by its lattice intersection. -/
def LatticeRational (L : Submodule ℤ E) (H : Submodule ℝ E) : Prop :=
  Submodule.span ℝ ((L ⊓ H.restrictScalars ℤ : Submodule ℤ E) : Set E) = H

def orthogonalGlueSubmodule (L : Submodule ℤ E) (H : Submodule ℝ E) : Submodule ℤ E :=
  (L ⊓ H.restrictScalars ℤ) ⊔ (L ⊓ Hᗮ.restrictScalars ℤ)

theorem orthogonalGlueSubmodule_le (L : Submodule ℤ E) (H : Submodule ℝ E) :
    orthogonalGlueSubmodule L H ≤ L :=
  sup_le inf_le_left inf_le_left

def orthogonalGlueRelation (L : Submodule ℤ E) (H : Submodule ℝ E) : Submodule ℤ L :=
  (orthogonalGlueSubmodule L H).comap L.subtype

abbrev OrthogonalGlueQuotient (L : Submodule ℤ E) (H : Submodule ℝ E) :=
  L ⧸ orthogonalGlueRelation L H

def glueRepresentative (L : Submodule ℤ E) (H : Submodule ℝ E)
    (g : OrthogonalGlueQuotient L H) : L := Quotient.out g

def glueProjectedRepresentative (L : Submodule ℤ E) (H : Submodule ℝ E)
    (g : OrthogonalGlueQuotient L H) : H :=
  ((H.prodEquivOfIsCompl Hᗮ H.isCompl_orthogonal).symm
    (glueRepresentative L H g : E)).1

def glueFibreRepresentative (L : Submodule ℤ E) (H : Submodule ℝ E)
    (g : OrthogonalGlueQuotient L H) : Hᗮ :=
  ((H.prodEquivOfIsCompl Hᗮ H.isCompl_orthogonal).symm
    (glueRepresentative L H g : E)).2

theorem glueRepresentative_decomposition (L : Submodule ℤ E) (H : Submodule ℝ E)
    (g : OrthogonalGlueQuotient L H) :
    (glueProjectedRepresentative L H g : E) + (glueFibreRepresentative L H g : E) =
      (glueRepresentative L H g : E) :=
  (H.prodEquivOfIsCompl Hᗮ H.isCompl_orthogonal).apply_symm_apply _

/-- Canonical quotient representatives give the literal glue decomposition.
This construction does not require finiteness of the quotient. -/
theorem canonical_orthogonal_glue (L : Submodule ℤ E) (H : Submodule ℝ E) :
    HasOrthogonalGlue L H (glueProjectedRepresentative L H) (glueFibreRepresentative L H) := by
  intro z
  constructor
  · intro hz
    let zL : L := ⟨z, hz⟩
    let g : OrthogonalGlueQuotient L H := Submodule.Quotient.mk zL
    have heq : (Submodule.Quotient.mk zL : OrthogonalGlueQuotient L H) =
        Submodule.Quotient.mk (glueRepresentative L H g) := by
      rw [glueRepresentative, Submodule.Quotient.mk_out]
    have hdiff := (Submodule.Quotient.eq (orthogonalGlueRelation L H)).mp heq
    change z - (glueRepresentative L H g : E) ∈ orthogonalGlueSubmodule L H at hdiff
    obtain ⟨n, hn, f, hf, hnf⟩ := Submodule.mem_sup.mp hdiff
    let nH : H := ⟨n, hn.2⟩
    let fW : Hᗮ := ⟨f, hf.2⟩
    refine ⟨g, nH + glueProjectedRepresentative L H g,
      fW + glueFibreRepresentative L H g, ?_, ?_, ?_⟩
    · change ((nH + glueProjectedRepresentative L H g) -
        glueProjectedRepresentative L H g : H) ∈ latticeIntersection L H
      rw [add_sub_cancel_right]
      change n ∈ L
      exact hn.1
    · change ((fW + glueFibreRepresentative L H g) -
        glueFibreRepresentative L H g : Hᗮ) ∈ latticeIntersection L Hᗮ
      rw [add_sub_cancel_right]
      change f ∈ L
      exact hf.1
    · have hrep := glueRepresentative_decomposition L H g
      simp only [Submodule.coe_add]
      change z = (n + (glueProjectedRepresentative L H g : E)) +
        (f + (glueFibreRepresentative L H g : E))
      have hzsum : z = (n + f) + (glueRepresentative L H g : E) :=
        sub_eq_iff_eq_add.mp hnf.symm
      rw [hzsum]
      rw [← hrep]
      abel
  · rintro ⟨g, x, t, hx, ht, rfl⟩
    have hxL : ((x : E) - (glueProjectedRepresentative L H g : E)) ∈ L := hx
    have htL : ((t : E) - (glueFibreRepresentative L H g : E)) ∈ L := ht
    have hrep := (glueRepresentative L H g).property
    have hsum := L.add_mem (L.add_mem hxL htL) hrep
    convert hsum using 1
    rw [← glueRepresentative_decomposition L H g]
    abel

/-- The canonical projected cosets are distinct.  Equality of the projected
cosets forces equality in the quotient by the two actual intersections. -/
theorem canonical_projected_cosets_distinct (L : Submodule ℤ E) (H : Submodule ℝ E) :
    Pairwise (fun g g' : OrthogonalGlueQuotient L H =>
      glueProjectedRepresentative L H g - glueProjectedRepresentative L H g' ∉
        latticeIntersection L H) := by
  intro g g' hne hproj
  apply hne
  have hprojL : ((glueProjectedRepresentative L H g : E) -
      (glueProjectedRepresentative L H g' : E)) ∈ L := hproj
  have hdiffL := L.sub_mem (glueRepresentative L H g).property
    (glueRepresentative L H g').property
  have hfibreL : ((glueFibreRepresentative L H g : E) -
      (glueFibreRepresentative L H g' : E)) ∈ L := by
    have hm := L.sub_mem hdiffL hprojL
    convert hm using 1
    rw [← glueRepresentative_decomposition L H g,
      ← glueRepresentative_decomposition L H g']
    abel
  have hsum : (glueRepresentative L H g : E) - (glueRepresentative L H g' : E) ∈
      orthogonalGlueSubmodule L H := by
    have hm := Submodule.add_mem_sup
      (show ((glueProjectedRepresentative L H g : E) -
        (glueProjectedRepresentative L H g' : E)) ∈ L ⊓ H.restrictScalars ℤ from
        ⟨hprojL, H.sub_mem (glueProjectedRepresentative L H g).property
          (glueProjectedRepresentative L H g').property⟩)
      (show ((glueFibreRepresentative L H g : E) -
        (glueFibreRepresentative L H g' : E)) ∈ L ⊓ Hᗮ.restrictScalars ℤ from
        ⟨hfibreL, Hᗮ.sub_mem (glueFibreRepresentative L H g).property
          (glueFibreRepresentative L H g').property⟩)
    change (glueRepresentative L H g : E) - (glueRepresentative L H g' : E) ∈
      (L ⊓ H.restrictScalars ℤ) ⊔ (L ⊓ Hᗮ.restrictScalars ℤ)
    convert hm using 1
    rw [← glueRepresentative_decomposition L H g,
      ← glueRepresentative_decomposition L H g']
    abel
  have hq := (Submodule.Quotient.eq (orthogonalGlueRelation L H)).mpr
    (show glueRepresentative L H g - glueRepresentative L H g' ∈
      orthogonalGlueRelation L H from hsum)
  simpa only [glueRepresentative, Submodule.Quotient.mk_out] using hq

/-- Rational complementary subspaces give a full-rank sum of intersections. -/
theorem orthogonalGlueSubmodule_span_top (L : Submodule ℤ E) (H : Submodule ℝ E)
    (hH : LatticeRational L H) (hW : LatticeRational L Hᗮ) :
    Submodule.span ℝ (orthogonalGlueSubmodule L H : Set E) = ⊤ := by
  apply le_antisymm le_top
  rw [← H.isCompl_orthogonal.sup_eq_top]
  apply sup_le
  · calc
      H = Submodule.span ℝ ((L ⊓ H.restrictScalars ℤ : Submodule ℤ E) : Set E) := hH.symm
      _ ≤ Submodule.span ℝ (orthogonalGlueSubmodule L H : Set E) :=
        Submodule.span_mono (fun _ hx => Submodule.mem_sup_left hx)
  · calc
      Hᗮ = Submodule.span ℝ ((L ⊓ Hᗮ.restrictScalars ℤ : Submodule ℤ E) : Set E) := hW.symm
      _ ≤ Submodule.span ℝ (orthogonalGlueSubmodule L H : Set E) :=
        Submodule.span_mono (fun _ hx => Submodule.mem_sup_right hx)

/-- The finite glue assertion follows from rationality; it is not an extra
finite-index assumption on the lattice or the subspaces. -/
theorem finite_orthogonalGlueQuotient
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (H : Submodule ℝ E) (hH : LatticeRational L H) (hW : LatticeRational L Hᗮ) :
    Finite (OrthogonalGlueQuotient L H) := by
  let K := orthogonalGlueSubmodule L H
  have hKL : K ≤ L := orthogonalGlueSubmodule_le L H
  letI : DiscreteTopology K := DiscreteTopology.of_subset
    (inferInstanceAs (DiscreteTopology L)) hKL
  letI : IsZLattice ℝ K := ⟨orthogonalGlueSubmodule_span_top L H hH hW⟩
  have hrank : Module.finrank ℤ (orthogonalGlueRelation L H) = Module.finrank ℤ L := by
    calc
      Module.finrank ℤ (orthogonalGlueRelation L H) = Module.finrank ℤ K :=
        (Submodule.comapSubtypeEquivOfLe hKL).finrank_eq
      _ = Module.finrank ℝ E := ZLattice.rank ℝ K
      _ = Module.finrank ℤ L := (ZLattice.rank ℝ L).symm
  exact Submodule.finiteQuotientOfFreeOfRankEq (orthogonalGlueRelation L H) hrank

/-- The full rational-subspace form of Proposition 6.1.  All finite glue data
are now constructed from the original lattice and subspace. -/
theorem rational_orthogonal_lattice_projection_transfer
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (H : Submodule ℝ E) (hH : LatticeRational L H) (hW : LatticeRational L Hᗮ)
    (t₀ : Hᗮ) (c : ℝ → ℝ)
    (hfibre : ∀ α : ℝ, 0 < α → ∀ g : OrthogonalGlueQuotient L H,
      normSetGaussian (latticeCoset (latticeIntersection L Hᗮ)
        (glueFibreRepresentative L H g)) α t₀ = c α)
    (K : Set E)
    (hK : ∀ α : ℝ, 0 < α → ∀ z : E,
      NormColdSpot (L : Set E) α z ↔ z ∈ K)
    (hmeet : ∃ x₀ : H, (x₀ : E) + (t₀ : E) ∈ K) :
    (∀ α : ℝ, 0 < α → ∀ x : H,
      NormColdSpot (latticeOrthogonalProjection L H : Set H) α x ↔
        (x : E) + (t₀ : E) ∈ K) ∧
    (∀ α : ℝ, 0 < α →
      sInf (Set.range (normSetGaussian (latticeOrthogonalProjection L H : Set H) α)) =
        sInf (Set.range (normSetGaussian (L : Set E) α)) / c α) ∧
    ((∀ z : E, z ∈ K ↔ NormDeepHole (L : Set E) z) → ∀ x : H,
      NormDeepHole (latticeOrthogonalProjection L H : Set H) x ↔
        (x : E) + (t₀ : E) ∈ K) := by
  letI : Finite (OrthogonalGlueQuotient L H) := finite_orthogonalGlueQuotient L H hH hW
  letI : Fintype (OrthogonalGlueQuotient L H) := Fintype.ofFinite _
  exact orthogonal_lattice_projection_transfer L H
    (glueProjectedRepresentative L H) (glueFibreRepresentative L H)
    (canonical_orthogonal_glue L H) (canonical_projected_cosets_distinct L H)
    t₀ c hfibre K hK hmeet

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.finite_orthogonalGlueQuotient
#print axioms PaperVerification.ColdSpots.rational_orthogonal_lattice_projection_transfer
end
end Source_RationalLatticeGlue
-- END ORIGINAL PaperVerification.RationalLatticeGlue


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
  let expected : Array Name := #[`PaperVerification.ColdSpots.canonical_orthogonal_glue, `PaperVerification.ColdSpots.canonical_projected_cosets_distinct, `PaperVerification.ColdSpots.coldSpot_coordinate_image, `PaperVerification.ColdSpots.deepHole_coordinate_image, `PaperVerification.ColdSpots.diagonalLatticeGlue_eq_orthogonalGlue, `PaperVerification.ColdSpots.diagonalLatticeGlue_gaussian_factorization, `PaperVerification.ColdSpots.discreteGaussian_laplace_limit, `PaperVerification.ColdSpots.discreteGaussian_log_sandwich, `PaperVerification.ColdSpots.euclideanLatticeCoset_gaussian_shift, `PaperVerification.ColdSpots.finite_orthogonalGlueQuotient, `PaperVerification.ColdSpots.finite_profile_projection_transfer, `PaperVerification.ColdSpots.gaussian_infimum_eq_of_equal_sums, `PaperVerification.ColdSpots.gaussian_range_coordinate_image, `PaperVerification.ColdSpots.latticeGaussian_minimum_pos, `PaperVerification.ColdSpots.latticeGaussian_shift_eq_of_sub_mem, `PaperVerification.ColdSpots.latticeGlueCosets_union, `PaperVerification.ColdSpots.lattice_coset_projection_transfer, `PaperVerification.ColdSpots.lattice_diagonal_gluing, `PaperVerification.ColdSpots.normDeepHole_iff_metric, `PaperVerification.ColdSpots.normSquaredDepth_eq_infDist_sq, `PaperVerification.ColdSpots.orthogonalGlueMap_bijective, `PaperVerification.ColdSpots.orthogonalGlueSubmodule_span_top, `PaperVerification.ColdSpots.orthogonalGlue_coordinate_image, `PaperVerification.ColdSpots.orthogonalProjection_coordinate_image, `PaperVerification.ColdSpots.orthogonal_lattice_projection_transfer, `PaperVerification.ColdSpots.orthogonal_summand_eq, `PaperVerification.ColdSpots.projection_common_fibre_depth, `PaperVerification.ColdSpots.projection_depth_factorization, `PaperVerification.ColdSpots.projection_gaussian_factorization, `PaperVerification.ColdSpots.projection_gaussian_minimum_value, `PaperVerification.ColdSpots.rational_orthogonal_lattice_projection_transfer, `PaperVerification.ColdSpots.setGaussian_coordinate_image, `PaperVerification.ColdSpots.setGaussian_orthogonalGlue, `PaperVerification.ColdSpots.sqDist_orthogonalCoordinates, `PaperVerification.ColdSpots.squaredDepth_coordinate_image, `PaperVerification.ColdSpots.squaredDepth_eq_of_gaussian_eq, `PaperVerification.ColdSpots.summable_gaussian_diagonalLatticeGlue_all, `PaperVerification.ColdSpots.summable_gaussian_euclideanLatticeCoset, `PaperVerification.ColdSpots.summable_gaussian_lattice_extension, `PaperVerification.ColdSpots.summable_gaussian_orthogonalGlue, `PaperVerification.ColdSpots.summable_gaussian_zlattice]
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
      ("type", if expected.contains name then toJson (toString ci.type) else Json.null),
      ("type_hash", toJson (hash ci.type).toNat),
      ("level_parameters", toJson (ci.levelParams.map Name.toString)),
      ("has_body", toJson (ci.value? (allowOpaque := true)).isSome),
      ("dependencies", Json.arr dependencyRows),
      ("axioms", toJson (axioms.map Name.toString))])
  for name in expected do
    if !entries.any (fun row => row.1 == name) then
      failures := failures.push (Json.mkObj [
        ("missing_required_endpoint", toJson name.toString)])
  let sourceHash ← IO.getEnv "PAPER_VERIFICATION_SOURCE_SHA256"
  let fingerprint ← IO.getEnv "PAPER_VERIFICATION_FINGERPRINT"
  let document := Json.mkObj [
    ("schema", toJson (2 : Nat)),
    ("type_hash_algorithm", toJson "Lean structural Expr hash; source SHA256 binds exact declarations"),
    ("module", toJson env.mainModule.toString),
    ("source_sha256", toJson sourceHash),
    ("fingerprint", toJson fingerprint),
    ("kernel_environment", toJson true),
    ("declarations", Json.arr rows),
    ("failures", Json.arr failures),
    ("passed", toJson failures.isEmpty)]
  let target := (← IO.getEnv "PAPER_VERIFICATION_AUDIT_PATH").getD ".lake/build/paper-audit/PaperVerification_Lattice008.json"
  let path : System.FilePath := target
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path (document.compress ++ "\n")
  if !failures.isEmpty then
    throwError "Kernel declaration audit rejected {failures.size} dependency/axiom findings; see {target}"
  logInfo m!"Kernel declaration audit passed for {rows.size} declarations; see {target}"
