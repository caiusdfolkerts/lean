module
import verification.internal.checkpoint
import verification.internal.extract
public import consolidated.pair_pin_progress01
import all consolidated.pair_pin_progress01
public import consolidated.pair_pin_progress02
import all consolidated.pair_pin_progress02
public import consolidated.rigidity_foundations01
import all consolidated.rigidity_foundations01
public import consolidated.rigidity_foundations02
import all consolidated.rigidity_foundations02
public import consolidated.rigidity_generic_tools
import all consolidated.rigidity_generic_tools
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Sym
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Data.Sym.Sym2
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Order.Minimal
public import Mathlib.Order.Preorder.Finite
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import papers.rigidity_mode_splitting
import all papers.rigidity_mode_splitting

set_option Elab.async false

section BundleSource0001
/- Source: Papers/RigidityVector3.lean -/









@[expose] public section

/-!
# Three-dimensional real coordinate vectors

The coordinate space is independent of the later classification and
integrability arguments. In particular, the pair-pin theorem depends on
the ordinary twist definitions without importing those separate proofs.
-/

namespace Papers.Rigidity

abbrev Vec3 := Fin 3 → ℝ

end Papers.Rigidity

end
end BundleSource0001

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0001/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0001.json"

section BundleSource0002
/- Source: Papers/RigidityWrenchRank.lean -/







@[expose] public section

/-!
# Rank of point-force wrench columns

The column at a point `p` with force direction `d` is literally
`(d, p × d)`. Nonzero directions avoiding every other point direction give
independence of any two columns. Four affinely independent points cannot
have all four columns in a two-dimensional space: a two-dimensional pencil
of force lines puts all their points in one plane.

This module is independent of the pair-pin defect formula. Its final bound
holds for every finite number of points, including the at-most-five case
used in Section 7.3 of the paper.
-/

namespace Papers.Rigidity.WrenchRank

noncomputable section

open Matrix
open scoped Matrix BigOperators

def wrench (p d : Vec3) : Vec3 × Vec3 := (d, p ⨯₃ d)

def wrenchSpan {I : Type*} (p d : I → Vec3) : Submodule ℝ (Vec3 × Vec3) :=
  Submodule.span ℝ (Set.range fun i => wrench (p i) (d i))

theorem wrench_ne_zero {p d : Vec3} (hd : d ≠ 0) : wrench p d ≠ 0 := by
  intro h
  exact hd (congrArg Prod.fst h)

/-- Force and moment equations, with the moment origin moved to `p`. -/
theorem relative_cross_eq_zero_of_combination
    (p₀ p₁ p d₀ d₁ d : Vec3) (a b : ℝ)
    (h : a • wrench p₀ d₀ + b • wrench p₁ d₁ = wrench p d) :
    a • ((p - p₀) ⨯₃ d₀) + b • ((p - p₁) ⨯₃ d₁) = 0 := by
  have hf : a • d₀ + b • d₁ = d := congrArg Prod.fst h
  have hm : a • (p₀ ⨯₃ d₀) + b • (p₁ ⨯₃ d₁) = p ⨯₃ d :=
    congrArg Prod.snd h
  calc
    a • ((p - p₀) ⨯₃ d₀) + b • ((p - p₁) ⨯₃ d₁) =
        p ⨯₃ (a • d₀ + b • d₁) -
          (a • (p₀ ⨯₃ d₀) + b • (p₁ ⨯₃ d₁)) := by
      ext k
      fin_cases k <;> simp [cross_apply] <;> ring
    _ = 0 := by rw [hf, hm, sub_self]

/-- Two forces cannot have proportional wrenches unless their lines coincide. -/
theorem pair_independent (p₀ p₁ d₀ d₁ : Vec3)
    (havoid : (p₀ - p₁) ⨯₃ d₀ ≠ 0) (hd₁ : d₁ ≠ 0) :
    LinearIndependent ℝ ![wrench p₀ d₀, wrench p₁ d₁] := by
  apply LinearIndependent.pair_iff.mpr
  intro a b h
  have h' : a • wrench p₀ d₀ + b • wrench p₁ d₁ = wrench p₁ 0 := by
    simpa [wrench] using h
  have hr := relative_cross_eq_zero_of_combination p₀ p₁ p₁ d₀ d₁ 0 a b h'
  have hs : a • ((p₀ - p₁) ⨯₃ d₀) = 0 := by
    calc
      a • ((p₀ - p₁) ⨯₃ d₀) =
          -(a • ((p₁ - p₀) ⨯₃ d₀) + b • ((p₁ - p₁) ⨯₃ d₁)) := by
        ext k
        fin_cases k <;> simp [cross_apply] <;> ring
      _ = 0 := by rw [hr]; simp
  have ha : a = 0 := (smul_eq_zero.mp hs).resolve_right havoid
  have hf : a • d₀ + b • d₁ = 0 := congrArg Prod.fst h
  have hb : b = 0 :=
    (smul_eq_zero.mp (by simpa [ha] using hf : b • d₁ = 0)).resolve_right hd₁
  exact ⟨ha, hb⟩

/-- A combination of two wrenches gives two scalar plane equations. -/
theorem plane_products_of_combination
    (p₀ p₁ p d₀ d₁ d : Vec3) (a b : ℝ)
    (h : a • wrench p₀ d₀ + b • wrench p₁ d₁ = wrench p d) :
    a * ((p - p₀) ⬝ᵥ (d₀ ⨯₃ d₁)) = 0 ∧
      b * ((p - p₁) ⬝ᵥ (d₀ ⨯₃ d₁)) = 0 := by
  have hr := relative_cross_eq_zero_of_combination p₀ p₁ p d₀ d₁ d a b h
  constructor
  · calc
      a * ((p - p₀) ⬝ᵥ (d₀ ⨯₃ d₁)) =
          (a • ((p - p₀) ⨯₃ d₀) + b • ((p - p₁) ⨯₃ d₁)) ⬝ᵥ d₁ := by
        simp [dotProduct, Fin.sum_univ_three, cross_apply]
        ring
      _ = 0 := by rw [hr]; simp
  · calc
      b * ((p - p₁) ⬝ᵥ (d₀ ⨯₃ d₁)) =
          -((a • ((p - p₀) ⨯₃ d₀) + b • ((p - p₁) ⨯₃ d₁)) ⬝ᵥ d₀) := by
        simp [dotProduct, Fin.sum_univ_three, cross_apply]
        ring
      _ = 0 := by rw [hr]; simp

/-- For parallel reference directions, a nonzero force still lies in one plane. -/
theorem plane_of_parallel_combination
    (p₀ p₁ p d₀ d₁ d : Vec3) (a b c : ℝ)
    (hc : d₁ = c • d₀) (hd : d ≠ 0)
    (h : a • wrench p₀ d₀ + b • wrench p₁ d₁ = wrench p d) :
    (p - p₀) ⬝ᵥ ((p₀ - p₁) ⨯₃ d₀) = 0 := by
  have hf : a • d₀ + b • d₁ = d := congrArg Prod.fst h
  have hk : a + b * c ≠ 0 := by
    intro hz
    apply hd
    calc
      d = a • d₀ + b • d₁ := hf.symm
      _ = (a + b * c) • d₀ := by rw [hc, add_smul, mul_smul]
      _ = 0 := by rw [hz, zero_smul]
  have hr := relative_cross_eq_zero_of_combination p₀ p₁ p d₀ d₁ d a b h
  have hs : (a + b * c) * ((p - p₀) ⬝ᵥ ((p₀ - p₁) ⨯₃ d₀)) = 0 := by
    calc
      (a + b * c) * ((p - p₀) ⬝ᵥ ((p₀ - p₁) ⨯₃ d₀)) =
          -((a • ((p - p₀) ⨯₃ d₀) + b • ((p - p₁) ⨯₃ d₁)) ⬝ᵥ (p₀ - p₁)) := by
        rw [hc]
        simp [dotProduct, Fin.sum_univ_three, cross_apply]
        ring
      _ = 0 := by rw [hr]; simp
  exact (mul_eq_zero.mp hs).resolve_left hk

/-- Three independent displacement vectors admit no nonzero common normal. -/
theorem normal_eq_zero_of_independent (v : Fin 3 → Vec3)
    (hv : LinearIndependent ℝ v) (n : Vec3) (hn : ∀ i, v i ⬝ᵥ n = 0) : n = 0 := by
  let L : Vec3 →ₗ[ℝ] ℝ :=
    { toFun := fun x => x ⬝ᵥ n
      map_add' := fun x y => add_dotProduct x y n
      map_smul' := fun c x => smul_dotProduct c x n }
  have htop : Submodule.span ℝ (Set.range v) = ⊤ :=
    hv.span_eq_top_of_card_eq_finrank (by simp [Vec3])
  have hsub : Submodule.span ℝ (Set.range v) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact hn i
  have hn' : n ∈ L.ker := hsub (by rw [htop]; trivial)
  change n ⬝ᵥ n = 0 at hn'
  exact dotProduct_self_eq_zero.mp hn'

theorem combination_coefficients_ne_zero
    (p d : Fin 4 → Vec3) (hd : ∀ i, d i ≠ 0)
    (havoid : ∀ i j, i ≠ j → (p i - p j) ⨯₃ d i ≠ 0)
    (i : Fin 4) (hi₀ : i ≠ 0) (hi₁ : i ≠ 1) (a b : ℝ)
    (h : a • wrench (p 0) (d 0) + b • wrench (p 1) (d 1) = wrench (p i) (d i)) :
    a ≠ 0 ∧ b ≠ 0 := by
  constructor
  · intro ha
    have hli := pair_independent (p 1) (p i) (d 1) (d i)
      (havoid 1 i hi₁.symm) (hd i)
    have hne := (LinearIndependent.pair_iff' (wrench_ne_zero (hd 1))).mp hli b
    exact hne (by simpa [ha] using h)
  · intro hb
    have hli := pair_independent (p 0) (p i) (d 0) (d i)
      (havoid 0 i hi₀.symm) (hd i)
    have hne := (LinearIndependent.pair_iff' (wrench_ne_zero (hd 0))).mp hli a
    exact hne (by simpa [hb] using h)

/-- Four noncoplanar points cannot have all their force lines in one pencil. -/
theorem four_not_all_mem_span_pair
    (p d : Fin 4 → Vec3)
    (hp : LinearIndependent ℝ (fun i : Fin 3 => p i.succ - p 0))
    (hd : ∀ i, d i ≠ 0)
    (havoid : ∀ i j, i ≠ j → (p i - p j) ⨯₃ d i ≠ 0) :
    ¬ ∀ i, wrench (p i) (d i) ∈
      Submodule.span ℝ ({wrench (p 0) (d 0), wrench (p 1) (d 1)} : Set (Vec3 × Vec3)) := by
  intro hspan
  by_cases hpar : d 0 ⨯₃ d 1 = 0
  · have hdep : ¬ LinearIndependent ℝ ![d 0, d 1] := by
      intro hli
      exact (crossProduct_ne_zero_iff_linearIndependent.mpr hli) hpar
    have hnot : ¬ ∀ c : ℝ, c • d 0 ≠ d 1 :=
      fun hc => hdep ((LinearIndependent.pair_iff' (hd 0)).mpr hc)
    obtain ⟨c, hc⟩ := not_forall_not.mp hnot
    have hn : (p 0 - p 1) ⨯₃ d 0 ≠ 0 := havoid 0 1 (by decide)
    apply hn
    apply normal_eq_zero_of_independent _ hp
    intro i
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hspan i.succ)
    exact plane_of_parallel_combination (p 0) (p 1) (p i.succ)
      (d 0) (d 1) (d i.succ) a b c hc.symm (hd i.succ) hab
  · obtain ⟨a₂, b₂, h₂⟩ := Submodule.mem_span_pair.mp (hspan 2)
    obtain ⟨a₃, b₃, h₃⟩ := Submodule.mem_span_pair.mp (hspan 3)
    have hc₂ := combination_coefficients_ne_zero p d hd havoid 2
      (by decide) (by decide) a₂ b₂ h₂
    have hc₃ := combination_coefficients_ne_zero p d hd havoid 3
      (by decide) (by decide) a₃ b₃ h₃
    have he₂ := plane_products_of_combination (p 0) (p 1) (p 2)
      (d 0) (d 1) (d 2) a₂ b₂ h₂
    have he₃ := plane_products_of_combination (p 0) (p 1) (p 3)
      (d 0) (d 1) (d 3) a₃ b₃ h₃
    have h₂₀ : (p 2 - p 0) ⬝ᵥ (d 0 ⨯₃ d 1) = 0 :=
      (mul_eq_zero.mp he₂.1).resolve_left hc₂.1
    have h₂₁ : (p 2 - p 1) ⬝ᵥ (d 0 ⨯₃ d 1) = 0 :=
      (mul_eq_zero.mp he₂.2).resolve_left hc₂.2
    have h₃₀ : (p 3 - p 0) ⬝ᵥ (d 0 ⨯₃ d 1) = 0 :=
      (mul_eq_zero.mp he₃.1).resolve_left hc₃.1
    have h₁₀ : (p 1 - p 0) ⬝ᵥ (d 0 ⨯₃ d 1) = 0 := by
      simp only [sub_dotProduct] at h₂₀ h₂₁ ⊢
      linarith
    apply hpar
    apply normal_eq_zero_of_independent _ hp
    intro i
    fin_cases i
    · simpa using h₁₀
    · simpa using h₂₀
    · simpa using h₃₀

theorem pair_span_finrank (p₀ p₁ d₀ d₁ : Vec3)
    (havoid : (p₀ - p₁) ⨯₃ d₀ ≠ 0) (hd₁ : d₁ ≠ 0) :
    Module.finrank ℝ
      (Submodule.span ℝ ({wrench p₀ d₀, wrench p₁ d₁} : Set (Vec3 × Vec3))) = 2 := by
  have hrange : Set.range (![wrench p₀ d₀, wrench p₁ d₁] : Fin 2 → Vec3 × Vec3) =
      ({wrench p₀ d₀, wrench p₁ d₁} : Set (Vec3 × Vec3)) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hr := finrank_span_eq_card (pair_independent p₀ p₁ d₀ d₁ havoid hd₁)
  rw [hrange] at hr
  simpa using hr

theorem four_point_rank_ge_three
    (p d : Fin 4 → Vec3)
    (hp : LinearIndependent ℝ (fun i : Fin 3 => p i.succ - p 0))
    (hd : ∀ i, d i ≠ 0)
    (havoid : ∀ i j, i ≠ j → (p i - p j) ⨯₃ d i ≠ 0) :
    3 ≤ Module.finrank ℝ (wrenchSpan p d) := by
  by_contra h
  have hdim : Module.finrank ℝ (wrenchSpan p d) ≤ 2 := by omega
  let S : Submodule ℝ (Vec3 × Vec3) :=
    Submodule.span ℝ ({wrench (p 0) (d 0), wrench (p 1) (d 1)} : Set (Vec3 × Vec3))
  have hS : Module.finrank ℝ S = 2 :=
    pair_span_finrank (p 0) (p 1) (d 0) (d 1) (havoid 0 1 (by decide)) (hd 1)
  have hle : S ≤ wrenchSpan p d := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      exact Submodule.subset_span ⟨0, rfl⟩
    · have hx' := Set.mem_singleton_iff.mp hx
      subst x
      exact Submodule.subset_span ⟨1, rfl⟩
  have heq : S = wrenchSpan p d :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hS]; exact hdim)
  apply four_not_all_mem_span_pair p d hp hd havoid
  intro i
  change wrench (p i) (d i) ∈ S
  rw [heq]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem wrenchSpan_finrank_comp_le {I J : Type*} (p d : I → Vec3) (f : J → I) :
    Module.finrank ℝ (wrenchSpan (p ∘ f) (d ∘ f)) ≤
      Module.finrank ℝ (wrenchSpan p d) := by
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  exact ⟨f i, rfl⟩

theorem one_le_wrenchSpan_finrank {I : Type*} (p d : I → Vec3) (i : I)
    (hd : d i ≠ 0) : 1 ≤ Module.finrank ℝ (wrenchSpan p d) := by
  have hle : Submodule.span ℝ ({wrench (p i) (d i)} : Set (Vec3 × Vec3)) ≤
      wrenchSpan p d := by
    apply Submodule.span_le.mpr
    intro x hx
    have hx' := Set.mem_singleton_iff.mp hx
    subst x
    exact Submodule.subset_span ⟨i, rfl⟩
  have h := Submodule.finrank_mono hle
  simpa [finrank_span_singleton (K := ℝ) (wrench_ne_zero hd)] using h

theorem two_le_wrenchSpan_finrank {I : Type*} (p d : I → Vec3) (i j : I)
    (havoid : (p i - p j) ⨯₃ d i ≠ 0) (hd : d j ≠ 0) :
    2 ≤ Module.finrank ℝ (wrenchSpan p d) := by
  have hle : Submodule.span ℝ ({wrench (p i) (d i), wrench (p j) (d j)} :
      Set (Vec3 × Vec3)) ≤ wrenchSpan p d := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      exact Submodule.subset_span ⟨i, rfl⟩
    · have hx' := Set.mem_singleton_iff.mp hx
      subst x
      exact Submodule.subset_span ⟨j, rfl⟩
  have h := Submodule.finrank_mono hle
  rwa [pair_span_finrank (p i) (p j) (d i) (d j) havoid hd] at h

/-- The exact wrench-rank lower bound used in the small-body budget. -/
theorem wrench_rank_lower_bound {I : Type*} [Fintype I]
    (p d : I → Vec3)
    (hp : ∀ f : Fin 4 ↪ I,
      LinearIndependent ℝ (fun i : Fin 3 => p (f i.succ) - p (f 0)))
    (hd : ∀ i, d i ≠ 0)
    (havoid : ∀ i j, i ≠ j → (p i - p j) ⨯₃ d i ≠ 0) :
    min (Fintype.card I) 2 + (if 4 ≤ Fintype.card I then 1 else 0) ≤
      Module.finrank ℝ (wrenchSpan p d) := by
  classical
  have h₁ (hc : 1 ≤ Fintype.card I) : 1 ≤ Module.finrank ℝ (wrenchSpan p d) := by
    obtain ⟨f : Fin 1 ↪ I⟩ :=
      Function.Embedding.nonempty_of_card_le (α := Fin 1) (β := I) (by simpa using hc)
    exact one_le_wrenchSpan_finrank p d (f 0) (hd (f 0))
  have h₂ (hc : 2 ≤ Fintype.card I) : 2 ≤ Module.finrank ℝ (wrenchSpan p d) := by
    obtain ⟨f : Fin 2 ↪ I⟩ :=
      Function.Embedding.nonempty_of_card_le (α := Fin 2) (β := I) (by simpa using hc)
    exact two_le_wrenchSpan_finrank p d (f 0) (f 1)
      (havoid (f 0) (f 1) (f.injective.ne (by decide))) (hd (f 1))
  have h₃ (hc : 4 ≤ Fintype.card I) : 3 ≤ Module.finrank ℝ (wrenchSpan p d) := by
    obtain ⟨f : Fin 4 ↪ I⟩ :=
      Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := I) (by simpa using hc)
    have hlocal : 3 ≤ Module.finrank ℝ (wrenchSpan (p ∘ f) (d ∘ f)) :=
      four_point_rank_ge_three (p ∘ f) (d ∘ f) (hp f) (fun i => hd (f i))
        (fun i j hij => havoid (f i) (f j) (f.injective.ne hij))
    exact hlocal.trans (wrenchSpan_finrank_comp_le p d f)
  split_ifs with hfour
  · have := h₃ hfour
    omega
  · by_cases htwo : 2 ≤ Fintype.card I
    · have := h₂ htwo
      omega
    · by_cases hone : 1 ≤ Fintype.card I
      · have := h₁ hone
        omega
      · omega

end

end Papers.Rigidity.WrenchRank

end
end BundleSource0002

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0002/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0002.json"

section BundleSource0003
/- Source: Papers/RigidityZheng_Incidence_UniversalHomogeneousChart.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Incidence/UniversalHomogeneousChart.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
The imported incidence definitions are factored into SparseNullCore;
all definitions, statements, and proofs in this file are retained.
-/





@[expose] public section

/-!
# The universal homogeneous incidence chart

This file separates pin provenance from twist provenance in one nested
polynomial ring.  The pin coordinates live in the coefficient ring

`S = ℚ[PinVariable E]`,

while the outer variables are the six grounded twist coordinates.  Thus the
ordinary grading of the outer polynomial ring is exactly the twist grading:
the Split--Klein null equation has degree two and each pin-compatibility
coordinate has degree one.

The last section supplies the semantic bridge to real incidence
realizations.  It evaluates the pin coefficients at the given placement and
the outer variables at the grounded twist assignment, and proves that all
active null and compatibility equations vanish.  No height, elimination, or
properness conclusion is made here.
-/

namespace RB31E2E

namespace UniversalHomogeneousChart

noncomputable section

open MvPolynomial
open GroundedTwistPolynomial

/-! ## The two provenance layers -/

/-- The inner coefficient ring retaining every pin occurrence and spatial
coordinate. -/
abbrev PinParameterRing (E : Type*) :=
  MvPolynomial (PinVariable E) ℚ

/-- The outer variables are precisely the six coordinates of every
off-root body twist. -/
abbrev GroundedTwistVariable {V : Type*} (root : V) :=
  GroundedColumn root

/-- The relative coordinate ring `S[τ]`: pin parameters are coefficients,
and only the grounded twist variables contribute to its standard grading. -/
abbrev RelativeRing {V : Type*} (root : V) (E : Type*) :=
  MvPolynomial (GroundedTwistVariable root) (PinParameterRing E)

/-! ## Universal pins and grounded twists -/

/-- One universal off-root twist in the outer variables. -/
def universalOffRootTwist {V E : Type*} {root : V}
    (w : OffRoot root) : Twist (RelativeRing root E) :=
  ⟨fun i ↦ X ⟨w, ⟨false, i⟩⟩,
    fun i ↦ X ⟨w, ⟨true, i⟩⟩⟩

/-- The universal grounded twist: the root is zero and every other body has
its own six outer variables. -/
def universalGroundedTwist {V E : Type*} [DecidableEq V] (root : V) :
    V → Twist (RelativeRing root E) :=
  extendOffRoot root (fun w ↦ universalOffRootTwist (E := E) w)

/-- A pin is a coefficient-valued vector in the outer polynomial ring. -/
def universalParameterPin {V E : Type*} {root : V} (e : E) :
    Vec3 (RelativeRing root E) :=
  fun i ↦ C (X ⟨e, i⟩)

/-- The relative universal twist belonging to one oriented occurrence. -/
def universalRelativeTwist {V E : Type*} [DecidableEq V] (root : V)
    (src dst : E → V) (e : E) : Twist (RelativeRing root E) :=
  universalGroundedTwist (E := E) root (src e) -
    universalGroundedTwist (E := E) root (dst e)

/-- The quadratic Split--Klein equation forced by a stationary pin. -/
def universalNullEquation {V E : Type*} [DecidableEq V] (root : V)
    (src dst : E → V) (e : E) : RelativeRing root E :=
  Twist.splitKlein (universalRelativeTwist root src dst e)

/-- One of the three linear pin-compatibility coordinates. -/
def universalCompatibilityCoordinate {V E : Type*} [DecidableEq V]
    (root : V) (src dst : E → V) (e : E) (j : Fin 3) :
    RelativeRing root E :=
  Twist.eval (universalRelativeTwist root src dst e)
      (universalParameterPin (root := root) e) j

/-! ## Homogeneity in the outer twist grading -/

theorem universalGroundedTwist_angular_isHomogeneous_one
    {V E : Type*} [DecidableEq V] (root v : V) (i : Fin 3) :
    ((universalGroundedTwist (E := E) root v).1 i).IsHomogeneous 1 := by
  by_cases hv : v = root
  · subst v
    simp [universalGroundedTwist,
      GroundedTwistPolynomial.extendOffRoot,
      MvPolynomial.isHomogeneous_zero]
  · simp [universalGroundedTwist,
      GroundedTwistPolynomial.extendOffRoot, hv,
      universalOffRootTwist, MvPolynomial.isHomogeneous_X]

theorem universalGroundedTwist_translational_isHomogeneous_one
    {V E : Type*} [DecidableEq V] (root v : V) (i : Fin 3) :
    ((universalGroundedTwist (E := E) root v).2 i).IsHomogeneous 1 := by
  by_cases hv : v = root
  · subst v
    simp [universalGroundedTwist,
      GroundedTwistPolynomial.extendOffRoot,
      MvPolynomial.isHomogeneous_zero]
  · simp [universalGroundedTwist,
      GroundedTwistPolynomial.extendOffRoot, hv,
      universalOffRootTwist, MvPolynomial.isHomogeneous_X]

theorem universalRelativeTwist_angular_isHomogeneous_one
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) :
    ((universalRelativeTwist root src dst e).1 i).IsHomogeneous 1 := by
  exact (universalGroundedTwist_angular_isHomogeneous_one
      (E := E) root (src e) i).sub
    (universalGroundedTwist_angular_isHomogeneous_one
      (E := E) root (dst e) i)

theorem universalRelativeTwist_translational_isHomogeneous_one
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) :
    ((universalRelativeTwist root src dst e).2 i).IsHomogeneous 1 := by
  exact (universalGroundedTwist_translational_isHomogeneous_one
      (E := E) root (src e) i).sub
    (universalGroundedTwist_translational_isHomogeneous_one
      (E := E) root (dst e) i)

private theorem universalNullTerm_isHomogeneous_two
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) :
    (((universalRelativeTwist root src dst e).1 i) *
      ((universalRelativeTwist root src dst e).2 i)).IsHomogeneous 2 := by
  simpa using
    (universalRelativeTwist_angular_isHomogeneous_one root src dst e i).mul
      (universalRelativeTwist_translational_isHomogeneous_one
        root src dst e i)

/-- The universal null equation is homogeneous of twist degree two. -/
theorem universalNullEquation_isHomogeneous_two
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) :
    (universalNullEquation root src dst e).IsHomogeneous 2 := by
  simp only [universalNullEquation, Twist.splitKlein, Vec3.dot]
  simpa using MvPolynomial.IsHomogeneous.sum Finset.univ
    (fun i ↦
      ((universalRelativeTwist root src dst e).1 i) *
        ((universalRelativeTwist root src dst e).2 i))
    2 (fun i _ ↦
      universalNullTerm_isHomogeneous_two root src dst e i)

private theorem universalCrossTerm_isHomogeneous_one
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i j : Fin 3) :
    (((universalRelativeTwist root src dst e).1 i) *
      universalParameterPin (root := root) e j).IsHomogeneous 1 := by
  simpa [universalParameterPin] using
    (universalRelativeTwist_angular_isHomogeneous_one root src dst e i).mul
      (MvPolynomial.isHomogeneous_C (GroundedTwistVariable root)
        (X (⟨e, j⟩ : PinVariable E) : PinParameterRing E))

/-- Every compatibility coordinate is homogeneous of twist degree one.
The pin coordinates have degree zero because they belong to the coefficient
ring. -/
theorem universalCompatibilityCoordinate_isHomogeneous_one
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (j : Fin 3) :
    (universalCompatibilityCoordinate root src dst e j).IsHomogeneous 1 := by
  fin_cases j
  all_goals
    simp only [universalCompatibilityCoordinate, Twist.eval, Vec3.cross,
      Pi.add_apply]
    apply (universalRelativeTwist_translational_isHomogeneous_one
      root src dst e _).add
    apply (universalCrossTerm_isHomogeneous_one root src dst e _ _).sub
      (universalCrossTerm_isHomogeneous_one root src dst e _ _)

/-! ## Evaluation at a real incidence realization -/

/-- Specialize the inner pin-parameter ring at a real placement. -/
def pinParameterEvaluation {E : Type*} (p : E → Vec3 ℝ) :
    PinParameterRing E →+* ℝ :=
  MvPolynomial.eval₂Hom (Rat.castHom ℝ) (assignmentOfPins p)

/-- Assign each outer variable the corresponding coordinate of the grounded
real twist `Y(w) - Y(root)`. -/
def groundedTwistAssignment {V : Type*} (root : V) (Y : V → Twist ℝ) :
    GroundedTwistVariable root → ℝ :=
  fun c ↦ twistCoordinates (Y c.1.1 - Y root) c.2

/-- Simultaneously specialize the pin coefficients and grounded twist
variables. -/
def realChartEvaluation {V E : Type*} (root : V)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ) :
    RelativeRing root E →+* ℝ :=
  MvPolynomial.eval₂Hom (pinParameterEvaluation p)
    (groundedTwistAssignment root Y)

@[simp]
theorem pinParameterEvaluation_X {E : Type*} (p : E → Vec3 ℝ)
    (e : E) (i : Fin 3) :
    pinParameterEvaluation p (X (⟨e, i⟩ : PinVariable E)) = p e i := by
  simp [pinParameterEvaluation, assignmentOfPins]

@[simp]
theorem realChartEvaluation_X {V E : Type*} (root : V)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ)
    (c : GroundedTwistVariable root) :
    realChartEvaluation root p Y (X c) =
      twistCoordinates (Y c.1.1 - Y root) c.2 := by
  simp [realChartEvaluation, groundedTwistAssignment]

@[simp]
theorem realChartEvaluation_pinCoefficient {V E : Type*} (root : V)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ)
    (e : E) (i : Fin 3) :
    realChartEvaluation root p Y
        (C (X (⟨e, i⟩ : PinVariable E))) = p e i := by
  simp [realChartEvaluation]

/-- The universal coefficient-valued pin specializes to the actual pin. -/
theorem map_universalParameterPin {V E : Type*} {root : V}
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ) (e : E) :
    mapVec3 (realChartEvaluation root p Y)
        (universalParameterPin (root := root) e) = p e := by
  funext i
  simp [mapVec3, universalParameterPin]

/-- The universal grounded twist specializes exactly to grounding by
subtraction at `root`. -/
theorem map_universalGroundedTwist {V E : Type*} [DecidableEq V]
    (root v : V) (p : E → Vec3 ℝ) (Y : V → Twist ℝ) :
    mapTwist (realChartEvaluation root p Y)
        (universalGroundedTwist (E := E) root v) = Y v - Y root := by
  by_cases hv : v = root
  · subst v
    simp [universalGroundedTwist,
      GroundedTwistPolynomial.extendOffRoot]
  · apply Prod.ext <;> funext i
    · simp [mapTwist, mapVec3, universalGroundedTwist,
        GroundedTwistPolynomial.extendOffRoot, hv,
        universalOffRootTwist]
    · simp [mapTwist, mapVec3, universalGroundedTwist,
        GroundedTwistPolynomial.extendOffRoot, hv,
        universalOffRootTwist]

/-- Relative universal twists specialize without retaining the arbitrary
grounding body. -/
theorem map_universalRelativeTwist {V E : Type*} [DecidableEq V]
    (root : V) (src dst : E → V) (p : E → Vec3 ℝ)
    (Y : V → Twist ℝ) (e : E) :
    mapTwist (realChartEvaluation root p Y)
        (universalRelativeTwist root src dst e) =
      Y (src e) - Y (dst e) := by
  rw [universalRelativeTwist, mapTwist_sub,
    map_universalGroundedTwist, map_universalGroundedTwist]
  module

private theorem map_splitKlein
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (Z : Twist R) :
    f (Twist.splitKlein Z) = Twist.splitKlein (mapTwist f Z) := by
  simp [Twist.splitKlein, Vec3.dot, mapTwist, mapVec3]

/-- Evaluation of a universal compatibility coordinate is exactly the
corresponding coordinate of the concrete relative pin velocity. -/
theorem realChartEvaluation_universalCompatibilityCoordinate
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ) (e : E) (j : Fin 3) :
    realChartEvaluation root p Y
        (universalCompatibilityCoordinate root src dst e j) =
      Twist.eval (Y (src e) - Y (dst e)) (p e) j := by
  have h := congrFun
    (mapVec3_eval (realChartEvaluation root p Y)
      (universalRelativeTwist root src dst e)
      (universalParameterPin (root := root) e)) j
  simpa [universalCompatibilityCoordinate, mapVec3,
    map_universalRelativeTwist, map_universalParameterPin] using h

/-- Evaluation of the universal null equation is the concrete
Split--Klein value of the relative twist. -/
theorem realChartEvaluation_universalNullEquation
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ) (e : E) :
    realChartEvaluation root p Y (universalNullEquation root src dst e) =
      Twist.splitKlein (Y (src e) - Y (dst e)) := by
  rw [universalNullEquation, map_splitKlein,
    map_universalRelativeTwist]

/-- Every selected incidence occurrence annihilates all three universal
compatibility coordinates. -/
theorem IsIncidenceRealization.realChartEvaluation_compatibility_eq_zero
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : SparseNullIncidence.IsIncidenceRealization src dst active p Y)
    (root : V) (e : active) (j : Fin 3) :
    realChartEvaluation root p Y
        (universalCompatibilityCoordinate root src dst e.1 j) = 0 := by
  rw [realChartEvaluation_universalCompatibilityCoordinate]
  exact congrFun (hY.2 e) j

/-- Every selected incidence occurrence annihilates its universal quadratic
null equation. -/
theorem IsIncidenceRealization.realChartEvaluation_null_eq_zero
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : SparseNullIncidence.IsIncidenceRealization src dst active p Y)
    (root : V) (e : active) :
    realChartEvaluation root p Y
        (universalNullEquation root src dst e.1) = 0 := by
  rw [realChartEvaluation_universalNullEquation]
  exact Twist.splitKlein_eq_zero_of_eval_eq_zero
    (Y (src e.1) - Y (dst e.1)) (p e.1) (hY.2 e)

end

end UniversalHomogeneousChart

end RB31E2E


end
end BundleSource0003

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0003/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0003.json"

section BundleSource0004
/- Source: Papers/RigidityZheng_Incidence_UniversalChartIdeal.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Incidence/UniversalChartIdeal.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Ideals on a universal incidence chart

This file packages the homogeneous equations from
`UniversalHomogeneousChart` into provenance-retaining generator sets and
ideals.  A chart chooses one angular coordinate for every active occurrence;
the linear part retains exactly the other two compatibility coordinates.
A separately selected subfamily of active occurrences contributes its
quadratic Split--Klein null equations.

The resulting ideal is homogeneous for the standard grading in the outer
grounded-twist variables.  Every concrete `IsIncidenceRealization` annihilates
the ideal under `realChartEvaluation`.  No denominator inversion, triangular
solution formula, height estimate, or elimination statement is used here.
-/

namespace RB31E2E

namespace UniversalHomogeneousChart

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Provenance indices and generator sets -/

/-- After choosing the angular chart coordinate `i`, these are precisely the
other two compatibility coordinates. -/
abbrev OtherCompatibilityCoordinate (i : Fin 3) :=
  {j : Fin 3 // j ≠ i}

/-- Provenance for the two retained linear equations at every active
occurrence. -/
abbrev ActiveCompatibilityIndex {E : Type*} [DecidableEq E]
    (active : Finset E) (chart : active → Fin 3) :=
  Σ e : active, OtherCompatibilityCoordinate (chart e)

/-- The compatibility polynomial indexed by an active occurrence and one of
the two coordinates different from its chosen angular chart coordinate. -/
def activeCompatibilityGenerator
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (a : ActiveCompatibilityIndex active chart) :
    RelativeRing root E :=
  universalCompatibilityCoordinate root src dst a.1.1 a.2.1

/-- All retained degree-one compatibility equations, with occurrence and
coordinate provenance kept in the range index. -/
def activeCompatibilityGeneratorSet
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) : Set (RelativeRing root E) :=
  Set.range (activeCompatibilityGenerator root src dst active chart)

/-- The ideal generated by the two retained compatibility coordinates at
each active occurrence. -/
def activeCompatibilityIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) : Ideal (RelativeRing root E) :=
  Ideal.span (activeCompatibilityGeneratorSet root src dst active chart)

/-- A selected occurrence is active by construction; no later subset proof
is needed to use its incidence equation. -/
abbrev SelectedOccurrence {E : Type*} [DecidableEq E]
    (active : Finset E) (selected : Finset active) :=
  {e : active // e ∈ selected}

/-- The degree-two null equation carrying the provenance of one selected
active occurrence. -/
def selectedNullGenerator
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (selected : Finset active) (e : SelectedOccurrence active selected) :
    RelativeRing root E :=
  universalNullEquation root src dst e.1.1

/-- The selected family of quadratic Split--Klein null equations. -/
def selectedNullGeneratorSet
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (selected : Finset active) : Set (RelativeRing root E) :=
  Set.range (selectedNullGenerator root src dst active selected)

/-- The complete chart generator set: two linear compatibility equations per
active occurrence and one quadratic null equation per selected occurrence. -/
def universalChartGeneratorSet
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active) :
    Set (RelativeRing root E) :=
  activeCompatibilityGeneratorSet root src dst active chart ∪
    selectedNullGeneratorSet root src dst active selected

/-- The universal homogeneous chart ideal. -/
def universalChartIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active) :
    Ideal (RelativeRing root E) :=
  Ideal.span
    (universalChartGeneratorSet root src dst active chart selected)

/-! ## Standard twist homogeneity -/

/-- Every retained compatibility generator has twist degree one. -/
theorem activeCompatibilityGenerator_isHomogeneous_one
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (a : ActiveCompatibilityIndex active chart) :
    (activeCompatibilityGenerator root src dst active chart a).IsHomogeneous 1 := by
  exact universalCompatibilityCoordinate_isHomogeneous_one
    root src dst a.1.1 a.2.1

/-- The linear active-compatibility ideal is homogeneous for the standard
grading in the outer twist variables. -/
theorem activeCompatibilityIdeal_isHomogeneous
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) :
    (activeCompatibilityIdeal root src dst active chart).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule
        (GroundedTwistVariable root) (PinParameterRing E)) := by
  apply Ideal.homogeneous_span
    (MvPolynomial.homogeneousSubmodule
      (GroundedTwistVariable root) (PinParameterRing E))
    (activeCompatibilityGeneratorSet root src dst active chart)
  intro f hf
  obtain ⟨a, rfl⟩ := hf
  exact ⟨1, activeCompatibilityGenerator_isHomogeneous_one
    root src dst active chart a⟩

/-- Every selected null generator has twist degree two. -/
theorem selectedNullGenerator_isHomogeneous_two
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (selected : Finset active) (e : SelectedOccurrence active selected) :
    (selectedNullGenerator root src dst active selected e).IsHomogeneous 2 := by
  exact universalNullEquation_isHomogeneous_two root src dst e.1.1

/-- Every generator of the complete chart ideal is homogeneous, with its
degree determined by its provenance branch. -/
theorem universalChartGeneratorSet_isHomogeneous
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active) :
    ∀ f ∈ universalChartGeneratorSet root src dst active chart selected,
      ∃ d : ℕ, f.IsHomogeneous d := by
  intro f hf
  rcases hf with hf | hf
  · obtain ⟨a, rfl⟩ := hf
    exact ⟨1, activeCompatibilityGenerator_isHomogeneous_one
      root src dst active chart a⟩
  · obtain ⟨e, rfl⟩ := hf
    exact ⟨2, selectedNullGenerator_isHomogeneous_two
      root src dst active selected e⟩

/-- The full linear-plus-quadratic chart ideal is standard homogeneous in
the grounded-twist variables. -/
theorem universalChartIdeal_isHomogeneous
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active) :
    (universalChartIdeal root src dst active chart selected).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule
        (GroundedTwistVariable root) (PinParameterRing E)) := by
  apply Ideal.homogeneous_span
    (MvPolynomial.homogeneousSubmodule
      (GroundedTwistVariable root) (PinParameterRing E))
    (universalChartGeneratorSet root src dst active chart selected)
  exact universalChartGeneratorSet_isHomogeneous
    root src dst active chart selected

/-! ## Semantic annihilation by actual incidence realizations -/

/-- Every actual incidence realization annihilates the retained linear
compatibility ideal, for every chart choice. -/
theorem IsIncidenceRealization.realChartEvaluation_annihilates_activeCompatibilityIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : SparseNullIncidence.IsIncidenceRealization src dst active p Y)
    (root : V) (chart : active → Fin 3) :
    activeCompatibilityIdeal root src dst active chart ≤
      RingHom.ker (realChartEvaluation root p Y) := by
  rw [activeCompatibilityIdeal, Ideal.span_le]
  rintro _ ⟨a, rfl⟩
  change realChartEvaluation root p Y
      (activeCompatibilityGenerator root src dst active chart a) = 0
  exact IsIncidenceRealization.realChartEvaluation_compatibility_eq_zero
    hY root a.1 a.2.1

/-- Every actual incidence realization annihilates all selected quadratic
null generators. -/
theorem IsIncidenceRealization.realChartEvaluation_annihilates_selectedNullGeneratorSet
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : SparseNullIncidence.IsIncidenceRealization src dst active p Y)
    (root : V) (selected : Finset active) :
    ∀ f ∈ selectedNullGeneratorSet root src dst active selected,
      realChartEvaluation root p Y f = 0 := by
  intro _ hf
  obtain ⟨e, rfl⟩ := hf
  exact IsIncidenceRealization.realChartEvaluation_null_eq_zero hY root e.1

/-- End-to-end semantic bridge for this layer: every concrete incidence
realization sends the complete universal chart ideal to zero. -/
theorem IsIncidenceRealization.realChartEvaluation_annihilates_universalChartIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : SparseNullIncidence.IsIncidenceRealization src dst active p Y)
    (root : V) (chart : active → Fin 3) (selected : Finset active) :
    universalChartIdeal root src dst active chart selected ≤
      RingHom.ker (realChartEvaluation root p Y) := by
  rw [universalChartIdeal, Ideal.span_le]
  intro f hf
  rcases hf with hf | hf
  · obtain ⟨a, rfl⟩ := hf
    change realChartEvaluation root p Y
        (activeCompatibilityGenerator root src dst active chart a) = 0
    exact IsIncidenceRealization.realChartEvaluation_compatibility_eq_zero
      hY root a.1 a.2.1
  · exact
      IsIncidenceRealization.realChartEvaluation_annihilates_selectedNullGeneratorSet
        hY root selected f hf

end

end UniversalHomogeneousChart

end RB31E2E


end
end BundleSource0004

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0004/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0004.json"

section BundleSource0005
/- Source: Papers/RigidityZheng_Incidence_Arithmetic.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Incidence/Arithmetic.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Module visibility and import paths adapted; umbrella Mathlib imports
replaced by the definitions and tactics used in this file.
-/


@[expose] public section

/-!
# Integer arithmetic for the sparse-skeleton and bad-pin estimates

These statements are deliberately separated from the geometric facts
that supply their hypotheses.
-/

namespace RB31E2E

structure TraceCounts where
  t : ℤ
  q : ℤ
  mInt : ℤ
  mCross : ℤ
  sInt : ℤ
  sCross : ℤ

def TraceCounts.Valid (d : TraceCounts) : Prop :=
  1 ≤ d.q ∧ d.q ≤ d.t ∧
  0 ≤ d.mInt ∧ 0 ≤ d.mCross ∧
  0 ≤ d.sInt ∧ 0 ≤ d.sCross ∧
  d.sInt ≤ d.mInt ∧
  6 * (d.t - 1) ≤
    2 * (d.mInt + d.mCross) + (d.sInt + d.sCross) ∧
  6 * (d.q - 1) ≤ 2 * d.mCross + d.sCross

def TraceCounts.requiredEdges (d : TraceCounts) : ℤ :=
  6 * (d.t - 1) - 2 * (d.mInt + d.mCross)

def TraceCounts.sparsePartitionTerm (d : TraceCounts) : ℤ :=
  2 * (d.t - d.q) + d.sCross

theorem partitionCondition_sparsePartitionTerm_ge
    (d : TraceCounts) (h : d.Valid) :
    d.requiredEdges ≤ d.sparsePartitionTerm := by
  rcases h with
    ⟨hqOne, hqt, hmInt, hmCross, hsInt, hsCross,
      hsIntMInt, hFine, hCoarse⟩
  simp only [TraceCounts.requiredEdges, TraceCounts.sparsePartitionTerm]
  omega

theorem strictOrbitDeficit
    (t M N R : ℤ) (hR : 6 * (t - 1) - 2 * M ≤ R) :
    6 * (t - 1) - R + M + 3 * (N - M) - 1 ≤ 3 * N - 1 := by
  omega

theorem badPin_dimension_arithmetic (t M N : ℤ) :
    let R := max 0 (6 * (t - 1) - 2 * M)
    6 * (t - 1) - R + M + 3 * (N - M) - 1 ≤ 3 * N - 1 := by
  dsimp
  apply strictOrbitDeficit
  exact Int.le_max_right _ _

/-- The exact sparse-null skeleton equation always pays the full grounded
twist-variable budget, including the branch where natural-number subtraction
has truncated to zero.  This is the arithmetic inequality used by the
relative-height chart argument. -/
theorem sparseNull_relativeHeight_budget
    (vertexCount activeCount edgeCount : ℕ)
    (hcard : edgeCount =
      6 * (vertexCount - 1) - 2 * activeCount) :
    6 * (vertexCount - 1) ≤ edgeCount + 2 * activeCount := by
  omega

end RB31E2E


end
end BundleSource0005

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0005/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0005.json"

section BundleSource0006
/- Source: Papers/RigidityZheng_Incidence_UniversalChartHeightElimination.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Incidence/UniversalChartHeightElimination.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/





@[expose] public section

/-!
# Height elimination for a universal incidence chart

The outer polynomial ring of `UniversalChartIdeal` has the pin-parameter
ring as coefficients.  Since the homogeneous height theorem used here is a
theorem over a field, this file performs the two honest changes of
coordinates required to apply it:

* extend the pin coefficients to their fraction field; and
* reindex the finite type of grounded twist variables by `Fin n`.

The image of the universal chart ideal under this composite map remains
standard homogeneous.  Under an explicitly named lower-height condition on
the homogeneous primes over that finite generic ideal, the existing
`map_eq_top_of_homogeneousPrime_height` theorem shows that every algebra map
which makes a selected twist coordinate a unit sends the ideal to `top`.
The final theorem is stated back on the original universal chart ideal via
the composite ring homomorphism.

No incidence height estimate is asserted in this file: the precise missing
estimate is exposed as `FiniteGenericChartPrimeHeightCondition`.
-/

namespace RB31E2E

namespace UniversalHomogeneousChart

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Generic coefficients and finite twist coordinates -/

/-- The generic coefficient field obtained from the provenance-labelled pin
parameter ring. -/
abbrev GenericPinCoefficientField (E : Type*) :=
  FractionRing (PinParameterRing E)

/-- The actual number of outer, grounded-twist variables. -/
def groundedTwistVariableCount {V : Type*} [Fintype V] [DecidableEq V]
    (root : V) : ℕ :=
  Fintype.card (GroundedTwistVariable root)

/-- There are exactly six twist coordinates for every body other than the
grounded root. -/
theorem groundedTwistVariableCount_eq_six_mul_pred
    {V : Type*} [Fintype V] [DecidableEq V] (root : V) :
    groundedTwistVariableCount root = 6 * (Fintype.card V - 1) := by
  have hoff : Fintype.card (OffRoot root) = Fintype.card V - 1 := by
    rw [Fintype.card_subtype_compl (fun v : V ↦ v = root)]
    simp
  simp [groundedTwistVariableCount, GroundedTwistVariable,
    GroundedTwistPolynomial.GroundedColumn,
    GroundedTwistPolynomial.TwistCoordinate, hoff, Nat.mul_comm]

/-- The two-coordinate provenance index has exactly two entries for each
active occurrence. -/
theorem card_activeCompatibilityIndex
    {E : Type*} [DecidableEq E] (active : Finset E)
    (chart : active → Fin 3) :
    Fintype.card (ActiveCompatibilityIndex active chart) =
      2 * active.card := by
  have hother (i : Fin 3) :
      Fintype.card (OtherCompatibilityCoordinate i) = 2 := by
    rw [Fintype.card_subtype_compl (fun j : Fin 3 ↦ j = i)]
    simp
  rw [Fintype.card_sigma]
  simp_rw [hother]
  simp [Nat.mul_comm]

/-- Under the exact sparse-null edge count, the indexed linear and
quadratic chart generators pay at least the complete grounded-twist variable
budget.  The right side counts two compatibility generators per active
occurrence and one null generator per selected occurrence. -/
theorem universalChartGenerator_budget
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (active : Finset E) (chart : active → Fin 3)
    (selected : Finset active)
    (hcard : selected.card =
      6 * (Fintype.card V - 1) - 2 * active.card) :
    groundedTwistVariableCount root ≤
      Fintype.card (ActiveCompatibilityIndex active chart) + selected.card := by
  rw [groundedTwistVariableCount_eq_six_mul_pred,
    card_activeCompatibilityIndex]
  have hbudget := sparseNull_relativeHeight_budget
    (Fintype.card V) active.card selected.card hcard
  omega

/-- The canonical finite reindexing of all grounded-twist coordinates. -/
def finiteTwistIndexEquiv {V : Type*} [Fintype V] [DecidableEq V]
    (root : V) :
    GroundedTwistVariable root ≃ Fin (groundedTwistVariableCount root) :=
  Fintype.equivFin (GroundedTwistVariable root)

/-- The finite-variable generic chart ring over the fraction field of all
pin parameters. -/
abbrev FiniteGenericRelativeRing
    {V : Type*} [Fintype V] [DecidableEq V] (root : V) (E : Type*) :=
  MvPolynomial (Fin (groundedTwistVariableCount root))
    (GenericPinCoefficientField E)

/-- Coefficient extension from polynomial pin parameters to their fraction
field. -/
def genericPinCoefficientHom (E : Type*) :
    PinParameterRing E →+* GenericPinCoefficientField E :=
  algebraMap (PinParameterRing E) (GenericPinCoefficientField E)

/-- First extend pin coefficients to their fraction field, then rename every
outer twist variable by the canonical finite index. -/
def finiteGenericChartHom
    {V E : Type*} [Fintype V] [DecidableEq V] (root : V) :
    RelativeRing root E →+* FiniteGenericRelativeRing root E :=
  ((MvPolynomial.renameEquiv (GenericPinCoefficientField E)
      (finiteTwistIndexEquiv root)).toRingEquiv.toRingHom).comp
    (MvPolynomial.map (genericPinCoefficientHom E))

@[simp]
theorem finiteGenericChartHom_X
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (c : GroundedTwistVariable root) :
    finiteGenericChartHom (E := E) root (X c) =
      X (finiteTwistIndexEquiv root c) := by
  simp [finiteGenericChartHom]

/-- The finite generic image of the original universal chart ideal. -/
def finiteGenericUniversalChartIdeal
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active) :
    Ideal (FiniteGenericRelativeRing root E) :=
  Ideal.map (finiteGenericChartHom root)
    (universalChartIdeal root src dst active chart selected)

/-! ## Homogeneity survives both changes of coordinates -/

private theorem finiteGenericChartHom_preserves_isHomogeneous
    {V E : Type*} [Fintype V] [DecidableEq V]
    {root : V} {f : RelativeRing root E} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    (finiteGenericChartHom root f).IsHomogeneous d := by
  change
    (MvPolynomial.rename (finiteTwistIndexEquiv root)
      (MvPolynomial.map (genericPinCoefficientHom E) f)).IsHomogeneous d
  exact (hf.map (genericPinCoefficientHom E)).rename_isHomogeneous

/-- Base change to generic pin coefficients and finite reindexing preserve
the standard twist homogeneity of the universal chart ideal. -/
theorem finiteGenericUniversalChartIdeal_isHomogeneous
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active) :
    (finiteGenericUniversalChartIdeal root src dst active chart selected).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule
        (Fin (groundedTwistVariableCount root))
        (GenericPinCoefficientField E)) := by
  rw [finiteGenericUniversalChartIdeal, universalChartIdeal, Ideal.map_span]
  apply Ideal.homogeneous_span
    (MvPolynomial.homogeneousSubmodule
      (Fin (groundedTwistVariableCount root))
      (GenericPinCoefficientField E))
    ((finiteGenericChartHom root) ''
      universalChartGeneratorSet root src dst active chart selected)
  intro f hf
  obtain ⟨g, hg, rfl⟩ := hf
  obtain ⟨d, hd⟩ := universalChartGeneratorSet_isHomogeneous
    root src dst active chart selected g hg
  exact ⟨d, finiteGenericChartHom_preserves_isHomogeneous hd⟩

/-! ## The transparent incidence-height obligation -/

/-- The exact local height input needed on a selected nonvanishing twist
coordinate.  It concerns only homogeneous primes over the finite generic
chart ideal which avoid that coordinate. -/
def FiniteGenericChartPrimeHeightCondition
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active)
    (c : GroundedTwistVariable root) : Prop :=
  ∀ (Q : Ideal (FiniteGenericRelativeRing root E)),
    Q.IsPrime →
    Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule
        (Fin (groundedTwistVariableCount root))
        (GenericPinCoefficientField E)) →
    finiteGenericUniversalChartIdeal root src dst active chart selected ≤ Q →
    X (finiteTwistIndexEquiv root c) ∉ Q →
    (groundedTwistVariableCount root : ℕ∞) ≤ Q.height

/-! ## Elimination on a nonvanishing twist-coordinate chart -/

/-- On the finite generic chart, the prime-height condition forces every
algebra map which makes the selected coordinate a unit to send the chart
ideal to `top`. -/
theorem map_finiteGenericUniversalChartIdeal_eq_top_of_primeHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active)
    (c : GroundedTwistVariable root)
    (hheight : FiniteGenericChartPrimeHeightCondition
      root src dst active chart selected c)
    {S : Type*} [CommRing S]
    [Algebra (FiniteGenericRelativeRing root E) S]
    (hunit : IsUnit
      (algebraMap (FiniteGenericRelativeRing root E) S
        (X (finiteTwistIndexEquiv root c)))) :
    Ideal.map (algebraMap (FiniteGenericRelativeRing root E) S)
        (finiteGenericUniversalChartIdeal
          root src dst active chart selected) = ⊤ := by
  exact NullCellulePolynomial.map_eq_top_of_homogeneousPrime_height
    (finiteGenericUniversalChartIdeal
      root src dst active chart selected)
    (finiteGenericUniversalChartIdeal_isHomogeneous
      root src dst active chart selected)
    (finiteTwistIndexEquiv root c) hheight hunit

/-- The same conclusion stated on the original universal chart ideal.  The
ring homomorphism in the conclusion is the explicit coefficient-extension,
finite-reindexing, and target-algebra composite.  Its unit hypothesis is
written on the image of the original provenance-labelled twist coordinate. -/
theorem map_universalChartIdeal_eq_top_of_primeHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active)
    (c : GroundedTwistVariable root)
    (hheight : FiniteGenericChartPrimeHeightCondition
      root src dst active chart selected c)
    {S : Type*} [CommRing S]
    [Algebra (FiniteGenericRelativeRing root E) S]
    (hunit : IsUnit
      (((algebraMap (FiniteGenericRelativeRing root E) S).comp
        (finiteGenericChartHom root)) (X c))) :
    Ideal.map
        ((algebraMap (FiniteGenericRelativeRing root E) S).comp
          (finiteGenericChartHom root))
        (universalChartIdeal root src dst active chart selected) = ⊤ := by
  have hunit' : IsUnit
      (algebraMap (FiniteGenericRelativeRing root E) S
        (X (finiteTwistIndexEquiv root c))) := by
    change IsUnit
      (algebraMap (FiniteGenericRelativeRing root E) S
        (finiteGenericChartHom root (X c))) at hunit
    rw [finiteGenericChartHom_X] at hunit
    exact hunit
  rw [← Ideal.map_map]
  exact map_finiteGenericUniversalChartIdeal_eq_top_of_primeHeight
    root src dst active chart selected c hheight hunit'

end

end UniversalHomogeneousChart

end RB31E2E


end
end BundleSource0006

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0006/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0006.json"

section BundleSource0007
/- Source: Papers/RigidityZheng_Incidence_DistinctProvenanceChart.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Incidence/DistinctProvenanceChart.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Finite provenance charts for the pairwise-distinct locus

A single nonzero grounded coordinate removes the common scaling orbit, but
it does not exclude components on which some other two body twists coincide.
The correct finite chart remembers one nonzero difference coordinate for
every ordered pair of distinct body labels.  Its denominator is the product
of those labelled linear forms.

This file defines that denominator and proves the two bookkeeping facts
needed by localized height elimination:

* every injective real twist assignment lies in one of the finite charts;
* after generic coefficient extension and finite reindexing, the denominator
  belongs to the twist irrelevant ideal (when there are at least two bodies).

No sparse-null height assertion is made here.
-/

namespace RB31E2E

namespace UniversalHomogeneousChart

noncomputable section

open MvPolynomial
open GroundedTwistPolynomial
open NullCellulePolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- An ordered pair of genuinely distinct body labels.  Using ordered pairs
keeps endpoint provenance explicit and avoids an arbitrary orientation of
`Sym2`. -/
abbrev OrderedDistinctBodyPair (V : Type*) :=
  {uv : V × V // uv.1 ≠ uv.2}

/-- One of six nonzero relative-twist coordinates for every labelled
ordered pair. -/
abbrev DistinctnessChart (V : Type*) :=
  OrderedDistinctBodyPair V → TwistCoordinate

/-- One coordinate of the universal grounded twist at a body. -/
def universalGroundedCoordinate
    {V E : Type*} [DecidableEq V] (root v : V)
    (c : TwistCoordinate) : RelativeRing root E :=
  if c.1 then
    (universalGroundedTwist (E := E) root v).2 c.2
  else
    (universalGroundedTwist (E := E) root v).1 c.2

/-- The provenance-labelled linear coordinate of `Y(u)-Y(v)`. -/
def universalBodyDifferenceCoordinate
    {V E : Type*} [DecidableEq V] (root : V)
    (uv : OrderedDistinctBodyPair V) (c : TwistCoordinate) :
    RelativeRing root E :=
  universalGroundedCoordinate (E := E) root uv.1.1 c -
    universalGroundedCoordinate (E := E) root uv.1.2 c

/-- Product cutting out the complement of one complete pairwise-distinct
provenance chart. -/
def universalDistinctnessDenominator
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (chart : DistinctnessChart V) : RelativeRing root E :=
  ∏ uv : OrderedDistinctBodyPair V,
    universalBodyDifferenceCoordinate (E := E) root uv (chart uv)

/-- A universal grounded coordinate specializes to the corresponding
coordinate of `Y(v)-Y(root)`. -/
theorem realChartEvaluation_universalGroundedCoordinate
    {V E : Type*} [DecidableEq V] (root v : V)
    (c : TwistCoordinate) (p : E → Vec3 ℝ) (Y : V → Twist ℝ) :
    realChartEvaluation root p Y
        (universalGroundedCoordinate (E := E) root v c) =
      twistCoordinates (Y v - Y root) c := by
  rcases c with ⟨b, i⟩
  cases b
  · have h := congrFun
      (congrArg Prod.fst
        (map_universalGroundedTwist root v p Y)) i
    simpa [universalGroundedCoordinate, mapTwist, mapVec3] using h
  · have h := congrFun
      (congrArg Prod.snd
        (map_universalGroundedTwist root v p Y)) i
    simpa [universalGroundedCoordinate, mapTwist, mapVec3] using h

/-- Difference-coordinate evaluation is independent of the arbitrary
grounding body. -/
theorem realChartEvaluation_universalBodyDifferenceCoordinate
    {V E : Type*} [DecidableEq V] (root : V)
    (uv : OrderedDistinctBodyPair V) (c : TwistCoordinate)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ) :
    realChartEvaluation root p Y
        (universalBodyDifferenceCoordinate (E := E) root uv c) =
      twistCoordinates (Y uv.1.1 - Y uv.1.2) c := by
  rw [universalBodyDifferenceCoordinate, map_sub,
    realChartEvaluation_universalGroundedCoordinate,
    realChartEvaluation_universalGroundedCoordinate]
  rcases c with ⟨b, i⟩
  cases b <;> simp [twistCoordinates]

/-- Injectivity supplies a simultaneous finite distinctness chart. -/
theorem exists_distinctnessChart_of_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (Y : V → Twist ℝ) (hY : Function.Injective Y) :
    ∃ chart : DistinctnessChart V,
      ∀ uv : OrderedDistinctBodyPair V,
        twistCoordinates (Y uv.1.1 - Y uv.1.2) (chart uv) ≠ 0 := by
  have hCoordinate : ∀ uv : OrderedDistinctBodyPair V,
      ∃ c : TwistCoordinate,
        twistCoordinates (Y uv.1.1 - Y uv.1.2) c ≠ 0 := by
    intro uv
    apply SparseNullIncidence.exists_twistCoordinate_ne_zero
    exact sub_ne_zero.mpr (hY.ne uv.2)
  choose chart hchart using hCoordinate
  exact ⟨chart, hchart⟩

/-- On its chosen chart, the complete provenance denominator evaluates to a
nonzero real number. -/
theorem realChartEvaluation_universalDistinctnessDenominator_ne_zero
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (chart : DistinctnessChart V)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ)
    (hchart : ∀ uv : OrderedDistinctBodyPair V,
      twistCoordinates (Y uv.1.1 - Y uv.1.2) (chart uv) ≠ 0) :
    realChartEvaluation root p Y
        (universalDistinctnessDenominator (E := E) root chart) ≠ 0 := by
  rw [universalDistinctnessDenominator, map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun uv _huv ↦ by
    rw [realChartEvaluation_universalBodyDifferenceCoordinate]
    exact hchart uv

/-! ## Generic finite-ring denominator -/

/-- The same denominator after extending pin coefficients to their fraction
field and reindexing all grounded twist variables by a finite type. -/
def finiteGenericDistinctnessDenominator
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (chart : DistinctnessChart V) :
    FiniteGenericRelativeRing root E :=
  finiteGenericChartHom root
    (universalDistinctnessDenominator (E := E) root chart)

/-- Each grounded coordinate maps into the finite irrelevant ideal. -/
theorem finiteGenericChartHom_universalGroundedCoordinate_mem_irrelevant
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root v : V) (c : TwistCoordinate) :
    finiteGenericChartHom (E := E) root
        (universalGroundedCoordinate (E := E) root v c) ∈
      finiteIrrelevantIdeal (k := GenericPinCoefficientField E)
        (groundedTwistVariableCount root) := by
  rcases c with ⟨b, i⟩
  cases b <;> by_cases hv : v = root
  · subst v
    simp [universalGroundedCoordinate, universalGroundedTwist,
      extendOffRoot]
  · simp [universalGroundedCoordinate, universalGroundedTwist,
      extendOffRoot, hv, universalOffRootTwist, finiteIrrelevantIdeal,
      X_mem_coordinateVariableIdeal_iff]
  · subst v
    simp [universalGroundedCoordinate, universalGroundedTwist,
      extendOffRoot]
  · simp [universalGroundedCoordinate, universalGroundedTwist,
      extendOffRoot, hv, universalOffRootTwist, finiteIrrelevantIdeal,
      X_mem_coordinateVariableIdeal_iff]

/-- Every labelled pair-difference factor maps into the twist irrelevant
ideal. -/
theorem finiteGenericChartHom_universalBodyDifferenceCoordinate_mem_irrelevant
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (uv : OrderedDistinctBodyPair V) (c : TwistCoordinate) :
    finiteGenericChartHom (E := E) root
        (universalBodyDifferenceCoordinate (E := E) root uv c) ∈
      finiteIrrelevantIdeal (k := GenericPinCoefficientField E)
        (groundedTwistVariableCount root) := by
  rw [universalBodyDifferenceCoordinate, map_sub]
  exact Ideal.sub_mem _
    (finiteGenericChartHom_universalGroundedCoordinate_mem_irrelevant
      (E := E) root uv.1.1 c)
    (finiteGenericChartHom_universalGroundedCoordinate_mem_irrelevant
      (E := E) root uv.1.2 c)

/-- With at least two bodies, the full generic distinctness denominator is
a positive-twist-degree element of the finite irrelevant ideal. -/
theorem finiteGenericDistinctnessDenominator_mem_irrelevant
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (chart : DistinctnessChart V)
    (hTwo : 2 ≤ Fintype.card V) :
    finiteGenericDistinctnessDenominator (E := E) root chart ∈
      finiteIrrelevantIdeal (k := GenericPinCoefficientField E)
        (groundedTwistVariableCount root) := by
  have hOne : 1 < Fintype.card V := by omega
  obtain ⟨u, v, huv⟩ := Fintype.one_lt_card_iff.mp hOne
  let uv : OrderedDistinctBodyPair V := ⟨(u, v), huv⟩
  let s : Finset (OrderedDistinctBodyPair V) := Finset.univ
  let f : OrderedDistinctBodyPair V → FiniteGenericRelativeRing root E :=
    fun w ↦ finiteGenericChartHom (E := E) root
      (universalBodyDifferenceCoordinate (E := E) root w (chart w))
  have huvMem : uv ∈ s := Finset.mem_univ uv
  have hfactor : f uv ∈
      finiteIrrelevantIdeal (k := GenericPinCoefficientField E)
        (groundedTwistVariableCount root) :=
    finiteGenericChartHom_universalBodyDifferenceCoordinate_mem_irrelevant
      (E := E) root uv (chart uv)
  have hproduct :
      f uv * ∏ w ∈ s.erase uv, f w ∈
      finiteIrrelevantIdeal (k := GenericPinCoefficientField E)
        (groundedTwistVariableCount root) :=
    Ideal.mul_mem_right _ _ hfactor
  rw [Finset.mul_prod_erase s f huvMem] at hproduct
  rw [finiteGenericDistinctnessDenominator,
    universalDistinctnessDenominator, map_prod]
  simpa [s, f] using hproduct

end

end UniversalHomogeneousChart

end RB31E2E


end
end BundleSource0007

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0007/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0007.json"

section BundleSource0008
/- Source: Papers/RigidityZheng_Incidence_FullProvenanceChart.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Incidence/FullProvenanceChart.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Complete incidence-provenance charts

Pairwise distinctness removes equality-collapse components, but the
private-pin triangular presentation also needs one nonzero angular
coordinate for every active occurrence.  This file records both pieces in
one denominator.  Its factors retain their body-pair and occurrence
provenance.

Every injective incidence realization belongs to one such finite chart.
After generic coefficient extension, the complete denominator lies in the
twist irrelevant ideal.  No height assertion is made here.
-/

namespace RB31E2E

namespace UniversalHomogeneousChart

noncomputable section

open MvPolynomial
open GroundedTwistPolynomial
open NullCellulePolynomial

/-! ## The angular and complete denominators -/

/-- The angular-coordinate factor attached to one active occurrence. -/
def universalActiveAngularFactor
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (e : active) :
    RelativeRing root E :=
  universalBodyDifferenceCoordinate (E := E) root
    ⟨(src e.1, dst e.1), hLoop e.1 e.2⟩
    ⟨false, angularChart e⟩

/-- Product of the selected nonzero angular coordinates of all active
relative twists. -/
def universalAngularDenominator
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) : RelativeRing root E :=
  ∏ e : active,
    universalActiveAngularFactor root src dst active hLoop angularChart e

/-- The complete denominator: all labelled body differences and all
selected active angular coordinates. -/
def universalIncidenceProvenanceDenominator
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3) : RelativeRing root E :=
  universalDistinctnessDenominator (E := E) root distinctChart *
    universalAngularDenominator root src dst active hLoop angularChart

/-! ## Evaluation on the intended incidence locus -/

theorem realChartEvaluation_universalActiveAngularFactor
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (e : active)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ) :
    realChartEvaluation root p Y
        (universalActiveAngularFactor
          root src dst active hLoop angularChart e) =
      (Y (src e.1) - Y (dst e.1)).1 (angularChart e) := by
  rw [universalActiveAngularFactor,
    realChartEvaluation_universalBodyDifferenceCoordinate]
  rfl

/-- The angular denominator is nonzero on the chosen angular chart. -/
theorem realChartEvaluation_universalAngularDenominator_ne_zero
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ)
    (hAngular : ∀ e : active,
      (Y (src e.1) - Y (dst e.1)).1 (angularChart e) ≠ 0) :
    realChartEvaluation root p Y
        (universalAngularDenominator
          root src dst active hLoop angularChart) ≠ 0 := by
  rw [universalAngularDenominator, map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun e _he ↦ by
    rw [realChartEvaluation_universalActiveAngularFactor]
    exact hAngular e

/-- Every injective incidence realization evaluates its complete
provenance denominator nontrivially on the charts supplied by its labelled
differences and active angular coordinates. -/
theorem realChartEvaluation_universalIncidenceProvenanceDenominator_ne_zero
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ)
    (hDistinct : ∀ uv : OrderedDistinctBodyPair V,
      twistCoordinates (Y uv.1.1 - Y uv.1.2) (distinctChart uv) ≠ 0)
    (hAngular : ∀ e : active,
      (Y (src e.1) - Y (dst e.1)).1 (angularChart e) ≠ 0) :
    realChartEvaluation root p Y
        (universalIncidenceProvenanceDenominator
          root src dst active hLoop distinctChart angularChart) ≠ 0 := by
  rw [universalIncidenceProvenanceDenominator, map_mul]
  exact mul_ne_zero
    (realChartEvaluation_universalDistinctnessDenominator_ne_zero
      root distinctChart p Y hDistinct)
    (realChartEvaluation_universalAngularDenominator_ne_zero
      root src dst active hLoop angularChart p Y hAngular)

/-! ## The complete denominator in the finite generic chart -/

/-- Generic coefficient extension and finite twist reindexing of the
complete provenance denominator. -/
def finiteGenericIncidenceProvenanceDenominator
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3) :
    FiniteGenericRelativeRing root E :=
  finiteGenericChartHom root
    (universalIncidenceProvenanceDenominator
      root src dst active hLoop distinctChart angularChart)

/-- With at least two bodies, the complete provenance denominator belongs
to the finite irrelevant ideal.  The pairwise-distinct factor already has
positive twist degree; multiplication by the angular factors preserves
ideal membership. -/
theorem finiteGenericIncidenceProvenanceDenominator_mem_irrelevant
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3)
    (hTwo : 2 ≤ Fintype.card V) :
    finiteGenericIncidenceProvenanceDenominator
        root src dst active hLoop distinctChart angularChart ∈
      finiteIrrelevantIdeal (k := GenericPinCoefficientField E)
        (groundedTwistVariableCount root) := by
  rw [finiteGenericIncidenceProvenanceDenominator,
    universalIncidenceProvenanceDenominator, map_mul]
  exact Ideal.mul_mem_right _ _
    (finiteGenericDistinctnessDenominator_mem_irrelevant
      (E := E) root distinctChart hTwo)

end

end UniversalHomogeneousChart

end RB31E2E


end
end BundleSource0008

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0008/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0008.json"

section BundleSource0009
/- Source: Papers/RigidityZheng_Algebra_RationalCertificateDescent.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/RationalCertificateDescent.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/





@[expose] public section

/-!
# Descent of rational polynomial certificates to the integers

A polynomial over `ℚ` involves only finitely many coefficients, even when its
variable type is infinite.  This file packages denominator clearing in a form
suited to geometric bad-locus certificates: every nonzero rational polynomial
is proportional to the coefficient cast of a nonzero integer polynomial, and
therefore its real zero set is contained in the real zero set of that integer
polynomial.

The construction below is structural rather than coefficientwise.  At an
addition node the two already-cleared denominators are cross-multiplied; at a
variable node the denominator is unchanged.  Thus no finiteness hypothesis on
the variable type is needed.
-/

namespace RB31E2E

namespace RationalCertificateDescent

noncomputable section

open MvPolynomial

variable {σ : Type*}

/-- Every rational multivariate polynomial has an integer multiple represented
by an integer polynomial.  The multiplier is a nonzero natural number. -/
theorem exists_natCast_mul_eq_map (P : MvPolynomial σ ℚ) :
    ∃ (Q : MvPolynomial σ ℤ) (d : ℕ), d ≠ 0 ∧
      map (Int.castRingHom ℚ) Q = C (d : ℚ) * P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      refine ⟨C a.num, a.den, a.den_ne_zero, ?_⟩
      rw [map_C, ← C_mul]
      have hden : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr a.den_ne_zero
      have hnum : (a.num : ℚ) = a * (a.den : ℚ) :=
        (div_eq_iff hden).mp a.num_div_den
      apply congrArg (fun x : ℚ ↦ (C x : MvPolynomial σ ℚ))
      change (a.num : ℚ) = (a.den : ℚ) * a
      exact hnum.trans (mul_comm _ _)
  | add P R hP hR =>
      obtain ⟨Q, d, hd, hQ⟩ := hP
      obtain ⟨S, e, he, hS⟩ := hR
      refine ⟨C (e : ℤ) * Q + C (d : ℤ) * S, d * e,
        Nat.mul_ne_zero hd he, ?_⟩
      simp only [map_add, map_mul, map_C, hQ, hS, Nat.cast_mul]
      simp only [Int.coe_castRingHom, Int.cast_natCast]
      ring
  | mul_X P i hP =>
      obtain ⟨Q, d, hd, hQ⟩ := hP
      refine ⟨Q * X i, d, hd, ?_⟩
      simp only [map_mul, map_X, hQ]
      ring

/-- A nonzero rational polynomial admits a nonzero integer certificate whose
coefficient cast is a nonzero rational scalar multiple of the original
polynomial. -/
theorem exists_integer_proportional
    (P : MvPolynomial σ ℚ) (hP : P ≠ 0) :
    ∃ (Q : MvPolynomial σ ℤ) (c : ℚ),
      Q ≠ 0 ∧ c ≠ 0 ∧
        map (Int.castRingHom ℚ) Q = C c * P := by
  obtain ⟨Q, d, hd, hQ⟩ := exists_natCast_mul_eq_map P
  refine ⟨Q, (d : ℚ), ?_, Nat.cast_ne_zero.mpr hd, hQ⟩
  intro hQzero
  rw [hQzero, map_zero] at hQ
  have hc : C (d : ℚ) ≠ (0 : MvPolynomial σ ℚ) :=
    C_ne_zero.mpr (Nat.cast_ne_zero.mpr hd)
  exact hP (mul_eq_zero.mp hQ.symm |>.resolve_left hc)

/-- Evaluation commutes with the two-stage coefficient cast `ℤ → ℚ → ℝ`.
This small lemma keeps the zero-set theorem below independent of definitional
details of the canonical cast homomorphisms. -/
theorem eval₂_map_intCast_ratCast
    (Q : MvPolynomial σ ℤ) (z : σ → ℝ) :
    eval₂ (Rat.castHom ℝ) z (map (Int.castRingHom ℚ) Q) =
      eval₂ (Int.castRingHom ℝ) z Q := by
  rw [eval₂_map]
  congr 1

/-- If a rational polynomial vanishes at a real assignment, then every
integer certificate obtained from a proportionality equation vanishes there
as well. -/
theorem eval₂_integer_eq_zero_of_proportional
    {P : MvPolynomial σ ℚ} {Q : MvPolynomial σ ℤ} {c : ℚ}
    (hProportional : map (Int.castRingHom ℚ) Q = C c * P)
    (z : σ → ℝ)
    (hPzero : eval₂ (Rat.castHom ℝ) z P = 0) :
    eval₂ (Int.castRingHom ℝ) z Q = 0 := by
  rw [← eval₂_map_intCast_ratCast Q z, hProportional]
  simp [hPzero]

/-- End-to-end one-polynomial descent packet: a nonzero rational certificate
produces a nonzero integer certificate and the latter vanishes at every real
zero of the former. -/
theorem exists_integer_certificate_vanishing_on_real_zeros
    (P : MvPolynomial σ ℚ) (hP : P ≠ 0) :
    ∃ (Q : MvPolynomial σ ℤ) (c : ℚ),
      Q ≠ 0 ∧ c ≠ 0 ∧
        map (Int.castRingHom ℚ) Q = C c * P ∧
        ∀ z : σ → ℝ,
          eval₂ (Rat.castHom ℝ) z P = 0 →
            eval₂ (Int.castRingHom ℝ) z Q = 0 := by
  obtain ⟨Q, c, hQ, hc, hProportional⟩ :=
    exists_integer_proportional P hP
  exact ⟨Q, c, hQ, hc, hProportional,
    fun z hz ↦ eval₂_integer_eq_zero_of_proportional hProportional z hz⟩

/-- A finite family of nonzero rational certificates can be descended one by
one to nonzero integer certificates, with all real zero-set implications
retained. -/
theorem exists_integer_certificate_family
    {ι : Type*} [Fintype ι]
    (P : ι → MvPolynomial σ ℚ) (hP : ∀ i, P i ≠ 0) :
    ∃ (Q : ι → MvPolynomial σ ℤ) (c : ι → ℚ),
      (∀ i, Q i ≠ 0) ∧ (∀ i, c i ≠ 0) ∧
      (∀ i, map (Int.castRingHom ℚ) (Q i) = C (c i) * P i) ∧
      ∀ i z, eval₂ (Rat.castHom ℝ) z (P i) = 0 →
        eval₂ (Int.castRingHom ℝ) z (Q i) = 0 := by
  choose Q c hQ hc hProportional hVanish using
    fun i ↦ exists_integer_certificate_vanishing_on_real_zeros (P i) (hP i)
  exact ⟨Q, c, hQ, hc, hProportional, hVanish⟩

/-- Proportionality is preserved when finitely many descended certificates
are multiplied. -/
theorem map_product_eq_scalar_mul_product
    {ι : Type*} [Fintype ι]
    (P : ι → MvPolynomial σ ℚ) (Q : ι → MvPolynomial σ ℤ)
    (c : ι → ℚ)
    (hProportional : ∀ i,
      map (Int.castRingHom ℚ) (Q i) = C (c i) * P i) :
    map (Int.castRingHom ℚ) (∏ i, Q i) =
      C (∏ i, c i) * ∏ i, P i := by
  classical
  calc
    map (Int.castRingHom ℚ) (∏ i, Q i) =
        ∏ i, map (Int.castRingHom ℚ) (Q i) := by rw [map_prod]
    _ = ∏ i, (C (c i) * P i) :=
      Finset.prod_congr rfl fun i _hi ↦ hProportional i
    _ = (∏ i, C (c i)) * ∏ i, P i := Finset.prod_mul_distrib
    _ = C (∏ i, c i) * ∏ i, P i := by rw [map_prod]

/-- Finite-product descent packet.  It is the direct interface needed after
a finite chart/component split: the product integer certificate is nonzero,
is proportional to the product rational certificate, and vanishes whenever
one chosen rational factor vanishes. -/
theorem exists_integer_product_certificate
    {ι : Type*} [Fintype ι]
    (P : ι → MvPolynomial σ ℚ) (hP : ∀ i, P i ≠ 0) :
    ∃ (Q : MvPolynomial σ ℤ) (c : ℚ),
      Q ≠ 0 ∧ c ≠ 0 ∧
        map (Int.castRingHom ℚ) Q = C c * ∏ i, P i ∧
        ∀ i z, eval₂ (Rat.castHom ℝ) z (P i) = 0 →
          eval₂ (Int.castRingHom ℝ) z Q = 0 := by
  classical
  obtain ⟨Q, c, hQ, hc, hProportional, hVanish⟩ :=
    exists_integer_certificate_family P hP
  refine ⟨∏ i, Q i, ∏ i, c i,
    Finset.prod_ne_zero_iff.mpr (fun i _hi ↦ hQ i),
    Finset.prod_ne_zero_iff.mpr (fun i _hi ↦ hc i),
    map_product_eq_scalar_mul_product P Q c hProportional, ?_⟩
  intro i z hz
  change (eval₂Hom (Int.castRingHom ℝ) z) (∏ i, Q i) = 0
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hVanish i z hz)

end

end RationalCertificateDescent

end RB31E2E


end
end BundleSource0009

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0009/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0009.json"

section BundleSource0010
/- Source: Papers/RigidityZheng_Incidence_UniversalChartContraction.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Incidence/UniversalChartContraction.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/




@[expose] public section

/-!
# Contracting a generic universal chart to pin parameters

The height argument over the fraction field of the pin-parameter ring forces
a power of the selected twist coordinate into the generic chart ideal.  This
file transports that membership back through the finite variable reindexing
and then uses the actual localization theorem for multivariate polynomial
rings to clear the pin denominator.  The result is a provenance-retaining
receipt

`C q * X c ^ m ∈ universalChartIdeal`

with a nonzero rational pin polynomial `q`.  On a real chart where the twist
coordinate `c` is nonzero, semantic annihilation of the universal chart ideal
therefore forces `q` to vanish.  The final theorem applies
`RationalCertificateDescent` and returns a nonzero integer pin polynomial.

No new properness, height, elimination, or incidence proposition is assumed
in this file.  Its only geometric input is the already explicit
`FiniteGenericChartPrimeHeightCondition`.
-/

namespace RB31E2E

namespace UniversalHomogeneousChart

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-! ## Clearing coefficients in a polynomial localization -/

/-- A denominator-clearing lemma specialized to coefficient localization.
Membership of a coordinate power after localizing the coefficient ring
produces one nonzero coefficient `q` whose constant embedding times that
power already belongs to the source ideal. -/
theorem exists_nonzero_coefficient_mul_X_pow_mem_of_mem_fraction_map
    {A K σ : Type*} [CommRing A] [IsDomain A] [CommRing K]
    [Algebra A K] [IsLocalization (nonZeroDivisors A) K]
    (I : Ideal (MvPolynomial σ A)) (c : σ) (m : ℕ)
    (hmem : algebraMap (MvPolynomial σ A) (MvPolynomial σ K) (X c ^ m) ∈
      Ideal.map (algebraMap (MvPolynomial σ A) (MvPolynomial σ K)) I) :
    ∃ q : A, q ≠ 0 ∧ C q * X c ^ m ∈ I := by
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
    ((nonZeroDivisors A).map (C (σ := σ)))
    (MvPolynomial σ K)] at hmem
  obtain ⟨s, hs, hsmem⟩ := hmem
  obtain ⟨q, hq, rfl⟩ := hs
  exact ⟨q, nonZeroDivisors.ne_zero hq, hsmem⟩

/-! ## Undoing the finite reindexing -/

/-- The un-reindexed generic relative ring. -/
abbrev GenericRelativeRing
    {V : Type*} [DecidableEq V] (root : V) (E : Type*) :=
  MvPolynomial (GroundedTwistVariable root)
    (GenericPinCoefficientField E)

/-- Coefficient extension without changing the twist provenance labels. -/
def genericCoefficientExtensionHom
    {V E : Type*} [DecidableEq V] (root : V) :
    RelativeRing root E →+* GenericRelativeRing root E :=
  MvPolynomial.map (genericPinCoefficientHom E)

/-- The universal chart ideal after extending only its pin coefficients. -/
def genericUniversalChartIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active) :
    Ideal (GenericRelativeRing root E) :=
  Ideal.map (genericCoefficientExtensionHom root)
    (universalChartIdeal root src dst active chart selected)

/-- The finite generic ideal is exactly the variable-renaming image of the
un-reindexed generic ideal. -/
theorem finiteGenericUniversalChartIdeal_eq_map_rename
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active) :
    finiteGenericUniversalChartIdeal root src dst active chart selected =
      Ideal.map
        (MvPolynomial.renameEquiv (GenericPinCoefficientField E)
          (finiteTwistIndexEquiv root)).toRingEquiv.toRingHom
        (genericUniversalChartIdeal
          root src dst active chart selected) := by
  rw [finiteGenericUniversalChartIdeal, genericUniversalChartIdeal,
    Ideal.map_map]
  rfl

/-- Undoing the finite reindexing transports a selected coordinate power
from the finite generic ideal to the coefficient-extended ideal with its
original provenance label. -/
theorem X_pow_mem_genericUniversalChartIdeal_of_mem_finite
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active)
    (c : GroundedTwistVariable root) (m : ℕ)
    (hmem : X (finiteTwistIndexEquiv root c) ^ m ∈
      finiteGenericUniversalChartIdeal
        root src dst active chart selected) :
    X c ^ m ∈ genericUniversalChartIdeal
      root src dst active chart selected := by
  let e := MvPolynomial.renameEquiv (GenericPinCoefficientField E)
    (finiteTwistIndexEquiv root)
  have hmapped :
      e.symm (X (finiteTwistIndexEquiv root c) ^ m) ∈
        Ideal.map e.symm.toRingEquiv.toRingHom
          (finiteGenericUniversalChartIdeal
            root src dst active chart selected) :=
    Ideal.mem_map_of_mem e.symm.toRingEquiv.toRingHom hmem
  rw [finiteGenericUniversalChartIdeal_eq_map_rename,
    Ideal.map_map] at hmapped
  have hcomp :
      e.symm.toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom =
        RingHom.id (GenericRelativeRing root E) := by
    apply DFunLike.ext _ _
    intro f
    exact e.symm_apply_apply f
  rw [hcomp, Ideal.map_id] at hmapped
  simpa [e] using hmapped

/-! ## The rational contraction witness -/

/-- The prime-height input produces a genuine denominator-clearing receipt
in the original universal chart ideal.  The coefficient `q` is a nonzero
rational polynomial in the pin parameters alone. -/
theorem exists_nonzero_pin_contraction_of_primeHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active)
    (c : GroundedTwistVariable root)
    (hheight : FiniteGenericChartPrimeHeightCondition
      root src dst active chart selected c) :
    ∃ (q : PinParameterRing E) (m : ℕ),
      q ≠ 0 ∧
      C q * X c ^ m ∈
        universalChartIdeal root src dst active chart selected := by
  obtain ⟨m, hm⟩ :=
    NullCellulePolynomial.exists_X_pow_mem_of_homogeneousPrime_height
      (finiteGenericUniversalChartIdeal
        root src dst active chart selected)
      (finiteGenericUniversalChartIdeal_isHomogeneous
        root src dst active chart selected)
      (finiteTwistIndexEquiv root c) hheight
  have hmGeneric : X c ^ m ∈ genericUniversalChartIdeal
      root src dst active chart selected :=
    X_pow_mem_genericUniversalChartIdeal_of_mem_finite
      root src dst active chart selected c m hm
  have hmLocalization :
      algebraMap (RelativeRing root E) (GenericRelativeRing root E) (X c ^ m) ∈
        Ideal.map
          (algebraMap (RelativeRing root E) (GenericRelativeRing root E))
          (universalChartIdeal root src dst active chart selected) := by
    simpa [genericUniversalChartIdeal, genericCoefficientExtensionHom,
      genericPinCoefficientHom] using hmGeneric
  obtain ⟨q, hq, hqmem⟩ :=
    exists_nonzero_coefficient_mul_X_pow_mem_of_mem_fraction_map
      (universalChartIdeal root src dst active chart selected) c m hmLocalization
  exact ⟨q, m, hq, hqmem⟩

/-! ## Evaluation and integer descent -/

/-- A denominator-clearing receipt forces its pin coefficient to vanish at
every actual incidence realization lying in the selected nonzero twist
chart. -/
theorem eval_pinContraction_eq_zero_of_incidenceRealization
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : SparseNullIncidence.IsIncidenceRealization src dst active p Y)
    (root : V) (chart : active → Fin 3) (selected : Finset active)
    (c : GroundedTwistVariable root) (q : PinParameterRing E) (m : ℕ)
    (hmem : C q * X c ^ m ∈
      universalChartIdeal root src dst active chart selected)
    (hc : GroundedTwistPolynomial.twistCoordinates
      (Y c.1.1 - Y root) c.2 ≠ 0) :
    eval₂ (Rat.castHom ℝ) (GroundedTwistPolynomial.assignmentOfPins p) q = 0 := by
  have hzero :=
    IsIncidenceRealization.realChartEvaluation_annihilates_universalChartIdeal
      hY root chart selected hmem
  rw [RingHom.mem_ker, map_mul] at hzero
  have hCoeff : realChartEvaluation root p Y (C q) =
      pinParameterEvaluation p q := by
    simp [realChartEvaluation]
  rw [hCoeff, map_pow, realChartEvaluation_X] at hzero
  have hqzero : pinParameterEvaluation p q = 0 :=
    (mul_eq_zero.mp hzero).resolve_right (pow_ne_zero m hc)
  simpa [pinParameterEvaluation] using hqzero

/-- A nonzero rational pin polynomial vanishes on every actual realization
in the selected chart. -/
theorem exists_nonzero_rational_pin_certificate_of_primeHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active)
    (c : GroundedTwistVariable root)
    (hheight : FiniteGenericChartPrimeHeightCondition
      root src dst active chart selected c) :
    ∃ q : PinParameterRing E,
      q ≠ 0 ∧
      ∀ (p : E → Vec3 ℝ) (Y : V → Twist ℝ),
        SparseNullIncidence.IsIncidenceRealization src dst active p Y →
        GroundedTwistPolynomial.twistCoordinates
          (Y c.1.1 - Y root) c.2 ≠ 0 →
        eval₂ (Rat.castHom ℝ)
          (GroundedTwistPolynomial.assignmentOfPins p) q = 0 := by
  obtain ⟨q, m, hq, hmem⟩ := exists_nonzero_pin_contraction_of_primeHeight
    root src dst active chart selected c hheight
  refine ⟨q, hq, ?_⟩
  intro p Y hY hc
  exact eval_pinContraction_eq_zero_of_incidenceRealization
    hY root chart selected c q m hmem hc

/-- End-to-end chart certificate: the height condition yields a nonzero
integer polynomial in the original pin-provenance variables, and every real
incidence realization in the selected nonzero twist chart annihilates it. -/
theorem exists_nonzero_integer_pin_certificate_of_primeHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active)
    (c : GroundedTwistVariable root)
    (hheight : FiniteGenericChartPrimeHeightCondition
      root src dst active chart selected c) :
    ∃ Q : MvPolynomial (GroundedTwistPolynomial.PinVariable E) ℤ,
      Q ≠ 0 ∧
      ∀ (p : E → Vec3 ℝ) (Y : V → Twist ℝ),
        SparseNullIncidence.IsIncidenceRealization src dst active p Y →
        GroundedTwistPolynomial.twistCoordinates
          (Y c.1.1 - Y root) c.2 ≠ 0 →
        eval₂ (Int.castRingHom ℝ)
          (GroundedTwistPolynomial.assignmentOfPins p) Q = 0 := by
  obtain ⟨q, hq, hqVanish⟩ :=
    exists_nonzero_rational_pin_certificate_of_primeHeight
      root src dst active chart selected c hheight
  obtain ⟨Q, _a, hQ, _ha, _hProportional, hDescent⟩ :=
    RationalCertificateDescent.exists_integer_certificate_vanishing_on_real_zeros
      q hq
  refine ⟨Q, hQ, ?_⟩
  intro p Y hY hc
  exact hDescent (GroundedTwistPolynomial.assignmentOfPins p)
    (hqVanish p Y hY hc)

end

end UniversalHomogeneousChart

end RB31E2E


end
end BundleSource0010

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0010/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0010.json"

section BundleSource0011
/- Source: Papers/RigidityZheng_Incidence_UniversalDistinctChartContraction.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Incidence/UniversalDistinctChartContraction.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Contracting a complete distinctness chart to pin provenance

This is the pairwise-distinct replacement for the earlier one-coordinate
contraction.  A chart denominator is the product of one labelled nonzero
twist-difference coordinate for every ordered pair of bodies.  The height
hypothesis is imposed only on homogeneous primes avoiding that product.
Thus equality components outside the intended incidence stratum do not enter
the obligation.

The abstract homogeneous-denominator theorem gives a power of the full
denominator in the generic chart ideal.  We undo the finite reindexing, clear
the pin-coefficient denominator, evaluate on a concrete distinct chart, and
descend from rational to integer coefficients.  No new height or properness
principle is asserted.
-/

namespace RB31E2E

namespace UniversalHomogeneousChart

noncomputable section

open MvPolynomial
open NullCellulePolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Correct localized height interface -/

/-- Full-height requirement only for homogeneous primes meeting the chosen
pairwise-distinct provenance chart. -/
def FiniteGenericDistinctChartPrimeHeightCondition
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V) : Prop :=
  ∀ (Q : Ideal (FiniteGenericRelativeRing root E)),
    Q.IsPrime →
    Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule
        (Fin (groundedTwistVariableCount root))
        (GenericPinCoefficientField E)) →
    finiteGenericUniversalChartIdeal
      root src dst active angularChart selected ≤ Q →
    finiteGenericDistinctnessDenominator (E := E) root distinctChart ∉ Q →
    (groundedTwistVariableCount root : ℕ∞) ≤ Q.height

/-! ## Reindexing and coefficient clearing for an arbitrary denominator -/

/-- Undo the finite twist-variable reindexing for an arbitrary polynomial,
not just a coordinate power. -/
theorem mem_genericUniversalChartIdeal_of_rename_mem_finite
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active)
    (f : GenericRelativeRing root E)
    (hmem :
      (MvPolynomial.renameEquiv (GenericPinCoefficientField E)
        (finiteTwistIndexEquiv root)) f ∈
        finiteGenericUniversalChartIdeal
          root src dst active angularChart selected) :
    f ∈ genericUniversalChartIdeal
      root src dst active angularChart selected := by
  let e := MvPolynomial.renameEquiv (GenericPinCoefficientField E)
    (finiteTwistIndexEquiv root)
  have hmapped :
      e.symm (e f) ∈
        Ideal.map e.symm.toRingEquiv.toRingHom
          (finiteGenericUniversalChartIdeal
            root src dst active angularChart selected) :=
    Ideal.mem_map_of_mem e.symm.toRingEquiv.toRingHom hmem
  rw [finiteGenericUniversalChartIdeal_eq_map_rename,
    Ideal.map_map] at hmapped
  have hcomp :
      e.symm.toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom =
        RingHom.id (GenericRelativeRing root E) := by
    apply DFunLike.ext _ _
    intro g
    exact e.symm_apply_apply g
  rw [hcomp, Ideal.map_id] at hmapped
  simpa [e] using hmapped

/-- Generic coefficient extension of the complete distinctness denominator. -/
def genericDistinctnessDenominator
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (distinctChart : DistinctnessChart V) :
    GenericRelativeRing root E :=
  genericCoefficientExtensionHom root
    (universalDistinctnessDenominator (E := E) root distinctChart)

theorem finiteGenericDistinctnessDenominator_eq_rename_generic
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (distinctChart : DistinctnessChart V) :
    finiteGenericDistinctnessDenominator (E := E) root distinctChart =
      (MvPolynomial.renameEquiv (GenericPinCoefficientField E)
        (finiteTwistIndexEquiv root))
        (genericDistinctnessDenominator (E := E) root distinctChart) := by
  rfl

/-- Coefficient-localization denominator clearing for an arbitrary source
polynomial. -/
theorem exists_nonzero_coefficient_mul_mem_of_mem_fraction_map
    {A K σ : Type*} [CommRing A] [IsDomain A] [CommRing K]
    [Algebra A K] [IsLocalization (nonZeroDivisors A) K]
    (I : Ideal (MvPolynomial σ A)) (f : MvPolynomial σ A)
    (hmem : algebraMap (MvPolynomial σ A) (MvPolynomial σ K) f ∈
      Ideal.map (algebraMap (MvPolynomial σ A) (MvPolynomial σ K)) I) :
    ∃ q : A, q ≠ 0 ∧ C q * f ∈ I := by
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
    ((nonZeroDivisors A).map (C (σ := σ)))
    (MvPolynomial σ K)] at hmem
  obtain ⟨s, hs, hsmem⟩ := hmem
  obtain ⟨q, hq, rfl⟩ := hs
  exact ⟨q, nonZeroDivisors.ne_zero hq, hsmem⟩

/-! ## Localized contraction receipt -/

/-- The corrected distinct-chart height condition produces a rational pin
coefficient times a power of the complete provenance denominator in the
original universal chart ideal. -/
theorem exists_nonzero_pin_contraction_of_distinctChartPrimeHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hTwo : 2 ≤ Fintype.card V)
    (hheight : FiniteGenericDistinctChartPrimeHeightCondition
      root src dst active angularChart selected distinctChart) :
    ∃ (q : PinParameterRing E) (m : ℕ),
      q ≠ 0 ∧
      C q *
          universalDistinctnessDenominator (E := E) root distinctChart ^ m ∈
        universalChartIdeal
          root src dst active angularChart selected := by
  let s : FiniteGenericRelativeRing root E :=
    finiteGenericDistinctnessDenominator (E := E) root distinctChart
  have hsIrrelevant : s ∈
      finiteIrrelevantIdeal (k := GenericPinCoefficientField E)
        (groundedTwistVariableCount root) := by
    exact finiteGenericDistinctnessDenominator_mem_irrelevant
      (E := E) root distinctChart hTwo
  obtain ⟨m, hm⟩ :=
    exists_denominator_pow_mem_of_homogeneousPrime_height
      (finiteGenericUniversalChartIdeal
        root src dst active angularChart selected)
      (finiteGenericUniversalChartIdeal_isHomogeneous
        root src dst active angularChart selected)
      s hsIrrelevant hheight
  have hmRenamed :
      (MvPolynomial.renameEquiv (GenericPinCoefficientField E)
          (finiteTwistIndexEquiv root))
          (genericDistinctnessDenominator (E := E) root distinctChart) ^ m ∈
        finiteGenericUniversalChartIdeal
          root src dst active angularChart selected := by
    simpa [s, finiteGenericDistinctnessDenominator_eq_rename_generic,
      map_pow] using hm
  have hmGeneric :
      genericDistinctnessDenominator (E := E) root distinctChart ^ m ∈
        genericUniversalChartIdeal
          root src dst active angularChart selected :=
    mem_genericUniversalChartIdeal_of_rename_mem_finite
      root src dst active angularChart selected _ (by
        simpa only [map_pow] using hmRenamed)
  have hmLocalization :
      algebraMap (RelativeRing root E) (GenericRelativeRing root E)
          (universalDistinctnessDenominator
            (E := E) root distinctChart ^ m) ∈
        Ideal.map
          (algebraMap (RelativeRing root E) (GenericRelativeRing root E))
          (universalChartIdeal
            root src dst active angularChart selected) := by
    simpa [genericUniversalChartIdeal, genericDistinctnessDenominator,
      genericCoefficientExtensionHom, genericPinCoefficientHom] using hmGeneric
  obtain ⟨q, hq, hqmem⟩ :=
    exists_nonzero_coefficient_mul_mem_of_mem_fraction_map
      (universalChartIdeal
        root src dst active angularChart selected)
      (universalDistinctnessDenominator (E := E) root distinctChart ^ m)
      hmLocalization
  exact ⟨q, m, hq, hqmem⟩

/-! ## Real evaluation and integer descent -/

/-- A distinct-chart contraction receipt forces its rational pin coefficient
to vanish at every actual realization in that provenance chart. -/
theorem eval_pinContraction_eq_zero_of_distinctIncidenceRealization
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : SparseNullIncidence.IsIncidenceRealization src dst active p Y)
    (root : V) (angularChart : active → Fin 3)
    (selected : Finset active) (distinctChart : DistinctnessChart V)
    (q : PinParameterRing E) (m : ℕ)
    (hmem : C q *
        universalDistinctnessDenominator (E := E) root distinctChart ^ m ∈
      universalChartIdeal root src dst active angularChart selected)
    (hdenom : realChartEvaluation root p Y
      (universalDistinctnessDenominator (E := E) root distinctChart) ≠ 0) :
    eval₂ (Rat.castHom ℝ)
      (GroundedTwistPolynomial.assignmentOfPins p) q = 0 := by
  have hzero :=
    IsIncidenceRealization.realChartEvaluation_annihilates_universalChartIdeal
      hY root angularChart selected hmem
  rw [RingHom.mem_ker, map_mul] at hzero
  have hCoeff : realChartEvaluation root p Y (C q) =
      pinParameterEvaluation p q := by
    simp [realChartEvaluation]
  rw [hCoeff, map_pow] at hzero
  have hqzero : pinParameterEvaluation p q = 0 :=
    (mul_eq_zero.mp hzero).resolve_right (pow_ne_zero m hdenom)
  simpa [pinParameterEvaluation] using hqzero

/-- End-to-end integer certificate on one complete pairwise-distinct chart. -/
theorem exists_nonzero_integer_pin_certificate_of_distinctChartPrimeHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hTwo : 2 ≤ Fintype.card V)
    (hheight : FiniteGenericDistinctChartPrimeHeightCondition
      root src dst active angularChart selected distinctChart) :
    ∃ Q : MvPolynomial (GroundedTwistPolynomial.PinVariable E) ℤ,
      Q ≠ 0 ∧
      ∀ (p : E → Vec3 ℝ) (Y : V → Twist ℝ),
        SparseNullIncidence.IsIncidenceRealization src dst active p Y →
        realChartEvaluation root p Y
          (universalDistinctnessDenominator (E := E) root distinctChart) ≠ 0 →
        eval₂ (Int.castRingHom ℝ)
          (GroundedTwistPolynomial.assignmentOfPins p) Q = 0 := by
  obtain ⟨q, m, hq, hmem⟩ :=
    exists_nonzero_pin_contraction_of_distinctChartPrimeHeight
      root src dst active angularChart selected distinctChart hTwo hheight
  obtain ⟨Q, _a, hQ, _ha, _hProportional, hDescent⟩ :=
    RationalCertificateDescent.exists_integer_certificate_vanishing_on_real_zeros
      q hq
  refine ⟨Q, hQ, ?_⟩
  intro p Y hY hdenom
  apply hDescent (GroundedTwistPolynomial.assignmentOfPins p)
  exact eval_pinContraction_eq_zero_of_distinctIncidenceRealization
    hY root angularChart selected distinctChart q m hmem hdenom

end

end UniversalHomogeneousChart

end RB31E2E


end
end BundleSource0011

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0011/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0011.json"

section BundleSource0012
/- Source: Papers/RigidityZheng_Incidence_UniversalFullProvenanceChartContraction.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Incidence/UniversalFullProvenanceChartContraction.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Contraction on the complete incidence-provenance chart

The complete chart denominator records both sources of localization used by
the proof: pairwise body distinctness and one nonzero angular coordinate for
every active occurrence.  A full-height theorem only on primes avoiding this
product suffices to eliminate the grounded twist variables and produce a
nonzero polynomial in the original pin parameters.

This file is denominator elimination and evaluation bookkeeping.  It does
not assert the localized prime-height theorem.
-/

namespace RB31E2E

namespace UniversalHomogeneousChart

noncomputable section

open MvPolynomial
open NullCellulePolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## The exact localized-height interface -/

/-- Full twist height is required only for homogeneous primes which meet
the complete pairwise-distinct and active-angular chart. -/
def FiniteGenericIncidenceProvenancePrimeHeightCondition
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V) : Prop :=
  ∀ (Q : Ideal (FiniteGenericRelativeRing root E)),
    Q.IsPrime →
    Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule
        (Fin (groundedTwistVariableCount root))
        (GenericPinCoefficientField E)) →
    finiteGenericUniversalChartIdeal
      root src dst active angularChart selected ≤ Q →
    finiteGenericIncidenceProvenanceDenominator
      root src dst active hLoop distinctChart angularChart ∉ Q →
    (groundedTwistVariableCount root : ℕ∞) ≤ Q.height

/-! ## Generic reindexing of the complete denominator -/

def genericIncidenceProvenanceDenominator
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3) : GenericRelativeRing root E :=
  genericCoefficientExtensionHom root
    (universalIncidenceProvenanceDenominator
      root src dst active hLoop distinctChart angularChart)

theorem finiteGenericIncidenceProvenanceDenominator_eq_rename_generic
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3) :
    finiteGenericIncidenceProvenanceDenominator
        root src dst active hLoop distinctChart angularChart =
      (MvPolynomial.renameEquiv (GenericPinCoefficientField E)
        (finiteTwistIndexEquiv root))
        (genericIncidenceProvenanceDenominator
          root src dst active hLoop distinctChart angularChart) := by
  rfl

/-! ## Elimination to the pin ring -/

/-- The complete localized-height condition yields a rational pin
coefficient times a power of the complete provenance denominator in the
original universal chart ideal. -/
theorem exists_nonzero_pin_contraction_of_incidenceProvenancePrimeHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hTwo : 2 ≤ Fintype.card V)
    (hheight : FiniteGenericIncidenceProvenancePrimeHeightCondition
      root src dst active hLoop angularChart selected distinctChart) :
    ∃ (q : PinParameterRing E) (m : ℕ),
      q ≠ 0 ∧
      C q *
          universalIncidenceProvenanceDenominator
            root src dst active hLoop distinctChart angularChart ^ m ∈
        universalChartIdeal
          root src dst active angularChart selected := by
  let s : FiniteGenericRelativeRing root E :=
    finiteGenericIncidenceProvenanceDenominator
      root src dst active hLoop distinctChart angularChart
  have hsIrrelevant : s ∈
      finiteIrrelevantIdeal (k := GenericPinCoefficientField E)
        (groundedTwistVariableCount root) := by
    exact finiteGenericIncidenceProvenanceDenominator_mem_irrelevant
      root src dst active hLoop distinctChart angularChart hTwo
  obtain ⟨m, hm⟩ :=
    exists_denominator_pow_mem_of_homogeneousPrime_height
      (finiteGenericUniversalChartIdeal
        root src dst active angularChart selected)
      (finiteGenericUniversalChartIdeal_isHomogeneous
        root src dst active angularChart selected)
      s hsIrrelevant hheight
  have hmRenamed :
      (MvPolynomial.renameEquiv (GenericPinCoefficientField E)
          (finiteTwistIndexEquiv root))
          (genericIncidenceProvenanceDenominator
            root src dst active hLoop distinctChart angularChart) ^ m ∈
        finiteGenericUniversalChartIdeal
          root src dst active angularChart selected := by
    simpa [s,
      finiteGenericIncidenceProvenanceDenominator_eq_rename_generic,
      map_pow] using hm
  have hmGeneric :
      genericIncidenceProvenanceDenominator
          root src dst active hLoop distinctChart angularChart ^ m ∈
        genericUniversalChartIdeal
          root src dst active angularChart selected :=
    mem_genericUniversalChartIdeal_of_rename_mem_finite
      root src dst active angularChart selected _ (by
        simpa only [map_pow] using hmRenamed)
  have hmLocalization :
      algebraMap (RelativeRing root E) (GenericRelativeRing root E)
          (universalIncidenceProvenanceDenominator
            root src dst active hLoop distinctChart angularChart ^ m) ∈
        Ideal.map
          (algebraMap (RelativeRing root E) (GenericRelativeRing root E))
          (universalChartIdeal
            root src dst active angularChart selected) := by
    simpa [genericUniversalChartIdeal,
      genericIncidenceProvenanceDenominator,
      genericCoefficientExtensionHom, genericPinCoefficientHom] using hmGeneric
  obtain ⟨q, hq, hqmem⟩ :=
    exists_nonzero_coefficient_mul_mem_of_mem_fraction_map
      (universalChartIdeal
        root src dst active angularChart selected)
      (universalIncidenceProvenanceDenominator
        root src dst active hLoop distinctChart angularChart ^ m)
      hmLocalization
  exact ⟨q, m, hq, hqmem⟩

/-! ## Evaluation and integer descent -/

theorem eval_pinContraction_eq_zero_of_incidenceProvenanceRealization
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : SparseNullIncidence.IsIncidenceRealization src dst active p Y)
    (root : V) (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (q : PinParameterRing E) (m : ℕ)
    (hmem : C q *
        universalIncidenceProvenanceDenominator
          root src dst active hLoop distinctChart angularChart ^ m ∈
      universalChartIdeal root src dst active angularChart selected)
    (hdenom : realChartEvaluation root p Y
      (universalIncidenceProvenanceDenominator
        root src dst active hLoop distinctChart angularChart) ≠ 0) :
    eval₂ (Rat.castHom ℝ)
      (GroundedTwistPolynomial.assignmentOfPins p) q = 0 := by
  have hzero :=
    IsIncidenceRealization.realChartEvaluation_annihilates_universalChartIdeal
      hY root angularChart selected hmem
  rw [RingHom.mem_ker, map_mul] at hzero
  have hCoeff : realChartEvaluation root p Y (C q) =
      pinParameterEvaluation p q := by
    simp [realChartEvaluation]
  rw [hCoeff, map_pow] at hzero
  have hqzero : pinParameterEvaluation p q = 0 :=
    (mul_eq_zero.mp hzero).resolve_right (pow_ne_zero m hdenom)
  simpa [pinParameterEvaluation] using hqzero

/-- End-to-end integer pin certificate on one complete incidence chart. -/
theorem exists_nonzero_integer_pin_certificate_of_incidenceProvenancePrimeHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hTwo : 2 ≤ Fintype.card V)
    (hheight : FiniteGenericIncidenceProvenancePrimeHeightCondition
      root src dst active hLoop angularChart selected distinctChart) :
    ∃ Q : MvPolynomial (GroundedTwistPolynomial.PinVariable E) ℤ,
      Q ≠ 0 ∧
      ∀ (p : E → Vec3 ℝ) (Y : V → Twist ℝ),
        SparseNullIncidence.IsIncidenceRealization src dst active p Y →
        realChartEvaluation root p Y
          (universalIncidenceProvenanceDenominator
            root src dst active hLoop distinctChart angularChart) ≠ 0 →
        eval₂ (Int.castRingHom ℝ)
          (GroundedTwistPolynomial.assignmentOfPins p) Q = 0 := by
  obtain ⟨q, m, hq, hmem⟩ :=
    exists_nonzero_pin_contraction_of_incidenceProvenancePrimeHeight
      root src dst active hLoop angularChart selected distinctChart
        hTwo hheight
  obtain ⟨Q, _a, hQ, _ha, _hProportional, hDescent⟩ :=
    RationalCertificateDescent.exists_integer_certificate_vanishing_on_real_zeros
      q hq
  refine ⟨Q, hQ, ?_⟩
  intro p Y hY hdenom
  apply hDescent (GroundedTwistPolynomial.assignmentOfPins p)
  exact eval_pinContraction_eq_zero_of_incidenceProvenanceRealization
    hY root hLoop angularChart selected distinctChart q m hmem hdenom

end

end UniversalHomogeneousChart

end RB31E2E


end
end BundleSource0012

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0012/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0012.json"

section BundleSource0013
/- Source: Papers/RigidityGenericPinIdeal.lean -/






@[expose] public section

/-!
# The actual generic pair-pin motion ideal

The pin coefficient field is the rational function field in one coordinate
variable for each pin occurrence and each of its three spatial coordinates.
The motion ideal is generated by the literal rows of the grounded pin
operator.  Universal incidence polynomials are identified with these rows,
and the selected null equations follow from compatibility by polynomial
identities.  No incidence codimension or rigidity conclusion is assumed.
-/

namespace Papers.Rigidity.GenericPinIdeal

noncomputable section

open MvPolynomial
open RB31E2E
open RB31E2E.GroundedTwistPolynomial
open RB31E2E.UniversalHomogeneousChart
open RB31E2E.LinearFormIdeal

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

instance genericPinCoefficientField_infinite : Infinite (GenericPinCoefficientField E) :=
  Infinite.of_injective (algebraMap ℚ (GenericPinCoefficientField E))
    (RingHom.injective _)

/-- The ordinary ideal generated by the actual homogeneous linear rows. -/
def motionIdeal (root : V) (src dst : E → V) :
    Ideal (GenericRelativeRing root E) :=
  linearFormIdeal (genericMotionMatrix root src dst).row

instance motionIdeal_isPrime (root : V) (src dst : E → V) :
    (motionIdeal root src dst).IsPrime :=
  linearFormIdeal_isPrime _

/-- Its height is exactly the rank of the genuine pin matrix. -/
theorem motionIdeal_height_eq_rank (root : V) (src dst : E → V) :
    (motionIdeal root src dst).height =
      ((genericMotionMatrix root src dst).rank : ℕ∞) :=
  LinearIdealRank.linearFormIdeal_height_eq_matrix_rank _

/-- Each universal compatibility coordinate, after extending pin
coefficients, is the literal linear polynomial of the corresponding row. -/
theorem genericCompatibility_eq_linearPolynomial
    (root : V) (src dst : E → V) (e : E) (j : Fin 3) :
    genericCoefficientExtensionHom root
        (universalCompatibilityCoordinate root src dst e j) =
      linearPolynomial ((genericMotionMatrix root src dst).row (e, j)) := by
  apply MvPolynomial.funext
  intro z
  let Y : OffRoot root → RB31E2E.Twist (GenericPinCoefficientField E) :=
    fun w => (fun i => z (w, false, i), fun i => z (w, true, i))
  have hY : groundedTwistCoordinates root Y = z := by
    funext c
    rcases c with ⟨w, b, i⟩
    cases b <;> rfl
  let φ : RelativeRing root E →+* GenericPinCoefficientField E :=
    (MvPolynomial.eval z).comp (genericCoefficientExtensionHom root)
  have htwist (v : V) :
      mapTwist φ (universalGroundedTwist (E := E) root v) =
        extendGrounded root Y v := by
    by_cases hv : v = root
    · subst v
      apply Prod.ext <;> funext i <;>
        simp [universalGroundedTwist, extendOffRoot, extendGrounded, mapTwist, mapVec3]
    · apply Prod.ext <;> funext i <;>
        simp [φ, universalGroundedTwist, extendOffRoot, extendGrounded, hv,
          universalOffRootTwist, genericCoefficientExtensionHom,
          mapTwist, mapVec3, Y]
  have hpin : mapVec3 φ (universalParameterPin (root := root) e) = genericPins e := by
    funext i
    simp [φ, universalParameterPin, genericCoefficientExtensionHom, genericPinCoefficientHom,
      mapVec3, genericPins]
  have heval :
      φ (universalCompatibilityCoordinate root src dst e j) =
        groundedPinOperator root src dst genericPins Y e j := by
    have h := congrFun (mapVec3_eval φ
      (universalRelativeTwist root src dst e)
      (universalParameterPin (root := root) e)) j
    rw [universalRelativeTwist, mapTwist_sub, htwist, htwist, hpin] at h
    simpa [φ, mapVec3, universalCompatibilityCoordinate, universalRelativeTwist] using h
  have hmatrix := congrFun (groundedPinMatrix_mulVec_coordinates
    root src dst genericPins Y) (e, j)
  rw [hY] at hmatrix
  calc
    MvPolynomial.eval z (genericCoefficientExtensionHom root
        (universalCompatibilityCoordinate root src dst e j)) =
        groundedPinOperator root src dst genericPins Y e j := heval
    _ = (genericMotionMatrix root src dst).mulVec z (e, j) := hmatrix.symm
    _ = MvPolynomial.eval z
        (linearPolynomial ((genericMotionMatrix root src dst).row (e, j))) := by
      simp [linearPolynomial, Matrix.mulVec, dotProduct]

/-- All three occurrence-level compatibility equations belong to the
motion ideal. No angular chart has yet been selected. -/
theorem genericCompatibility_mem_motionIdeal
    (root : V) (src dst : E → V) (e : E) (j : Fin 3) :
    genericCoefficientExtensionHom root
      (universalCompatibilityCoordinate root src dst e j) ∈ motionIdeal root src dst := by
  rw [genericCompatibility_eq_linearPolynomial]
  exact Ideal.subset_span ⟨(e, j), rfl⟩

/-- A stationary pin forces its relative twist to be null already in the
actual linear motion ideal.  The identity is polynomial: dotting the
three compatibility coordinates with angular velocity gives the null
quadratic, so no quotient-instance coercion is needed. -/
theorem genericNull_mem_motionIdeal
    (root : V) (src dst : E → V) (e : E) :
    genericCoefficientExtensionHom root
      (universalNullEquation root src dst e) ∈ motionIdeal root src dst := by
  have hidentity : universalNullEquation root src dst e =
      ∑ j : Fin 3, (universalRelativeTwist root src dst e).1 j *
        universalCompatibilityCoordinate root src dst e j := by
    simp only [universalNullEquation, universalCompatibilityCoordinate,
      RB31E2E.Twist.splitKlein, RB31E2E.Twist.eval, RB31E2E.Vec3.dot,
      Pi.add_apply, mul_add, Finset.sum_add_distrib]
    change RB31E2E.Vec3.dot (universalRelativeTwist root src dst e).1
      (universalRelativeTwist root src dst e).2 =
        RB31E2E.Vec3.dot (universalRelativeTwist root src dst e).1
          (universalRelativeTwist root src dst e).2 +
        RB31E2E.Vec3.dot (universalRelativeTwist root src dst e).1
          (RB31E2E.Vec3.cross (universalRelativeTwist root src dst e).1
            (universalParameterPin (root := root) e))
    rw [RB31E2E.Vec3.dot_cross_self_left, add_zero]
  rw [hidentity, map_sum]
  apply Ideal.sum_mem
  intro j _
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ (genericCompatibility_mem_motionIdeal root src dst e j)

/-- Every universal incidence chart ideal lies in the genuine linear
motion ideal. Its two retained coordinates and quadratic equations are
consequences of the three original linear rows at every occurrence. -/
theorem genericChartIdeal_le_motionIdeal
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active) :
    genericUniversalChartIdeal root src dst active chart selected ≤
      motionIdeal root src dst := by
  rw [genericUniversalChartIdeal, Ideal.map_le_iff_le_comap,
    universalChartIdeal, Ideal.span_le]
  rintro q (hactive | hnull)
  · obtain ⟨a, rfl⟩ := hactive
    exact genericCompatibility_mem_motionIdeal root src dst a.1.1 a.2.1
  · obtain ⟨e, rfl⟩ := hnull
    exact genericNull_mem_motionIdeal root src dst e.1.1

/-- Only a coordinate relabelling to `Fin` is used by the finite-height
interface. This is the image of the same actual linear motion ideal. -/
def finiteMotionIdeal (root : V) (src dst : E → V) :
    Ideal (FiniteGenericRelativeRing root E) :=
  Ideal.map (MvPolynomial.renameEquiv (GenericPinCoefficientField E)
    (finiteTwistIndexEquiv root)).toRingEquiv (motionIdeal root src dst)

instance finiteMotionIdeal_isPrime (root : V) (src dst : E → V) :
    (finiteMotionIdeal root src dst).IsPrime :=
  Ideal.map_isPrime_of_equiv _

theorem finiteMotionIdeal_height_eq_rank (root : V) (src dst : E → V) :
    (finiteMotionIdeal root src dst).height =
      ((genericMotionMatrix root src dst).rank : ℕ∞) := by
  rw [finiteMotionIdeal, RingEquiv.height_map, motionIdeal_height_eq_rank]

theorem finiteChartIdeal_le_finiteMotionIdeal
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active) :
    finiteGenericUniversalChartIdeal root src dst active chart selected ≤
      finiteMotionIdeal root src dst := by
  rw [finiteGenericUniversalChartIdeal_eq_map_rename, finiteMotionIdeal]
  exact Ideal.map_mono (genericChartIdeal_le_motionIdeal root src dst active chart selected)

end

end Papers.Rigidity.GenericPinIdeal

end
end BundleSource0013

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0013/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0013.json"

section BundleSource0014
/- Source: Papers/RigidityMotionQuotient.lean -/





@[expose] public section

/-!
# Collapsing exactly the bodies that move together

The equality partition is defined from the actual kernel of the pin
operator. Collapsing its classes preserves the entire motion space, and
the collapsed system has no further pair of bodies moving together.
Every original pin occurrence remains labelled; internal occurrences
become zero rows rather than being discarded implicitly.
-/

namespace Papers.Rigidity.MotionQuotient

noncomputable section

open RB31E2E

variable {k V E : Type*} [Field k]

/-- The ordinary, ungrounded linear pin operator over any field. -/
def motionOperator (src dst : E → V) (p : E → RB31E2E.Vec3 k) :
    (V → RB31E2E.Twist k) →ₗ[k] (E → RB31E2E.Vec3 k) :=
  LinearMap.pi fun e => (RB31E2E.Twist.evalLinear (p e)).comp
    (LinearMap.proj (R := k) (φ := fun _ : V => RB31E2E.Twist k) (src e) -
      LinearMap.proj (R := k) (φ := fun _ : V => RB31E2E.Twist k) (dst e))

abbrev motionSpace (src dst : E → V) (p : E → RB31E2E.Vec3 k) :=
  (motionOperator src dst p).ker

@[simp] theorem motionOperator_apply (src dst : E → V) (p : E → RB31E2E.Vec3 k)
    (X : V → RB31E2E.Twist k) (e : E) :
    motionOperator src dst p X e =
      RB31E2E.Twist.eval (X (src e)) (p e) - RB31E2E.Twist.eval (X (dst e)) (p e) := by
  simp [motionOperator, RB31E2E.Twist.eval_sub]

theorem mem_motionSpace_iff (src dst : E → V) (p : E → RB31E2E.Vec3 k)
    (X : V → RB31E2E.Twist k) :
    X ∈ motionSpace src dst p ↔ IsTwistMotion src dst p X := by
  simp only [motionSpace, LinearMap.mem_ker, funext_iff,
    motionOperator_apply, Pi.zero_apply, sub_eq_zero, IsTwistMotion]

/-- Two bodies are identified exactly when every compatible motion gives
them the same full six-coordinate twist. -/
def equalityPartition (src dst : E → V) (p : E → RB31E2E.Vec3 k) : Setoid V where
  r u v := ∀ X : motionSpace src dst p, X.1 u = X.1 v
  iseqv := ⟨fun _ _ => rfl, fun h X => (h X).symm,
    fun h₁ h₂ X => (h₁ X).trans (h₂ X)⟩

abbrev BodyClasses (src dst : E → V) (p : E → RB31E2E.Vec3 k) :=
  Quotient (equalityPartition src dst p)

def bodyClass (src dst : E → V) (p : E → RB31E2E.Vec3 k) : V → BodyClasses src dst p :=
  Quotient.mk _

def classSource (src dst : E → V) (p : E → RB31E2E.Vec3 k) (e : E) :=
  bodyClass src dst p (src e)

def classTarget (src dst : E → V) (p : E → RB31E2E.Vec3 k) (e : E) :=
  bodyClass src dst p (dst e)

/-- Pull a motion on the classes back to the original bodies. -/
def liftClassMotion (src dst : E → V) (p : E → RB31E2E.Vec3 k) :
    motionSpace (classSource src dst p) (classTarget src dst p) p →ₗ[k]
      motionSpace src dst p where
  toFun X := ⟨fun v => X.1 (bodyClass src dst p v), by
    apply (mem_motionSpace_iff src dst p _).mpr
    exact (mem_motionSpace_iff _ _ _ _).mp X.2⟩
  map_add' X Y := rfl
  map_smul' a X := rfl

theorem liftClassMotion_injective (src dst : E → V) (p : E → RB31E2E.Vec3 k) :
    Function.Injective (liftClassMotion src dst p) := by
  intro X Y h
  apply Subtype.ext
  funext q
  induction q using Quotient.inductionOn with
  | h v => exact congrFun (congrArg Subtype.val h) v

theorem liftClassMotion_surjective (src dst : E → V) (p : E → RB31E2E.Vec3 k) :
    Function.Surjective (liftClassMotion src dst p) := by
  intro X
  let Y : BodyClasses src dst p → RB31E2E.Twist k :=
    Quotient.lift X.1 (fun _ _ h => h X)
  have hY : Y ∈ motionSpace (classSource src dst p) (classTarget src dst p) p := by
    apply (mem_motionSpace_iff _ _ _ _).mpr
    exact (mem_motionSpace_iff src dst p _).mp X.2
  exact ⟨⟨Y, hY⟩, rfl⟩

/-- The quotient construction preserves every compatible motion, in both
directions, rather than only a numerical dimension bound. -/
def motionClassEquiv (src dst : E → V) (p : E → RB31E2E.Vec3 k) :
    motionSpace (classSource src dst p) (classTarget src dst p) p ≃ₗ[k]
      motionSpace src dst p :=
  LinearEquiv.ofBijective (liftClassMotion src dst p)
    ⟨liftClassMotion_injective src dst p, liftClassMotion_surjective src dst p⟩

theorem motionClass_finrank [Fintype V]
    (src dst : E → V) (p : E → RB31E2E.Vec3 k) :
    Module.finrank k (motionSpace (classSource src dst p) (classTarget src dst p) p) =
      Module.finrank k (motionSpace src dst p) :=
  (motionClassEquiv src dst p).finrank_eq

/-- Distinct classes remain distinguishable by an actual compatible
motion of the collapsed system. -/
theorem distinct_classes_separated (src dst : E → V) (p : E → RB31E2E.Vec3 k)
    (q r : BodyClasses src dst p) (hqr : q ≠ r) :
    ∃ X : motionSpace (classSource src dst p) (classTarget src dst p) p,
      X.1 q ≠ X.1 r := by
  classical
  induction q using Quotient.inductionOn with
  | h u =>
    induction r using Quotient.inductionOn with
    | h v =>
      by_contra h
      apply hqr
      apply Quotient.sound
      intro X
      obtain ⟨Y, hY⟩ := liftClassMotion_surjective src dst p X
      have heq : Y.1 (bodyClass src dst p u) = Y.1 (bodyClass src dst p v) := by
        by_contra hne
        exact h ⟨Y, hne⟩
      have hu := congrFun (congrArg Subtype.val hY) u
      have hv := congrFun (congrArg Subtype.val hY) v
      exact hu.symm.trans (heq.trans hv)

/-- Imposing zero twist at a fixed body removes the common motions using
the actual evaluation map at that body. -/
def groundedMotionSpace (root : V) (src dst : E → V) (p : E → RB31E2E.Vec3 k) :
    Submodule k (V → RB31E2E.Twist k) :=
  motionSpace src dst p ⊓
    (LinearMap.proj (R := k) (φ := fun _ : V => RB31E2E.Twist k) root).ker

/-- Collapsing bodies also preserves grounded motions exactly. -/
def groundedClassEquiv (root : V) (src dst : E → V) (p : E → RB31E2E.Vec3 k) :
    groundedMotionSpace (bodyClass src dst p root)
      (classSource src dst p) (classTarget src dst p) p ≃ₗ[k]
    groundedMotionSpace root src dst p where
  toFun X := ⟨fun v => X.1 (bodyClass src dst p v),
    (liftClassMotion src dst p ⟨X.1, X.2.1⟩).2, X.2.2⟩
  invFun X := ⟨Quotient.lift X.1 (fun _ _ h => h ⟨X.1, X.2.1⟩), by
    constructor
    · apply (mem_motionSpace_iff _ _ _ _).mpr
      exact (mem_motionSpace_iff src dst p _).mp X.2.1
    · exact X.2.2⟩
  left_inv X := by
    apply Subtype.ext
    funext q
    induction q using Quotient.inductionOn with
    | h v => rfl
  right_inv X := rfl
  map_add' X Y := rfl
  map_smul' a X := rfl

/-- Explicitly grounding an assignment identifies the original grounded
operator kernel with the subspace of full assignments vanishing at root. -/
def groundedKernelEquiv [DecidableEq V]
    (root : V) (src dst : E → V) (p : E → RB31E2E.Vec3 k) :
    (groundedPinOperator root src dst p).ker ≃ₗ[k]
      groundedMotionSpace root src dst p where
  toFun X := ⟨extendGrounded root X.1, by
    constructor
    · exact (mem_motionSpace_iff src dst p _).mpr
        ((mem_ker_groundedPinOperator_iff root src dst p _).mp X.2)
    · exact extendGrounded_root root X.1⟩
  invFun X := ⟨fun w => X.1 w.1, by
    apply (mem_ker_groundedPinOperator_iff root src dst p _).mpr
    have hroot : X.1 root = 0 := X.2.2
    have hext : extendGrounded root (fun w : OffRoot root => X.1 w.1) = X.1 := by
      funext v
      by_cases hv : v = root
      · subst v
        simpa using hroot.symm
      · simp [extendGrounded, hv]
    rw [hext]
    exact (mem_motionSpace_iff src dst p _).mp X.2.1⟩
  left_inv X := by
    apply Subtype.ext
    funext w
    exact extendGrounded_offRoot root X.1 w
  right_inv X := by
    apply Subtype.ext
    funext v
    by_cases hv : v = root
    · subst v
      have hroot : X.1 root = 0 := X.2.2
      simpa only [extendGrounded_root] using hroot.symm
    · simp [extendGrounded, hv]
  map_add' X Y := by
    apply Subtype.ext
    funext v
    by_cases hv : v = root <;> simp [extendGrounded, hv]
  map_smul' a X := by
    apply Subtype.ext
    funext v
    by_cases hv : v = root <;> simp [extendGrounded, hv]

/-- An equivalence of body labels only changes coordinates of the actual
grounded motion space. Occurrence labels and their pins are preserved. -/
def groundedReindexEquiv {W : Type*} (e : V ≃ W)
    (root : V) (src dst : E → V) (p : E → RB31E2E.Vec3 k) :
    groundedMotionSpace (e root) (e ∘ src) (e ∘ dst) p ≃ₗ[k]
      groundedMotionSpace root src dst p where
  toFun X := ⟨fun v => X.1 (e v), by
    constructor
    · exact (mem_motionSpace_iff src dst p _).mpr
        ((mem_motionSpace_iff _ _ _ _).mp X.2.1)
    · exact X.2.2⟩
  invFun X := ⟨fun w => X.1 (e.symm w), by
    constructor
    · apply (mem_motionSpace_iff _ _ _ _).mpr
      intro a
      simpa using ((mem_motionSpace_iff src dst p _).mp X.2.1 a)
    · change X.1 (e.symm (e root)) = 0
      simpa using X.2.2⟩
  left_inv X := by
    apply Subtype.ext
    funext w
    simp
  right_inv X := by
    apply Subtype.ext
    funext v
    simp
  map_add' X Y := rfl
  map_smul' a X := rfl

/-- Any surjective body labelling embeds block-constant grounded motions
into the original grounded motion space. -/
def pullbackGroundedMotion {W : Type*} (π : V → W)
    (root : V) (src dst : E → V) (p : E → RB31E2E.Vec3 k) :
    groundedMotionSpace (π root) (π ∘ src) (π ∘ dst) p →ₗ[k]
      groundedMotionSpace root src dst p where
  toFun X := ⟨fun v => X.1 (π v), by
    constructor
    · exact (mem_motionSpace_iff src dst p _).mpr
        ((mem_motionSpace_iff _ _ _ _).mp X.2.1)
    · exact X.2.2⟩
  map_add' X Y := rfl
  map_smul' a X := rfl

theorem pullbackGroundedMotion_injective {W : Type*} (π : V → W)
    (hπ : Function.Surjective π) (root : V) (src dst : E → V) (p : E → RB31E2E.Vec3 k) :
    Function.Injective (pullbackGroundedMotion π root src dst p) := by
  intro X Y h
  apply Subtype.ext
  funext w
  obtain ⟨v, rfl⟩ := hπ w
  exact congrFun (congrArg Subtype.val h) v

/-- The literal block-constant kernel has no more dimensions than the
original compatible kernel. -/
theorem groundedKernel_finrank_le_of_surjective
    {W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (π : V → W) (hπ : Function.Surjective π) (root : V)
    (src dst : E → V) (p : E → RB31E2E.Vec3 k) :
    Module.finrank k (groundedPinOperator (π root) (π ∘ src) (π ∘ dst) p).ker ≤
      Module.finrank k (groundedPinOperator root src dst p).ker := by
  rw [(groundedKernelEquiv (π root) (π ∘ src) (π ∘ dst) p).finrank_eq,
    (groundedKernelEquiv root src dst p).finrank_eq]
  exact LinearMap.finrank_le_finrank_of_injective
    (pullbackGroundedMotion_injective π hπ root src dst p)

/-- If the block-constant grounded kernel has the whole dimension, it is
the whole kernel. Hence bodies in a block receive identical twists in
every actual compatible motion. -/
theorem equal_twists_of_groundedKernel_finrank_eq
    {W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (π : V → W) (hπ : Function.Surjective π) (root : V)
    (src dst : E → V) (p : E → RB31E2E.Vec3 k)
    (hdim : Module.finrank k (groundedPinOperator (π root) (π ∘ src) (π ∘ dst) p).ker =
      Module.finrank k (groundedPinOperator root src dst p).ker)
    (u v : V) (hblock : π u = π v) (Y : V → RB31E2E.Twist k)
    (hY : IsTwistMotion src dst p Y) : Y u = Y v := by
  have hspaces : Module.finrank k (groundedMotionSpace (π root) (π ∘ src) (π ∘ dst) p) =
      Module.finrank k (groundedMotionSpace root src dst p) := by
    rw [← (groundedKernelEquiv (π root) (π ∘ src) (π ∘ dst) p).finrank_eq,
      ← (groundedKernelEquiv root src dst p).finrank_eq]
    exact hdim
  have hsurj : Function.Surjective (pullbackGroundedMotion π root src dst p) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hspaces).mp
      (pullbackGroundedMotion_injective π hπ root src dst p)
  let X : groundedMotionSpace root src dst p := ⟨fun w => Y w - Y root, by
    constructor
    · apply (mem_motionSpace_iff src dst p _).mpr
      intro a
      simp only [RB31E2E.Twist.eval_sub, hY a]
    · exact sub_self _⟩
  obtain ⟨Z, hZ⟩ := hsurj X
  have hu := congrFun (congrArg Subtype.val hZ) u
  have hv := congrFun (congrArg Subtype.val hZ) v
  have hsub : Y u - Y root = Y v - Y root := by
    calc
      Y u - Y root = Z.1 (π u) := hu.symm
      _ = Z.1 (π v) := congrArg Z.1 hblock
      _ = Y v - Y root := hv
  exact sub_left_injective hsub

end

end Papers.Rigidity.MotionQuotient

end
end BundleSource0014

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0014/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0014.json"

section BundleSource0015
/- Source: Papers/RigidityGenericPinCharts.lean -/




@[expose] public section

/-!
# The generic motion prime meets a distinct-body incidence chart

Each chosen coordinate is separated by an actual compatible motion.
Primality of the ordinary linear row ideal combines these individual
witnesses into one nonvanishing chart denominator. No additional generic
motion or unproved incidence hypothesis is introduced.
-/

namespace Papers.Rigidity.GenericPinIdeal

noncomputable section

open MvPolynomial
open RB31E2E
open RB31E2E.GroundedTwistPolynomial
open RB31E2E.UniversalHomogeneousChart
open RB31E2E.LinearFormIdeal

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The literal coordinates obtained by grounding an actual body motion. -/
def groundedMotionCoordinates (root : V) (Y : V → RB31E2E.Twist (GenericPinCoefficientField E)) :
    GroundedTwistVariable root → GenericPinCoefficientField E :=
  fun c => twistCoordinates (Y c.1.1 - Y root) c.2

def motionEvaluation (root : V) (Y : V → RB31E2E.Twist (GenericPinCoefficientField E)) :
    GenericRelativeRing root E →+* GenericPinCoefficientField E :=
  MvPolynomial.eval (groundedMotionCoordinates root Y)

def universalMotionEvaluation (root : V) (Y : V → RB31E2E.Twist (GenericPinCoefficientField E)) :
    RelativeRing root E →+* GenericPinCoefficientField E :=
  (motionEvaluation root Y).comp (genericCoefficientExtensionHom root)

theorem universalMotionEvaluation_groundedTwist (root v : V)
    (Y : V → RB31E2E.Twist (GenericPinCoefficientField E)) :
    mapTwist (universalMotionEvaluation root Y)
      (universalGroundedTwist (E := E) root v) = Y v - Y root := by
  by_cases hv : v = root
  · subst v
    apply Prod.ext <;> funext i <;>
      simp [universalGroundedTwist, extendOffRoot, mapTwist, mapVec3]
  · apply Prod.ext <;> funext i <;>
      simp [universalMotionEvaluation, motionEvaluation, genericCoefficientExtensionHom,
        universalGroundedTwist, extendOffRoot, hv, universalOffRootTwist,
        mapTwist, mapVec3, groundedMotionCoordinates, twistCoordinates]

theorem universalMotionEvaluation_difference (root : V)
    (uv : OrderedDistinctBodyPair V) (c : TwistCoordinate)
    (Y : V → RB31E2E.Twist (GenericPinCoefficientField E)) :
    universalMotionEvaluation root Y
      (universalBodyDifferenceCoordinate (E := E) root uv c) =
      twistCoordinates (Y uv.1.1 - Y uv.1.2) c := by
  have hground (v : V) :
      universalMotionEvaluation root Y (universalGroundedCoordinate (E := E) root v c) =
        twistCoordinates (Y v - Y root) c := by
    rcases c with ⟨b, i⟩
    cases b
    · exact congrFun (congrArg Prod.fst
        (universalMotionEvaluation_groundedTwist root v Y)) i
    · exact congrFun (congrArg Prod.snd
        (universalMotionEvaluation_groundedTwist root v Y)) i
  rw [universalBodyDifferenceCoordinate, map_sub, hground, hground]
  rcases c with ⟨b, i⟩
  cases b <;> simp [twistCoordinates]

theorem universalMotionEvaluation_compatibility (root : V) (src dst : E → V)
    (Y : V → RB31E2E.Twist (GenericPinCoefficientField E)) (e : E) (j : Fin 3) :
    universalMotionEvaluation root Y
      (universalCompatibilityCoordinate root src dst e j) =
      RB31E2E.Twist.eval (Y (src e) - Y (dst e)) (genericPins e) j := by
  have hpin : mapVec3 (universalMotionEvaluation root Y)
      (universalParameterPin (root := root) e) = genericPins e := by
    funext i
    simp [universalMotionEvaluation, motionEvaluation, genericCoefficientExtensionHom,
      genericPinCoefficientHom, universalParameterPin, genericPins, mapVec3]
  have hrel : mapTwist (universalMotionEvaluation root Y)
      (universalRelativeTwist root src dst e) = Y (src e) - Y (dst e) := by
    rw [universalRelativeTwist, mapTwist_sub,
      universalMotionEvaluation_groundedTwist, universalMotionEvaluation_groundedTwist]
    abel
  have h := congrFun (mapVec3_eval (universalMotionEvaluation root Y)
    (universalRelativeTwist root src dst e)
    (universalParameterPin (root := root) e)) j
  rw [hrel, hpin] at h
  exact h

/-- Evaluating at any actual compatible motion annihilates the entire
linear motion ideal, not only its displayed generators. -/
theorem motionIdeal_le_ker_motionEvaluation (root : V) (src dst : E → V)
    (Y : V → RB31E2E.Twist (GenericPinCoefficientField E))
    (hY : IsTwistMotion src dst genericPins Y) :
    motionIdeal root src dst ≤ RingHom.ker (motionEvaluation root Y) := by
  rw [motionIdeal, linearFormIdeal, Ideal.span_le]
  rintro _ ⟨⟨e, j⟩, rfl⟩
  change linearPolynomial ((genericMotionMatrix root src dst).row (e, j)) ∈
    RingHom.ker (motionEvaluation root Y)
  rw [← genericCompatibility_eq_linearPolynomial]
  change universalMotionEvaluation root Y
    (universalCompatibilityCoordinate root src dst e j) = 0
  rw [universalMotionEvaluation_compatibility]
  exact congrFun (eval_sub_eq_zero_of_isTwistMotion hY e) j

/-- A genuine separating motion certifies that its nonzero difference
coordinate lies outside the motion prime. -/
theorem difference_not_mem_motionIdeal (root : V) (src dst : E → V)
    (uv : OrderedDistinctBodyPair V) (c : TwistCoordinate)
    (Y : V → RB31E2E.Twist (GenericPinCoefficientField E))
    (hY : IsTwistMotion src dst genericPins Y)
    (hc : twistCoordinates (Y uv.1.1 - Y uv.1.2) c ≠ 0) :
    genericCoefficientExtensionHom root
      (universalBodyDifferenceCoordinate (E := E) root uv c) ∉
        motionIdeal root src dst := by
  intro h
  have hz := motionIdeal_le_ker_motionEvaluation root src dst Y hY h
  change universalMotionEvaluation root Y
    (universalBodyDifferenceCoordinate (E := E) root uv c) = 0 at hz
  rw [universalMotionEvaluation_difference] at hz
  exact hc hz

/-- No pair of body labels is identified on the actual compatible-motion
space over the independent pin coefficient field. -/
def BodiesSeparated (src dst : E → V) : Prop :=
  ∀ u v : V, u ≠ v → ∃ Y : V → RB31E2E.Twist (GenericPinCoefficientField E),
    IsTwistMotion src dst genericPins Y ∧ Y u ≠ Y v

/-- There are complete distinct-body and active-angular charts whose
literal denominator avoids the actual motion prime. -/
theorem exists_incidenceChart_of_bodiesSeparated
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) (hsep : BodiesSeparated src dst) :
    ∃ (distinctChart : DistinctnessChart V) (angularChart : active → Fin 3),
      genericIncidenceProvenanceDenominator
        root src dst active hLoop distinctChart angularChart ∉ motionIdeal root src dst := by
  classical
  have hd : ∀ uv : OrderedDistinctBodyPair V, ∃ c : TwistCoordinate,
      genericCoefficientExtensionHom root
        (universalBodyDifferenceCoordinate (E := E) root uv c) ∉ motionIdeal root src dst := by
    intro uv
    obtain ⟨Y, hY, hne⟩ := hsep uv.1.1 uv.1.2 uv.2
    obtain ⟨c, hc⟩ := SparseNullIncidence.exists_twistCoordinate_ne_zero (sub_ne_zero.mpr hne)
    exact ⟨c, difference_not_mem_motionIdeal root src dst uv c Y hY hc⟩
  have ha : ∀ e : active, ∃ i : Fin 3,
      genericCoefficientExtensionHom root
        (universalBodyDifferenceCoordinate (E := E) root
          ⟨(src e.1, dst e.1), hLoop e.1 e.2⟩ (false, i)) ∉ motionIdeal root src dst := by
    intro e
    obtain ⟨Y, hY, hne⟩ := hsep (src e.1) (dst e.1) (hLoop e.1 e.2)
    have hangular := RB31E2E.Twist.angular_ne_zero_of_ne_zero_of_eval_eq_zero
      (Y (src e.1) - Y (dst e.1)) (genericPins e.1)
      (sub_ne_zero.mpr hne) (eval_sub_eq_zero_of_isTwistMotion hY e.1)
    obtain ⟨i, hi⟩ : ∃ i : Fin 3, (Y (src e.1) - Y (dst e.1)).1 i ≠ 0 := by
      by_contra h
      apply hangular
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    exact ⟨i, difference_not_mem_motionIdeal root src dst
      ⟨(src e.1, dst e.1), hLoop e.1 e.2⟩ (false, i) Y hY hi⟩
  choose dc hdc using hd
  choose ac hac using ha
  refine ⟨dc, ac, ?_⟩
  rw [genericIncidenceProvenanceDenominator, universalIncidenceProvenanceDenominator,
    map_mul, Ideal.IsPrime.mul_mem_iff_mem_or_mem (motionIdeal_isPrime root src dst)]
  apply not_or.mpr
  constructor
  · rw [universalDistinctnessDenominator, map_prod, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨uv, _, huv⟩
    exact hdc uv huv
  · rw [universalAngularDenominator, map_prod, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨e, _, he⟩
    exact hac e he

/-- Renaming the finite twist coordinates does not change whether the
motion prime meets a chart. -/
theorem exists_finiteIncidenceChart_of_bodiesSeparated
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) (hsep : BodiesSeparated src dst) :
    ∃ (distinctChart : DistinctnessChart V) (angularChart : active → Fin 3),
      finiteGenericIncidenceProvenanceDenominator
        root src dst active hLoop distinctChart angularChart ∉ finiteMotionIdeal root src dst := by
  obtain ⟨dc, ac, h⟩ := exists_incidenceChart_of_bodiesSeparated root src dst active hLoop hsep
  refine ⟨dc, ac, ?_⟩
  rw [finiteGenericIncidenceProvenanceDenominator_eq_rename_generic,
    finiteMotionIdeal]
  intro hx
  apply h
  exact (Ideal.apply_mem_of_equiv_iff
    (f := (MvPolynomial.renameEquiv (GenericPinCoefficientField E)
      (finiteTwistIndexEquiv root)).toRingEquiv)).mp hx

end

end Papers.Rigidity.GenericPinIdeal

end
end BundleSource0015

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0015/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0015.json"

section BundleSource0016
/- Source: Papers/RigidityZheng_Incidence_CollinearityPolynomial.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Incidence/CollinearityPolynomial.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# A nonzero polynomial certificate for three collinear pins

The high-multiplicity branch of the incidence proof is not merely called
"nongeneric": three specified pin occurrences satisfy an explicit nonzero
integer polynomial.  Keeping the occurrence labels in the variable type is
the provenance needed to know that the certificate is genuinely nonzero.
-/

namespace RB31E2E

namespace PinCollinearity

noncomputable section

open MvPolynomial

/-- Three coordinates for every pin occurrence. -/
abbrev Variable (E : Type*) := E × Fin 3

def coordinate {E : Type*} (e : E) (i : Fin 3) :
    MvPolynomial (Variable E) ℤ :=
  X (e, i)

/-- One `2×2` minor of the two displacement vectors from `e₀`. -/
def minor01 {E : Type*} (e₀ e₁ e₂ : E) :
    MvPolynomial (Variable E) ℤ :=
  (coordinate e₁ 0 - coordinate e₀ 0) *
      (coordinate e₂ 1 - coordinate e₀ 1) -
    (coordinate e₁ 1 - coordinate e₀ 1) *
      (coordinate e₂ 0 - coordinate e₀ 0)

def assignmentOfPins {k E : Type*} [CommRing k]
    (p : E → Vec3 k) : Variable E → k :=
  fun ei ↦ p ei.1 ei.2

theorem eval_minor01 {k E : Type*} [CommRing k]
    (p : E → Vec3 k) (e₀ e₁ e₂ : E) :
    eval₂ (Int.castRingHom k) (assignmentOfPins p) (minor01 e₀ e₁ e₂) =
      (p e₁ 0 - p e₀ 0) * (p e₂ 1 - p e₀ 1) -
        (p e₁ 1 - p e₀ 1) * (p e₂ 0 - p e₀ 0) := by
  simp [minor01, coordinate, assignmentOfPins]

/-- Affine collinearity with a retained direction witness. -/
def Collinear {k : Type*} [CommRing k] (p₀ p₁ p₂ : Vec3 k) : Prop :=
  ∃ (d : Vec3 k) (c₁ c₂ : k),
    p₁ - p₀ = c₁ • d ∧ p₂ - p₀ = c₂ • d

theorem minor01_eq_zero_of_collinear {k E : Type*} [CommRing k]
    (p : E → Vec3 k) (e₀ e₁ e₂ : E)
    (hcol : Collinear (p e₀) (p e₁) (p e₂)) :
    eval₂ (Int.castRingHom k) (assignmentOfPins p) (minor01 e₀ e₁ e₂) = 0 := by
  obtain ⟨d, c₁, c₂, h₁, h₂⟩ := hcol
  rw [eval_minor01]
  have h₁0 := congrFun h₁ 0
  have h₁1 := congrFun h₁ 1
  have h₂0 := congrFun h₂ 0
  have h₂1 := congrFun h₂ 1
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h₁0 h₁1 h₂0 h₂1
  rw [h₁0, h₁1, h₂0, h₂1]
  ring

/-- A common nonzero relative twist forces the polynomial certificate to
vanish on any three compatible pins. -/
theorem minor01_eq_zero_of_common_twist {k E : Type*} [Field k]
    (p : E → Vec3 k) (e₀ e₁ e₂ : E) (Y : Twist k) (hY : Y ≠ 0)
    (h₀ : Twist.eval Y (p e₀) = 0)
    (h₁ : Twist.eval Y (p e₁) = 0)
    (h₂ : Twist.eval Y (p e₂) = 0) :
    eval₂ (Int.castRingHom k) (assignmentOfPins p) (minor01 e₀ e₁ e₂) = 0 := by
  apply minor01_eq_zero_of_collinear p e₀ e₁ e₂
  obtain ⟨c₁, c₂, hc₁, hc₂⟩ :=
    Twist.three_pin_solutions_collinear_of_ne_zero Y
      (p e₀) (p e₁) (p e₂) hY h₀ h₁ h₂
  exact ⟨Y.1, c₁, c₂, hc₁, hc₂⟩

/-- The test assignment `e₁ ↦ (1,0,0)`, `e₂ ↦ (0,1,0)`,
`e₀ ↦ 0` witnesses that the minor polynomial is not zero. -/
def testAssignment {E : Type*} [DecidableEq E] (e₁ e₂ : E) :
    Variable E → ℤ
  | (e, i) =>
      if e = e₁ ∧ i = 0 then 1
      else if e = e₂ ∧ i = 1 then 1
      else 0

theorem eval_testAssignment_minor01 {E : Type*} [DecidableEq E]
    {e₀ e₁ e₂ : E} (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂)
    (h₁₂ : e₁ ≠ e₂) :
    eval (testAssignment e₁ e₂) (minor01 e₀ e₁ e₂) = 1 := by
  simp [minor01, coordinate, testAssignment, h₀₁, h₀₂, h₁₂,
    Ne.symm h₁₂]

theorem minor01_ne_zero {E : Type*} [DecidableEq E]
    {e₀ e₁ e₂ : E} (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂)
    (h₁₂ : e₁ ≠ e₂) :
    minor01 e₀ e₁ e₂ ≠ 0 := by
  intro hzero
  have := eval_testAssignment_minor01 h₀₁ h₀₂ h₁₂
  rw [hzero] at this
  simp at this

end

end PinCollinearity

end RB31E2E


end
end BundleSource0016

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0016/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0016.json"

section BundleSource0017
/- Source: Papers/RigidityGenericPinSeparation.lean -/





@[expose] public section

/-!
# Three independent generic pins force body equality

The proof uses the explicit provenance-labelled two-by-two collinearity
minor. Its nonzero polynomial remains nonzero in the actual rational
function field. Thus no distinct motion classes can share three pin
occurrences.
-/

namespace Papers.Rigidity.GenericPinIdeal

noncomputable section

open MvPolynomial
open RB31E2E
open RB31E2E.UniversalHomogeneousChart

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem genericCollinearityMinor_ne_zero
    {e₀ e₁ e₂ : E} (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂) (h₁₂ : e₁ ≠ e₂) :
    MvPolynomial.eval₂ (Int.castRingHom (GenericPinCoefficientField E))
      (PinCollinearity.assignmentOfPins (genericPins (E := E)))
      (PinCollinearity.minor01 e₀ e₁ e₂) ≠ 0 := by
  let f : MvPolynomial (E × Fin 3) ℤ →+* GenericPinCoefficientField E :=
    (genericPinCoefficientHom E).comp (MvPolynomial.map (Int.castRingHom ℚ))
  have hinj : Function.Injective f :=
    (IsFractionRing.injective (PinParameterRing E) (GenericPinCoefficientField E)).comp
      (MvPolynomial.map_injective _ Int.cast_injective)
  have hne : f (PinCollinearity.minor01 e₀ e₁ e₂) ≠ 0 := by
    intro hz
    exact PinCollinearity.minor01_ne_zero h₀₁ h₀₂ h₁₂ (hinj (by simpa using hz))
  simpa [f, PinCollinearity.minor01, PinCollinearity.coordinate,
    PinCollinearity.assignmentOfPins, genericPins, genericPinCoefficientHom] using hne

/-- A twist vanishing at three distinct generic occurrence pins is zero. -/
theorem twist_eq_zero_of_three_genericPins
    {e₀ e₁ e₂ : E} (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂) (h₁₂ : e₁ ≠ e₂)
    (X : RB31E2E.Twist (GenericPinCoefficientField E))
    (h₀ : RB31E2E.Twist.eval X (genericPins e₀) = 0)
    (h₁ : RB31E2E.Twist.eval X (genericPins e₁) = 0)
    (h₂ : RB31E2E.Twist.eval X (genericPins e₂) = 0) : X = 0 := by
  by_contra hX
  exact genericCollinearityMinor_ne_zero h₀₁ h₀₂ h₁₂
    (PinCollinearity.minor01_eq_zero_of_common_twist
      genericPins e₀ e₁ e₂ X hX h₀ h₁ h₂)

/-- Compatibility is independent of which orientation stores a pin. -/
theorem eval_difference_eq_zero_of_unordered_endpoints
    (src dst : E → V) (Y : V → RB31E2E.Twist (GenericPinCoefficientField E))
    (hY : IsTwistMotion src dst genericPins Y) (u v : V) (e : E)
    (he : s(src e, dst e) = s(u, v)) :
    RB31E2E.Twist.eval (Y u - Y v) (genericPins e) = 0 := by
  rw [RB31E2E.Twist.eval_sub, sub_eq_zero]
  rcases Sym2.eq_iff.mp he with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · simpa only [hu, hv] using hY e
  · simpa only [hu, hv] using (hY e).symm

/-- A pair of separated bodies can be joined by at most two occurrences. -/
theorem bundle_card_le_two_of_bodiesSeparated
    (src dst : E → V) (hsep : BodiesSeparated src dst)
    (u v : V) (huv : u ≠ v) :
    (Finset.univ.filter fun e => s(src e, dst e) = s(u, v)).card ≤ 2 := by
  classical
  by_contra h
  have hcard : 2 < (Finset.univ.filter fun e => s(src e, dst e) = s(u, v)).card := by omega
  obtain ⟨e₀, e₁, e₂, he₀, he₁, he₂, h₀₁, h₀₂, h₁₂⟩ := Finset.two_lt_card_iff.mp hcard
  have h₀ := (Finset.mem_filter.mp he₀).2
  have h₁ := (Finset.mem_filter.mp he₁).2
  have h₂ := (Finset.mem_filter.mp he₂).2
  obtain ⟨Y, hY, hne⟩ := hsep u v huv
  apply (sub_ne_zero.mpr hne)
  exact twist_eq_zero_of_three_genericPins h₀₁ h₀₂ h₁₂ (Y u - Y v)
    (eval_difference_eq_zero_of_unordered_endpoints src dst Y hY u v e₀ h₀)
    (eval_difference_eq_zero_of_unordered_endpoints src dst Y hY u v e₁ h₁)
    (eval_difference_eq_zero_of_unordered_endpoints src dst Y hY u v e₂ h₂)

/-- The small-bundle hypothesis in the sparse-skeleton argument follows
from separation of the actual generic motion classes. -/
theorem fineMultiplicity_le_two_of_bodiesSeparated
    (H : BodyPinIncidence) {I : Type} [Fintype I] [DecidableEq I]
    (label : H.Body → I)
    (hsep : BodiesSeparated (label ∘ H.left) (label ∘ H.right))
    (e : SimpleEdge I) : H.fineMultiplicityOn label e ≤ 2 := by
  have hout : s(e.1.out.1, e.1.out.2) = e.1 := e.1.out_eq
  have hne : e.1.out.1 ≠ e.1.out.2 := by
    intro heq
    apply e.2
    rw [← hout]
    simp [heq]
  have h := bundle_card_le_two_of_bodiesSeparated
    (label ∘ H.left) (label ∘ H.right) hsep e.1.out.1 e.1.out.2 hne
  simpa only [BodyPinIncidence.fineMultiplicityOn,
    BodyPinIncidence.bundleMultiplicityOn, Function.comp_apply, hout] using h

end

end Papers.Rigidity.GenericPinIdeal

end
end BundleSource0017

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0017/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0017.json"

section BundleSource0018
/- Source: Papers/RigidityZheng_Algebra_PolynomialPrimeTrdegHeight.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/PolynomialPrimeTrdegHeight.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/










@[expose] public section

/-!
# Heights of primes in finite polynomial rings

This file develops the commutative-algebra bridge needed to turn a
function-field dimension estimate for a selected-null component into a
height estimate in its ambient finite polynomial ring.

The first kernel theorem records the equidimensionality of closed points of
finite affine space over a field.  It is proved directly from the one-variable
height formula and the Jacobson property of finite polynomial rings; it does
not assume catenarity or a dimension formula as an extra premise.
-/

namespace RB31E2E

namespace PolynomialPrimeTrdegHeight

noncomputable section

open MvPolynomial

/-- The contraction of a polynomial-ring ideal to its coefficient ring. -/
def coefficientContraction {A τ : Type*} [CommRing A]
    (P : Ideal (MvPolynomial τ A)) : Ideal A :=
  P.comap (MvPolynomial.C : A →+* MvPolynomial τ A)

/-! ## Coordinate transcendence bases in polynomial quotients -/

/-- The image of a polynomial coordinate in a quotient. -/
def quotientCoordinate {k ι : Type*} [CommRing k]
    (P : Ideal (MvPolynomial ι k)) (i : ι) :
    MvPolynomial ι k ⧸ P :=
  Ideal.Quotient.mk P (MvPolynomial.X i)

/-- A polynomial quotient is generated, as an algebra, by the images of its
coordinate variables. -/
theorem adjoin_range_quotientCoordinate
    {k ι : Type*} [CommRing k]
    (P : Ideal (MvPolynomial ι k)) :
    Algebra.adjoin k (Set.range (quotientCoordinate P)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  apply top_unique
  rintro b -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨f, ?_⟩
  change MvPolynomial.aeval
    (fun d : ι ↦ Ideal.Quotient.mk P (MvPolynomial.X d)) f =
      Ideal.Quotient.mk P f
  rw [← MvPolynomial.mkₐ_eq_aeval P]
  rfl

/-- Every prime quotient of a finite polynomial ring admits a
transcendence basis chosen from the images of the original coordinates.
This is an existence theorem, not a premise of the later height formula. -/
theorem exists_coordinate_transcendenceBasis
    {k ι : Type*} [Field k] [Finite ι]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] :
    ∃ t : Set (MvPolynomial ι k ⧸ P),
      t ⊆ Set.range (quotientCoordinate P) ∧
      IsTranscendenceBasis k
        ((↑) : t → (MvPolynomial ι k ⧸ P)) := by
  let B := MvPolynomial ι k ⧸ P
  let x : ι → B := quotientCoordinate P
  have htop : Algebra.adjoin k (Set.range x) = ⊤ :=
    adjoin_range_quotientCoordinate P
  letI : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range x)) B := by
    constructor
    intro b
    have hb : b ∈ Algebra.adjoin k (Set.range x) := by
      rw [htop]
      trivial
    exact isAlgebraic_algebraMap
      (⟨b, hb⟩ : Algebra.adjoin k (Set.range x))
  exact exists_isTranscendenceBasis_subset (R := k) (A := B)
    (Set.range x)

/-- Index-level version: one can choose a subset of the original variable
indices whose quotient-coordinate images form a transcendence basis. -/
theorem exists_coordinateIndex_transcendenceBasis
    {k ι : Type*} [Field k] [Finite ι]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] :
    ∃ S : Set ι,
      IsTranscendenceBasis k
        (fun i : S ↦ quotientCoordinate P i) := by
  obtain ⟨t, ht, htb⟩ := exists_coordinate_transcendenceBasis P
  let g : t → ι := fun y ↦
    Classical.choose (ht y.property)
  have hg (y : t) : quotientCoordinate P (g y) = y :=
    Classical.choose_spec (ht y.property)
  have hginj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    simpa [hg] using congrArg (quotientCoordinate P) hab
  let S : Set ι := Set.range g
  let e : t ≃ S := Equiv.ofInjective g hginj
  have heq :
      (fun i : S ↦ quotientCoordinate P i) ∘ e =
        ((↑) : t → (MvPolynomial ι k ⧸ P)) := by
    funext y
    exact hg y
  refine ⟨S, ?_⟩
  exact (isTranscendenceBasis_equiv' e heq).mp htb

/-- Split a finite variable set into a chosen coordinate set and its
complement, viewing the latter as polynomial variables over the former. -/
def coordinateSplitEquiv {k ι : Type*} [CommRing k] (S : Set ι) :
    MvPolynomial (Sᶜ : Set ι) (MvPolynomial S k) ≃ₐ[k]
      MvPolynomial ι k := by
  classical
  exact (MvPolynomial.sumAlgEquiv k (Sᶜ : Set ι) S).symm.trans
    (MvPolynomial.renameEquiv k
      ((Equiv.sumComm (Sᶜ : Set ι) S).trans
        (Equiv.Set.sumCompl S)))

/-- Pull a polynomial prime back along the coordinate splitting
equivalence. -/
def coordinateSplitPrime {k ι : Type*} [CommRing k]
    (P : Ideal (MvPolynomial ι k)) (S : Set ι) :
    Ideal (MvPolynomial (Sᶜ : Set ι) (MvPolynomial S k)) :=
  P.comap (coordinateSplitEquiv (k := k) S).toAlgHom.toRingHom

theorem coordinateSplitPrime_isPrime
    {k ι : Type*} [CommRing k]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] (S : Set ι) :
    (coordinateSplitPrime P S).IsPrime := by
  exact Ideal.comap_isPrime
    (f := (coordinateSplitEquiv (k := k) S).toAlgHom.toRingHom)
    (K := P)

/-- On the coefficient-polynomial subring, the coordinate splitting
equivalence is simply renaming by the subtype inclusion. -/
theorem coordinateSplitEquiv_comp_C
    {k ι : Type*} [CommRing k] (S : Set ι) :
    (coordinateSplitEquiv (k := k) S).toAlgHom.toRingHom.comp
      (MvPolynomial.C :
        MvPolynomial S k →+*
          MvPolynomial (Sᶜ : Set ι) (MvPolynomial S k)) =
      (MvPolynomial.rename ((↑) : S → ι)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [coordinateSplitEquiv]
  · intro i
    classical
    simp only [coordinateSplitEquiv, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, rename_X, AlgEquiv.toAlgHom_eq_coe,
      AlgEquiv.toAlgHom_toRingHom, RingHom.coe_comp,
      AlgEquiv.coe_trans, Function.comp_apply,
      MvPolynomial.sumAlgEquiv_symm_C_X,
      renameEquiv_apply, Equiv.coe_trans, Equiv.sumComm_apply,
      Sum.swap_inr, Equiv.Set.sumCompl_apply_inl]

/-- Algebraic independence of the chosen quotient coordinates says exactly
that the split prime has zero coefficient contraction. -/
theorem coordinateSplitPrime_contraction_eq_bot
    {k ι : Type*} [Field k]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] (S : Set ι)
    (hS : AlgebraicIndependent k
      (fun i : S ↦ quotientCoordinate P i)) :
    coefficientContraction (coordinateSplitPrime P S) = ⊥ := by
  let f : MvPolynomial S k →ₐ[k] (MvPolynomial ι k ⧸ P) :=
    (Ideal.Quotient.mkₐ k P).comp
      (MvPolynomial.rename ((↑) : S → ι))
  have hf : f = MvPolynomial.aeval
      (fun i : S ↦ quotientCoordinate P i) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [f, quotientCoordinate]
  have hfinj : Function.Injective f := by
    rw [hf]
    exact algebraicIndependent_iff_injective_aeval.mp hS
  rw [coefficientContraction, coordinateSplitPrime,
    Ideal.comap_comap, coordinateSplitEquiv_comp_C]
  rw [← @Ideal.mk_ker _ _ P,
    RingHom.comap_ker]
  exact (RingHom.injective_iff_ker_eq_bot f.toRingHom).mp hfinj

/-- Evaluation of the chosen coordinate-polynomial ring in the prime
quotient. -/
def coordinateAeval {k ι : Type*} [Field k]
    (P : Ideal (MvPolynomial ι k)) (S : Set ι) :
    MvPolynomial S k →ₐ[k] (MvPolynomial ι k ⧸ P) :=
  MvPolynomial.aeval (fun i : S ↦ quotientCoordinate P i)

/-- The fraction-field map induced by evaluating a polynomial in an
algebraically independent family of quotient coordinates. -/
def coordinateFractionHom {k ι : Type*} [Field k]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] (S : Set ι)
    (hS : AlgebraicIndependent k
      (fun i : S ↦ quotientCoordinate P i)) :
    FractionRing (MvPolynomial S k) →ₐ[k]
      FractionRing (MvPolynomial ι k ⧸ P) :=
  let B := MvPolynomial ι k ⧸ P
  let L := FractionRing B
  let gL : MvPolynomial S k →ₐ[k] L :=
    (IsScalarTower.toAlgHom k B L).comp (coordinateAeval P S)
  IsFractionRing.liftAlgHom (g := gL)
    ((FaithfulSMul.algebraMap_injective B L).comp
      (algebraicIndependent_iff_injective_aeval.mp hS))

/-- A coordinate transcendence basis makes the fraction field of the prime
quotient algebraic over the fraction field of the basis-coordinate
polynomial ring.  The algebra structure on the target fraction field is the
canonical lift of coordinate evaluation. -/
theorem fractionRing_quotient_isAlgebraic_over_coordinateBasis
    {k ι : Type*} [Field k]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] (S : Set ι)
    (hS : IsTranscendenceBasis k
      (fun i : S ↦ quotientCoordinate P i)) :
    let A := MvPolynomial S k
    let B := MvPolynomial ι k ⧸ P
    let K := FractionRing A
    let L := FractionRing B
    let κ : K →ₐ[k] L := coordinateFractionHom P S hS.1
    @Algebra.IsAlgebraic K L
      (inferInstance : CommRing K) (inferInstance : Ring L)
      κ.toRingHom.toAlgebra := by
  dsimp only
  let A := MvPolynomial S k
  let B := MvPolynomial ι k ⧸ P
  let K := FractionRing A
  let L := FractionRing B
  let g : A →ₐ[k] B := coordinateAeval P S
  have hg : Function.Injective g :=
    algebraicIndependent_iff_injective_aeval.mp hS.1
  letI : Algebra A B := g.toRingHom.toAlgebra
  have hAB : Algebra.IsAlgebraic A B := by
    let E := hS.1.aevalEquiv
    haveI : Algebra.IsAlgebraic
        (Algebra.adjoin k
          (Set.range (fun i : S ↦ quotientCoordinate P i))) B :=
      hS.isAlgebraic
    apply Algebra.IsAlgebraic.of_ringHom_of_comp_eq
      (f := E.toRingHom) (g := RingHom.id B)
      E.surjective Function.injective_id
    apply DFunLike.ext _ _
    intro a
    change algebraMap
      (Algebra.adjoin k
        (Set.range (fun i : S ↦ quotientCoordinate P i))) B
        (hS.1.aevalEquiv a) =
      MvPolynomial.aeval
        (fun i : S ↦ quotientCoordinate P i) a
    exact hS.1.algebraMap_aevalEquiv a
  let gL : A →ₐ[k] L :=
    (IsScalarTower.toAlgHom k B L).comp g
  have hBL : Algebra.IsAlgebraic B L :=
    IsLocalization.isAlgebraic L (nonZeroDivisors B)
  have hAL : Algebra.IsAlgebraic A L :=
    Algebra.IsAlgebraic.trans A B L
  have hgL : Function.Injective gL :=
    (FaithfulSMul.algebraMap_injective B L).comp hg
  let κ : K →ₐ[k] L := coordinateFractionHom P S hS.1
  letI : Algebra K L := κ.toRingHom.toAlgebra
  letI : IsScalarTower A K L :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change gL a = κ (algebraMap A K a)
      exact (IsFractionRing.lift_algebraMap hgL a).symm
  exact IsFractionRing.comap_isAlgebraic_iff.mp hAL

/-- After localizing the chosen coordinate-transcendence-basis ring, the
remaining-coordinate quotient is algebraic.  This is the generic-fibre
statement that converts coordinate provenance into a height computation. -/
theorem coordinateSplitPrime_genericFibre_trdeg_eq_zero
    {k ι : Type*} [Field k]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] (S : Set ι)
    (hS : IsTranscendenceBasis k
      (fun i : S ↦ quotientCoordinate P i)) :
    Algebra.trdeg (FractionRing (MvPolynomial S k))
      (MvPolynomial (Sᶜ : Set ι)
          (FractionRing (MvPolynomial S k)) ⧸
        (coordinateSplitPrime P S).map
          (MvPolynomial.map
            (algebraMap (MvPolynomial S k)
              (FractionRing (MvPolynomial S k))))) = 0 := by
  let A := MvPolynomial S k
  let B := MvPolynomial ι k ⧸ P
  let K := FractionRing A
  let L := FractionRing B
  let R := MvPolynomial (Sᶜ : Set ι) A
  let RK := MvPolynomial (Sᶜ : Set ι) K
  let E : R ≃ₐ[k] MvPolynomial ι k := coordinateSplitEquiv S
  let J : Ideal R := coordinateSplitPrime P S
  let Q : Ideal RK :=
    J.map (MvPolynomial.map (algebraMap A K))
  let g : A →ₐ[k] B := coordinateAeval P S
  have hg : Function.Injective g :=
    algebraicIndependent_iff_injective_aeval.mp hS.1
  let gL : A →ₐ[k] L :=
    (IsScalarTower.toAlgHom k B L).comp g
  have hgL : Function.Injective gL :=
    (FaithfulSMul.algebraMap_injective B L).comp hg
  let κ : K →ₐ[k] L := coordinateFractionHom P S hS.1
  letI : Algebra K L := κ.toRingHom.toAlgebra
  have hκ (a : A) :
      κ (algebraMap A K a) = algebraMap B L (g a) := by
    change κ (algebraMap A K a) = gL a
    exact IsFractionRing.lift_algebraMap hgL a
  have hKL : Algebra.IsAlgebraic K L := by
    simpa [A, B, K, L, κ] using
      fractionRing_quotient_isAlgebraic_over_coordinateBasis P S hS
  letI : Algebra.IsAlgebraic K L := hKL
  let y : (Sᶜ : Set ι) → L := fun i ↦
    algebraMap B L (quotientCoordinate P i)
  let φ : RK →ₐ[K] L := MvPolynomial.aeval y
  have hEcoeff (a : A) :
      Ideal.Quotient.mk P (E (MvPolynomial.C a)) = g a := by
    calc
      Ideal.Quotient.mk P (E (MvPolynomial.C a)) =
          Ideal.Quotient.mk P
            (MvPolynomial.rename ((↑) : S → ι) a) := by
        congr 1
        exact DFunLike.congr_fun
          (coordinateSplitEquiv_comp_C (k := k) S) a
      _ = MvPolynomial.aeval
          (fun i : ι ↦ quotientCoordinate P i)
          (MvPolynomial.rename ((↑) : S → ι) a) := by
        change (Ideal.Quotient.mkₐ k P)
            (MvPolynomial.rename ((↑) : S → ι) a) = _
        rw [MvPolynomial.mkₐ_eq_aeval]
        rfl
      _ = MvPolynomial.aeval
          (fun i : S ↦ quotientCoordinate P i) a := by
        rw [MvPolynomial.aeval_rename]
        rfl
      _ = g a := rfl
  have hEX (i : (Sᶜ : Set ι)) :
      E (MvPolynomial.X i) = MvPolynomial.X (i : ι) := by
    classical
    change MvPolynomial.rename ((Equiv.Set.sumCompl S) ∘ Sum.swap)
      ((MvPolynomial.sumAlgEquiv k (Sᶜ : Set ι) S).symm (MvPolynomial.X i)) = _
    rw [MvPolynomial.sumAlgEquiv_symm_X k (Sᶜ : Set ι) S i,
      MvPolynomial.rename_X]
    rfl
  have hcomp :
      φ.toRingHom.comp (MvPolynomial.map (algebraMap A K)) =
        (algebraMap B L).comp
          ((Ideal.Quotient.mk P).comp E.toRingEquiv.toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.coe_comp, Function.comp_apply]
      calc
        φ.toRingHom
            (MvPolynomial.map (algebraMap A K) (MvPolynomial.C a)) =
            κ (algebraMap A K a) := by
          rw [MvPolynomial.map_C]
          change MvPolynomial.aeval y
            (MvPolynomial.C (algebraMap A K a)) = _
          rw [MvPolynomial.aeval_C]
          rfl
        _ = algebraMap B L (g a) := hκ a
        _ = algebraMap B L
            (Ideal.Quotient.mk P (E (MvPolynomial.C a))) := by
          rw [hEcoeff]
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply]
      calc
        φ.toRingHom
            (MvPolynomial.map (algebraMap A K) (MvPolynomial.X i)) =
            y i := by
          rw [MvPolynomial.map_X]
          change MvPolynomial.aeval y (MvPolynomial.X i) = y i
          rw [MvPolynomial.aeval_X]
        _ = algebraMap B L (quotientCoordinate P i) := rfl
        _ = algebraMap B L
            (Ideal.Quotient.mk P (E (MvPolynomial.X i))) := by
          rw [hEX]
          rfl
  letI : Algebra R RK := MvPolynomial.algebraMvPolynomial
  let M : Submonoid R :=
    (nonZeroDivisors A).map
      (MvPolynomial.C : A →+* R)
  have hcomap :
      (RingHom.ker φ.toRingHom).comap (algebraMap R RK) = J := by
    apply Ideal.ext
    intro r
    change φ ((algebraMap R RK) r) = 0 ↔ r ∈ J
    change φ (MvPolynomial.map (algebraMap A K) r) = 0 ↔ r ∈ J
    have hrcomp := DFunLike.congr_fun hcomp r
    change φ (MvPolynomial.map (algebraMap A K) r) =
      algebraMap B L (Ideal.Quotient.mk P (E r)) at hrcomp
    rw [hrcomp]
    constructor
    · intro hr
      have hr' : Ideal.Quotient.mk P (E r) = 0 :=
        (FaithfulSMul.algebraMap_injective B L) (by
          rw [map_zero]
          exact hr)
      have : E r ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hr'
      exact this
    · intro hr
      have hr' : Ideal.Quotient.mk P (E r) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hr
      simpa using congrArg (algebraMap B L) hr'
  have hker : RingHom.ker φ.toRingHom = Q := by
    have hloc := IsLocalization.map_under M RK
      (RingHom.ker φ.toRingHom)
    rw [Ideal.under_def, hcomap] at hloc
    exact hloc.symm
  have hzero : ∀ x : RK, x ∈ Q → φ x = 0 := by
    intro x hx
    exact (RingHom.mem_ker).mp (hker.symm ▸ hx)
  let φbar : RK ⧸ Q →ₐ[K] L :=
    Ideal.Quotient.liftₐ Q φ hzero
  have hφbar : Function.Injective φbar := by
    change Function.Injective
      (Ideal.Quotient.lift Q φ.toRingHom hzero)
    exact (Ideal.injective_lift_iff hzero).mpr hker
  letI : Algebra.IsAlgebraic K (RK ⧸ Q) :=
    Algebra.IsAlgebraic.of_injective φbar hφbar
  exact trdeg_eq_zero

/-! ## The canonical coefficient contraction and fibre prime -/

/-- The prime in `(A / p)[Y]` obtained from `P ⊂ A[Y]`, where
`p = P ∩ A`.  We first quotient by `p A[Y]` and then use the canonical
coefficient-quotient polynomial equivalence. -/
def polynomialFibreIdeal {A τ : Type*} [CommRing A]
    (P : Ideal (MvPolynomial τ A)) :
    Ideal (MvPolynomial τ (A ⧸ coefficientContraction P)) :=
  let p := coefficientContraction P
  Ideal.map
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) p).symm.toRingEquiv
    (P.map (Ideal.Quotient.mk
      (p.map (MvPolynomial.C : A →+* MvPolynomial τ A))))

/-- A prime polynomial ideal has prime coefficient contraction. -/
theorem coefficientContraction_isPrime
    {A τ : Type*} [CommRing A]
    (P : Ideal (MvPolynomial τ A)) [P.IsPrime] :
    (coefficientContraction P).IsPrime := by
  exact Ideal.comap_isPrime
    (f := (MvPolynomial.C : A →+* MvPolynomial τ A)) (K := P)

/-- The canonical fibre ideal of a prime is prime. -/
theorem polynomialFibreIdeal_isPrime
    {A τ : Type*} [CommRing A]
    (P : Ideal (MvPolynomial τ A)) [P.IsPrime] :
    (polynomialFibreIdeal P).IsPrime := by
  let p := coefficientContraction P
  letI : p.IsPrime := coefficientContraction_isPrime P
  have hpP : p.map
      (MvPolynomial.C : A →+* MvPolynomial τ A) ≤ P := by
    exact Ideal.map_comap_le
  let q : Ideal
      (MvPolynomial τ A ⧸
        p.map (MvPolynomial.C : A →+* MvPolynomial τ A)) :=
    P.map (Ideal.Quotient.mk
      (p.map (MvPolynomial.C : A →+* MvPolynomial τ A)))
  letI : q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpP
  change (Ideal.map
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) p).symm.toRingEquiv
    q).IsPrime
  infer_instance

/-- The canonical fibre prime contracts to zero in the coefficient-domain
quotient. -/
theorem polynomialFibreIdeal_comap_C
    {A τ : Type*} [CommRing A]
    (P : Ideal (MvPolynomial τ A)) [P.IsPrime] :
    (polynomialFibreIdeal P).comap
      (MvPolynomial.C :
        (A ⧸ coefficientContraction P) →+*
          MvPolynomial τ (A ⧸ coefficientContraction P)) = ⊥ := by
  let p := coefficientContraction P
  let J : Ideal (MvPolynomial τ A) :=
    p.map (MvPolynomial.C : A →+* MvPolynomial τ A)
  have hJP : J ≤ P := by
    exact Ideal.map_comap_le
  let E : MvPolynomial τ (A ⧸ p) ≃ₐ[A]
      (MvPolynomial τ A ⧸ J) :=
    MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) p
  let q : Ideal (MvPolynomial τ A ⧸ J) :=
    P.map (Ideal.Quotient.mk J)
  apply le_antisymm
  · intro a ha
    rw [Ideal.mem_bot]
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change MvPolynomial.C (Ideal.Quotient.mk p a) ∈
      Ideal.map E.symm.toRingEquiv q at ha
    rw [Ideal.mem_map_iff_of_surjective E.symm.toRingEquiv
      E.symm.surjective] at ha
    obtain ⟨z, hz, hza⟩ := ha
    have heq : E (MvPolynomial.C (Ideal.Quotient.mk p a)) = z := by
      calc
        E (MvPolynomial.C (Ideal.Quotient.mk p a)) = E (E.symm z) :=
          congrArg E hza.symm
        _ = z := E.apply_symm_apply z
    have hz' : E (MvPolynomial.C (Ideal.Quotient.mk p a)) ∈ q := by
      rw [heq]
      exact hz
    have hE : E (MvPolynomial.C (Ideal.Quotient.mk p a)) =
        Ideal.Quotient.mk J (MvPolynomial.C a) := by
      simp [E, J, MvPolynomial.quotientEquivQuotientMvPolynomial]
    rw [hE, Ideal.mem_quotient_iff_mem hJP] at hz'
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hz'
  · exact bot_le

/-- A prime whose quotient is algebraic over a field is maximal.

This is the zero-dimensional endpoint used after passing to the fraction
field of a chosen transcendence basis.  Over a field, algebraicity is
integrality; lying over the maximal zero ideal then makes the zero ideal of
the quotient maximal.
-/
theorem prime_isMaximal_of_quotient_isAlgebraic
    {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (P : Ideal R) [P.IsPrime] [Algebra.IsAlgebraic K (R ⧸ P)] :
    P.IsMaximal := by
  rw [← Ideal.bot_quotient_isMaximal_iff P]
  letI : Algebra.IsIntegral K (R ⧸ P) :=
    Algebra.IsAlgebraic.isIntegral
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under
      (R := K) (S := R ⧸ P) (⊥ : Ideal (R ⧸ P))
  simpa using (Ideal.bot_isMaximal (K := K))

/-- Every maximal ideal of a polynomial ring in finitely many variables over
a field has height equal to the number of variables.

The proof peels off one variable at a time.  The contraction of a maximal
ideal remains maximal because the coefficient ring is Jacobson, and
`Polynomial.height_eq_height_add_one` supplies the exact height increment.
-/
theorem maximalIdeal_height_eq_natCard
    {k ι : Type*} [Field k] [Finite ι]
    (P : Ideal (MvPolynomial ι k)) [P.IsMaximal] :
    P.height = (Nat.card ι : ℕ∞) := by
  induction ι using Finite.induction_empty_option with
  | @of_equiv α β e IH =>
      let E : MvPolynomial β k ≃ₐ[k] MvPolynomial α k :=
        MvPolynomial.renameEquiv k e.symm
      let Q : Ideal (MvPolynomial α k) := Ideal.map E.toRingEquiv P
      letI : Q.IsMaximal := Ideal.map_isMaximal_of_equiv E.toRingEquiv
      calc
        P.height = Q.height := (E.toRingEquiv.height_map P).symm
        _ = (Nat.card α : ℕ∞) := IH Q
        _ = (Nat.card β : ℕ∞) := by rw [Nat.card_congr e]
  | h_empty =>
      let E : MvPolynomial PEmpty k ≃+* k :=
        MvPolynomial.isEmptyRingEquiv k PEmpty
      let Q : Ideal k := Ideal.map E P
      letI : Q.IsMaximal := Ideal.map_isMaximal_of_equiv E
      have hQ : Q = ⊥ := Ideal.eq_bot_of_prime Q
      calc
        P.height = Q.height := (E.height_map P).symm
        _ = (0 : ℕ∞) := by rw [hQ, Ideal.height_bot]
        _ = (Nat.card PEmpty : ℕ∞) := by simp
  | @h_option α _ IH =>
      let E : MvPolynomial (Option α) k ≃ₐ[k]
          Polynomial (MvPolynomial α k) :=
        MvPolynomial.optionEquivLeft k α
      let Q : Ideal (Polynomial (MvPolynomial α k)) :=
        Ideal.map E.toRingEquiv P
      letI : Q.IsMaximal := Ideal.map_isMaximal_of_equiv E.toRingEquiv
      let p : Ideal (MvPolynomial α k) := Q.comap Polynomial.C
      letI : p.IsMaximal :=
        Polynomial.isMaximal_comap_C_of_isJacobsonRing Q
      letI : Q.LiesOver p := ⟨rfl⟩
      calc
        P.height = Q.height := (E.toRingEquiv.height_map P).symm
        _ = p.height + 1 := Polynomial.height_eq_height_add_one p Q
        _ = (Nat.card α : ℕ∞) + 1 := by rw [IH p]
        _ = (Nat.card (Option α) : ℕ∞) := by
          simp only [Nat.card_eq_fintype_card, Fintype.card_option,
            Nat.cast_add, Nat.cast_one]

/-! ## The fraction-field height bridge -/

/-- Let `P` be a prime of `A[Y]`, where `A` is itself a finite polynomial
ring over a field.  Suppose that `P` contracts to zero in `A`.  After
localizing `A` to its fraction field `K`, if the quotient by the extended
prime has transcendence degree zero over `K`, then `P` has height exactly the
number of `Y` variables.

This is the form of the affine dimension formula needed by the provenance
argument.  Its proof is short and structural:

* zero contraction makes `P` disjoint from all nonzero coefficients;
* localization therefore preserves its height;
* transcendence degree zero makes the localized quotient algebraic, hence
  the extended prime maximal;
* the preceding closed-point theorem computes its height.

No catenarity or global prime-height formula is used as an assumption.
-/
theorem iteratedPrime_height_eq_remainingCard_of_fraction_trdeg_zero
    {A τ : Type*} [CommRing A] [IsDomain A] [Finite τ]
    (P : Ideal (MvPolynomial τ A)) [P.IsPrime]
    (hcontract :
      P.comap (MvPolynomial.C :
        A →+* MvPolynomial τ A) = ⊥)
    (htrdeg :
      Algebra.trdeg (FractionRing A)
        (MvPolynomial τ (FractionRing A) ⧸
          P.map (MvPolynomial.map
            (algebraMap A (FractionRing A)))) = 0) :
    P.height = (Nat.card τ : ℕ∞) := by
  letI : Algebra
      (MvPolynomial τ A)
      (MvPolynomial τ (FractionRing A)) :=
    MvPolynomial.algebraMvPolynomial
  let M : Submonoid (MvPolynomial τ A) :=
    (nonZeroDivisors A).map
      (MvPolynomial.C :
        A →+* MvPolynomial τ A)
  let Q : Ideal (MvPolynomial τ (FractionRing A)) :=
    P.map (MvPolynomial.map
      (algebraMap A (FractionRing A)))
  have hdisj : Disjoint
      (M : Set (MvPolynomial τ A))
      (P : Set (MvPolynomial τ A)) := by
    rw [Set.disjoint_left]
    rintro x ⟨a, ha, rfl⟩ hxP
    have haP : a ∈ P.comap
        (MvPolynomial.C :
          A →+* MvPolynomial τ A) := hxP
    rw [hcontract] at haP
    have ha0 : a = 0 := Ideal.mem_bot.mp haP
    subst a
    exact zero_notMem_nonZeroDivisors ha
  letI : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M
      (MvPolynomial τ (FractionRing A)) P inferInstance hdisj
  letI : Algebra.IsAlgebraic
      (FractionRing A)
      (MvPolynomial τ (FractionRing A) ⧸ Q) :=
    trdeg_eq_zero_iff.mp htrdeg
  letI : Q.IsMaximal :=
    prime_isMaximal_of_quotient_isAlgebraic
      (K := FractionRing A) Q
  calc
    P.height = Q.height :=
      (IsLocalization.height_map_of_disjoint M P hdisj).symm
    _ = (Nat.card τ : ℕ∞) := maximalIdeal_height_eq_natCard Q

/-! ## The unconditional finite polynomial-prime dimension formula -/

/-- If a chosen set of quotient coordinates is a transcendence basis, then
the height of the prime is exactly the number of complementary coordinates.
The generic-fibre algebraicity required by the height bridge is proved above,
not supplied as a premise. -/
theorem prime_height_eq_complementCard_of_coordinateBasis
    {k ι : Type*} [Field k] [Finite ι]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] (S : Set ι)
    (hS : IsTranscendenceBasis k
      (fun i : S ↦ quotientCoordinate P i)) :
    P.height = (Nat.card (Sᶜ : Set ι) : ℕ∞) := by
  let E : MvPolynomial (Sᶜ : Set ι) (MvPolynomial S k) ≃ₐ[k]
      MvPolynomial ι k := coordinateSplitEquiv S
  let J : Ideal
      (MvPolynomial (Sᶜ : Set ι) (MvPolynomial S k)) :=
    coordinateSplitPrime P S
  letI : J.IsPrime := coordinateSplitPrime_isPrime P S
  have hJ : J.height = (Nat.card (Sᶜ : Set ι) : ℕ∞) :=
    iteratedPrime_height_eq_remainingCard_of_fraction_trdeg_zero J
      (coordinateSplitPrime_contraction_eq_bot P S hS.1)
      (coordinateSplitPrime_genericFibre_trdeg_eq_zero P S hS)
  have htransport : P.height = J.height := by
    calc
      P.height = (P.map E.symm.toRingEquiv).height :=
        (E.symm.toRingEquiv.height_map P).symm
      _ = J.height := by
        change (P.map E.symm.toRingEquiv).height =
          (P.comap E.toRingEquiv).height
        exact congrArg Ideal.height (Ideal.map_symm E.toRingEquiv)
  exact htransport.trans hJ

/-- The affine dimension formula for an arbitrary prime of a polynomial ring
in finitely many variables over a field.  The transcendence degree is taken
in the quotient function field; `Cardinal.toNat` is harmless here because a
coordinate transcendence basis is finite. -/
theorem polynomialPrime_height_add_fractionTrdeg_eq_natCard
    {k ι : Type*} [Field k] [Finite ι]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] :
    P.height +
        ((Algebra.trdeg k
          (FractionRing (MvPolynomial ι k ⧸ P))).toNat : ℕ∞) =
      (Nat.card ι : ℕ∞) := by
  classical
  obtain ⟨S, hS⟩ := exists_coordinateIndex_transcendenceBasis P
  let B := MvPolynomial ι k ⧸ P
  let L := FractionRing B
  letI : Algebra.IsAlgebraic B L :=
    IsLocalization.isAlgebraic L (nonZeroDivisors B)
  have hSL : IsTranscendenceBasis k
      ((algebraMap B L) ∘
        (fun i : S ↦ quotientCoordinate P i)) :=
    hS.algebraMap_comp
  have htrdegNat :
      (Algebra.trdeg k L).toNat = Nat.card S := by
    have hlift := hSL.lift_cardinalMk_eq_trdeg
    have hnat := congrArg Cardinal.toNat hlift
    simpa [Nat.card] using hnat.symm
  have hcardSum :
      Nat.card S + Nat.card (Sᶜ : Set ι) = Nat.card ι := by
    calc
      Nat.card S + Nat.card (Sᶜ : Set ι) =
          Nat.card (S ⊕ (Sᶜ : Set ι)) := by
        rw [Nat.card_sum]
      _ = Nat.card ι := Nat.card_congr (Equiv.Set.sumCompl S)
  rw [prime_height_eq_complementCard_of_coordinateBasis P S hS]
  change (Nat.card (Sᶜ : Set ι) : ℕ∞) +
      ((Algebra.trdeg k L).toNat : ℕ∞) = (Nat.card ι : ℕ∞)
  rw [htrdegNat, ← Nat.cast_add]
  exact_mod_cast (by simpa [add_comm] using hcardSum)

/-- Relative prime-height formula over an arbitrary noetherian coefficient
domain.  The only geometric input is that the canonical generic fibre has
transcendence degree zero. -/
theorem polynomialPrime_height_eq_contractionHeight_add_card_of_fibre_trdeg_zero
    {A τ : Type*} [CommRing A] [IsNoetherianRing A] [Finite τ]
    (P : Ideal (MvPolynomial τ A)) [P.IsPrime]
    (htrdeg :
      Algebra.trdeg
        (FractionRing (A ⧸ coefficientContraction P))
        (MvPolynomial τ
            (FractionRing (A ⧸ coefficientContraction P)) ⧸
          (polynomialFibreIdeal P).map
            (MvPolynomial.map
              (algebraMap
                (A ⧸ coefficientContraction P)
                (FractionRing (A ⧸ coefficientContraction P))))) = 0) :
    P.height =
      (coefficientContraction P).height + (Nat.card τ : ℕ∞) := by
  let p := coefficientContraction P
  letI : p.IsPrime := coefficientContraction_isPrime P
  let F := polynomialFibreIdeal P
  letI : F.IsPrime := polynomialFibreIdeal_isPrime P
  have hFheight : F.height = (Nat.card τ : ℕ∞) :=
    iteratedPrime_height_eq_remainingCard_of_fraction_trdeg_zero F
      (polynomialFibreIdeal_comap_C P) htrdeg
  let J : Ideal (MvPolynomial τ A) :=
    p.map (MvPolynomial.C : A →+* MvPolynomial τ A)
  let q : Ideal (MvPolynomial τ A ⧸ J) :=
    P.map (Ideal.Quotient.mk J)
  let E : MvPolynomial τ (A ⧸ p) ≃ₐ[A]
      (MvPolynomial τ A ⧸ J) :=
    MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) p
  letI : P.LiesOver p := ⟨rfl⟩
  have hsplit :=
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
  have htransport : q.height = F.height := by
    exact (E.symm.toRingEquiv.height_map q).symm
  calc
    P.height = p.height + q.height := by
      exact hsplit
    _ = p.height + F.height := by rw [htransport]
    _ = p.height + (Nat.card τ : ℕ∞) := by rw [hFheight]

/-! ## A coordinate-transcendence-basis form -/

/-- Regard the right variables as coefficient variables and the left
variables as the remaining polynomial variables. -/
def splitPrimeIdeal {k τ σ : Type*} [CommRing k]
    (P : Ideal (MvPolynomial (τ ⊕ σ) k)) :
    Ideal (MvPolynomial τ (MvPolynomial σ k)) :=
  P.map (MvPolynomial.sumAlgEquiv k τ σ).toRingEquiv

/-- A split transport of a prime is prime. -/
theorem splitPrimeIdeal_isPrime
    {k τ σ : Type*} [CommRing k]
    (P : Ideal (MvPolynomial (τ ⊕ σ) k)) [P.IsPrime] :
    (splitPrimeIdeal P).IsPrime := by
  unfold splitPrimeIdeal
  infer_instance

/-- Coordinate-basis height formula.  If the right-coordinate polynomial
ring injects into the quotient and the remaining generic fibre is algebraic,
then the height is the number of left coordinates. -/
theorem splitPrime_height_eq_leftCard_of_right_coordinate_basis
    {k τ σ : Type*} [Field k] [Finite τ] [Finite σ]
    (P : Ideal (MvPolynomial (τ ⊕ σ) k)) [P.IsPrime]
    (hcontract :
      coefficientContraction (splitPrimeIdeal P) = ⊥)
    (htrdeg :
      Algebra.trdeg (FractionRing (MvPolynomial σ k))
        (MvPolynomial τ (FractionRing (MvPolynomial σ k)) ⧸
          (splitPrimeIdeal P).map
            (MvPolynomial.map
              (algebraMap (MvPolynomial σ k)
                (FractionRing (MvPolynomial σ k))))) = 0) :
    P.height = (Nat.card τ : ℕ∞) := by
  let Q := splitPrimeIdeal P
  letI : Q.IsPrime := splitPrimeIdeal_isPrime P
  have hQ : Q.height = (Nat.card τ : ℕ∞) :=
    iteratedPrime_height_eq_remainingCard_of_fraction_trdeg_zero
      Q hcontract htrdeg
  calc
    P.height = Q.height :=
      ((MvPolynomial.sumAlgEquiv k τ σ).toRingEquiv.height_map P).symm
    _ = (Nat.card τ : ℕ∞) := hQ

/-- The same coordinate-basis theorem in the classical
`height + transcendence-degree = number of variables` shape, with the size
of the chosen right-coordinate basis standing for the transcendence degree.
-/
theorem splitPrime_height_add_rightCard_eq_totalCard
    {k τ σ : Type*} [Field k] [Finite τ] [Finite σ]
    (P : Ideal (MvPolynomial (τ ⊕ σ) k)) [P.IsPrime]
    (hcontract :
      coefficientContraction (splitPrimeIdeal P) = ⊥)
    (htrdeg :
      Algebra.trdeg (FractionRing (MvPolynomial σ k))
        (MvPolynomial τ (FractionRing (MvPolynomial σ k)) ⧸
          (splitPrimeIdeal P).map
            (MvPolynomial.map
              (algebraMap (MvPolynomial σ k)
                (FractionRing (MvPolynomial σ k))))) = 0) :
    P.height + (Nat.card σ : ℕ∞) =
      (Nat.card (τ ⊕ σ) : ℕ∞) := by
  rw [splitPrime_height_eq_leftCard_of_right_coordinate_basis
    P hcontract htrdeg]
  rw [Nat.card_sum, Nat.cast_add]

end

end PolynomialPrimeTrdegHeight

end RB31E2E


end
end BundleSource0018

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0018/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0018.json"

section BundleSource0019
/- Source: Papers/RigidityZheng_Incidence_PinTriangularElimination.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Incidence/PinTriangularElimination.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Triangular elimination of one active pin

Fix a nonzero angular coordinate `i` of a relative twist.  A stationary pin
then has one free coordinate, namely its `i`-th coordinate.  The other two
compatibility coordinates are triangular: after clearing the single angular
denominator they are exactly the two private-pin coordinate relations.

This file proves that statement first over an arbitrary commutative ring and
then in the provenance-retaining universal homogeneous chart.  In particular,
the two denominator-cleared private-coordinate relations generate exactly the
same ideal as the selected pair of compatibility coordinates.  No height or
codimension conclusion is made here.
-/

namespace RB31E2E

namespace PinTriangularElimination

noncomputable section

open MvPolynomial
open UniversalHomogeneousChart

/-! ## The two private coordinates in each angular chart -/

/-- The two pin coordinates other than the free chart coordinate `i`. -/
def privateCoordinate (i : Fin 3) (slot : Fin 2) : Fin 3 :=
  if i = 0 then
    if slot = 0 then 1 else 2
  else if i = 1 then
    if slot = 0 then 0 else 2
  else
    if slot = 0 then 0 else 1

/-- The compatibility coordinate which solves the corresponding private pin
coordinate.  The order is chosen to agree with `privateCoordinate`. -/
def solvingCompatibilityCoordinate (i : Fin 3) (slot : Fin 2) : Fin 3 :=
  if i = 0 then
    if slot = 0 then 2 else 1
  else if i = 1 then
    if slot = 0 then 2 else 0
  else
    if slot = 0 then 1 else 0

theorem privateCoordinate_ne (i : Fin 3) (slot : Fin 2) :
    privateCoordinate i slot ≠ i := by
  fin_cases i <;> fin_cases slot <;> decide

theorem privateCoordinate_injective (i : Fin 3) :
    Function.Injective (privateCoordinate i) := by
  intro a b hab
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [privateCoordinate] at hab ⊢

/-! ## Denominator-cleared chart relations over an arbitrary ring -/

/-- The numerator vector in the angular chart `i`.  Dividing it by `Z.1 i`
gives the stationary-pin formula; its `i`-th entry is deliberately
`Z.1 i * p i`, so that only the other two entries carry information. -/
def stationaryPinNumerator {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) : Vec3 R :=
  if i = 0 then
    ![Z.1 0 * p 0,
      Z.1 1 * p 0 - Z.2 2,
      Z.2 1 + Z.1 2 * p 0]
  else if i = 1 then
    ![Z.2 2 + Z.1 0 * p 1,
      Z.1 1 * p 1,
      Z.1 2 * p 1 - Z.2 0]
  else
    ![Z.1 0 * p 2 - Z.2 1,
      Z.2 0 + Z.1 1 * p 2,
      Z.1 2 * p 2]

/-- One denominator-cleared private-coordinate relation. -/
def triangularResidual {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2) : R :=
  Z.1 i * p (privateCoordinate i slot) -
    stationaryPinNumerator Z p i (privateCoordinate i slot)

/-- The selected compatibility equation, without the harmless orientation
sign appearing in the triangular identity. -/
def selectedCompatibilityEquation {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2) : R :=
  Twist.eval Z p (solvingCompatibilityCoordinate i slot)

/-- Orient the selected compatibility equation so that it is literally the
denominator-cleared private-coordinate residual. -/
def orientedCompatibilityEquation {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2) : R :=
  if i = 0 then
    if slot = 0 then Twist.eval Z p 2 else -Twist.eval Z p 1
  else if i = 1 then
    if slot = 0 then -Twist.eval Z p 2 else Twist.eval Z p 0
  else
    if slot = 0 then Twist.eval Z p 1 else -Twist.eval Z p 0

/-- The six cross-product calculations, packaged as one uniform triangular
identity. -/
theorem triangularResidual_eq_orientedCompatibilityEquation
    {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2) :
    triangularResidual Z p i slot =
      orientedCompatibilityEquation Z p i slot := by
  fin_cases i <;> fin_cases slot <;>
    simp [triangularResidual, stationaryPinNumerator, privateCoordinate,
      orientedCompatibilityEquation, Twist.eval, Vec3.cross] <;> ring

/-- Orientation changes only a sign; provenance and the selected
compatibility coordinate are unchanged. -/
theorem orientedCompatibilityEquation_eq_selected_or_neg
    {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2) :
    orientedCompatibilityEquation Z p i slot =
        selectedCompatibilityEquation Z p i slot ∨
      orientedCompatibilityEquation Z p i slot =
        -selectedCompatibilityEquation Z p i slot := by
  fin_cases i <;> fin_cases slot <;>
    simp [orientedCompatibilityEquation, selectedCompatibilityEquation,
      solvingCompatibilityCoordinate]

/-- The ideal of the two compatibility coordinates selected by chart `i`. -/
def compatibilityPairIdeal {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) : Ideal R :=
  Ideal.span (Set.range (selectedCompatibilityEquation Z p i))

/-- The ideal of the two denominator-cleared private-pin relations. -/
def triangularResidualIdeal {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) : Ideal R :=
  Ideal.span (Set.range (triangularResidual Z p i))

private theorem orientedCompatibilityEquation_mem_compatibilityPairIdeal
    {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2) :
    orientedCompatibilityEquation Z p i slot ∈
      compatibilityPairIdeal Z p i := by
  rcases orientedCompatibilityEquation_eq_selected_or_neg Z p i slot with h | h
  · rw [h]
    exact Ideal.subset_span ⟨slot, rfl⟩
  · rw [h]
    exact (compatibilityPairIdeal Z p i).neg_mem
      (Ideal.subset_span ⟨slot, rfl⟩)

private theorem selectedCompatibilityEquation_mem_orientedSpan
    {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2) :
    selectedCompatibilityEquation Z p i slot ∈
      Ideal.span (Set.range (orientedCompatibilityEquation Z p i)) := by
  rcases orientedCompatibilityEquation_eq_selected_or_neg Z p i slot with h | h
  · rw [← h]
    exact Ideal.subset_span ⟨slot, rfl⟩
  · have hm : -selectedCompatibilityEquation Z p i slot ∈
        Ideal.span (Set.range (orientedCompatibilityEquation Z p i)) := by
      rw [← h]
      exact Ideal.subset_span ⟨slot, rfl⟩
    simpa using
      (Ideal.span (Set.range (orientedCompatibilityEquation Z p i))).neg_mem hm

/-- The two compatibility equations and the two denominator-cleared
private-coordinate relations generate exactly the same ideal.  This is an
identity over the original ring; no localization or dimension theorem is
needed. -/
theorem triangularResidualIdeal_eq_compatibilityPairIdeal
    {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) :
    triangularResidualIdeal Z p i = compatibilityPairIdeal Z p i := by
  apply le_antisymm
  · rw [triangularResidualIdeal, Ideal.span_le]
    rintro _ ⟨slot, rfl⟩
    rw [triangularResidual_eq_orientedCompatibilityEquation]
    exact orientedCompatibilityEquation_mem_compatibilityPairIdeal
      Z p i slot
  · rw [compatibilityPairIdeal, Ideal.span_le]
    rintro _ ⟨slot, rfl⟩
    rw [triangularResidualIdeal]
    have h := selectedCompatibilityEquation_mem_orientedSpan Z p i slot
    have hfun : triangularResidual Z p i =
        orientedCompatibilityEquation Z p i := by
      funext s
      exact triangularResidual_eq_orientedCompatibilityEquation Z p i s
    rwa [hfun]

/-! ## The same elimination after inverting the angular coordinate -/

/-- The distinguished angular coordinate as a unit in any away
localization at that coordinate. -/
def localizedAngularUnit
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (Z : Twist R) (i : Fin 3) [IsLocalization.Away (Z.1 i) A] : Aˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := A) (Z.1 i)).unit

@[simp]
theorem localizedAngularUnit_coe
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (Z : Twist R) (i : Fin 3) [IsLocalization.Away (Z.1 i) A] :
    ((localizedAngularUnit (A := A) Z i : Aˣ) : A) =
      algebraMap R A (Z.1 i) := by
  exact (IsLocalization.Away.algebraMap_isUnit (S := A) (Z.1 i)).unit_spec

/-- The normalized relation `p_j - numerator_j / ω_i`, represented in an
arbitrary away localization by multiplying the cleared residual by the
inverse of the distinguished angular unit. -/
def normalizedPrivateRelation
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2)
    [IsLocalization.Away (Z.1 i) A] : A :=
  (((localizedAngularUnit (A := A) Z i)⁻¹ : Aˣ) : A) *
    algebraMap R A (triangularResidual Z p i slot)

/-- The normalized relation is literally a private pin coordinate minus its
rational chart expression. -/
theorem normalizedPrivateRelation_eq_coordinate_sub_fraction
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2)
    [IsLocalization.Away (Z.1 i) A] :
    normalizedPrivateRelation (A := A) Z p i slot =
      algebraMap R A (p (privateCoordinate i slot)) -
        (((localizedAngularUnit (A := A) Z i)⁻¹ : Aˣ) : A) *
          algebraMap R A
            (stationaryPinNumerator Z p i (privateCoordinate i slot)) := by
  rw [normalizedPrivateRelation, triangularResidual, map_sub, map_mul,
    ← localizedAngularUnit_coe (A := A) Z i]
  rw [mul_sub, ← mul_assoc, Units.inv_mul, one_mul]

/-- The selected compatibility pair after applying the away-localization
map. -/
def localizedCompatibilityPairIdeal
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) : Ideal A :=
  Ideal.span (Set.range (fun slot : Fin 2 ↦
    algebraMap R A (selectedCompatibilityEquation Z p i slot)))

/-- The two normalized private-coordinate relations in the away chart. -/
def normalizedPrivateRelationIdeal
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3)
    [IsLocalization.Away (Z.1 i) A] : Ideal A :=
  Ideal.span (Set.range (fun slot : Fin 2 ↦
    normalizedPrivateRelation (A := A) Z p i slot))

private theorem mapped_orientedCompatibility_mem_localizedPair
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2) :
    algebraMap R A (orientedCompatibilityEquation Z p i slot) ∈
      localizedCompatibilityPairIdeal (A := A) Z p i := by
  rcases orientedCompatibilityEquation_eq_selected_or_neg Z p i slot with h | h
  · rw [h]
    exact Ideal.subset_span ⟨slot, rfl⟩
  · rw [h, map_neg]
    exact (localizedCompatibilityPairIdeal (A := A) Z p i).neg_mem
      (Ideal.subset_span ⟨slot, rfl⟩)

/-- After inverting `Z.1 i`, the two compatibility coordinates generate
exactly the ideal of the two explicit rational private-coordinate
relations. -/
theorem localizedCompatibilityPairIdeal_eq_normalizedPrivateRelationIdeal
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3)
    [IsLocalization.Away (Z.1 i) A] :
    localizedCompatibilityPairIdeal (A := A) Z p i =
      normalizedPrivateRelationIdeal (A := A) Z p i := by
  apply le_antisymm
  · rw [localizedCompatibilityPairIdeal, Ideal.span_le]
    rintro _ ⟨slot, rfl⟩
    let J := normalizedPrivateRelationIdeal (A := A) Z p i
    have hn : normalizedPrivateRelation (A := A) Z p i slot ∈ J :=
      Ideal.subset_span ⟨slot, rfl⟩
    have hu := J.mul_mem_left
      ((localizedAngularUnit (A := A) Z i : Aˣ) : A) hn
    have hres : algebraMap R A (triangularResidual Z p i slot) ∈ J := by
      rw [normalizedPrivateRelation, ← mul_assoc, Units.mul_inv, one_mul] at hu
      exact hu
    have hor : algebraMap R A
        (orientedCompatibilityEquation Z p i slot) ∈ J := by
      rwa [triangularResidual_eq_orientedCompatibilityEquation] at hres
    change algebraMap R A (selectedCompatibilityEquation Z p i slot) ∈ J
    rcases orientedCompatibilityEquation_eq_selected_or_neg Z p i slot with h | h
    · simpa only [h] using hor
    · have hneg := J.neg_mem hor
      simpa only [h, map_neg, neg_neg] using hneg
  · rw [normalizedPrivateRelationIdeal, Ideal.span_le]
    rintro _ ⟨slot, rfl⟩
    change (((localizedAngularUnit (A := A) Z i)⁻¹ : Aˣ) : A) *
      algebraMap R A (triangularResidual Z p i slot) ∈
        localizedCompatibilityPairIdeal (A := A) Z p i
    apply (localizedCompatibilityPairIdeal (A := A) Z p i).mul_mem_left
    rw [triangularResidual_eq_orientedCompatibilityEquation]
    exact mapped_orientedCompatibility_mem_localizedPair Z p i slot

/-- Concrete `Localization.Away` form of the preceding theorem. -/
theorem awayCompatibilityPairIdeal_eq_normalizedPrivateRelationIdeal
    {R : Type*} [CommRing R] (Z : Twist R) (p : Vec3 R) (i : Fin 3) :
    localizedCompatibilityPairIdeal
        (A := Localization.Away (Z.1 i)) Z p i =
      normalizedPrivateRelationIdeal
        (A := Localization.Away (Z.1 i)) Z p i := by
  exact localizedCompatibilityPairIdeal_eq_normalizedPrivateRelationIdeal
    Z p i

/-! ## Specialization to the universal homogeneous chart -/

/-- The selected private-coordinate relation with both provenance layers
retained. -/
def universalTriangularResidual
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) (slot : Fin 2) : RelativeRing root E :=
  triangularResidual
    (universalRelativeTwist root src dst e)
    (universalParameterPin (root := root) e) i slot

/-- The sign-oriented pair written directly in terms of the named universal
compatibility coordinates. -/
def universalOrientedCompatibilityEquation
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) (slot : Fin 2) : RelativeRing root E :=
  if i = 0 then
    if slot = 0 then
      universalCompatibilityCoordinate root src dst e 2
    else -universalCompatibilityCoordinate root src dst e 1
  else if i = 1 then
    if slot = 0 then
      -universalCompatibilityCoordinate root src dst e 2
    else universalCompatibilityCoordinate root src dst e 0
  else
    if slot = 0 then
      universalCompatibilityCoordinate root src dst e 1
    else -universalCompatibilityCoordinate root src dst e 0

/-- Universal triangular identity with the named provenance polynomial on
the right-hand side. -/
theorem universalTriangularResidual_eq_orientedCompatibilityEquation
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) (slot : Fin 2) :
    universalTriangularResidual root src dst e i slot =
      universalOrientedCompatibilityEquation root src dst e i slot := by
  rw [universalTriangularResidual,
    triangularResidual_eq_orientedCompatibilityEquation]
  rfl

/-- Sign-free form of the universal triangular identity.  It exposes the
literal compatibility-coordinate provenance selected by the chart. -/
theorem universalTriangularResidual_eq_compatibility_or_neg
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) (slot : Fin 2) :
    universalTriangularResidual root src dst e i slot =
        universalCompatibilityCoordinate root src dst e
          (solvingCompatibilityCoordinate i slot) ∨
      universalTriangularResidual root src dst e i slot =
        -universalCompatibilityCoordinate root src dst e
          (solvingCompatibilityCoordinate i slot) := by
  rw [universalTriangularResidual,
    triangularResidual_eq_orientedCompatibilityEquation]
  exact orientedCompatibilityEquation_eq_selected_or_neg
    (universalRelativeTwist root src dst e)
    (universalParameterPin (root := root) e) i slot

/-- The two universal denominator-cleared private-coordinate relations. -/
def universalTriangularResidualIdeal
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) : Ideal (RelativeRing root E) :=
  triangularResidualIdeal
    (universalRelativeTwist root src dst e)
    (universalParameterPin (root := root) e) i

/-- The selected pair of universal compatibility coordinates. -/
def universalCompatibilityPairIdeal
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) : Ideal (RelativeRing root E) :=
  compatibilityPairIdeal
    (universalRelativeTwist root src dst e)
    (universalParameterPin (root := root) e) i

/-- Universal form of the exact two-generator ideal identity. -/
theorem universalTriangularResidualIdeal_eq_compatibilityPairIdeal
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) :
    universalTriangularResidualIdeal root src dst e i =
      universalCompatibilityPairIdeal root src dst e i := by
  exact triangularResidualIdeal_eq_compatibilityPairIdeal
    (universalRelativeTwist root src dst e)
    (universalParameterPin (root := root) e) i

/-- Every universal triangular residual has twist degree one. -/
theorem universalTriangularResidual_isHomogeneous_one
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) (slot : Fin 2) :
    (universalTriangularResidual root src dst e i slot).IsHomogeneous 1 := by
  rcases universalTriangularResidual_eq_compatibility_or_neg
      root src dst e i slot with h | h
  · rw [h]
    exact universalCompatibilityCoordinate_isHomogeneous_one
      root src dst e _
  · rw [h]
    exact (universalCompatibilityCoordinate_isHomogeneous_one
      root src dst e _).neg

/-- Incidence semantics: every active realization annihilates both
triangular private-coordinate relations. -/
theorem realChartEvaluation_universalTriangularResidual_eq_zero
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : SparseNullIncidence.IsIncidenceRealization src dst active p Y)
    (root : V) (e : active) (i : Fin 3) (slot : Fin 2) :
    realChartEvaluation root p Y
        (universalTriangularResidual root src dst e.1 i slot) = 0 := by
  rcases universalTriangularResidual_eq_compatibility_or_neg
      root src dst e.1 i slot with h | h
  · rw [h]
    exact UniversalHomogeneousChart.IsIncidenceRealization.realChartEvaluation_compatibility_eq_zero
      hY root e _
  · rw [h, map_neg,
      UniversalHomogeneousChart.IsIncidenceRealization.realChartEvaluation_compatibility_eq_zero
        hY root e _]
    exact neg_zero

end

end PinTriangularElimination

end RB31E2E


end
end BundleSource0019

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0019/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0019.json"

section BundleSource0020
/- Source: Papers/RigidityZheng_Incidence_ActivePinPrimeHeight.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Incidence/ActivePinPrimeHeight.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/






@[expose] public section

/-!
# Primewise height contributed by private pin coordinates

On an angular away chart, `PinTriangularElimination` rewrites the two
compatibility equations of one active pin as

`private coordinate - expression in the retained coordinates`.

The algebraic content of “this pin contributes two” is therefore the
translated-coordinate lemma proved here.  Over any domain, any injectively
labelled family of `n` private variables, translated by coefficient-ring
elements, generates a prime ideal of height at least `n`.  The proof is an
explicit polynomial translation automorphism followed by the coordinate
prime chain from `FilteredInitialHeight`; all dimension estimates used below are proved there.

The final section packages the `n = 2` active-pin fibre and an
occurrence-indexed family with two disjoint private variables per occurrence.
It also gives a ring-equivalence transport lemma for applying the result after
quotienting by a prior prime and isolating the private variables.  No claim is
made that an arbitrary ideal admits such a private-variable presentation.
-/

namespace RB31E2E

namespace ActivePinPrimeHeight

noncomputable section

open MvPolynomial
open NullCellulePolynomial

/-! ## Translation of polynomial coordinates -/

/-- Simultaneously translate every polynomial variable by a coefficient. -/
def coordinateTranslationHom {k σ : Type*} [CommRing k] (a : σ → k) :
    MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun x ↦ X x + C (a x))

@[simp]
theorem coordinateTranslationHom_X {k σ : Type*} [CommRing k]
    (a : σ → k) (x : σ) :
    coordinateTranslationHom a (X x) = X x + C (a x) := by
  simp [coordinateTranslationHom]

@[simp]
theorem coordinateTranslationHom_C {k σ : Type*} [CommRing k]
    (a : σ → k) (r : k) :
    coordinateTranslationHom a (C r) = C r := by
  simp [coordinateTranslationHom]

/-- Polynomial translation is an automorphism; translation by `-a` is its
inverse. -/
def coordinateTranslationEquiv {k σ : Type*} [CommRing k] (a : σ → k) :
    MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k := by
  apply AlgEquiv.ofAlgHom
    (coordinateTranslationHom a)
    (coordinateTranslationHom (fun x ↦ -a x))
  · apply MvPolynomial.algHom_ext
    intro x
    simp [coordinateTranslationHom]
  · apply MvPolynomial.algHom_ext
    intro x
    simp [coordinateTranslationHom]

@[simp]
theorem coordinateTranslationEquiv_X {k σ : Type*} [CommRing k]
    (a : σ → k) (x : σ) :
    coordinateTranslationEquiv a (X x) = X x + C (a x) := by
  simp [coordinateTranslationEquiv]

@[simp]
theorem coordinateTranslationEquiv_C {k σ : Type*} [CommRing k]
    (a : σ → k) (r : k) :
    coordinateTranslationEquiv a (C r) = C r := by
  simp [coordinateTranslationEquiv]

/-! ## A translated coordinate prime of the expected height -/

/-- The ideal generated by `n` translated, injectively labelled coordinate
variables. -/
def translatedCoordinateIdeal {k σ : Type*} [CommRing k] {n : ℕ}
    (c : Fin n → σ) (a : σ → k) : Ideal (MvPolynomial σ k) :=
  Ideal.span (Set.range (fun j ↦ X (c j) - C (a (c j))))

/-- Translation identifies the translated-coordinate ideal with the image
of the corresponding ordinary coordinate ideal. -/
theorem translatedCoordinateIdeal_eq_map_coordinateVariableIdeal
    {k σ : Type*} [CommRing k] {n : ℕ}
    (c : Fin n → σ) (a : σ → k) :
    translatedCoordinateIdeal c a =
      Ideal.map (coordinateTranslationEquiv (fun x ↦ -a x)).toRingEquiv
        (coordinateVariableIdeal (k := k) (Set.range c)) := by
  rw [translatedCoordinateIdeal, coordinateVariableIdeal, Ideal.map_span]
  congr 1
  ext q
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨X (c j), ⟨c j, ⟨j, rfl⟩, rfl⟩, ?_⟩
    simp [sub_eq_add_neg]
  · rintro ⟨q, ⟨x, ⟨j, rfl⟩, rfl⟩, rfl⟩
    exact ⟨j, by simp [sub_eq_add_neg]⟩

/-- A translated family of independent coordinates still generates a prime
ideal. -/
theorem translatedCoordinateIdeal_isPrime
    {k σ : Type*} [CommRing k] [IsDomain k] {n : ℕ}
    (c : Fin n → σ) (a : σ → k) :
    (translatedCoordinateIdeal c a).IsPrime := by
  rw [translatedCoordinateIdeal_eq_map_coordinateVariableIdeal]
  letI : (coordinateVariableIdeal (k := k) (Set.range c)).IsPrime :=
    coordinateVariableIdeal_isPrime (k := k) (Set.range c)
  exact Ideal.map_isPrime_of_equiv
    (coordinateTranslationEquiv (fun x ↦ -a x)).toRingEquiv

/-- An injectively labelled translated coordinate family contributes at
least one unit of height per private variable. -/
theorem translatedCoordinateIdeal_height_ge_card
    {k σ : Type*} [CommRing k] [IsDomain k] {n : ℕ}
    (c : Fin n → σ) (hc : Function.Injective c) (a : σ → k) :
    (n : ℕ∞) ≤ (translatedCoordinateIdeal c a).height := by
  rw [translatedCoordinateIdeal_eq_map_coordinateVariableIdeal,
    (coordinateTranslationEquiv (fun x ↦ -a x)).toRingEquiv.height_map]
  exact coordinateVariableIdeal_height_ge_card (k := k) c hc

/-! ## One active pin: two private coordinates -/

/-- The normal-form ideal of one active pin after quotienting the prior
constraints and retaining only its two private polynomial coordinates. -/
def activePinRelationIdeal {k : Type*} [CommRing k] (a : Fin 2 → k) :
    Ideal (MvPolynomial (Fin 2) k) :=
  translatedCoordinateIdeal (fun j : Fin 2 ↦ j) a

theorem activePinRelationIdeal_isPrime
    {k : Type*} [CommRing k] [IsDomain k] (a : Fin 2 → k) :
    (activePinRelationIdeal a).IsPrime := by
  exact translatedCoordinateIdeal_isPrime (fun j : Fin 2 ↦ j) a

/-- The precise primewise fibre statement: after the previous prime has been
quotiented out, the two private relations of one active pin have height at
least two. -/
theorem activePinRelationIdeal_height_ge_two
    {k : Type*} [CommRing k] [IsDomain k] (a : Fin 2 → k) :
    (2 : ℕ∞) ≤ (activePinRelationIdeal a).height := by
  exact translatedCoordinateIdeal_height_ge_card
    (fun j : Fin 2 ↦ j) Function.injective_id a

/-! ## Adding the active pair above a prior prime -/

/-- Change only the coefficient ring by quotienting a prior prime. -/
def quotientCoefficientMap {R σ : Type*} [CommRing R] (P : Ideal R) :
    MvPolynomial σ R →+* MvPolynomial σ (R ⧸ P) :=
  MvPolynomial.map (Ideal.Quotient.mk P)

theorem quotientCoefficientMap_surjective
    {R σ : Type*} [CommRing R] (P : Ideal R) :
    Function.Surjective (quotientCoefficientMap (P := P) ( σ := σ)) := by
  exact MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective

theorem quotientCoefficientMap_ker
    {R σ : Type*} [CommRing R] (P : Ideal R) :
    RingHom.ker (quotientCoefficientMap (P := P) (σ := σ)) =
      Ideal.map (C : R →+* MvPolynomial σ R) P := by
  rw [quotientCoefficientMap, MvPolynomial.ker_map, Ideal.mk_ker]

/-- Extend a coefficient prime and then kill a selected set of polynomial
coordinates. -/
def basePrimeCoordinateIdeal {R σ : Type*} [CommRing R]
    (P : Ideal R) (S : Set σ) : Ideal (MvPolynomial σ R) :=
  Ideal.map (C : R →+* MvPolynomial σ R) P ⊔
    coordinateVariableIdeal (k := R) S

theorem quotientCoefficientMap_map_coordinateVariableIdeal
    {R σ : Type*} [CommRing R] (P : Ideal R) (S : Set σ) :
    Ideal.map (quotientCoefficientMap (P := P) (σ := σ))
        (coordinateVariableIdeal (k := R) S) =
      coordinateVariableIdeal (k := R ⧸ P) S := by
  rw [coordinateVariableIdeal, coordinateVariableIdeal, Ideal.map_span]
  congr 1
  ext q
  simp [quotientCoefficientMap]

/-- The extended-prime-plus-coordinates ideal is the inverse image of the
coordinate ideal over the quotient domain. -/
theorem basePrimeCoordinateIdeal_eq_comap
    {R σ : Type*} [CommRing R] (P : Ideal R) (S : Set σ) :
    basePrimeCoordinateIdeal P S =
      Ideal.comap (quotientCoefficientMap (P := P) (σ := σ))
        (coordinateVariableIdeal (k := R ⧸ P) S) := by
  rw [← quotientCoefficientMap_map_coordinateVariableIdeal P S,
    Ideal.comap_map_of_surjective _
      (quotientCoefficientMap_surjective (P := P) (σ := σ)),
    ← RingHom.ker_eq_comap_bot, quotientCoefficientMap_ker,
    basePrimeCoordinateIdeal, sup_comm]

/-- Every such lifted coordinate ideal is prime when the coefficient ideal
is prime. -/
theorem basePrimeCoordinateIdeal_isPrime
    {R σ : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] (S : Set σ) :
    (basePrimeCoordinateIdeal P S).IsPrime := by
  rw [basePrimeCoordinateIdeal_eq_comap]
  letI : (coordinateVariableIdeal (k := R ⧸ P) S).IsPrime :=
    coordinateVariableIdeal_isPrime (k := R ⧸ P) S
  exact Ideal.comap_isPrime _ _

/-- Distinct coordinate prefixes remain strictly distinct after lifting
above a coefficient prime. -/
theorem basePrimeCoordinatePrefix_lt
    {R σ : Type*} [CommRing R] (P : Ideal R) [P.IsPrime]
    {n : ℕ} (c : Fin n → σ) (hc : Function.Injective c)
    {j l : Fin (n + 1)} (hjl : j < l) :
    basePrimeCoordinateIdeal P (coordinatePrefixSet c j) <
      basePrimeCoordinateIdeal P (coordinatePrefixSet c l) := by
  rw [basePrimeCoordinateIdeal_eq_comap,
    basePrimeCoordinateIdeal_eq_comap]
  have htarget := coordinatePrefixIdeal_lt
    (k := R ⧸ P) c hc hjl
  have hsurj := quotientCoefficientMap_surjective (P := P) (σ := σ)
  refine lt_of_le_of_ne (Ideal.comap_mono htarget.le) ?_
  intro heq
  exact htarget.ne
    ((Ideal.comap_injective_of_surjective _ hsurj) heq)

/-- Extension by constants contracts back to the original coefficient
ideal. -/
theorem comap_map_C_eq_self
    {R σ : Type*} [CommRing R] (P : Ideal R) :
    Ideal.comap (C : R →+* MvPolynomial σ R)
      (Ideal.map C P) = P := by
  classical
  ext r
  simp only [Ideal.mem_comap, MvPolynomial.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro hr m
    rw [coeff_C]
    split_ifs
    · exact hr
    · exact P.zero_mem

/-- Over a Noetherian coefficient ring, extending a prime to a finite
polynomial ring preserves its height. -/
theorem height_map_C_eq
    {R σ : Type*} [CommRing R] [IsNoetherianRing R] [Finite σ]
    (P : Ideal R) [P.IsPrime] :
    (Ideal.map (C : R →+* MvPolynomial σ R) P).height = P.height := by
  let Pext : Ideal (MvPolynomial σ R) := Ideal.map C P
  letI : Pext.IsPrime := by
    simpa [Pext, basePrimeCoordinateIdeal, coordinateVariableIdeal] using
      (basePrimeCoordinateIdeal_isPrime ( σ := σ) P (∅ : Set σ))
  letI : Pext.LiesOver P := ⟨by
    change P = Ideal.comap (C : R →+* MvPolynomial σ R) Pext
    exact (comap_map_C_eq_self ( σ := σ) P).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown P Pext
  have hmap : Ideal.map
      (Ideal.Quotient.mk
        (Ideal.map (algebraMap R (MvPolynomial σ R)) P)) Pext = ⊥ := by
    change Ideal.map
      (Ideal.Quotient.mk
        (Ideal.map (C : R →+* MvPolynomial σ R) P))
      (Ideal.map C P) = ⊥
    exact Ideal.map_quotient_self _
  letI : (Ideal.map
      (algebraMap R (MvPolynomial σ R)) P).IsPrime := by
    simpa [Pext] using (inferInstance : Pext.IsPrime)
  rw [hmap, Ideal.height_bot, add_zero] at h
  exact h

/-- Before translation, adjoining both private coordinates above a prior
prime raises height by at least two. -/
theorem basePrimeCoordinateIdeal_height_ge_add_two
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (P : Ideal R) [P.IsPrime] :
    P.height + 2 ≤
      (basePrimeCoordinateIdeal P (Set.univ : Set (Fin 2))).height := by
  let c : Fin 2 → Fin 2 := fun j ↦ j
  let I : Fin 3 → Ideal (MvPolynomial (Fin 2) R) := fun j ↦
    basePrimeCoordinateIdeal P (coordinatePrefixSet c j)
  have h01 : I 0 < I 1 := by
    exact basePrimeCoordinatePrefix_lt P c Function.injective_id (by decide)
  have h12 : I 1 < I 2 := by
    exact basePrimeCoordinatePrefix_lt P c Function.injective_id (by decide)
  letI : (I 0).IsPrime :=
    basePrimeCoordinateIdeal_isPrime P (coordinatePrefixSet c 0)
  letI : (I 1).IsPrime :=
    basePrimeCoordinateIdeal_isPrime P (coordinatePrefixSet c 1)
  letI : (I 2).IsPrime :=
    basePrimeCoordinateIdeal_isPrime P (coordinatePrefixSet c 2)
  have hfirst := Ideal.height_add_one_le_of_lt_of_isPrime h01
  have hsecond := Ideal.height_add_one_le_of_lt_of_isPrime h12
  have hchain : (I 0).height + 2 ≤ (I 2).height := by
    calc
      (I 0).height + 2 =
          ((I 0).height + 1) + 1 := by norm_num [add_assoc]
      _ ≤ (I 1).height + 1 := by
        simpa [add_assoc, add_comm, add_left_comm] using
          (add_le_add_right hfirst 1)
      _ ≤ (I 2).height := hsecond
  have hzero : I 0 = Ideal.map
      (C : R →+* MvPolynomial (Fin 2) R) P := by
    simp [I, c, coordinatePrefixSet, basePrimeCoordinateIdeal,
      coordinateVariableIdeal]
  have hlast : I 2 =
      basePrimeCoordinateIdeal P (Set.univ : Set (Fin 2)) := by
    change basePrimeCoordinateIdeal P
        (coordinatePrefixSet c (Fin.last 2)) = _
    rw [coordinatePrefixSet_last]
    simp [c]
  rw [hzero, hlast, height_map_C_eq ( σ := Fin 2) P] at hchain
  exact hchain

/-- Add a translated pair of active-pin relations above a prior coefficient
prime. -/
def primeWithActivePinIdeal {R : Type*} [CommRing R]
    (P : Ideal R) (a : Fin 2 → R) : Ideal (MvPolynomial (Fin 2) R) :=
  Ideal.map (C : R →+* MvPolynomial (Fin 2) R) P ⊔
    activePinRelationIdeal a

private theorem translation_map_map_C
    {R σ : Type*} [CommRing R] (P : Ideal R) (a : σ → R) :
    Ideal.map (coordinateTranslationEquiv a).toRingEquiv
        (Ideal.map (C : R →+* MvPolynomial σ R) P) =
      Ideal.map C P := by
  rw [show Ideal.map (coordinateTranslationEquiv a).toRingEquiv
        (Ideal.map (C : R →+* MvPolynomial σ R) P) =
      Ideal.map
        ((coordinateTranslationEquiv a).toRingEquiv.toRingHom.comp C) P by
        exact Ideal.map_map C
          (coordinateTranslationEquiv a).toRingEquiv.toRingHom]
  congr 1
  ext r
  simp

theorem primeWithActivePinIdeal_eq_map_basePrimeCoordinateIdeal
    {R : Type*} [CommRing R] (P : Ideal R) (a : Fin 2 → R) :
    primeWithActivePinIdeal P a =
      Ideal.map
        (coordinateTranslationEquiv (fun x ↦ -a x)).toRingEquiv
        (basePrimeCoordinateIdeal P (Set.univ : Set (Fin 2))) := by
  rw [primeWithActivePinIdeal, basePrimeCoordinateIdeal, Ideal.map_sup,
    translation_map_map_C]
  change _ ⊔ activePinRelationIdeal a = _ ⊔ _
  rw [activePinRelationIdeal,
    translatedCoordinateIdeal_eq_map_coordinateVariableIdeal]
  simp

theorem primeWithActivePinIdeal_isPrime
    {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime]
    (a : Fin 2 → R) :
    (primeWithActivePinIdeal P a).IsPrime := by
  rw [primeWithActivePinIdeal_eq_map_basePrimeCoordinateIdeal]
  letI : (basePrimeCoordinateIdeal P
      (Set.univ : Set (Fin 2))).IsPrime :=
    basePrimeCoordinateIdeal_isPrime P Set.univ
  exact Ideal.map_isPrime_of_equiv
    (coordinateTranslationEquiv (fun x ↦ -a x)).toRingEquiv

/-- Main increment theorem in private-coordinate normal form: adding one
active occurrence raises the height above the prior coefficient prime by at
least two. -/
theorem primeWithActivePinIdeal_height_ge_add_two
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (P : Ideal R) [P.IsPrime] (a : Fin 2 → R) :
    P.height + 2 ≤ (primeWithActivePinIdeal P a).height := by
  rw [primeWithActivePinIdeal_eq_map_basePrimeCoordinateIdeal,
    (coordinateTranslationEquiv (fun x ↦ -a x)).toRingEquiv.height_map]
  exact basePrimeCoordinateIdeal_height_ge_add_two P

/-- Quotient specialization: a prior prime ideal supplies a domain of
coefficients, and the active pin contributes height two over that quotient. -/
theorem quotient_activePinRelationIdeal_height_ge_two
    {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime]
    (a : Fin 2 → R ⧸ P) :
    (2 : ℕ∞) ≤ (activePinRelationIdeal a).height := by
  exact activePinRelationIdeal_height_ge_two a

/-- The same quotient fibre is prime, so the two-step coordinate chain can
be continued primewise. -/
theorem quotient_activePinRelationIdeal_isPrime
    {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime]
    (a : Fin 2 → R ⧸ P) :
    (activePinRelationIdeal a).IsPrime := by
  exact activePinRelationIdeal_isPrime a

/-! ## Two private variables for every occurrence -/

/-- Flatten an occurrence and one of its two private slots into the finite
index used by the coordinate-height theorem. -/
def occurrencePrivateVariable {m : ℕ} {σ : Type*}
    (pinVar : Fin m → Fin 2 → σ) : Fin (m * 2) → σ :=
  fun q ↦
    pinVar (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

/-- All translated private-coordinate relations for `m` occurrences. -/
def occurrencePrivateRelationIdeal
    {k σ : Type*} [CommRing k] {m : ℕ}
    (pinVar : Fin m → Fin 2 → σ) (a : σ → k) :
    Ideal (MvPolynomial σ k) :=
  translatedCoordinateIdeal (occurrencePrivateVariable pinVar) a

theorem occurrencePrivateVariable_injective
    {m : ℕ} {σ : Type*} (pinVar : Fin m → Fin 2 → σ)
    (hpin : Function.Injective
      (fun q : Fin m × Fin 2 ↦ pinVar q.1 q.2)) :
    Function.Injective (occurrencePrivateVariable pinVar) := by
  intro q r hqr
  apply finProdFinEquiv.symm.injective
  exact hpin hqr

/-- Disjoint provenance variables give exactly two certified height units
per occurrence. -/
theorem occurrencePrivateRelationIdeal_height_ge_twice_card
    {k σ : Type*} [CommRing k] [IsDomain k] {m : ℕ}
    (pinVar : Fin m → Fin 2 → σ)
    (hpin : Function.Injective
      (fun q : Fin m × Fin 2 ↦ pinVar q.1 q.2))
    (a : σ → k) :
    (m * 2 : ℕ) ≤ (occurrencePrivateRelationIdeal pinVar a).height := by
  exact translatedCoordinateIdeal_height_ge_card
    (occurrencePrivateVariable pinVar)
    (occurrencePrivateVariable_injective pinVar hpin) a

theorem occurrencePrivateRelationIdeal_isPrime
    {k σ : Type*} [CommRing k] [IsDomain k] {m : ℕ}
    (pinVar : Fin m → Fin 2 → σ) (a : σ → k) :
    (occurrencePrivateRelationIdeal pinVar a).IsPrime := by
  exact translatedCoordinateIdeal_isPrime
    (occurrencePrivateVariable pinVar) a

/-! ## Transport from an explicit private-coordinate presentation -/

/-- Height transport for a concrete chart presentation.  The hypothesis is
an equality of explicit ideals under a supplied ring equivalence, not a new
properness or dimension principle. -/
theorem height_ge_two_of_equiv_to_activePinRelationIdeal
    {A k : Type*} [CommRing A] [CommRing k] [IsDomain k]
    (e : A ≃+* MvPolynomial (Fin 2) k) (J : Ideal A) (a : Fin 2 → k)
    (hJ : Ideal.map e J = activePinRelationIdeal a) :
    (2 : ℕ∞) ≤ J.height := by
  rw [← e.height_map J, hJ]
  exact activePinRelationIdeal_height_ge_two a

/-- Relative-height transport: an explicit private-coordinate presentation
of a prior prime together with one active-pin pair inherits the proved
height increment two. -/
theorem height_ge_add_two_of_equiv_to_primeWithActivePinIdeal
    {A R : Type*} [CommRing A] [CommRing R] [IsNoetherianRing R]
    (e : A ≃+* MvPolynomial (Fin 2) R) (J : Ideal A)
    (P : Ideal R) [P.IsPrime] (a : Fin 2 → R)
    (hJ : Ideal.map e J = primeWithActivePinIdeal P a) :
    P.height + 2 ≤ J.height := by
  rw [← e.height_map J, hJ]
  exact primeWithActivePinIdeal_height_ge_add_two P a

/-- Away-chart form specialized to the normalized two-relation ideal from
`PinTriangularElimination`.  Supplying the explicit coefficient/private-
variable ring equivalence closes the height-two step. -/
theorem normalizedPrivateRelationIdeal_height_ge_two_of_equiv
    {R A k : Type*} [CommRing R] [CommRing A] [CommRing k]
    [Algebra R A] [IsDomain k]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3)
    [IsLocalization.Away (Z.1 i) A]
    (e : A ≃+* MvPolynomial (Fin 2) k) (a : Fin 2 → k)
    (hmap : Ideal.map e
      (PinTriangularElimination.normalizedPrivateRelationIdeal
        (A := A) Z p i) = activePinRelationIdeal a) :
    (2 : ℕ∞) ≤
      (PinTriangularElimination.normalizedPrivateRelationIdeal
        (A := A) Z p i).height := by
  exact height_ge_two_of_equiv_to_activePinRelationIdeal e _ a hmap

/-- Null-ideal sum form used by the incidence induction.  Once a concrete
away chart presents `prior ⊔ normalizedPrivateRelationIdeal` as a polynomial
ring in the two private pin coordinates over the quotient of a prior prime,
the height increases by two. -/
theorem prior_sup_normalizedPrivateRelationIdeal_height_ge_add_two_of_equiv
    {R A k : Type*} [CommRing R] [CommRing A] [CommRing k]
    [Algebra R A] [IsNoetherianRing k]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3)
    [IsLocalization.Away (Z.1 i) A]
    (prior : Ideal A) (P : Ideal k) [P.IsPrime]
    (e : A ≃+* MvPolynomial (Fin 2) k) (a : Fin 2 → k)
    (hmap : Ideal.map e
      (prior ⊔
        PinTriangularElimination.normalizedPrivateRelationIdeal
          (A := A) Z p i) = primeWithActivePinIdeal P a) :
    P.height + 2 ≤
      (prior ⊔
        PinTriangularElimination.normalizedPrivateRelationIdeal
          (A := A) Z p i).height := by
  exact height_ge_add_two_of_equiv_to_primeWithActivePinIdeal
    e _ P a hmap

end

end ActivePinPrimeHeight

end RB31E2E


end
end BundleSource0020

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0020/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0020.json"

section BundleSource0021
/- Source: Papers/RigidityZheng_Algebra_MinimalPrimeLinearFibre.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/MinimalPrimeLinearFibre.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/





@[expose] public section

/-!
# Minimal primes in a coefficient generic fibre

Given a minimal prime `P` above an ideal in `A[Y]`, contract `P` to the
coefficient ring, quotient by that contraction, and then pass to its fraction
field.  This file proves that the resulting prime remains minimal above the
image of the original ideal.  Consequently, if the generic-fibre equations
are visibly a linear-form prime lying below the image of `P`, minimality
identifies the two ideals.

The quotient and localization steps are both explicit; no generic-fibre
minimality or equidimensionality statement is assumed.
-/

namespace RB31E2E

namespace MinimalPrimeLinearFibre

noncomputable section

open MvPolynomial
open PolynomialPrimeTrdegHeight
open ActivePinPrimeHeight

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The coefficient-quotient map on a polynomial ring. -/
abbrev coefficientQuotientMap
    {A τ : Type*} [CommRing A] (p : Ideal A) :
    MvPolynomial τ A →+* MvPolynomial τ (A ⧸ p) :=
  quotientCoefficientMap (P := p) ( σ := τ)

/-- The image of a prime under coefficient quotient has zero coefficient
contraction when the quotient ideal is exactly its coefficient contraction. -/
theorem coefficientQuotient_prime_comap_C_eq_bot
    {A τ : Type*} [CommRing A]
    (P : Ideal (MvPolynomial τ A)) [P.IsPrime] :
    let p := coefficientContraction P
    let q := coefficientQuotientMap ( τ := τ) p
    (Ideal.map q P).comap
      (C : (A ⧸ p) →+* MvPolynomial τ (A ⧸ p)) = ⊥ := by
  classical
  dsimp only
  let p := coefficientContraction P
  let q := coefficientQuotientMap ( τ := τ) p
  have hqSurj : Function.Surjective q :=
    quotientCoefficientMap_surjective (P := p) ( σ := τ)
  have hker : RingHom.ker q ≤ P := by
    rw [quotientCoefficientMap_ker]
    exact Ideal.map_comap_le
  apply le_antisymm
  · intro b hb
    rw [Ideal.mem_bot]
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hb' : C (Ideal.Quotient.mk p a) ∈ Ideal.map q P := hb
    rw [Ideal.mem_map_iff_of_surjective q hqSurj] at hb'
    obtain ⟨z, hzP, hz⟩ := hb'
    have hdiff : z - C a ∈ RingHom.ker q := by
      rw [RingHom.mem_ker, map_sub, hz]
      simp [q, quotientCoefficientMap]
    have hCa : C a ∈ P := by
      have hzsub : z - (z - C a) ∈ P := P.sub_mem hzP (hker hdiff)
      simpa only [sub_sub_cancel] using hzsub
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hCa
  · exact bot_le

/-- A minimal prime remains minimal after quotienting by its own coefficient
contraction. -/
theorem coefficientQuotient_map_mem_minimalPrimes
    {A τ : Type*} [CommRing A]
    (I P : Ideal (MvPolynomial τ A))
    (hP : P ∈ I.minimalPrimes) :
    let p := coefficientContraction P
    let q := coefficientQuotientMap ( τ := τ) p
    Ideal.map q P ∈ (Ideal.map q I).minimalPrimes := by
  classical
  dsimp only
  let p := coefficientContraction P
  let q := coefficientQuotientMap ( τ := τ) p
  have hqSurj : Function.Surjective q :=
    quotientCoefficientMap_surjective (P := p) ( σ := τ)
  have hkerP : RingHom.ker q ≤ P := by
    rw [quotientCoefficientMap_ker]
    exact Ideal.map_comap_le
  have hPjoin : P ∈ (I ⊔ RingHom.ker q).minimalPrimes := by
    refine ⟨⟨hP.1.1, sup_le hP.1.2 hkerP⟩, ?_⟩
    intro Q hQ hQP
    exact hP.2 ⟨hQ.1, le_sup_left.trans hQ.2⟩ hQP
  rw [Ideal.minimalPrimes_map_of_surjective hqSurj I]
  exact ⟨P, hPjoin, rfl⟩

/-- After quotienting the coefficient contraction and localizing the
coefficient domain to its fraction field, the image of `P` is still a
minimal prime above the image of `I`. -/
theorem fractionFibre_map_mem_minimalPrimes
    {A τ : Type*} [CommRing A]
    (I P : Ideal (MvPolynomial τ A))
    (hP : P ∈ I.minimalPrimes) :
    let p := coefficientContraction P
    let B := A ⧸ p
    let K := FractionRing B
    let q := coefficientQuotientMap ( τ := τ) p
    let ℓ := MvPolynomial.map (algebraMap B K)
    Ideal.map ℓ (Ideal.map q P) ∈
      (Ideal.map ℓ (Ideal.map q I)).minimalPrimes := by
  classical
  dsimp only
  let p := coefficientContraction P
  let B := A ⧸ p
  let K := FractionRing B
  let R := MvPolynomial τ B
  let RK := MvPolynomial τ K
  let q := coefficientQuotientMap ( τ := τ) p
  let ℓ : R →+* RK := MvPolynomial.map (algebraMap B K)
  letI : P.IsPrime := hP.1.1
  letI : p.IsPrime := coefficientContraction_isPrime P
  let M : Submonoid R :=
    (nonZeroDivisors B).map (C : B →+* R)
  have hPq := coefficientQuotient_map_mem_minimalPrimes I P hP
  let Pq : Ideal R := Ideal.map q P
  let Iq : Ideal R := Ideal.map q I
  have hPqPrime : Pq.IsPrime := hPq.1.1
  letI : Pq.IsPrime := hPqPrime
  have hcontract : Pq.comap (C : B →+* R) = ⊥ := by
    exact coefficientQuotient_prime_comap_C_eq_bot P
  have hdisj : Disjoint (M : Set R) (Pq : Set R) := by
    rw [Set.disjoint_left]
    rintro x ⟨b, hb, rfl⟩ hx
    have hbP : b ∈ Pq.comap (C : B →+* R) := hx
    rw [hcontract] at hbP
    have hb0 : b = 0 := Ideal.mem_bot.mp hbP
    subst b
    exact zero_notMem_nonZeroDivisors hb
  have hPLPrime : (Ideal.map ℓ Pq).IsPrime := by
    change (Ideal.map (algebraMap R RK) Pq).IsPrime
    exact IsLocalization.isPrime_of_isPrime_disjoint M RK Pq
      (inferInstance : Pq.IsPrime) hdisj
  letI : (Ideal.map ℓ Pq).IsPrime := hPLPrime
  change Ideal.map (algebraMap R RK) Pq ∈
    (Ideal.map (algebraMap R RK) Iq).minimalPrimes
  rw [IsLocalization.minimalPrimes_map M RK Iq]
  change Ideal.comap (algebraMap R RK) (Ideal.map ℓ Pq) ∈
    Iq.minimalPrimes
  have hcomap :
      Ideal.comap (algebraMap R RK) (Ideal.map ℓ Pq) = Pq := by
    change Ideal.comap (algebraMap R RK)
      (Ideal.map (algebraMap R RK) Pq) = Pq
    exact IsLocalization.comap_map_of_isPrime_disjoint M RK
      (inferInstance : Pq.IsPrime) hdisj
  rw [hcomap]
  exact hPq

/-- Minimality identifies any prime linear-form ideal sandwiched between the
generic-fibre equations and the surviving generic-fibre component. -/
theorem linearFormIdeal_eq_fractionFibrePrime
    {A τ J : Type*} [CommRing A]
    [Fintype τ] [DecidableEq τ]
    (I P : Ideal (MvPolynomial τ A))
    [P.IsPrime]
    [(coefficientContraction P).IsPrime]
    (hP : P ∈ I.minimalPrimes)
    (row : J → τ → FractionRing (A ⧸ coefficientContraction P))
    (hI :
      Ideal.map
          (MvPolynomial.map
            (algebraMap (A ⧸ coefficientContraction P)
              (FractionRing (A ⧸ coefficientContraction P))))
          (Ideal.map
            (coefficientQuotientMap ( τ := τ) (coefficientContraction P)) I) ≤
        LinearFormIdeal.linearFormIdeal row)
    (hPupper :
      LinearFormIdeal.linearFormIdeal row ≤
        Ideal.map
          (MvPolynomial.map
            (algebraMap (A ⧸ coefficientContraction P)
              (FractionRing (A ⧸ coefficientContraction P))))
          (Ideal.map
            (coefficientQuotientMap ( τ := τ) (coefficientContraction P)) P)) :
    LinearFormIdeal.linearFormIdeal row =
      Ideal.map
        (MvPolynomial.map
          (algebraMap (A ⧸ coefficientContraction P)
            (FractionRing (A ⧸ coefficientContraction P))))
        (Ideal.map
          (coefficientQuotientMap ( τ := τ) (coefficientContraction P)) P) := by
  let Q := LinearFormIdeal.linearFormIdeal row
  let PL := Ideal.map
    (MvPolynomial.map
      (algebraMap (A ⧸ coefficientContraction P)
        (FractionRing (A ⧸ coefficientContraction P))))
    (Ideal.map
      (coefficientQuotientMap ( τ := τ) (coefficientContraction P)) P)
  have hmin := fractionFibre_map_mem_minimalPrimes I P hP
  have hQPrime : Q.IsPrime := LinearFormIdeal.linearFormIdeal_isPrime row
  exact le_antisymm hPupper (hmin.2 ⟨hQPrime, hI⟩ hPupper)

end

end MinimalPrimeLinearFibre

end RB31E2E


end
end BundleSource0021

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0021/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0021.json"

section BundleSource0022
/- Source: Papers/RigidityZheng_Algebra_MinimalPrimeLinearFibreHeight.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/MinimalPrimeLinearFibreHeight.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Relative height through the coefficient generic fibre

For a prime in `A[Y]`, height splits into the height of its coefficient
contraction and the height of its prime generic fibre.  This is proved by
the canonical coefficient quotient and localization; no dimension formula
is assumed.
-/

namespace RB31E2E

namespace MinimalPrimeLinearFibre

noncomputable section

open MvPolynomial
open PolynomialPrimeTrdegHeight

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The direct coefficient-quotient image used in this namespace is the
canonical polynomial fibre ideal. -/
theorem coefficientQuotient_map_eq_polynomialFibreIdeal
    {A τ : Type*} [CommRing A]
    (P : Ideal (MvPolynomial τ A)) :
    Ideal.map
        (coefficientQuotientMap (τ := τ) (coefficientContraction P)) P =
      polynomialFibreIdeal P := by
  classical
  let p := coefficientContraction P
  let J : Ideal (MvPolynomial τ A) :=
    p.map (C : A →+* MvPolynomial τ A)
  let E : MvPolynomial τ (A ⧸ p) ≃ₐ[A]
      (MvPolynomial τ A ⧸ J) :=
    MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) p
  have hhom :
      E.symm.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk J) =
        coefficientQuotientMap (τ := τ) p := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [E, J, coefficientQuotientMap,
        ActivePinPrimeHeight.quotientCoefficientMap,
        MvPolynomial.quotientEquivQuotientMvPolynomial]
    · intro i
      simp [E, J, coefficientQuotientMap,
        ActivePinPrimeHeight.quotientCoefficientMap,
        MvPolynomial.quotientEquivQuotientMvPolynomial]
  change Ideal.map (coefficientQuotientMap (τ := τ) p) P =
    Ideal.map E.symm.toRingEquiv
      (Ideal.map (Ideal.Quotient.mk J) P)
  calc
    Ideal.map (coefficientQuotientMap (τ := τ) p) P =
        Ideal.map
          (E.symm.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk J)) P :=
      congrArg (fun f ↦ Ideal.map f P) hhom.symm
    _ = Ideal.map E.symm.toRingEquiv
        (Ideal.map (Ideal.Quotient.mk J) P) := by
      exact (Ideal.map_map (Ideal.Quotient.mk J)
        E.symm.toRingEquiv.toRingHom).symm

/-- Exact prime-height decomposition into coefficient contraction and
localized generic-fibre height. -/
theorem polynomialPrime_height_eq_contractionHeight_add_fractionFibreHeight
    {A τ : Type*} [CommRing A] [IsNoetherianRing A] [Finite τ]
    (P : Ideal (MvPolynomial τ A)) [P.IsPrime] :
    let p := coefficientContraction P
    let B := A ⧸ p
    let K := FractionRing B
    let q := coefficientQuotientMap (τ := τ) p
    let ℓ := MvPolynomial.map (algebraMap B K)
    P.height = p.height +
      (Ideal.map ℓ (Ideal.map q P)).height := by
  classical
  dsimp only
  let p := coefficientContraction P
  let B := A ⧸ p
  let K := FractionRing B
  let R := MvPolynomial τ B
  let RK := MvPolynomial τ K
  let q := coefficientQuotientMap (τ := τ) p
  let ℓ : R →+* RK := MvPolynomial.map (algebraMap B K)
  let Pq : Ideal R := Ideal.map q P
  let PL : Ideal RK := Ideal.map ℓ Pq
  letI : p.IsPrime := coefficientContraction_isPrime P
  have hPqF : Pq = polynomialFibreIdeal P := by
    exact coefficientQuotient_map_eq_polynomialFibreIdeal P
  have hPqPrime : Pq.IsPrime := by
    rw [hPqF]
    exact polynomialFibreIdeal_isPrime P
  letI : Pq.IsPrime := hPqPrime
  have hcontract : Pq.comap (C : B →+* R) = ⊥ := by
    exact coefficientQuotient_prime_comap_C_eq_bot P
  let M : Submonoid R :=
    (nonZeroDivisors B).map (C : B →+* R)
  have hdisj : Disjoint (M : Set R) (Pq : Set R) := by
    rw [Set.disjoint_left]
    rintro x ⟨b, hb, rfl⟩ hx
    have hbP : b ∈ Pq.comap (C : B →+* R) := hx
    rw [hcontract] at hbP
    have hb0 : b = 0 := Ideal.mem_bot.mp hbP
    subst b
    exact zero_notMem_nonZeroDivisors hb
  have hlocal : PL.height = Pq.height := by
    change (Ideal.map (algebraMap R RK) Pq).height = Pq.height
    exact IsLocalization.height_map_of_disjoint M Pq hdisj
  let J : Ideal (MvPolynomial τ A) :=
    p.map (C : A →+* MvPolynomial τ A)
  let qabs : Ideal (MvPolynomial τ A ⧸ J) :=
    P.map (Ideal.Quotient.mk J)
  let E : MvPolynomial τ B ≃ₐ[A]
      (MvPolynomial τ A ⧸ J) :=
    MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) p
  letI : P.LiesOver p := ⟨rfl⟩
  have hsplit :=
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
  have htransport : qabs.height = Pq.height := by
    calc
      qabs.height = (polynomialFibreIdeal P).height :=
        (E.symm.toRingEquiv.height_map qabs).symm
      _ = Pq.height := congrArg Ideal.height hPqF.symm
  calc
    P.height = p.height + qabs.height := by
      exact hsplit
    _ = p.height + Pq.height := by rw [htransport]
    _ = p.height + PL.height := by rw [hlocal]

end

end MinimalPrimeLinearFibre

end RB31E2E


end
end BundleSource0022

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0022/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0022.json"

section BundleSource0023
/- Source: Papers/RigidityZheng_Algebra_CoefficientLinearFibre.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/CoefficientLinearFibre.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Generic fibre of a coefficient-linear row ideal

A family of polynomials linear in the outer variables remains the literal
linear row ideal after quotienting and localizing its coefficient ring.  A
minimal prime above it therefore has precisely that generic fibre.
-/

namespace RB31E2E

namespace CoefficientLinearFibre

noncomputable section

open MvPolynomial
open PolynomialPrimeTrdegHeight
open MinimalPrimeLinearFibre

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- A homogeneous linear polynomial over an arbitrary commutative
coefficient ring. -/
def linearPolynomialOver
    {A τ : Type*} [CommRing A] [Fintype τ]
    (v : τ → A) : MvPolynomial τ A :=
  ∑ i, C (v i) * X i

/-- The ideal generated by a coefficient-valued row family. -/
def linearFormIdealOver
    {A τ J : Type*} [CommRing A] [Fintype τ]
    (row : J → τ → A) : Ideal (MvPolynomial τ A) :=
  Ideal.span (Set.range (fun j ↦ linearPolynomialOver (row j)))

theorem map_linearPolynomialOver
    {A B τ : Type*} [CommRing A] [CommRing B] [Fintype τ]
    (f : A →+* B) (v : τ → A) :
    MvPolynomial.map f (linearPolynomialOver v) =
      linearPolynomialOver (fun i ↦ f (v i)) := by
  simp [linearPolynomialOver]

theorem map_linearFormIdealOver
    {A B τ J : Type*} [CommRing A] [CommRing B] [Fintype τ]
    (f : A →+* B) (row : J → τ → A) :
    Ideal.map (MvPolynomial.map f) (linearFormIdealOver row) =
      linearFormIdealOver (fun j i ↦ f (row j i)) := by
  rw [linearFormIdealOver, linearFormIdealOver, Ideal.map_span]
  congr 1
  ext g
  constructor
  · rintro ⟨p, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, (map_linearPolynomialOver f (row j)).symm⟩
  · rintro ⟨j, rfl⟩
    refine ⟨linearPolynomialOver (row j), ⟨j, rfl⟩, ?_⟩
    exact map_linearPolynomialOver f (row j)

theorem linearPolynomialOver_eq_linearPolynomial
    {k τ : Type*} [Field k] [Fintype τ]
    (v : τ → k) :
    linearPolynomialOver v =
      LinearFormIdeal.linearPolynomial v := rfl

theorem linearFormIdealOver_eq_linearFormIdeal
    {k τ J : Type*} [Field k] [Fintype τ]
    (row : J → τ → k) :
    linearFormIdealOver row =
      LinearFormIdeal.linearFormIdeal row := rfl

/-- The generic fibre of a minimal prime above a coefficient-linear row
ideal is exactly the ordinary linear-form ideal obtained by mapping the
row coefficients to the coefficient fraction field. -/
theorem fractionFibrePrime_eq_linearFormIdeal
    {A τ J : Type*} [CommRing A]
    [Fintype τ] [DecidableEq τ]
    (row : J → τ → A)
    (P : Ideal (MvPolynomial τ A)) [P.IsPrime]
    [(coefficientContraction P).IsPrime]
    (hP : P ∈ (linearFormIdealOver row).minimalPrimes) :
    let p := coefficientContraction P
    let B := A ⧸ p
    let K := FractionRing B
    let q := coefficientQuotientMap (τ := τ) p
    let ℓ := MvPolynomial.map (algebraMap B K)
    let rowK : J → τ → K := fun j i ↦
      algebraMap B K (Ideal.Quotient.mk p (row j i))
    Ideal.map ℓ (Ideal.map q P) =
      LinearFormIdeal.linearFormIdeal rowK := by
  classical
  dsimp only
  let p := coefficientContraction P
  let B := A ⧸ p
  let K := FractionRing B
  let q := coefficientQuotientMap (τ := τ) p
  let ℓ : MvPolynomial τ B →+* MvPolynomial τ K :=
    MvPolynomial.map (algebraMap B K)
  let rowK : J → τ → K := fun j i ↦
    algebraMap B K (Ideal.Quotient.mk p (row j i))
  have hmapq : Ideal.map q (linearFormIdealOver row) =
      linearFormIdealOver (fun j i ↦ Ideal.Quotient.mk p (row j i)) := by
    exact map_linearFormIdealOver (Ideal.Quotient.mk p) row
  have hmapℓ : Ideal.map ℓ
      (linearFormIdealOver
        (fun j i ↦ Ideal.Quotient.mk p (row j i))) =
      LinearFormIdeal.linearFormIdeal rowK := by
    rw [map_linearFormIdealOver]
    rfl
  have hIeq : Ideal.map ℓ
      (Ideal.map q (linearFormIdealOver row)) =
      LinearFormIdeal.linearFormIdeal rowK := by
    rw [hmapq, hmapℓ]
  have hI : Ideal.map ℓ
      (Ideal.map q (linearFormIdealOver row)) ≤
      LinearFormIdeal.linearFormIdeal rowK := hIeq.le
  have hPupper : LinearFormIdeal.linearFormIdeal rowK ≤
      Ideal.map ℓ (Ideal.map q P) := by
    rw [← hIeq]
    exact Ideal.map_mono (Ideal.map_mono hP.1.2)
  exact (linearFormIdeal_eq_fractionFibrePrime
    (linearFormIdealOver row) P hP rowK hI hPupper).symm

end

end CoefficientLinearFibre

end RB31E2E


end
end BundleSource0023

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0023/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0023.json"

section BundleSource0024
/- Source: Papers/RigidityZheng_Algebra_FractionQuotientCoordinates.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/FractionQuotientCoordinates.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Coordinate generation of a polynomial quotient function field

The fraction field of a prime quotient of a polynomial ring is generated,
as a field over the base field, by the images of the polynomial coordinate
variables.  The proof expands quotient elements polynomially and fraction
field elements by the localization universal representation.
-/

namespace RB31E2E

namespace FractionQuotientCoordinates

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The quotient-function-field coordinate family. -/
def coordinate
    {k ι : Type*} [Field k]
    (p : Ideal (MvPolynomial ι k)) [p.IsPrime] (
      i : ι) : FractionRing (MvPolynomial ι k ⧸ p) :=
  algebraMap (MvPolynomial ι k ⧸ p)
      (FractionRing (MvPolynomial ι k ⧸ p))
    (Ideal.Quotient.mk p (X i))

/-- Polynomial coordinate images generate the entire quotient function
field. -/
theorem adjoin_coordinate_eq_top
    {k ι : Type*} [Field k]
    (p : Ideal (MvPolynomial ι k)) [p.IsPrime] :
    IntermediateField.adjoin k (Set.range (coordinate p)) = ⊤ := by
  classical
  let B := MvPolynomial ι k ⧸ p
  let K := FractionRing B
  let L : IntermediateField k K :=
    IntermediateField.adjoin k (Set.range (coordinate p))
  apply top_unique
  intro z _hz
  have hpoly : ∀ f : MvPolynomial ι k,
      algebraMap B K (Ideal.Quotient.mk p f) ∈ L := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r =>
        change algebraMap B K (algebraMap k B r) ∈ L
        rw [← IsScalarTower.algebraMap_apply k B K]
        exact L.algebraMap_mem r
    | add f g hf hg =>
        simpa using L.add_mem hf hg
    | mul_X f i hf =>
        have hXi : coordinate p i ∈ L :=
          IntermediateField.subset_adjoin k
            (Set.range (coordinate p)) ⟨i, rfl⟩
        simpa [coordinate, B, K] using L.mul_mem hf hXi
  have hquot : ∀ b : B, algebraMap B K b ∈ L := by
    intro b
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact hpoly f
  obtain ⟨x, hx⟩ := IsLocalization.surj (nonZeroDivisors B) z
  rcases x with ⟨num, den⟩
  have hden : algebraMap B K (den : B) ≠ 0 :=
    (IsLocalization.map_units K den).ne_zero
  have hzdiv : z = algebraMap B K num / algebraMap B K (den : B) :=
    (eq_div_iff hden).2 hx
  rw [hzdiv]
  exact L.div_mem (hquot num) (hquot den)

end

end FractionQuotientCoordinates

end RB31E2E


end
end BundleSource0024

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0024/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0024.json"

section BundleSource0025
/- Source: Papers/RigidityZheng_Incidence_SkeletonOccurrenceSelection.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Incidence/SkeletonOccurrenceSelection.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Selecting provenance occurrences for a sparse skeleton

The properness input says that every simple skeleton edge is represented by
an actual active pin occurrence.  This file makes one such choice for every
edge and proves that the choice is automatically injective: a single
occurrence has only one unordered endpoint edge.  Consequently the selected
occurrence finset has exactly the skeleton cardinality required by the
universal chart budget.

No rigidity, height, elimination, or choice-independent mathematical claim is
assumed.  Classical choice is used only to select the already supplied finite
provenance witnesses.
-/

namespace RB31E2E

namespace SparseNullIncidence

noncomputable section

/-- Choose one actual active occurrence representing each skeleton edge. -/
def representedOccurrence
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f)
    (f : F) : active :=
  Classical.choose (hRepresented f.1 f.2)

/-- The chosen occurrence retains the exact simple-edge provenance. -/
theorem representedOccurrence_activeEdge
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f)
    (f : F) :
    activeEdge src dst active hLoop
        (representedOccurrence src dst active hLoop F hRepresented f) = f.1 :=
  Classical.choose_spec (hRepresented f.1 f.2)

/-- Distinct skeleton edges select distinct active occurrences. -/
theorem representedOccurrence_injective
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f) :
    Function.Injective
      (representedOccurrence src dst active hLoop F hRepresented) := by
  intro f g hfg
  apply Subtype.ext
  calc
    f.1 = activeEdge src dst active hLoop
        (representedOccurrence src dst active hLoop F hRepresented f) :=
      (representedOccurrence_activeEdge
        src dst active hLoop F hRepresented f).symm
    _ = activeEdge src dst active hLoop
        (representedOccurrence src dst active hLoop F hRepresented g) := by
      rw [hfg]
    _ = g.1 := representedOccurrence_activeEdge
      src dst active hLoop F hRepresented g

/-- The actual active occurrences selected by the skeleton, with their
occurrence labels retained. -/
def selectedSkeletonOccurrences
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f) : Finset active :=
  Finset.univ.image
    (representedOccurrence src dst active hLoop F hRepresented)

theorem representedOccurrence_mem_selectedSkeletonOccurrences
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f)
    (f : F) :
    representedOccurrence src dst active hLoop F hRepresented f ∈
      selectedSkeletonOccurrences src dst active hLoop F hRepresented := by
  simp [selectedSkeletonOccurrences]

/-- The selected occurrence family has exactly one member per skeleton edge. -/
theorem card_selectedSkeletonOccurrences
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f) :
    (selectedSkeletonOccurrences
      src dst active hLoop F hRepresented).card = F.card := by
  rw [selectedSkeletonOccurrences,
    Finset.card_image_of_injective Finset.univ
      (representedOccurrence_injective
        src dst active hLoop F hRepresented)]
  simp

/-- Every skeleton edge is represented by a member of the selected finset. -/
theorem exists_selectedOccurrence_activeEdge_eq
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f)
    (f : SimpleEdge V) (hf : f ∈ F) :
    ∃ e : selectedSkeletonOccurrences
        src dst active hLoop F hRepresented,
      activeEdge src dst active hLoop e.1 = f := by
  let fF : F := ⟨f, hf⟩
  refine ⟨
    ⟨representedOccurrence src dst active hLoop F hRepresented fF,
      representedOccurrence_mem_selectedSkeletonOccurrences
        src dst active hLoop F hRepresented fF⟩, ?_⟩
  exact representedOccurrence_activeEdge
    src dst active hLoop F hRepresented fF

/-- Conversely, every selected occurrence comes from an edge of the given
skeleton; the selection introduces no auxiliary null equation. -/
theorem activeEdge_mem_of_mem_selectedSkeletonOccurrences
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f)
    (e : active)
    (he : e ∈ selectedSkeletonOccurrences
      src dst active hLoop F hRepresented) :
    activeEdge src dst active hLoop e ∈ F := by
  rw [selectedSkeletonOccurrences] at he
  obtain ⟨f, _hf, hfe⟩ := Finset.mem_image.mp he
  subst e
  rw [representedOccurrence_activeEdge
    src dst active hLoop F hRepresented f]
  exact f.2

/-- The exact sparse-null skeleton count transfers verbatim to the universal
chart generator budget, while retaining one actual occurrence as provenance
for every selected null equation. -/
theorem selectedSkeletonUniversalChartGenerator_budget
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f)
    (chart : active → Fin 3)
    (hcard : F.card =
      6 * (Fintype.card V - 1) - 2 * active.card) :
    UniversalHomogeneousChart.groundedTwistVariableCount root ≤
      Fintype.card
          (UniversalHomogeneousChart.ActiveCompatibilityIndex active chart) +
        (selectedSkeletonOccurrences
          src dst active hLoop F hRepresented).card := by
  apply UniversalHomogeneousChart.universalChartGenerator_budget
  rw [card_selectedSkeletonOccurrences]
  exact hcard

end

end SparseNullIncidence

end RB31E2E


end
end BundleSource0025

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0025/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0025.json"

section BundleSource0026
/- Source: Papers/RigidityZheng_Incidence_TotalRingProvenanceSwap.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Incidence/TotalRingProvenanceSwap.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Swapping the two provenance layers in the total incidence ring

The universal homogeneous chart is written as

`Q[pin][twist] = MvPolynomial twist (MvPolynomial pin Q)`.

For active-pin elimination it is useful to regard the same total ring as

`Q[twist][pin] = MvPolynomial pin (MvPolynomial twist Q)`.

This file implements that change of viewpoint with
`MvPolynomial.commAlgEquiv`.  In the swapped presentation every pin
coordinate is an outer polynomial variable, while every grounded-twist
coordinate lies in the coefficient ring.  The final theorem computes the
image of an actual universal compatibility coordinate in these explicit
swapped coordinates.
-/

namespace RB31E2E

namespace TotalRingProvenanceSwap

noncomputable section

open MvPolynomial
open GroundedTwistPolynomial
open UniversalHomogeneousChart

/-! ## The swapped total ring -/

/-- The same total polynomial algebra as `RelativeRing`, with pin variables
on the outside and grounded-twist variables in the coefficient ring. -/
abbrev PinOuterRing {V : Type*} (root : V) (E : Type*) :=
  MvPolynomial (PinVariable E)
    (MvPolynomial (GroundedTwistVariable root) ℚ)

/-- Exchange the pin and grounded-twist polynomial layers. -/
def totalRingSwap {V E : Type*} (root : V) :
    RelativeRing root E ≃ₐ[ℚ] PinOuterRing root E :=
  MvPolynomial.commAlgEquiv ℚ
    (GroundedTwistVariable root) (PinVariable E)

/-- The underlying ring homomorphism of `totalRingSwap`, convenient for the
coordinatewise maps on vectors and twists. -/
abbrev totalRingSwapHom {V E : Type*} (root : V) :
    RelativeRing root E →+* PinOuterRing root E :=
  (totalRingSwap (E := E) root).toRingEquiv.toRingHom

@[simp]
theorem totalRingSwap_pinVariable {V E : Type*} (root : V)
    (p : PinVariable E) :
    totalRingSwap (E := E) root (C (X p)) = X p := by
  exact MvPolynomial.commAlgEquiv_C_X p

@[simp]
theorem totalRingSwap_twistVariable {V E : Type*} (root : V)
    (c : GroundedTwistVariable root) :
    totalRingSwap (E := E) root (X c) = C (X c) := by
  exact MvPolynomial.commAlgEquiv_X c

@[simp]
theorem totalRingSwapHom_pinVariable {V E : Type*} (root : V)
    (p : PinVariable E) :
    totalRingSwapHom (E := E) root (C (X p)) = X p := by
  exact totalRingSwap_pinVariable root p

@[simp]
theorem totalRingSwapHom_twistVariable {V E : Type*} (root : V)
    (c : GroundedTwistVariable root) :
    totalRingSwapHom (E := E) root (X c) = C (X c) := by
  exact totalRingSwap_twistVariable root c

/-! ## Explicit pins and twists after the swap -/

/-- The universal pin after the swap: its three coordinates are now outer
pin variables rather than coefficients. -/
def pinOuterUniversalPin {V E : Type*} (root : V) (e : E) :
    Vec3 (PinOuterRing root E) :=
  fun i ↦ X ⟨e, i⟩

/-- One off-root universal twist after the swap: its six coordinates are
coefficients in the inner twist-polynomial ring. -/
def pinOuterOffRootTwist {V E : Type*} {root : V}
    (w : OffRoot root) : Twist (PinOuterRing root E) :=
  ⟨fun i ↦ C (X ⟨w, ⟨false, i⟩⟩),
    fun i ↦ C (X ⟨w, ⟨true, i⟩⟩)⟩

/-- The root-zero universal twist assignment in the swapped presentation. -/
def pinOuterGroundedTwist {V E : Type*} [DecidableEq V] (root : V) :
    V → Twist (PinOuterRing root E) :=
  extendOffRoot root (fun w ↦ pinOuterOffRootTwist (E := E) w)

/-- The relative twist for an oriented occurrence in the swapped
presentation. -/
def pinOuterRelativeTwist {V E : Type*} [DecidableEq V] (root : V)
    (src dst : E → V) (e : E) : Twist (PinOuterRing root E) :=
  pinOuterGroundedTwist (E := E) root (src e) -
    pinOuterGroundedTwist (E := E) root (dst e)

@[simp]
theorem map_universalParameterPin {V E : Type*} (root : V) (e : E) :
    mapVec3 (totalRingSwapHom (E := E) root)
        (universalParameterPin (root := root) e) =
      pinOuterUniversalPin root e := by
  funext i
  simp [mapVec3, universalParameterPin, pinOuterUniversalPin]

@[simp]
theorem map_universalOffRootTwist {V E : Type*} {root : V}
    (w : OffRoot root) :
    mapTwist (totalRingSwapHom (E := E) root)
        (universalOffRootTwist (E := E) w) =
      pinOuterOffRootTwist (E := E) w := by
  apply Prod.ext <;> funext i <;>
    simp [mapTwist, mapVec3, universalOffRootTwist,
      pinOuterOffRootTwist]

@[simp]
theorem map_universalGroundedTwist {V E : Type*} [DecidableEq V]
    (root v : V) :
    mapTwist (totalRingSwapHom (E := E) root)
        (universalGroundedTwist (E := E) root v) =
      pinOuterGroundedTwist (E := E) root v := by
  by_cases hv : v = root
  · subst v
    simp [universalGroundedTwist, pinOuterGroundedTwist,
      extendOffRoot]
  · simp only [universalGroundedTwist, pinOuterGroundedTwist,
      extendOffRoot, hv, dite_false]
    exact map_universalOffRootTwist (E := E) ⟨v, hv⟩

@[simp]
theorem map_universalRelativeTwist {V E : Type*} [DecidableEq V]
    (root : V) (src dst : E → V) (e : E) :
    mapTwist (totalRingSwapHom (E := E) root)
        (universalRelativeTwist root src dst e) =
      pinOuterRelativeTwist root src dst e := by
  rw [universalRelativeTwist, mapTwist_sub,
    map_universalGroundedTwist, map_universalGroundedTwist]
  rfl

/-! ## Compatibility coordinates in the pin-outer presentation -/

/-- The actual universal compatibility coordinate after changing the order
of the two polynomial layers.  This is the concrete generator-level bridge:
the pin coordinates on the right are outer variables, whereas every twist
coordinate is a coefficient. -/
theorem totalRingSwap_universalCompatibilityCoordinate
    {V E : Type*} [DecidableEq V]
    (root : V) (src dst : E → V) (e : E) (j : Fin 3) :
    totalRingSwap (E := E) root
        (universalCompatibilityCoordinate root src dst e j) =
      Twist.eval (pinOuterRelativeTwist root src dst e)
        (pinOuterUniversalPin root e) j := by
  change totalRingSwapHom (E := E) root
      (Twist.eval (universalRelativeTwist root src dst e)
        (universalParameterPin (root := root) e) j) = _
  calc
    _ = Twist.eval
        (mapTwist (totalRingSwapHom (E := E) root)
          (universalRelativeTwist root src dst e))
        (mapVec3 (totalRingSwapHom (E := E) root)
          (universalParameterPin (root := root) e)) j :=
      congrFun
        (mapVec3_eval (totalRingSwapHom (E := E) root)
          (universalRelativeTwist root src dst e)
          (universalParameterPin (root := root) e)) j
    _ = _ := by
      rw [map_universalRelativeTwist, map_universalParameterPin]

end

end TotalRingProvenanceSwap

end RB31E2E


end
end BundleSource0026

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0026/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0026.json"

section BundleSource0027
/- Source: Papers/RigidityZheng_Incidence_PinOuterActiveHeight.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Incidence/PinOuterActiveHeight.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Active-pin height in the pin-outer total ring

After `TotalRingProvenanceSwap`, the universal incidence algebra is written
as a polynomial ring in the labelled pin coordinates over the grounded-twist
coefficient ring.  This file performs the second, provenance-sensitive split:
for every active occurrence it puts the two chart-private pin coordinates in
the outer variable layer and puts the free pin coordinate (together with all
unused pin coordinates) in the coefficient layer.

The split is literal: the private-variable map is injective because its first
component is the occurrence label.  Thus different occurrences can never
silently reuse a private coordinate.  The selected angular coefficients are
then inverted in the twist coefficient ring.  In that chart the actual
compatibility pair is normalized to translated private coordinates.

No height, rank, or properness principle is assumed in this construction.
-/

namespace RB31E2E

namespace PinOuterActiveHeight

noncomputable section

open MvPolynomial
open GroundedTwistPolynomial
open UniversalHomogeneousChart
open PinTriangularElimination
open TotalRingProvenanceSwap
open ActivePinPrimeHeight

/-! ## Twist coefficients before pin variables -/

/-- The grounded-twist coefficient ring in the pin-outer presentation. -/
abbrev TwistCoefficientRing {V : Type*} (root : V) :=
  MvPolynomial (GroundedTwistVariable root) ℚ

/-- One off-root universal twist in the coefficient ring. -/
def coefficientOffRootTwist {V : Type*} {root : V}
    (w : OffRoot root) : Twist (TwistCoefficientRing root) :=
  ⟨fun i ↦ X ⟨w, ⟨false, i⟩⟩,
    fun i ↦ X ⟨w, ⟨true, i⟩⟩⟩

/-- The root-zero universal twist assignment in the coefficient ring. -/
def coefficientGroundedTwist {V : Type*} [DecidableEq V] (root : V) :
    V → Twist (TwistCoefficientRing root) :=
  extendOffRoot root coefficientOffRootTwist

/-- Relative twist whose coordinates are still in the coefficient ring. -/
def coefficientRelativeTwist {V E : Type*} [DecidableEq V] (root : V)
    (src dst : E → V) (e : E) : Twist (TwistCoefficientRing root) :=
  coefficientGroundedTwist root (src e) -
    coefficientGroundedTwist root (dst e)

@[simp]
theorem pinOuterOffRootTwist_eq_map_coefficientOffRootTwist
    {V E : Type*} {root : V} (w : OffRoot root) :
    pinOuterOffRootTwist (E := E) w =
      mapTwist (C : TwistCoefficientRing root →+*
        PinOuterRing root E) (coefficientOffRootTwist w) := by
  apply Prod.ext <;> funext i <;> rfl

@[simp]
theorem pinOuterGroundedTwist_eq_map_coefficientGroundedTwist
    {V E : Type*} [DecidableEq V] (root v : V) :
    pinOuterGroundedTwist (E := E) root v =
      mapTwist (C : TwistCoefficientRing root →+*
        PinOuterRing root E) (coefficientGroundedTwist root v) := by
  by_cases hv : v = root
  · subst v
    simp [pinOuterGroundedTwist, coefficientGroundedTwist,
      extendOffRoot]
  · simp [pinOuterGroundedTwist, coefficientGroundedTwist,
      extendOffRoot, hv,
      pinOuterOffRootTwist_eq_map_coefficientOffRootTwist]

@[simp]
theorem pinOuterRelativeTwist_eq_map_coefficientRelativeTwist
    {V E : Type*} [DecidableEq V] (root : V)
    (src dst : E → V) (e : E) :
    pinOuterRelativeTwist root src dst e =
      mapTwist (C : TwistCoefficientRing root →+*
        PinOuterRing root E) (coefficientRelativeTwist root src dst e) := by
  rw [pinOuterRelativeTwist, coefficientRelativeTwist, mapTwist_sub,
    pinOuterGroundedTwist_eq_map_coefficientGroundedTwist,
    pinOuterGroundedTwist_eq_map_coefficientGroundedTwist]

/-! ## Provenance-disjoint private variables -/

/-- The labelled pin variable occupied by a private chart slot of an active
occurrence. -/
def activePrivatePinVariable
    {E : Type*} [DecidableEq E] {active : Finset E}
    (chart : active → Fin 3) (q : active × Fin 2) : PinVariable E :=
  ⟨q.1.1, privateCoordinate (chart q.1) q.2⟩

/-- Occurrence provenance makes all selected private pin variables distinct. -/
theorem activePrivatePinVariable_injective
    {E : Type*} [DecidableEq E] {active : Finset E}
    (chart : active → Fin 3) :
    Function.Injective (activePrivatePinVariable chart) := by
  rintro ⟨e, s⟩ ⟨f, t⟩ h
  have hef : e = f := by
    apply Subtype.ext
    exact congrArg Prod.fst h
  subst f
  have hst : s = t :=
    privateCoordinate_injective (chart e) (congrArg Prod.snd h)
  subst t
  rfl

/-- The set of all selected private pin variables. -/
def activePrivatePinSet
    {E : Type*} [DecidableEq E] (active : Finset E)
    (chart : active → Fin 3) : Set (PinVariable E) :=
  Set.range (activePrivatePinVariable chart)

/-- The subtype of labelled private pin variables. -/
abbrev ActivePrivatePin
    {E : Type*} [DecidableEq E] (active : Finset E)
    (chart : active → Fin 3) :=
  activePrivatePinSet active chart

/-- All pin variables not selected as private coordinates. -/
abbrev RetainedPin
    {E : Type*} [DecidableEq E] (active : Finset E)
    (chart : active → Fin 3) :=
  (activePrivatePinSet active chart)ᶜ

/-- An occurrence-slot pair as an element of the private-variable subtype. -/
def activePrivatePin
    {E : Type*} [DecidableEq E] {active : Finset E}
    (chart : active → Fin 3) (q : active × Fin 2) :
    ActivePrivatePin active chart :=
  ⟨activePrivatePinVariable chart q, ⟨q, rfl⟩⟩

/-- Every private-variable subtype element remembers a unique occurrence and
slot. -/
def activePrivatePinEquiv
    {E : Type*} [DecidableEq E] (active : Finset E)
    (chart : active → Fin 3) :
    active × Fin 2 ≃ ActivePrivatePin active chart :=
  {
    toFun := activePrivatePin chart
    invFun := fun p ↦ Classical.choose p.2
    left_inv := fun q ↦ by
      apply activePrivatePinVariable_injective chart
      exact Classical.choose_spec ((activePrivatePin chart q).2)
    right_inv := fun p ↦ by
      apply Subtype.ext
      exact Classical.choose_spec p.2
  }

@[simp]
theorem activePrivatePinEquiv_apply
    {E : Type*} [DecidableEq E] (active : Finset E)
    (chart : active → Fin 3) (q : active × Fin 2) :
    (activePrivatePinEquiv active chart q : PinVariable E) =
      activePrivatePinVariable chart q := by
  rfl

/-- The free chart coordinate is never one of the private coordinates, even
when compared with every other occurrence. -/
theorem activeFreePinVariable_not_mem
    {E : Type*} [DecidableEq E] {active : Finset E}
    (chart : active → Fin 3) (e : active) :
    (⟨e.1, chart e⟩ : PinVariable E) ∉
      activePrivatePinSet active chart := by
  rintro ⟨⟨f, slot⟩, h⟩
  have hef : f = e := by
    apply Subtype.ext
    exact congrArg Prod.fst h
  subst f
  exact privateCoordinate_ne (chart e) slot (congrArg Prod.snd h)

/-- The free pin coordinate as an element of the retained coefficient
variables. -/
def activeFreeRetainedPin
    {E : Type*} [DecidableEq E] {active : Finset E}
    (chart : active → Fin 3) (e : active) : RetainedPin active chart :=
  ⟨⟨e.1, chart e⟩, activeFreePinVariable_not_mem chart e⟩

/-! ## Splitting the pin polynomial layer -/

/-- Reindex all pin variables as private or retained, then make the private
variables the outer polynomial layer. -/
def splitPinVariables
    {E A : Type*} [DecidableEq E] [CommSemiring A]
    (active : Finset E) (chart : active → Fin 3) :
    MvPolynomial (PinVariable E) A ≃ₐ[A]
      MvPolynomial (ActivePrivatePin active chart)
        (MvPolynomial (RetainedPin active chart) A) :=
  by
    classical
    exact
      (renameEquiv A (Equiv.Set.sumCompl
          (activePrivatePinSet active chart)).symm).trans
        (sumAlgEquiv A (ActivePrivatePin active chart)
          (RetainedPin active chart))

@[simp]
theorem splitPinVariables_private_X
    {E A : Type*} [DecidableEq E] [CommSemiring A]
    (active : Finset E) (chart : active → Fin 3)
    (q : active × Fin 2) :
    splitPinVariables (A := A) active chart
        (X (activePrivatePinVariable chart q)) =
      X (activePrivatePin chart q) := by
  classical
  rw [splitPinVariables, AlgEquiv.trans_apply, renameEquiv_apply,
    rename_X,
    Equiv.Set.sumCompl_symm_apply_of_mem
      (show activePrivatePinVariable chart q ∈
        activePrivatePinSet active chart from ⟨q, rfl⟩),
    sumAlgEquiv_X_inl] <;> rfl

@[simp]
theorem splitPinVariables_free_X
    {E A : Type*} [DecidableEq E] [CommSemiring A]
    (active : Finset E) (chart : active → Fin 3) (e : active) :
    splitPinVariables (A := A) active chart
        (X (⟨e.1, chart e⟩ : PinVariable E)) =
      C (X (activeFreeRetainedPin chart e)) := by
  classical
  rw [splitPinVariables, AlgEquiv.trans_apply, renameEquiv_apply,
    rename_X,
    Equiv.Set.sumCompl_symm_apply_of_notMem
      (activeFreePinVariable_not_mem chart e),
    sumAlgEquiv_X_inr] <;> rfl

/-! ## The simultaneous angular localization -/

/-- The selected angular coefficient of one active relative twist. -/
def activeAngularCoefficient
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    TwistCoefficientRing root :=
  (coefficientRelativeTwist root src dst e.1).1 (chart e)

/-- Inverting one product simultaneously inverts every selected angular
coefficient. -/
def activeAngularDenominator
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) : TwistCoefficientRing root :=
  ∏ e : active, activeAngularCoefficient root src dst active chart e

/-- The concrete coefficient localization used by the private-pin chart. -/
abbrev AngularCoefficientLocalization
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) :=
  Localization.Away
    (activeAngularDenominator root src dst active chart)

/-- Coefficients after retaining all non-private pin variables. -/
abbrev RetainedCoefficientRing
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) :=
  MvPolynomial (RetainedPin active chart)
    (AngularCoefficientLocalization root src dst active chart)

/-- Final private-variable presentation of the localized total ring. -/
abbrev PrivatePresentationRing
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) :=
  MvPolynomial (ActivePrivatePin active chart)
    (RetainedCoefficientRing root src dst active chart)

theorem activeAngularCoefficient_dvd_denominator
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    activeAngularCoefficient root src dst active chart e ∣
      activeAngularDenominator root src dst active chart := by
  classical
  refine ⟨∏ f ∈ (Finset.univ.erase e),
    activeAngularCoefficient root src dst active chart f, ?_⟩
  simpa [activeAngularDenominator] using
    (Finset.mul_prod_erase
      (s := (Finset.univ : Finset active))
      (f := fun f ↦ activeAngularCoefficient
        root src dst active chart f)
      (Finset.mem_univ e)).symm

/-- A loopless occurrence has a genuinely nonzero labelled angular
coefficient. -/
theorem activeAngularCoefficient_ne_zero
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) (e : active) :
    activeAngularCoefficient root src dst active chart e ≠ 0 := by
  have hsd : src e.1 ≠ dst e.1 := hLoop e.1 e.2
  by_cases hs : src e.1 = root
  · have hd : dst e.1 ≠ root := by
      intro h
      exact hsd (hs.trans h.symm)
    simp [activeAngularCoefficient, coefficientRelativeTwist,
      coefficientGroundedTwist, extendOffRoot, hs, hd,
      coefficientOffRootTwist]
  · by_cases hd : dst e.1 = root
    · simp [activeAngularCoefficient, coefficientRelativeTwist,
        coefficientGroundedTwist, extendOffRoot, hs, hd,
        coefficientOffRootTwist]
    · intro hzero
      have hX :
          (X (⟨⟨src e.1, hs⟩, ⟨false, chart e⟩⟩ :
              GroundedTwistVariable root) : TwistCoefficientRing root) =
            (X (⟨⟨dst e.1, hd⟩, ⟨false, chart e⟩⟩ :
              GroundedTwistVariable root) : TwistCoefficientRing root) := by
        simpa [activeAngularCoefficient, coefficientRelativeTwist,
          coefficientGroundedTwist, extendOffRoot, hs, hd,
          coefficientOffRootTwist, sub_eq_zero] using hzero
      have hvar := MvPolynomial.X_injective hX
      exact hsd (congrArg (fun c : GroundedTwistVariable root ↦ c.1.1) hvar)

/-- The simultaneous angular denominator is nonzero for loopless active
occurrences. -/
theorem activeAngularDenominator_ne_zero
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) :
    activeAngularDenominator root src dst active chart ≠ 0 := by
  classical
  rw [activeAngularDenominator]
  exact Finset.prod_ne_zero_iff.mpr fun e _ ↦
    activeAngularCoefficient_ne_zero
      root src dst active chart hLoop e

/-- The concrete away localization is a domain on every loopless chart. -/
@[reducible] def angularCoefficientLocalizationIsDomain
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) :
    IsDomain (AngularCoefficientLocalization
      root src dst active chart) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (activeAngularDenominator_ne_zero
        root src dst active chart hLoop))

/-- Every selected angular coefficient is a unit in the simultaneous
localization. -/
theorem activeAngularCoefficient_isUnit
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    IsUnit (algebraMap (TwistCoefficientRing root)
      (AngularCoefficientLocalization root src dst active chart)
      (activeAngularCoefficient root src dst active chart e)) := by
  apply isUnit_of_dvd_unit
    (map_dvd (algebraMap (TwistCoefficientRing root)
      (AngularCoefficientLocalization root src dst active chart))
      (activeAngularCoefficient_dvd_denominator
        root src dst active chart e))
  exact IsLocalization.Away.algebraMap_isUnit
    (S := AngularCoefficientLocalization root src dst active chart)
    (activeAngularDenominator root src dst active chart)

/-- The selected angular coefficient as an explicit unit. -/
def activeAngularUnit
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    (AngularCoefficientLocalization root src dst active chart)ˣ :=
  (activeAngularCoefficient_isUnit root src dst active chart e).unit

@[simp]
theorem activeAngularUnit_coe
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    ((activeAngularUnit root src dst active chart e :
      (AngularCoefficientLocalization root src dst active chart)ˣ) :
      AngularCoefficientLocalization root src dst active chart) =
    algebraMap (TwistCoefficientRing root)
      (AngularCoefficientLocalization root src dst active chart)
      (activeAngularCoefficient root src dst active chart e) := by
  exact (activeAngularCoefficient_isUnit
    root src dst active chart e).unit_spec

/-! ## The actual total-ring map into the private presentation -/

/-- Base-change the pin-outer polynomial ring to the angular localization
and then perform the private/retained variable split. -/
def localizedSplitPinOuterHom
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) :
    PinOuterRing root E →+*
      PrivatePresentationRing root src dst active chart :=
  (splitPinVariables
      (A := AngularCoefficientLocalization root src dst active chart)
      active chart).toRingEquiv.toRingHom.comp
    (MvPolynomial.map (algebraMap (TwistCoefficientRing root)
      (AngularCoefficientLocalization root src dst active chart)))

/-- The complete map from the original `Q[pin][twist]` presentation. -/
def localizedPrivatePresentationHom
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) :
    RelativeRing root E →+*
      PrivatePresentationRing root src dst active chart :=
  (localizedSplitPinOuterHom root src dst active chart).comp
    (totalRingSwapHom (E := E) root)

@[simp]
theorem localizedSplitPinOuterHom_C
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (f : TwistCoefficientRing root) :
    localizedSplitPinOuterHom root src dst active chart (C f) =
      C (C (algebraMap (TwistCoefficientRing root)
        (AngularCoefficientLocalization root src dst active chart) f)) := by
  classical
  simp [localizedSplitPinOuterHom, splitPinVariables]

@[simp]
theorem localizedSplitPinOuterHom_private_X
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (q : active × Fin 2) :
    localizedSplitPinOuterHom root src dst active chart
        (X (activePrivatePinVariable chart q)) =
      X (activePrivatePin chart q) := by
  classical
  simp [localizedSplitPinOuterHom]

@[simp]
theorem localizedSplitPinOuterHom_free_X
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    localizedSplitPinOuterHom root src dst active chart
        (X (⟨e.1, chart e⟩ : PinVariable E)) =
      C (X (activeFreeRetainedPin chart e)) := by
  classical
  simp [localizedSplitPinOuterHom]

@[simp]
theorem localizedPrivatePresentationHom_privatePin
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (q : active × Fin 2) :
    localizedPrivatePresentationHom root src dst active chart
        (C (X (activePrivatePinVariable chart q))) =
      X (activePrivatePin chart q) := by
  simp [localizedPrivatePresentationHom]

@[simp]
theorem localizedPrivatePresentationHom_freePin
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    localizedPrivatePresentationHom root src dst active chart
        (C (X (⟨e.1, chart e⟩ : PinVariable E))) =
      C (X (activeFreeRetainedPin chart e)) := by
  simp [localizedPrivatePresentationHom]

/-! ## Compatibility generators in retained/private normal form -/

/-- Mapping commutes with the explicit stationary-pin numerator. -/
theorem map_stationaryPinNumerator
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (Z : Twist R) (p : Vec3 R)
    (i j : Fin 3) :
    f (stationaryPinNumerator Z p i j) =
      stationaryPinNumerator (mapTwist f Z) (mapVec3 f p) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [stationaryPinNumerator, mapTwist, mapVec3]

/-- Mapping commutes with a triangular residual. -/
theorem map_triangularResidual
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (Z : Twist R) (p : Vec3 R)
    (i : Fin 3) (slot : Fin 2) :
    f (triangularResidual Z p i slot) =
      triangularResidual (mapTwist f Z) (mapVec3 f p) i slot := by
  simp [triangularResidual, map_stationaryPinNumerator, mapTwist, mapVec3]

theorem mapTwist_comp_local
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (g : S →+* T) (f : R →+* S) (Z : Twist R) :
    mapTwist (g.comp f) Z = mapTwist g (mapTwist f Z) := by
  rfl

/-- The relative twist after localizing the twist coefficient ring. -/
def localizedCoefficientRelativeTwist
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : E) :
    Twist (AngularCoefficientLocalization root src dst active chart) :=
  mapTwist (algebraMap (TwistCoefficientRing root)
    (AngularCoefficientLocalization root src dst active chart))
    (coefficientRelativeTwist root src dst e)

/-- The same relative twist embedded in the retained-pin coefficient ring. -/
def retainedRelativeTwist
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : E) :
    Twist (RetainedCoefficientRing root src dst active chart) :=
  mapTwist (C : AngularCoefficientLocalization
      root src dst active chart →+*
      RetainedCoefficientRing root src dst active chart)
    (localizedCoefficientRelativeTwist
      root src dst active chart e)

/-- In the retained coefficient ring only the free chart coordinate of this
pin is needed by the stationary-pin numerator. -/
def retainedChartPin
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    Vec3 (RetainedCoefficientRing root src dst active chart) :=
  fun j ↦ if j = chart e then X (activeFreeRetainedPin chart e) else 0

@[simp]
theorem retainedChartPin_free
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    retainedChartPin root src dst active chart e (chart e) =
      X (activeFreeRetainedPin chart e) := by
  simp [retainedChartPin]

theorem localizedPrivatePresentationHom_relativeTwist_angular
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : E) (i : Fin 3) :
    localizedPrivatePresentationHom root src dst active chart
        ((universalRelativeTwist root src dst e).1 i) =
      (C ((retainedRelativeTwist
        root src dst active chart e).1 i) :
        PrivatePresentationRing root src dst active chart) := by
  have hswap := congrArg (fun Z ↦ Z.1 i)
    (map_universalRelativeTwist (E := E) root src dst e)
  have hcoeff := congrArg (fun Z ↦ Z.1 i)
    (pinOuterRelativeTwist_eq_map_coefficientRelativeTwist
      root src dst e)
  change totalRingSwapHom (E := E) root
      ((universalRelativeTwist root src dst e).1 i) =
    (pinOuterRelativeTwist root src dst e).1 i at hswap
  change (pinOuterRelativeTwist root src dst e).1 i =
    C ((coefficientRelativeTwist root src dst e).1 i) at hcoeff
  rw [localizedPrivatePresentationHom]
  change localizedSplitPinOuterHom root src dst active chart
      (totalRingSwapHom (E := E) root
        ((universalRelativeTwist root src dst e).1 i)) = _
  rw [hswap, hcoeff, localizedSplitPinOuterHom_C]
  rfl

theorem localizedPrivatePresentationHom_relativeTwist_translational
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : E) (i : Fin 3) :
    localizedPrivatePresentationHom root src dst active chart
        ((universalRelativeTwist root src dst e).2 i) =
      (C ((retainedRelativeTwist
        root src dst active chart e).2 i) :
        PrivatePresentationRing root src dst active chart) := by
  have hswap := congrArg (fun Z ↦ Z.2 i)
    (map_universalRelativeTwist (E := E) root src dst e)
  have hcoeff := congrArg (fun Z ↦ Z.2 i)
    (pinOuterRelativeTwist_eq_map_coefficientRelativeTwist
      root src dst e)
  change totalRingSwapHom (E := E) root
      ((universalRelativeTwist root src dst e).2 i) =
    (pinOuterRelativeTwist root src dst e).2 i at hswap
  change (pinOuterRelativeTwist root src dst e).2 i =
    C ((coefficientRelativeTwist root src dst e).2 i) at hcoeff
  rw [localizedPrivatePresentationHom]
  change localizedSplitPinOuterHom root src dst active chart
      (totalRingSwapHom (E := E) root
        ((universalRelativeTwist root src dst e).2 i)) = _
  rw [hswap, hcoeff, localizedSplitPinOuterHom_C]
  rfl

@[simp]
theorem localizedPrivatePresentationHom_pin_private
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) (slot : Fin 2) :
    localizedPrivatePresentationHom root src dst active chart
        (universalParameterPin (root := root) e.1
          (privateCoordinate (chart e) slot)) =
      (X (activePrivatePin chart ⟨e, slot⟩) :
        PrivatePresentationRing root src dst active chart) := by
  exact localizedPrivatePresentationHom_privatePin
    root src dst active chart ⟨e, slot⟩

@[simp]
theorem localizedPrivatePresentationHom_pin_free
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    localizedPrivatePresentationHom root src dst active chart
        (universalParameterPin (root := root) e.1 (chart e)) =
      (C (retainedChartPin root src dst active chart e (chart e)) :
        PrivatePresentationRing root src dst active chart) := by
  rw [retainedChartPin_free]
  exact localizedPrivatePresentationHom_freePin
    root src dst active chart e

/-- The scalar numerator occurring on one private slot.  Writing the six
branches directly keeps the total-ring proof small: only the free pin
coordinate occurs. -/
def retainedPrivateNumerator
    {R : Type*} [CommRing R] (Z : Twist R) (free : R)
    (i : Fin 3) (slot : Fin 2) : R :=
  if i = 0 then
    if slot = 0 then Z.1 1 * free - Z.2 2
    else Z.2 1 + Z.1 2 * free
  else if i = 1 then
    if slot = 0 then Z.2 2 + Z.1 0 * free
    else Z.1 2 * free - Z.2 0
  else
    if slot = 0 then Z.1 0 * free - Z.2 1
    else Z.2 0 + Z.1 1 * free

theorem retainedPrivateNumerator_eq_stationaryPinNumerator
    {R : Type*} [CommRing R] (Z : Twist R) (p : Vec3 R)
    (i : Fin 3) (slot : Fin 2) :
    retainedPrivateNumerator Z (p i) i slot =
      stationaryPinNumerator Z p i (privateCoordinate i slot) := by
  fin_cases i <;> fin_cases slot <;>
    simp [retainedPrivateNumerator, stationaryPinNumerator,
      privateCoordinate]

/-- At a private coordinate, the mapped stationary numerator contains no
private pin variable: it lies literally in the retained coefficient ring. -/
theorem localizedPrivatePresentationHom_stationaryPinNumerator_private
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (e : active) (slot : Fin 2) :
    localizedPrivatePresentationHom root src dst active chart
        (stationaryPinNumerator
          (universalRelativeTwist root src dst e.1)
          (universalParameterPin (root := root) e.1)
          (chart e) (privateCoordinate (chart e) slot)) =
      C (stationaryPinNumerator
        (retainedRelativeTwist root src dst active chart e.1)
        (retainedChartPin root src dst active chart e)
        (chart e) (privateCoordinate (chart e) slot)) := by
  let hDomain : IsDomain (AngularCoefficientLocalization
      root src dst active chart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active chart hLoop
  letI : Nontrivial (AngularCoefficientLocalization
      root src dst active chart) := hDomain.toNontrivial
  generalize hi : chart e = i
  have hfree :
      localizedPrivatePresentationHom root src dst active chart
          (universalParameterPin (root := root) e.1 i) =
        (C (X (activeFreeRetainedPin chart e)) :
          PrivatePresentationRing root src dst active chart) := by
    have h := localizedPrivatePresentationHom_pin_free
      root src dst active chart e
    rw [retainedChartPin_free] at h
    simpa [hi] using h
  have hang (j : Fin 3) :=
    localizedPrivatePresentationHom_relativeTwist_angular
      root src dst active chart e.1 j
  have htrans (j : Fin 3) :=
    localizedPrivatePresentationHom_relativeTwist_translational
      root src dst active chart e.1 j
  let f := localizedPrivatePresentationHom root src dst active chart
  have hmulSub (a p b : RelativeRing root E)
      (A P B : RetainedCoefficientRing root src dst active chart)
      (ha : f a = C A) (hp : f p = C P) (hb : f b = C B) :
      f (a * p - b) = C (A * P - B) := by
    have hneg : f (-b) = C (-B) := by
      apply add_right_cancel (b := C B)
      calc
        f (-b) + C B = f (-b) + f b := by rw [hb]
        _ = f (-b + b) := (f.map_add _ _).symm
        _ = f 0 := congrArg f (neg_add_cancel b)
        _ = 0 := f.map_zero
        _ = C (-B) + C B := by
          calc
            0 = C 0 := (C.map_zero).symm
            _ = C (-B + B) := congrArg C (neg_add_cancel B).symm
            _ = C (-B) + C B := C.map_add _ _
    rw [sub_eq_add_neg, f.map_add, f.map_mul, hneg,
      ha, hp]
    simp [sub_eq_add_neg]
  have haddMul (b a p : RelativeRing root E)
      (B A P : RetainedCoefficientRing root src dst active chart)
      (hb : f b = C B) (ha : f a = C A) (hp : f p = C P) :
      f (b + a * p) = C (B + A * P) := by
    rw [f.map_add, f.map_mul, hb, ha, hp]
    simp
  have hretfree :
      retainedChartPin root src dst active chart e i =
        X (activeFreeRetainedPin chart e) := by
    simpa [hi] using retainedChartPin_free
      root src dst active chart e
  rw [← retainedPrivateNumerator_eq_stationaryPinNumerator]
  rw [← retainedPrivateNumerator_eq_stationaryPinNumerator]
  rw [hretfree]
  fin_cases i <;> fin_cases slot
  · simpa [retainedPrivateNumerator, hi] using
      hmulSub
        ((universalRelativeTwist root src dst e.1).1 1)
        (universalParameterPin (root := root) e.1 0)
        ((universalRelativeTwist root src dst e.1).2 2)
        ((retainedRelativeTwist root src dst active chart e.1).1 1)
        (X (activeFreeRetainedPin chart e))
        ((retainedRelativeTwist root src dst active chart e.1).2 2)
        (hang 1) hfree (htrans 2)
  · simpa [retainedPrivateNumerator, hi] using
      haddMul
        ((universalRelativeTwist root src dst e.1).2 1)
        ((universalRelativeTwist root src dst e.1).1 2)
        (universalParameterPin (root := root) e.1 0)
        ((retainedRelativeTwist root src dst active chart e.1).2 1)
        ((retainedRelativeTwist root src dst active chart e.1).1 2)
        (X (activeFreeRetainedPin chart e))
        (htrans 1) (hang 2) hfree
  · simpa [retainedPrivateNumerator, hi] using
      haddMul
        ((universalRelativeTwist root src dst e.1).2 2)
        ((universalRelativeTwist root src dst e.1).1 0)
        (universalParameterPin (root := root) e.1 1)
        ((retainedRelativeTwist root src dst active chart e.1).2 2)
        ((retainedRelativeTwist root src dst active chart e.1).1 0)
        (X (activeFreeRetainedPin chart e))
        (htrans 2) (hang 0) hfree
  · simpa [retainedPrivateNumerator, hi] using
      hmulSub
        ((universalRelativeTwist root src dst e.1).1 2)
        (universalParameterPin (root := root) e.1 1)
        ((universalRelativeTwist root src dst e.1).2 0)
        ((retainedRelativeTwist root src dst active chart e.1).1 2)
        (X (activeFreeRetainedPin chart e))
        ((retainedRelativeTwist root src dst active chart e.1).2 0)
        (hang 2) hfree (htrans 0)
  · simpa [retainedPrivateNumerator, hi] using
      hmulSub
        ((universalRelativeTwist root src dst e.1).1 0)
        (universalParameterPin (root := root) e.1 2)
        ((universalRelativeTwist root src dst e.1).2 1)
        ((retainedRelativeTwist root src dst active chart e.1).1 0)
        (X (activeFreeRetainedPin chart e))
        ((retainedRelativeTwist root src dst active chart e.1).2 1)
        (hang 0) hfree (htrans 1)
  · simpa [retainedPrivateNumerator, hi] using
      haddMul
        ((universalRelativeTwist root src dst e.1).2 0)
        ((universalRelativeTwist root src dst e.1).1 1)
        (universalParameterPin (root := root) e.1 2)
        ((retainedRelativeTwist root src dst active chart e.1).2 0)
        ((retainedRelativeTwist root src dst active chart e.1).1 1)
        (X (activeFreeRetainedPin chart e))
        (htrans 0) (hang 1) hfree

/-! ## Unit normalization of the actual triangular residual -/

/-- The selected angular coefficient, now as a unit of the retained-pin
coefficient ring. -/
def retainedAngularUnit
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    (RetainedCoefficientRing root src dst active chart)ˣ :=
  Units.map
    (C : AngularCoefficientLocalization root src dst active chart →+*
      RetainedCoefficientRing root src dst active chart)
    (activeAngularUnit root src dst active chart e)

@[simp]
theorem retainedAngularUnit_coe
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    ((retainedAngularUnit root src dst active chart e :
      (RetainedCoefficientRing root src dst active chart)ˣ) :
      RetainedCoefficientRing root src dst active chart) =
      (retainedRelativeTwist root src dst active chart e.1).1
        (chart e) := by
  change C (((activeAngularUnit root src dst active chart e :
      (AngularCoefficientLocalization root src dst active chart)ˣ) :
      AngularCoefficientLocalization root src dst active chart)) =
    C (algebraMap (TwistCoefficientRing root)
      (AngularCoefficientLocalization root src dst active chart)
      (activeAngularCoefficient root src dst active chart e))
  rw [activeAngularUnit_coe]

/-- The retained coefficient on the right of one normalized private
relation. -/
def privateRelationRhs
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) (slot : Fin 2) :
    RetainedCoefficientRing root src dst active chart :=
  (((retainedAngularUnit root src dst active chart e)⁻¹ :
      (RetainedCoefficientRing root src dst active chart)ˣ) :
      RetainedCoefficientRing root src dst active chart) *
    retainedPrivateNumerator
      (retainedRelativeTwist root src dst active chart e.1)
      (X (activeFreeRetainedPin chart e)) (chart e) slot

/-- Literal translated-coordinate normal form associated with one active
occurrence and one private slot. -/
def normalizedPrivateGenerator
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) (slot : Fin 2) :
    PrivatePresentationRing root src dst active chart :=
  (X (activePrivatePin chart ⟨e, slot⟩) :
      PrivatePresentationRing root src dst active chart) +
    (C (-privateRelationRhs root src dst active chart e slot) :
      PrivatePresentationRing root src dst active chart)

/-- Before division by the angular unit, the actual universal triangular
residual has the expected private-linear form. -/
theorem localizedPrivatePresentationHom_universalTriangularResidual
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (e : active) (slot : Fin 2) :
    localizedPrivatePresentationHom root src dst active chart
        (universalTriangularResidual root src dst e.1 (chart e) slot) =
      (C ((retainedRelativeTwist root src dst active chart e.1).1
            (chart e)) : PrivatePresentationRing
              root src dst active chart) *
          (X (activePrivatePin chart ⟨e, slot⟩) :
            PrivatePresentationRing root src dst active chart) +
        (C (-retainedPrivateNumerator
            (retainedRelativeTwist root src dst active chart e.1)
            (X (activeFreeRetainedPin chart e)) (chart e) slot) :
          PrivatePresentationRing root src dst active chart) := by
  let hDomain : IsDomain (AngularCoefficientLocalization
      root src dst active chart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active chart hLoop
  letI : Nontrivial (AngularCoefficientLocalization
      root src dst active chart) := hDomain.toNontrivial
  let f := localizedPrivatePresentationHom root src dst active chart
  let Z := universalRelativeTwist root src dst e.1
  let p := universalParameterPin (root := root) e.1
  let numerator := stationaryPinNumerator Z p (chart e)
    (privateCoordinate (chart e) slot)
  have hangular : f (Z.1 (chart e)) =
      C ((retainedRelativeTwist
        root src dst active chart e.1).1 (chart e)) :=
    localizedPrivatePresentationHom_relativeTwist_angular
      root src dst active chart e.1 (chart e)
  have hprivate : f (p (privateCoordinate (chart e) slot)) =
      X (activePrivatePin chart ⟨e, slot⟩) :=
    localizedPrivatePresentationHom_pin_private
      root src dst active chart e slot
  have hnumerator : f numerator = C
      (retainedPrivateNumerator
        (retainedRelativeTwist root src dst active chart e.1)
        (X (activeFreeRetainedPin chart e)) (chart e) slot) := by
    dsimp [numerator, Z, p]
    rw [localizedPrivatePresentationHom_stationaryPinNumerator_private
      root src dst active chart hLoop e slot]
    rw [← retainedPrivateNumerator_eq_stationaryPinNumerator]
    rw [retainedChartPin_free]
  let N := retainedPrivateNumerator
    (retainedRelativeTwist root src dst active chart e.1)
    (X (activeFreeRetainedPin chart e)) (chart e) slot
  have hneg : f (-numerator) = C (-N) := by
    apply add_right_cancel (b := C N)
    calc
      f (-numerator) + C N = f (-numerator) + f numerator := by
        rw [hnumerator]
      _ = f (-numerator + numerator) := (f.map_add _ _).symm
      _ = f 0 := congrArg f (neg_add_cancel numerator)
      _ = 0 := f.map_zero
      _ = C (-N) + C N := by
        calc
          0 = C 0 := (C.map_zero).symm
          _ = C (-N + N) := congrArg C (neg_add_cancel N).symm
          _ = C (-N) + C N := C.map_add _ _
  change f (triangularResidual Z p (chart e) slot) = _
  rw [triangularResidual, sub_eq_add_neg,
    f.map_add, f.map_mul, hneg, hangular, hprivate]

/-- Dividing by the selected angular unit turns the actual residual into the
literal translated private coordinate `X_private - rhs`. -/
theorem normalize_localized_universalTriangularResidual
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (e : active) (slot : Fin 2) :
    C ((((retainedAngularUnit root src dst active chart e)⁻¹ :
        (RetainedCoefficientRing root src dst active chart)ˣ) :
        RetainedCoefficientRing root src dst active chart)) *
      localizedPrivatePresentationHom root src dst active chart
        (universalTriangularResidual root src dst e.1 (chart e) slot) =
      normalizedPrivateGenerator root src dst active chart e slot := by
  letI : IsDomain (AngularCoefficientLocalization
      root src dst active chart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active chart hLoop
  letI : Nontrivial (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  rw [localizedPrivatePresentationHom_universalTriangularResidual
    root src dst active chart hLoop e slot]
  rw [normalizedPrivateGenerator, privateRelationRhs,
    ← retainedAngularUnit_coe]
  let u := retainedAngularUnit root src dst active chart e
  let N := retainedPrivateNumerator
    (retainedRelativeTwist root src dst active chart e.1)
    (X (activeFreeRetainedPin chart e)) (chart e) slot
  change C ((↑(u⁻¹) : RetainedCoefficientRing
      root src dst active chart)) *
      (C ((↑u : RetainedCoefficientRing
        root src dst active chart)) *
          X (activePrivatePin chart ⟨e, slot⟩) + C (-N)) =
      X (activePrivatePin chart ⟨e, slot⟩) +
        C (-((↑(u⁻¹) : RetainedCoefficientRing
          root src dst active chart) * N))
  rw [mul_add, ← mul_assoc, ← C_mul, Units.inv_mul, C_1, one_mul,
    ← C_mul]
  congr 2
  exact mul_neg
    ((↑(u⁻¹) : RetainedCoefficientRing root src dst active chart)) N

/-! ## Simultaneous height of all active private pairs -/

/-- The retained-coordinate response attached to a labelled private pin
variable.  The inverse equivalence recovers the unique occurrence and slot,
so the right-hand side cannot lose its provenance. -/
def activePrivateTranslation
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (p : ActivePrivatePin active chart) :
    RetainedCoefficientRing root src dst active chart :=
  let q := (activePrivatePinEquiv active chart).symm p
  privateRelationRhs root src dst active chart q.1 q.2

@[simp]
theorem activePrivateTranslation_activePrivatePin
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (q : active × Fin 2) :
    activePrivateTranslation root src dst active chart
        (activePrivatePin chart q) =
      privateRelationRhs root src dst active chart q.1 q.2 := by
  change privateRelationRhs root src dst active chart
      ((activePrivatePinEquiv active chart).symm
        ((activePrivatePinEquiv active chart) q)).1
      ((activePrivatePinEquiv active chart).symm
        ((activePrivatePinEquiv active chart) q)).2 = _
  rw [Equiv.symm_apply_apply]

/-- Enumerate the two private variables of every active occurrence by
`Fin (active.card * 2)`. -/
def activePrivateEnumeration
    {E : Type*} [DecidableEq E] (active : Finset E)
    (chart : active → Fin 3) :
    Fin (active.card * 2) → ActivePrivatePin active chart :=
  occurrencePrivateVariable
    (fun i slot ↦
      activePrivatePin chart ⟨active.equivFin.symm i, slot⟩)

/-- The enumeration remains injective: the finite enumeration of active
occurrences and the labelled private-pin equivalence are both injective. -/
theorem activePrivateEnumeration_injective
    {E : Type*} [DecidableEq E] (active : Finset E)
    (chart : active → Fin 3) :
    Function.Injective (activePrivateEnumeration active chart) := by
  apply occurrencePrivateVariable_injective
  intro q r hqr
  have hpairs :
      (active.equivFin.symm q.1, q.2) =
        (active.equivFin.symm r.1, r.2) :=
    (activePrivatePinEquiv active chart).injective hqr
  apply Prod.ext
  · exact active.equivFin.symm.injective (congrArg Prod.fst hpairs)
  · exact congrArg (fun p : active × Fin 2 ↦ p.2) hpairs

/-- The literal ideal generated by every normalized active compatibility
relation, indexed by its occurrence and private slot. -/
def activeNormalizedPrivateIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) :
    Ideal (PrivatePresentationRing root src dst active chart) :=
  Ideal.span (Set.range (fun q : active × Fin 2 ↦
    normalizedPrivateGenerator
      root src dst active chart q.1 q.2))

/-- Every enumerated translated coordinate is one of the literal normalized
relations.  This is the ideal-level provenance bridge needed by the height
chain; it assumes no abstract presentation map. -/
theorem translatedCoordinateIdeal_le_activeNormalizedPrivateIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) :
    letI : IsDomain (AngularCoefficientLocalization
        root src dst active chart) :=
      angularCoefficientLocalizationIsDomain
        root src dst active chart hLoop
    letI : Nontrivial (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : CommRing (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : CommRing (PrivatePresentationRing
        root src dst active chart) := inferInstance
    translatedCoordinateIdeal
        (activePrivateEnumeration active chart)
        (activePrivateTranslation root src dst active chart) ≤
      activeNormalizedPrivateIdeal root src dst active chart := by
  letI : IsDomain (AngularCoefficientLocalization
      root src dst active chart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active chart hLoop
  letI : Nontrivial (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active chart) := inferInstance
  rw [translatedCoordinateIdeal, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  let q : Fin active.card × Fin 2 := finProdFinEquiv.symm j
  let e : active := active.equivFin.symm q.1
  have hmem : normalizedPrivateGenerator
      root src dst active chart e q.2 ∈
      activeNormalizedPrivateIdeal root src dst active chart := by
    apply Ideal.subset_span
    exact ⟨⟨e, q.2⟩, rfl⟩
  have henum : activePrivateEnumeration active chart j =
      activePrivatePin chart ⟨e, q.2⟩ := by
    rfl
  have hCneg (a : RetainedCoefficientRing
      root src dst active chart) :
      (C (-a) : PrivatePresentationRing
        root src dst active chart) = -C a :=
    map_neg C a
  change X (activePrivateEnumeration active chart j) -
      C (activePrivateTranslation root src dst active chart
        (activePrivateEnumeration active chart j)) ∈
    activeNormalizedPrivateIdeal root src dst active chart
  rw [henum, activePrivateTranslation_activePrivatePin,
    sub_eq_add_neg, ← hCneg]
  simpa only [normalizedPrivateGenerator] using hmem

/-- Main simultaneous increment theorem: after the concrete angular
localization, the actual normalized active relations contribute at least two
height units for every active occurrence. -/
theorem activeNormalizedPrivateIdeal_height_ge_twice_card
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) :
    letI : IsDomain (AngularCoefficientLocalization
        root src dst active chart) :=
      angularCoefficientLocalizationIsDomain
        root src dst active chart hLoop
    letI : Nontrivial (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : CommRing (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : IsDomain (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : CommRing (PrivatePresentationRing
        root src dst active chart) := inferInstance
    (active.card * 2 : ℕ) ≤
      (activeNormalizedPrivateIdeal
        root src dst active chart).height := by
  letI : IsDomain (AngularCoefficientLocalization
      root src dst active chart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active chart hLoop
  letI : Nontrivial (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : IsDomain (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active chart) := inferInstance
  exact (translatedCoordinateIdeal_height_ge_card
      (activePrivateEnumeration active chart)
      (activePrivateEnumeration_injective active chart)
      (activePrivateTranslation root src dst active chart)).trans
    (Ideal.height_mono
      (translatedCoordinateIdeal_le_activeNormalizedPrivateIdeal
        root src dst active chart hLoop))

/-! ## Returning from normal form to the actual compatibility equations -/

/-- The localized ideal generated by the two oriented compatibility
coordinates of every active occurrence.  Each oriented generator is
definitionally a genuine universal compatibility coordinate or its negative;
the sign has no effect on the generated ideal. -/
def localizedActiveCompatibilityIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) :
    Ideal (PrivatePresentationRing root src dst active chart) :=
  Ideal.span (Set.range (fun q : active × Fin 2 ↦
    localizedPrivatePresentationHom root src dst active chart
      (universalOrientedCompatibilityEquation
        root src dst q.1.1 (chart q.1) q.2)))

/-- Unit normalization identifies the ideal of the actual oriented
compatibility pairs with the literal translated-private-coordinate ideal. -/
theorem localizedActiveCompatibilityIdeal_eq_activeNormalizedPrivateIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) :
    letI : IsDomain (AngularCoefficientLocalization
        root src dst active chart) :=
      angularCoefficientLocalizationIsDomain
        root src dst active chart hLoop
    letI : Nontrivial (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : CommRing (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : CommRing (PrivatePresentationRing
        root src dst active chart) := inferInstance
    localizedActiveCompatibilityIdeal root src dst active chart =
      activeNormalizedPrivateIdeal root src dst active chart := by
  letI : IsDomain (AngularCoefficientLocalization
      root src dst active chart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active chart hLoop
  letI : Nontrivial (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active chart) := inferInstance
  apply le_antisymm
  · rw [localizedActiveCompatibilityIdeal, Ideal.span_le]
    rintro _ ⟨q, rfl⟩
    have hn : normalizedPrivateGenerator
        root src dst active chart q.1 q.2 ∈
        activeNormalizedPrivateIdeal root src dst active chart := by
      apply Ideal.subset_span
      exact ⟨q, rfl⟩
    have hu := Ideal.mul_mem_left
      (activeNormalizedPrivateIdeal root src dst active chart)
      (C (((retainedAngularUnit
        root src dst active chart q.1 :
          (RetainedCoefficientRing
            root src dst active chart)ˣ) :
          RetainedCoefficientRing root src dst active chart))) hn
    have hnormalize :=
      normalize_localized_universalTriangularResidual
        root src dst active chart hLoop q.1 q.2
    rw [universalTriangularResidual_eq_orientedCompatibilityEquation]
      at hnormalize
    rw [← hnormalize, ← mul_assoc, ← C_mul,
      Units.mul_inv, C_1, one_mul] at hu
    exact hu
  · rw [activeNormalizedPrivateIdeal, Ideal.span_le]
    rintro _ ⟨q, rfl⟩
    have hr : localizedPrivatePresentationHom
        root src dst active chart
        (universalOrientedCompatibilityEquation
          root src dst q.1.1 (chart q.1) q.2) ∈
        localizedActiveCompatibilityIdeal
          root src dst active chart := by
      apply Ideal.subset_span
      exact ⟨q, rfl⟩
    have hu := Ideal.mul_mem_left
      (localizedActiveCompatibilityIdeal root src dst active chart)
      (C (((retainedAngularUnit
        root src dst active chart q.1)⁻¹ :
          (RetainedCoefficientRing
            root src dst active chart)ˣ) :
          RetainedCoefficientRing root src dst active chart)) hr
    have hnormalize :=
      normalize_localized_universalTriangularResidual
        root src dst active chart hLoop q.1 q.2
    rw [universalTriangularResidual_eq_orientedCompatibilityEquation]
      at hnormalize
    rw [hnormalize] at hu
    exact hu

/-- Final active-compatibility height theorem in the concrete pin-outer
presentation: the original two compatibility equations per loopless active
occurrence have height at least `2 * active.card` after inverting exactly the
selected angular factors. -/
theorem localizedActiveCompatibilityIdeal_height_ge_twice_card
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) :
    letI : IsDomain (AngularCoefficientLocalization
        root src dst active chart) :=
      angularCoefficientLocalizationIsDomain
        root src dst active chart hLoop
    letI : Nontrivial (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : CommRing (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : IsDomain (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : CommRing (PrivatePresentationRing
        root src dst active chart) := inferInstance
    (active.card * 2 : ℕ) ≤
      (localizedActiveCompatibilityIdeal
        root src dst active chart).height := by
  letI : IsDomain (AngularCoefficientLocalization
      root src dst active chart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active chart hLoop
  letI : Nontrivial (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : IsDomain (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active chart) := inferInstance
  rw [localizedActiveCompatibilityIdeal_eq_activeNormalizedPrivateIdeal
    root src dst active chart hLoop]
  exact activeNormalizedPrivateIdeal_height_ge_twice_card
    root src dst active chart hLoop

end

end PinOuterActiveHeight

end RB31E2E


end
end BundleSource0027

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0027/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0027.json"

section BundleSource0028
/- Source: Papers/RigidityZheng_Linear_FiniteFamilyBaseChange.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/FiniteFamilyBaseChange.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/




@[expose] public section

/-!
# Rank of a finite vector family under field extension

The rank of a finite labelled family of vectors does not change after
applying an injective field extension coordinatewise.  This is the exact
base-change fact needed when the child configuration of the flag induction
lives in its own coordinate function field.
-/

namespace RB31E2E

namespace FiniteFamilyBaseChange

noncomputable section

open Set Submodule

variable {L K I J : Type*}
  [Field L] [Field K] [Algebra L K]
  [Fintype I] [Finite J]

/-- Coordinatewise extension of scalars for a vector in a finite function
space. -/
def mapVector (x : J → L) : J → K :=
  algebraMap L K ∘ x

omit [Fintype I] in
/-- The span rank of a finite vector family is invariant under a field
extension. -/
theorem finrank_span_range_mapVector (v : I → J → L) :
    Module.finrank L (span L (Set.range v)) =
      Module.finrank K (span K (Set.range (fun i ↦ mapVector (K := K) (v i)))) := by
  letI : FaithfulSMul L K :=
    (faithfulSMul_iff_algebraMap_injective L K).2 (RingHom.injective _)
  let vK : I → J → K := fun i ↦ mapVector (K := K) (v i)
  apply Nat.le_antisymm
  · obtain ⟨f, hfmem, hfspan, hfLI⟩ :=
      exists_fun_fin_finrank_span_eq L (Set.range v)
    let fK : Fin (Module.finrank L (span L (Set.range v))) → J → K :=
      fun i ↦ mapVector (K := K) (f i)
    have hfKLI : LinearIndependent K fK := by
      exact (linearIndependent_algebraMap_comp_iff).2 hfLI
    have hfKsub : span K (Set.range fK) ≤ span K (Set.range vK) := by
      apply span_mono
      rintro _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hfmem i
      refine ⟨j, ?_⟩
      dsimp [fK, vK, mapVector]
      exact congrArg (fun z : J → L ↦ algebraMap L K ∘ z) hj
    calc
      Module.finrank L (span L (Set.range v)) =
          Fintype.card (Fin (Module.finrank L (span L (Set.range v)))) := by
        simp
      _ = Module.finrank K (span K (Set.range fK)) := by
        symm
        exact finrank_span_eq_card hfKLI
      _ ≤ Module.finrank K (span K (Set.range vK)) :=
        Submodule.finrank_mono hfKsub
  · obtain ⟨g, hgmem, hgspan, hgLI⟩ :=
      exists_fun_fin_finrank_span_eq K (Set.range vK)
    choose idx hidx using hgmem
    have hgEq : g = fun i ↦ vK (idx i) := by
      funext i
      exact (hidx i).symm
    have hidxKLI : LinearIndependent K (fun i ↦ vK (idx i)) := by
      rw [← hgEq]
      exact hgLI
    have hidxLLI : LinearIndependent L (fun i ↦ v (idx i)) := by
      apply (linearIndependent_algebraMap_comp_iff
        (R := L) (S := K) (v := fun i ↦ v (idx i))).1
      simpa [vK, mapVector] using hidxKLI
    have hsub : span L (Set.range (fun i ↦ v (idx i))) ≤
        span L (Set.range v) := by
      apply span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨idx i, rfl⟩
    calc
      Module.finrank K (span K (Set.range vK)) =
          Fintype.card (Fin (Module.finrank K (span K (Set.range vK)))) := by
        simp
      _ = Module.finrank L
          (span L (Set.range (fun i ↦ v (idx i)))) := by
        symm
        exact finrank_span_eq_card hidxLLI
      _ ≤ Module.finrank L (span L (Set.range v)) :=
        Submodule.finrank_mono hsub

/-- The same rank-invariance statement for a family indexed by an arbitrary
finite type.  This is the form consumed by direction-row families. -/
theorem finrank_span_range_mapVector_finite
    {I' : Type*} [Finite I'] (v : I' → J → L) :
    Module.finrank L (span L (Set.range v)) =
      Module.finrank K
        (span K (Set.range (fun i ↦ mapVector (K := K) (v i)))) := by
  letI : Fintype I' := Fintype.ofFinite I'
  exact finrank_span_range_mapVector v

end

end FiniteFamilyBaseChange

end RB31E2E


end
end BundleSource0028

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0028/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0028.json"

section BundleSource0029
/- Source: Papers/RigidityZheng_Linear_FiniteRowSystem.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/FiniteRowSystem.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Finite row systems and their stress ledger

This file packages a finite family of row vectors as both a constraint map
and its transpose synthesis map.  It proves the exact rank--nullity ledger
and invariance of the solution-space dimension under field extension.
-/

namespace RB31E2E

namespace FiniteRowSystem

noncomputable section

variable {k L I J : Type*}
  [Field k] [Fintype I] [Fintype J]

/-- Matrix of a labelled finite row family. -/
def matrix (row : J → I → k) : Matrix J I k := row

/-- Evaluation of the row family on a coordinate vector. -/
def constraint (row : J → I → k) : (I → k) →ₗ[k] (J → k) :=
  (matrix row).mulVecLin

/-- Transpose synthesis of labelled row weights. -/
def synthesis (row : J → I → k) : (J → k) →ₗ[k] (I → k) :=
  (matrix row).transpose.mulVecLin

/-- Dimension of the row-relation/stress space. -/
def stressDim (row : J → I → k) : ℕ :=
  Module.finrank k (LinearMap.ker (synthesis row))

theorem finrank_range_constraint_eq_finrank_range_synthesis
    (row : J → I → k) :
    Module.finrank k (LinearMap.range (constraint row)) =
      Module.finrank k (LinearMap.range (synthesis row)) := by
  change (matrix row).rank = (matrix row).transpose.rank
  exact (Matrix.rank_transpose (matrix row)).symm

/-- Subtraction-free row/solution/stress dimension identity. -/
theorem solutionDim_add_rowCard_eq_coordinateCard_add_stressDim
    (row : J → I → k) :
    Module.finrank k (LinearMap.ker (constraint row)) + Fintype.card J =
      Fintype.card I + stressDim row := by
  have hc := (constraint row).finrank_range_add_finrank_ker
  have hs := (synthesis row).finrank_range_add_finrank_ker
  have hcrange := finrank_range_constraint_eq_finrank_range_synthesis row
  have hI : Module.finrank k (I → k) = Fintype.card I := by
    rw [Module.finrank_fintype_fun_eq_card]
  have hJ : Module.finrank k (J → k) = Fintype.card J := by
    rw [Module.finrank_fintype_fun_eq_card]
  rw [hI] at hc
  rw [hJ] at hs
  dsimp [stressDim]
  omega

variable [Field L] [Algebra k L]

/-- Coordinatewise scalar extension of a row family. -/
def mapRows (row : J → I → k) : J → I → L :=
  fun j ↦ FiniteFamilyBaseChange.mapVector (K := L) (row j)

omit [Fintype J] in
theorem constraint_mapRows_mapVector
    (row : J → I → k) (x : I → k) :
    constraint (mapRows (L := L) row)
        (FiniteFamilyBaseChange.mapVector (K := L) x) =
      FiniteFamilyBaseChange.mapVector (K := L) (constraint row x) := by
  funext j
  change (∑ i : I, algebraMap k L (row j i) * algebraMap k L (x i)) =
    algebraMap k L (∑ i : I, row j i * x i)
  simp only [map_sum, map_mul]

/-- The constraint kernel dimension is invariant under field extension. -/
theorem finrank_ker_constraint_mapRows
    (row : J → I → k) :
    Module.finrank L (LinearMap.ker (constraint (mapRows (L := L) row))) =
      Module.finrank k (LinearMap.ker (constraint row)) := by
  have hrank :
      Module.finrank L
          (Submodule.span L (Set.range (mapRows (L := L) row))) =
        Module.finrank k (Submodule.span k (Set.range row)) := by
    exact (FiniteFamilyBaseChange.finrank_span_range_mapVector row).symm
  have hL := (constraint (mapRows (L := L) row)).finrank_range_add_finrank_ker
  have hk := (constraint row).finrank_range_add_finrank_ker
  have hrangeL :
      Module.finrank L
          (LinearMap.range (constraint (mapRows (L := L) row))) =
        Module.finrank L
          (Submodule.span L (Set.range (mapRows (L := L) row))) := by
    change (matrix (mapRows (L := L) row)).rank = _
    rw [Matrix.rank_eq_finrank_span_row]
    rfl
  have hrangek :
      Module.finrank k (LinearMap.range (constraint row)) =
        Module.finrank k (Submodule.span k (Set.range row)) := by
    change (matrix row).rank = _
    rw [Matrix.rank_eq_finrank_span_row]
    rfl
  have hI_L : Module.finrank L (I → L) = Fintype.card I := by
    rw [Module.finrank_fintype_fun_eq_card]
  have hI_k : Module.finrank k (I → k) = Fintype.card I := by
    rw [Module.finrank_fintype_fun_eq_card]
  rw [hrangeL, hI_L] at hL
  rw [hrangek, hI_k] at hk
  omega

end

end FiniteRowSystem

end RB31E2E


end
end BundleSource0029

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0029/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0029.json"

section BundleSource0030
/- Source: Papers/RigidityZheng_Linear_DirectionStress.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/DirectionStress.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/




@[expose] public section

/-!
# Direction rows and their stress space

For a finite simple edge set `F` and a placement `a : V → k³`, this file
defines the transpose of the ordinary three-dimensional direction matrix as
an explicit linear map

`(F → k) →ₗ[k] (V → Fin 3 → k)`.

Its kernel is the direction-stress space used by the provenance-flag
induction.  The orientation chosen for an unordered edge is bookkeeping
only: a direction row has opposite endpoint loads, so reversing the
orientation leaves the row unchanged.  No sparsity, genericity,
semismallness, or height assertion is made here.
-/

namespace RB31E2E

namespace SimpleEdge

noncomputable section

variable {V : Type*}

/-- A bookkeeping source for an unordered simple edge. -/
def source (e : SimpleEdge V) : V :=
  e.1.out.1

/-- A bookkeeping target for an unordered simple edge. -/
def target (e : SimpleEdge V) : V :=
  e.1.out.2

/-- The chosen ordered endpoints recover the original unordered pair. -/
theorem source_target_mk (e : SimpleEdge V) :
    s(e.source, e.target) = e.1 :=
  Quot.out_eq e.1

/-- The two oriented endpoints of a simple edge are distinct. -/
theorem source_ne_target (e : SimpleEdge V) : e.source ≠ e.target := by
  intro h
  apply e.2
  rw [← e.source_target_mk, Sym2.mk_isDiag_iff]
  exact h

end


end SimpleEdge

namespace DirectionStress

noncomputable section

variable {k V : Type*} [Field k] [Fintype V] [DecidableEq V]

/-- The oriented difference vector carried by one simple edge. -/
def edgeDirection (a : V → Fin 3 → k) (e : SimpleEdge V) : Fin 3 → k :=
  fun j ↦ a e.source j - a e.target j

/--
The direction row of one edge, viewed as a load on all vertex-coordinate
blocks.  It is `a_source - a_target` at the source, its negative at the
target, and zero elsewhere.
-/
def directionRow (a : V → Fin 3 → k) (e : SimpleEdge V) :
    V → Fin 3 → k :=
  fun v j ↦
    (if e.source = v then edgeDirection a e j else 0) +
      (if e.target = v then -(edgeDirection a e j) else 0)

omit [Fintype V] in
@[simp]
theorem directionRow_source (a : V → Fin 3 → k) (e : SimpleEdge V) :
    directionRow a e e.source = edgeDirection a e := by
  funext j
  simp [directionRow, Ne.symm e.source_ne_target]

omit [Fintype V] in
@[simp]
theorem directionRow_target (a : V → Fin 3 → k) (e : SimpleEdge V) :
    directionRow a e e.target = -(edgeDirection a e) := by
  funext j
  simp [directionRow, e.source_ne_target]

omit [Fintype V] in
theorem directionRow_eq_zero_of_ne
    (a : V → Fin 3 → k) (e : SimpleEdge V) (v : V)
    (hsource : e.source ≠ v) (htarget : e.target ≠ v) :
    directionRow a e v = 0 := by
  funext j
  simp [directionRow, hsource, htarget]

/-- One coordinate of the endpoint-equilibrium load of edge weights. -/
def directionEquilibriumCoordinate
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k)
    (weight : F → k) (v : V) (j : Fin 3) : k :=
  ∑ e : F, weight e * directionRow a e.1 v j

/--
The transpose of the direction matrix.  It sends edge weights to the three
equilibrium coordinates at every vertex.
-/
def directionEquilibrium
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    (F → k) →ₗ[k] (V → Fin 3 → k) where
  toFun weight v j := directionEquilibriumCoordinate F a weight v j
  map_add' x y := by
    funext v j
    simp only [directionEquilibriumCoordinate, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rw [add_mul]
  map_smul' c x := by
    funext v j
    simp only [directionEquilibriumCoordinate, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [RingHom.id_apply, mul_assoc]

omit [Fintype V] in
@[simp]
theorem directionEquilibrium_apply
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k)
    (weight : F → k) (v : V) (j : Fin 3) :
    directionEquilibrium F a weight v j =
      directionEquilibriumCoordinate F a weight v j :=
  rfl

omit [Fintype V] in
/-- The equilibrium map is literally the linear combination of edge rows. -/
theorem directionEquilibrium_eq_sum_smul_directionRow
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (weight : F → k) :
    directionEquilibrium F a weight =
      ∑ e : F, weight e • directionRow a e.1 := by
  funext v j
  change (∑ e : F, weight e * directionRow a e.1 v j) =
    (∑ e : F, weight e • directionRow a e.1) v j
  simp

omit [Fintype V] in
/-- The range of the equilibrium synthesis map is exactly the span of the
labelled direction rows. -/
theorem range_directionEquilibrium_eq_span_directionRows
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    LinearMap.range (directionEquilibrium F a) =
      Submodule.span k (Set.range (fun e : F ↦ directionRow a e.1)) := by
  apply le_antisymm
  · rintro y ⟨weight, rfl⟩
    rw [directionEquilibrium_eq_sum_smul_directionRow]
    exact Submodule.sum_mem _ fun e _ ↦
      Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self e))
  · rw [Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    let weight : F → k := Pi.single e 1
    refine ⟨weight, ?_⟩
    rw [directionEquilibrium_eq_sum_smul_directionRow]
    change (∑ x ∈ F.attach,
      Pi.single e 1 x • directionRow a x.1) = directionRow a e.1
    rw [Finset.sum_eq_single e]
    · simp
    · intro b _ hbe
      simp [hbe]
    · intro he
      exact (he (Finset.mem_attach F e)).elim

/-- Pointwise equilibrium, with every vertex and spatial coordinate visible. -/
def IsDirectionStress
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (weight : F → k) : Prop :=
  ∀ v j, directionEquilibriumCoordinate F a weight v j = 0

/-- The actual direction-stress vector space. -/
abbrev DirectionStressSpace
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :=
  LinearMap.ker (directionEquilibrium F a)

omit [Fintype V] in
/-- Pointwise equilibrium is exactly membership in the explicit kernel. -/
theorem isDirectionStress_iff_mem
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (weight : F → k) :
    IsDirectionStress F a weight ↔ weight ∈ DirectionStressSpace F a := by
  constructor
  · intro h
    rw [LinearMap.mem_ker]
    funext v j
    exact h v j
  · intro h v j
    rw [LinearMap.mem_ker] at h
    have hv := congrFun (congrFun h v) j
    simpa using hv

/-- The finite dimension of the direction-stress space. -/
def directionStressDim
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) : ℕ :=
  Module.finrank k (DirectionStressSpace F a)

/-- The row rank of the direction matrix, read from its synthesis map. -/
def directionEquilibriumRank
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) : ℕ :=
  Module.finrank k (LinearMap.range (directionEquilibrium F a))

omit [Fintype V] in
/-- Row rank as the dimension of the span of the literal direction-row
family. -/
theorem directionEquilibriumRank_eq_finrank_span_rows
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    directionEquilibriumRank F a =
      Module.finrank k
        (Submodule.span k (Set.range (fun e : F ↦ directionRow a e.1))) := by
  rw [directionEquilibriumRank,
    range_directionEquilibrium_eq_span_directionRows]

/-- Rank--nullity with the edge-set cardinality kept explicit. -/
theorem directionEquilibriumRank_add_directionStressDim
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    directionEquilibriumRank F a + directionStressDim F a = F.card := by
  have h := (directionEquilibrium F a).finrank_range_add_finrank_ker
  have hdomain : Module.finrank k (F → k) = F.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  simpa [directionEquilibriumRank, directionStressDim,
    DirectionStressSpace, hdomain] using h

/-- The same rank--nullity identity with stress dimension first. -/
theorem directionStressDim_add_directionEquilibriumRank
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    directionStressDim F a + directionEquilibriumRank F a = F.card := by
  simpa [add_comm] using
    directionEquilibriumRank_add_directionStressDim F a

/-- Stress dimension never exceeds the number of live edges. -/
theorem directionStressDim_le_card
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    directionStressDim F a ≤ F.card := by
  calc
    directionStressDim F a ≤
        directionStressDim F a + directionEquilibriumRank F a :=
      Nat.le_add_right _ _
    _ = F.card := directionStressDim_add_directionEquilibriumRank F a

/-- Stress dimension is edge cardinality minus direction-row rank. -/
theorem directionStressDim_eq_card_sub_rank
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    directionStressDim F a = F.card - directionEquilibriumRank F a :=
  Nat.eq_sub_of_add_eq (directionStressDim_add_directionEquilibriumRank F a)

end

end DirectionStress

end RB31E2E


end
end BundleSource0030

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0030/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0030.json"

section BundleSource0031
/- Source: Papers/RigidityZheng_Linear_GroundedDirectionConstraint.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/GroundedDirectionConstraint.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/




@[expose] public section

/-!
# Grounded direction constraints

The translational projection of a grounded Split--Klein null system leaves
a linear system in the angular coordinates.  This file identifies that
system with the ordinary direction matrix and proves that deleting the root
load block does not change its stress space: every direction row has total
vertex load zero.
-/

namespace RB31E2E

namespace GroundedDirectionConstraint

noncomputable section

variable {k V : Type*} [Field k] [Fintype V] [DecidableEq V]

/-- The three coordinate labels at all non-root vertices. -/
abbrev GroundedSpatialCoordinate (root : V) := OffRoot root × Fin 3

/-- One ordinary direction row restricted to non-root vertex blocks. -/
def groundedDirectionRow (root : V) (a : V → Fin 3 → k)
    (e : SimpleEdge V) : GroundedSpatialCoordinate root → k :=
  fun x ↦ DirectionStress.directionRow a e x.1.1 x.2

/-- The grounded direction constraint map. -/
def constraint (root : V) (F : SimpleEdgeSet V)
    (a : V → Fin 3 → k) :
    (GroundedSpatialCoordinate root → k) →ₗ[k] (F → k) :=
  FiniteRowSystem.constraint
    (fun e : F ↦ groundedDirectionRow root a e.1)

/-- Transpose synthesis using only non-root output blocks. -/
def synthesis (root : V) (F : SimpleEdgeSet V)
    (a : V → Fin 3 → k) :
    (F → k) →ₗ[k] (GroundedSpatialCoordinate root → k) :=
  FiniteRowSystem.synthesis
    (fun e : F ↦ groundedDirectionRow root a e.1)

omit [Fintype V] in
theorem synthesis_apply
    (root : V) (F : SimpleEdgeSet V) (a : V → Fin 3 → k)
    (w : F → k) (x : GroundedSpatialCoordinate root) :
    synthesis root F a w x =
      DirectionStress.directionEquilibrium F a w x.1.1 x.2 := by
  change (∑ e : F, DirectionStress.directionRow a e.val x.1.val x.2 * w e) =
    ∑ e : F, w e * DirectionStress.directionRow a e.val x.1.val x.2
  apply Finset.sum_congr rfl
  intro e _
  exact mul_comm _ _

/-- Every direction row has total vertex load zero in each spatial
coordinate. -/
theorem sum_directionRow_eq_zero
    (a : V → Fin 3 → k) (e : SimpleEdge V) (j : Fin 3) :
    ∑ v : V, DirectionStress.directionRow a e v j = 0 := by
  rw [show (∑ v : V, DirectionStress.directionRow a e v j) =
      (∑ v : V, if e.source = v then
          DirectionStress.edgeDirection a e j else 0) +
        (∑ v : V, if e.target = v then
          -DirectionStress.edgeDirection a e j else 0) by
    simp only [DirectionStress.directionRow, Finset.sum_add_distrib]]
  have hs : (∑ v : V, if e.source = v then
      DirectionStress.edgeDirection a e j else 0) =
      DirectionStress.edgeDirection a e j := by
    have hfun : (fun v : V ↦ if e.source = v then
        DirectionStress.edgeDirection a e j else 0) =
        (fun v : V ↦ if v = e.source then
          DirectionStress.edgeDirection a e j else 0) := by
      funext v
      by_cases h : e.source = v
      · subst v
        simp
      · have hv : v ≠ e.source := Ne.symm h
        simp [h, hv]
    rw [hfun]
    simp
  have ht : (∑ v : V, if e.target = v then
      -DirectionStress.edgeDirection a e j else 0) =
      -DirectionStress.edgeDirection a e j := by
    have hfun : (fun v : V ↦ if e.target = v then
        -DirectionStress.edgeDirection a e j else 0) =
        (fun v : V ↦ if v = e.target then
          -DirectionStress.edgeDirection a e j else 0) := by
      funext v
      by_cases h : e.target = v
      · subst v
        simp
      · have hv : v ≠ e.target := Ne.symm h
        simp [h, hv]
    rw [hfun]
    simp
  rw [hs, ht, add_neg_cancel]

/-- Every synthesized equilibrium load has total vertex load zero. -/
theorem sum_directionEquilibrium_eq_zero
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k)
    (w : F → k) (j : Fin 3) :
    ∑ v : V, DirectionStress.directionEquilibrium F a w v j = 0 := by
  simp only [DirectionStress.directionEquilibrium_apply,
    DirectionStress.directionEquilibriumCoordinate]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _he
  rw [← Finset.mul_sum]
  rw [sum_directionRow_eq_zero, mul_zero]

/-- If all non-root blocks of an equilibrium load vanish, its root block
vanishes automatically. -/
theorem root_equilibrium_eq_zero_of_offRoot_eq_zero
    (root : V) (F : SimpleEdgeSet V) (a : V → Fin 3 → k)
    (w : F → k)
    (haway : ∀ x : OffRoot root,
      DirectionStress.directionEquilibrium F a w x.1 = 0) :
    DirectionStress.directionEquilibrium F a w root = 0 := by
  funext j
  have hsum := sum_directionEquilibrium_eq_zero F a w j
  have hsingle :
      (∑ v : V, DirectionStress.directionEquilibrium F a w v j) =
        DirectionStress.directionEquilibrium F a w root j := by
    rw [Finset.sum_eq_single root]
    · intro v _hv hvr
      have hv := congrFun (haway ⟨v, hvr⟩) j
      exact hv
    · simp
  rw [hsingle] at hsum
  exact hsum

/-- Restricting equilibrium output to non-root blocks preserves the stress
kernel literally. -/
theorem ker_synthesis_eq_directionStressSpace
    (root : V) (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    LinearMap.ker (synthesis root F a) =
      DirectionStress.DirectionStressSpace F a := by
  ext w
  simp only [LinearMap.mem_ker]
  constructor
  · intro hw
    funext v j
    by_cases hv : v = root
    · subst v
      exact congrFun
        (root_equilibrium_eq_zero_of_offRoot_eq_zero root F a w
          (fun x ↦ by
            funext q
            have hx := congrFun hw ⟨x, q⟩
            simpa [synthesis_apply] using hx)) j
    · have hx := congrFun hw ⟨⟨v, hv⟩, j⟩
      simpa [synthesis_apply] using hx
  · intro hw
    funext x
    have hx := congrFun (congrFun hw x.1.1) x.2
    simpa [synthesis_apply] using hx

theorem stressDim_eq_directionStressDim
    (root : V) (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    FiniteRowSystem.stressDim
        (fun e : F ↦ groundedDirectionRow root a e.1) =
      DirectionStress.directionStressDim F a := by
  change Module.finrank k (LinearMap.ker (synthesis root F a)) =
    Module.finrank k (DirectionStress.DirectionStressSpace F a)
  rw [ker_synthesis_eq_directionStressSpace]

set_option backward.isDefEq.respectTransparency false in
/-- Exact grounded solution/stress ledger. -/
theorem solutionDim_add_edgeCard_eq_groundedCard_add_stressDim
    (root : V) (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    Module.finrank k (LinearMap.ker (constraint root F a)) + F.card =
      Fintype.card (GroundedSpatialCoordinate root) +
        DirectionStress.directionStressDim F a := by
  have h := FiniteRowSystem.solutionDim_add_rowCard_eq_coordinateCard_add_stressDim
    (fun e : F ↦ groundedDirectionRow root a e.1)
  rw [stressDim_eq_directionStressDim, Fintype.card_coe] at h
  change Module.finrank k (LinearMap.ker (constraint root F a)) + F.card =
    Fintype.card (GroundedSpatialCoordinate root) +
      DirectionStress.directionStressDim F a at h
  exact h

end

end GroundedDirectionConstraint

end RB31E2E


end
end BundleSource0031

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0031/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0031.json"

section BundleSource0032
/- Source: Papers/RigidityZheng_NullCellule_WittShear.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/WittShear.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Angular-fixing Witt shears for the Split--Klein form

This file supplies the literal coordinate change used by the direct
selected-null height argument.  A shear fixes the angular half of a twist
and replaces its translational half by `v + ω × s`.  It is an automorphism,
with inverse parameter `-s`, and it preserves the Split--Klein form exactly.

The second half constructs the induced polynomial algebra equivalence on a
provenance-labelled family of twists.  No height, genericity, or
semismallness statement is assumed.
-/

namespace RB31E2E

namespace WittShear

noncomputable section

open MvPolynomial
open GroundedTwistPolynomial

/-! ## The six-dimensional linear shear -/

/-- The angular-fixing skew Witt shear with parameter `s`. -/
def shear {k : Type*} [CommRing k] (s : Vec3 k) (X : Twist k) : Twist k :=
  (X.1, X.2 + Vec3.cross X.1 s)

@[simp]
theorem shear_fst {k : Type*} [CommRing k]
    (s : Vec3 k) (X : Twist k) :
    (shear s X).1 = X.1 := rfl

@[simp]
theorem shear_snd {k : Type*} [CommRing k]
    (s : Vec3 k) (X : Twist k) :
    (shear s X).2 = X.2 + Vec3.cross X.1 s := rfl

theorem cross_neg_right {k : Type*} [CommRing k]
    (x s : Vec3 k) :
    Vec3.cross x (-s) = -Vec3.cross x s := by
  funext i
  fin_cases i <;> simp [Vec3.cross] <;> ring

theorem cross_sub_right {k : Type*} [CommRing k]
    (x s t : Vec3 k) :
    Vec3.cross x (s - t) = Vec3.cross x s - Vec3.cross x t := by
  funext i
  fin_cases i <;> simp [Vec3.cross] <;> ring

theorem shear_neg_apply_shear {k : Type*} [CommRing k]
    (s : Vec3 k) (X : Twist k) :
    shear (-s) (shear s X) = X := by
  apply Prod.ext
  · rfl
  · simp only [shear_snd, shear_fst, cross_neg_right]
    abel

theorem shear_apply_shear_neg {k : Type*} [CommRing k]
    (s : Vec3 k) (X : Twist k) :
    shear s (shear (-s) X) = X := by
  simpa only [neg_neg] using shear_neg_apply_shear (-s) X

/-- The shear is additive. -/
theorem shear_add {k : Type*} [CommRing k]
    (s : Vec3 k) (X Y : Twist k) :
    shear s (X + Y) = shear s X + shear s Y := by
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i <;> simp [shear, Vec3.cross] <;> ring

/-- The shear commutes with differences. -/
theorem shear_sub {k : Type*} [CommRing k]
    (s : Vec3 k) (X Y : Twist k) :
    shear s (X - Y) = shear s X - shear s Y := by
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i <;> simp [shear, Vec3.cross] <;> ring

/-- If a twist is nonzero, a one-parameter skew shear can make its
translational half nonzero over any infinite field.  The parameter is a
scalar multiple of an explicitly chosen coordinate axis. -/
theorem exists_scalar_shear_snd_ne_zero
    {k : Type*} [Field k] [Infinite k]
    (X : Twist k) (hX : X ≠ 0) :
    ∃ (r : k) (axis : Fin 3),
      (shear (r • GroundedTwistPolynomial.coordinateUnit axis) X).2 ≠ 0 := by
  by_cases hv : X.2 ≠ 0
  · refine ⟨0, 0, ?_⟩
    intro hs
    apply hv
    have hz : Vec3.cross X.1 (0 : Vec3 k) = 0 := by
      funext i
      fin_cases i <;> simp [Vec3.cross]
    change X.2 + Vec3.cross X.1
      (0 • GroundedTwistPolynomial.coordinateUnit 0) = 0 at hs
    simpa only [zero_smul, hz, add_zero] using hs
  have hv0 : X.2 = 0 := not_ne_iff.mp hv
  have hω : X.1 ≠ 0 := by
    intro hω
    apply hX
    apply Prod.ext
    · exact hω
    · exact hv0
  have hcross : ∃ axis : Fin 3,
      Vec3.cross X.1 (GroundedTwistPolynomial.coordinateUnit axis) ≠ 0 := by
    by_contra h
    have hzero : ∀ axis : Fin 3,
        Vec3.cross X.1
          (GroundedTwistPolynomial.coordinateUnit axis) = 0 := by
      intro axis
      exact not_ne_iff.mp (not_exists.mp h axis)
    have h0 : X.1 0 = 0 := by
      have hz := congrFun (hzero 1) 2
      simpa [Vec3.cross, GroundedTwistPolynomial.coordinateUnit] using hz
    have h1 : X.1 1 = 0 := by
      have hz := congrFun (hzero 2) 0
      simpa [Vec3.cross, GroundedTwistPolynomial.coordinateUnit] using hz
    have h2 : X.1 2 = 0 := by
      have hz := congrFun (hzero 0) 1
      simpa [Vec3.cross, GroundedTwistPolynomial.coordinateUnit] using hz
    apply hω
    funext i
    fin_cases i <;> assumption
  obtain ⟨axis, haxis⟩ := hcross
  exact ⟨1, axis, by
    simpa [shear, hv0, Vec3.cross_smul_left] using haxis⟩

/-! ## One common base-field shear for a finite family -/

/-- The cubic moment curve in the three-dimensional shear-parameter
space. -/
def momentCurve {k : Type*} [CommRing k] (r : k) : Vec3 k :=
  fun i ↦ r ^ (i.val + 1)

/-- Polynomial version of the same moment curve. -/
def polynomialMomentCurve {K : Type*} [CommRing K] :
    Vec3 (Polynomial K) :=
  fun i ↦ Polynomial.X ^ (i.val + 1)

/-- Translational half of a twist sheared by the polynomial moment curve. -/
def polynomialShearSnd {K : Type*} [CommRing K] (Z : Twist K) :
    Vec3 (Polynomial K) :=
  fun i ↦ Polynomial.C (Z.2 i) +
    Vec3.cross (fun j ↦ Polynomial.C (Z.1 j))
      polynomialMomentCurve i

theorem vecHead_eq_apply_zero {K : Type*} (v : Fin 3 → K) :
    Matrix.vecHead v = v 0 := rfl

theorem vecHead_tail_eq_apply_one {K : Type*} (v : Fin 3 → K) :
    Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl

theorem vecHead_tail_tail_eq_apply_two {K : Type*} (v : Fin 3 → K) :
    Matrix.vecHead (Matrix.vecTail (Matrix.vecTail v)) = v 2 := rfl

theorem eval_polynomialShearSnd
    {K : Type*} [CommRing K] (Z : Twist K) (r : K) (i : Fin 3) :
    Polynomial.eval r (polynomialShearSnd Z i) =
      (shear (momentCurve r) Z).2 i := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;>
    simp [polynomialShearSnd, polynomialMomentCurve, momentCurve,
      shear, Vec3.cross, Fin.isValue, vecHead_eq_apply_zero,
      vecHead_tail_eq_apply_one, vecHead_tail_tail_eq_apply_two]

/-- A nonzero twist gives a nonzero scalar polynomial among the three
coordinates of its moment-curve shear. -/
theorem exists_polynomialShearSnd_ne_zero
    {K : Type*} [Field K] (Z : Twist K) (hZ : Z ≠ 0) :
    ∃ i : Fin 3, polynomialShearSnd Z i ≠ 0 := by
  by_cases hv : Z.2 ≠ 0
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    refine ⟨i, fun h ↦ hi ?_⟩
    have he := congrArg (Polynomial.eval 0) h
    have hz := eval_polynomialShearSnd Z 0 i
    rw [h] at hz
    simp only [Polynomial.eval_zero] at hz
    have hs : (shear (momentCurve 0) Z).2 = Z.2 := by
      funext j
      rcases j with ⟨j, hj⟩
      interval_cases j <;>
        simp [shear, momentCurve, Vec3.cross, Fin.isValue,
          vecHead_eq_apply_zero, vecHead_tail_eq_apply_one,
          vecHead_tail_tail_eq_apply_two]
    rw [hs] at hz
    exact hz.symm
  have hv0 : Z.2 = 0 := not_ne_iff.mp hv
  have hω : Z.1 ≠ 0 := by
    intro hω
    apply hZ
    exact Prod.ext hω hv0
  by_cases h0 : Z.1 0 ≠ 0
  · refine ⟨2, fun h ↦ h0 ?_⟩
    have hc := congrArg (fun p : Polynomial K ↦ p.coeff 2) h
    simpa [polynomialShearSnd, polynomialMomentCurve, Vec3.cross,
      hv0] using hc
  have h0z : Z.1 0 = 0 := not_ne_iff.mp h0
  by_cases h1 : Z.1 1 ≠ 0
  · refine ⟨0, fun h ↦ h1 ?_⟩
    have hc := congrArg (fun p : Polynomial K ↦ p.coeff 3) h
    simpa [polynomialShearSnd, polynomialMomentCurve, Vec3.cross,
      hv0] using hc
  have h1z : Z.1 1 = 0 := not_ne_iff.mp h1
  have h2 : Z.1 2 ≠ 0 := by
    intro h2
    apply hω
    funext i
    fin_cases i <;> assumption
  refine ⟨1, fun h ↦ h2 ?_⟩
  have hc := congrArg (fun p : Polynomial K ↦ p.coeff 1) h
  simpa [polynomialShearSnd, polynomialMomentCurve, Vec3.cross,
    hv0, h0z, h1z] using hc

/-- A nonzero polynomial over an extension field is nonzero at some point
coming from the infinite base field. -/
theorem exists_base_eval_ne_zero
    {k K : Type*} [Field k] [Infinite k] [Field K] [Algebra k K]
    (p : Polynomial K) (hp : p ≠ 0) :
    ∃ r : k, Polynomial.eval (algebraMap k K r) p ≠ 0 := by
  by_contra h
  push Not at h
  have hinf : Set.Infinite (Set.range (algebraMap k K)) :=
    Set.infinite_range_of_injective (RingHom.injective (algebraMap k K))
  have hzeroSet : Set.range (algebraMap k K) ⊆
      {x : K | Polynomial.eval x p = Polynomial.eval x 0} := by
    rintro _ ⟨r, rfl⟩
    simpa using h r
  have heval : Set.Infinite
      {x : K | Polynomial.eval x p = Polynomial.eval x 0} :=
    hinf.mono hzeroSet
  exact hp (Polynomial.eq_of_infinite_eval_eq p 0 heval)

/-- A finite family of nonzero twists over an extension field admits one
common shear whose parameter lies in the infinite base field and whose
translational half is nonzero for every member. -/
theorem exists_common_base_shear_snd_ne_zero
    {k K I : Type*} [Field k] [Infinite k]
    [Field K] [Algebra k K] [Fintype I]
    (Z : I → Twist K) (hZ : ∀ i, Z i ≠ 0) :
    ∃ s : Vec3 k, ∀ i,
      (shear (fun j ↦ algebraMap k K (s j)) (Z i)).2 ≠ 0 := by
  classical
  choose c hc using fun i ↦ exists_polynomialShearSnd_ne_zero (Z i) (hZ i)
  let q : I → Polynomial K := fun i ↦ polynomialShearSnd (Z i) (c i)
  have hq (i : I) : q i ≠ 0 := hc i
  let Q : Polynomial K := ∏ i : I, q i
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ hq i
  obtain ⟨r, hr⟩ := exists_base_eval_ne_zero (k := k) Q hQ
  refine ⟨momentCurve r, fun i hi ↦ ?_⟩
  apply hr
  dsimp [Q]
  change (Polynomial.evalRingHom (algebraMap k K r))
      (∏ i : I, q i) = 0
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hcoord := congrFun hi (c i)
  have hs : (fun j ↦ algebraMap k K (momentCurve r j)) =
      momentCurve (algebraMap k K r) := by
    funext j
    rcases j with ⟨j, hj⟩
    interval_cases j <;> simp [momentCurve, map_pow]
  rw [hs] at hcoord
  rw [← eval_polynomialShearSnd (Z i) (algebraMap k K r) (c i)] at hcoord
  simpa [q] using hcoord

/-- A skew Witt shear preserves the Split--Klein quadratic form literally. -/
@[simp]
theorem splitKlein_shear {k : Type*} [CommRing k]
    (s : Vec3 k) (X : Twist k) :
    Twist.splitKlein (shear s X) = Twist.splitKlein X := by
  simp only [Twist.splitKlein, shear_fst, shear_snd, Vec3.dot,
    Pi.add_apply, mul_add, Finset.sum_add_distrib]
  change Twist.splitKlein X + Vec3.dot X.1 (Vec3.cross X.1 s) =
    Twist.splitKlein X
  rw [Vec3.dot_cross_self_left, add_zero]

/-! ## The induced polynomial algebra equivalence -/

/-- Six coordinate variables for each provenance label. -/
abbrev Variable (U : Type*) := U × TwistCoordinate

/-- The universal twist carried by one label. -/
def universalTwist {k U : Type*} [CommRing k] (u : U) :
    Twist (MvPolynomial (Variable U) k) :=
  (λ i ↦ X ⟨u, ⟨false, i⟩⟩, λ i ↦ X ⟨u, ⟨true, i⟩⟩)

/-- Coordinate assignment defining the polynomial Witt shear. -/
def coordinateImage {k U : Type*} [CommRing k]
    (s : Vec3 k) : Variable U → MvPolynomial (Variable U) k
  | ⟨u, false, i⟩ => X ⟨u, ⟨false, i⟩⟩
  | ⟨u, true, i⟩ =>
      X ⟨u, ⟨true, i⟩⟩ +
        (Vec3.cross (universalTwist (k := k) u).1
          (fun j ↦ C (s j))) i

/-- Polynomial endomorphism induced by the Witt shear. -/
def hom {k U : Type*} [CommRing k] (s : Vec3 k) :
    MvPolynomial (Variable U) k →ₐ[k] MvPolynomial (Variable U) k :=
  MvPolynomial.aeval (coordinateImage s)

@[simp]
theorem hom_angular_X {k U : Type*} [CommRing k]
    (s : Vec3 k) (u : U) (i : Fin 3) :
    hom s (X ⟨u, ⟨false, i⟩⟩) = X ⟨u, ⟨false, i⟩⟩ := by
  simp [hom, coordinateImage]

@[simp]
theorem hom_translational_X {k U : Type*} [CommRing k]
    (s : Vec3 k) (u : U) (i : Fin 3) :
    hom s (X ⟨u, ⟨true, i⟩⟩) =
      X ⟨u, ⟨true, i⟩⟩ +
        (Vec3.cross (universalTwist (k := k) u).1
          (fun j ↦ C (s j))) i := by
  simp [hom, coordinateImage]

theorem map_cross_universal_angular
    {k U : Type*} [CommRing k]
    (s t : Vec3 k) (u : U) (i : Fin 3) :
    hom s
        ((Vec3.cross (universalTwist (k := k) u).1
          (fun j ↦ C (t j))) i) =
      (Vec3.cross (universalTwist (k := k) u).1
        (fun j ↦ C (t j))) i := by
  fin_cases i <;>
    simp [hom, coordinateImage, universalTwist, Vec3.cross]

theorem hom_comp_neg {k U : Type*} [CommRing k] (s : Vec3 k) :
    (hom (U := U) s).comp (hom (U := U) (-s)) =
      AlgHom.id k (MvPolynomial (Variable U) k) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨u, ⟨b, i⟩⟩
  cases b
  · simp
  · rw [AlgHom.comp_apply, hom_translational_X, map_add,
      hom_translational_X, map_cross_universal_angular]
    rw [show (fun j ↦ C ((-s) j)) =
        -(fun j ↦ C (s j)) by funext j; simp]
    rw [cross_neg_right]
    simp only [Pi.neg_apply]
    simp

theorem hom_neg_comp {k U : Type*} [CommRing k] (s : Vec3 k) :
    (hom (U := U) (-s)).comp (hom (U := U) s) =
      AlgHom.id k (MvPolynomial (Variable U) k) := by
  simpa only [neg_neg] using hom_comp_neg (U := U) (-s)

/-- The polynomial algebra automorphism induced by a Witt shear. -/
def algEquiv {k U : Type*} [CommRing k] (s : Vec3 k) :
    MvPolynomial (Variable U) k ≃ₐ[k] MvPolynomial (Variable U) k :=
  AlgEquiv.ofAlgHom (hom s) (hom (-s))
    (hom_comp_neg s) (hom_neg_comp s)

@[simp]
theorem algEquiv_apply {k U : Type*} [CommRing k]
    (s : Vec3 k) (f : MvPolynomial (Variable U) k) :
    algEquiv s f = hom s f := rfl

theorem map_universalTwist {k U : Type*} [CommRing k]
    (s : Vec3 k) (u : U) :
    mapTwist (algEquiv s).toRingEquiv.toRingHom
        (universalTwist (k := k) u) =
      shear (fun j ↦ C (s j)) (universalTwist (k := k) u) := by
  apply Prod.ext <;> funext i
  · change algEquiv s (X ⟨u, ⟨false, i⟩⟩) = X ⟨u, ⟨false, i⟩⟩
    exact hom_angular_X s u i
  · change algEquiv s (X ⟨u, ⟨true, i⟩⟩) =
      X ⟨u, ⟨true, i⟩⟩ +
        (Vec3.cross (universalTwist (k := k) u).1
          (fun j ↦ C (s j))) i
    exact hom_translational_X s u i

theorem map_splitKlein {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (Z : Twist R) :
    f (Twist.splitKlein Z) = Twist.splitKlein (mapTwist f Z) := by
  simp [Twist.splitKlein, Vec3.dot, mapTwist, mapVec3]

/-- Every labelled Split--Klein difference polynomial is fixed. -/
theorem algEquiv_splitKlein_sub {k U : Type*} [CommRing k]
    (s : Vec3 k) (u v : U) :
    algEquiv s
        (Twist.splitKlein
          (universalTwist (k := k) u - universalTwist (k := k) v)) =
      Twist.splitKlein
        (universalTwist (k := k) u - universalTwist (k := k) v) := by
  have hmap : mapTwist (algEquiv s).toRingEquiv.toRingHom
      (universalTwist (k := k) u - universalTwist (k := k) v) =
      shear (fun j ↦ C (s j))
        (universalTwist (k := k) u - universalTwist (k := k) v) := by
    rw [mapTwist_sub, map_universalTwist, map_universalTwist, ← shear_sub]
  change (algEquiv s).toRingEquiv.toRingHom
      (Twist.splitKlein
        (universalTwist (k := k) u - universalTwist (k := k) v)) = _
  rw [map_splitKlein, hmap, splitKlein_shear]

end

end WittShear

end RB31E2E


end
end BundleSource0032

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0032/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0032.json"

section BundleSource0033
/- Source: Papers/RigidityZheng_NullCellule_GroundedTwistSplit.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/GroundedTwistSplit.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/






@[expose] public section

/-!
# Angular/translational splitting of grounded twists

The grounded six-coordinate polynomial ring is rewritten as a polynomial
ring in angular coordinates over the polynomial ring in translational
coordinates.  A Split--Klein null equation then becomes a literal linear
form in the angular variables, with the ordinary grounded direction row as
its coefficient vector.
-/

namespace RB31E2E

namespace GroundedTwistSplit

noncomputable section

open MvPolynomial
open GroundedTwistPolynomial
open PinOuterActiveHeight
open LinearFormIdeal
open UniversalHomogeneousChart

/-- Three spatial coordinates at every non-root body.  The same label type
is used once in the coefficient layer and once in the outer layer. -/
abbrev SpatialVariable {V : Type*} (root : V) := OffRoot root × Fin 3

/-- Angular variables are the left summand and translational variables are
the right summand. -/
def splitIndexEquiv {V : Type*} (root : V) :
    SpatialVariable root ⊕ SpatialVariable root ≃
      GroundedTwistVariable root where
  toFun
    | Sum.inl x => ⟨x.1, ⟨false, x.2⟩⟩
    | Sum.inr x => ⟨x.1, ⟨true, x.2⟩⟩
  invFun x := if x.2.1 then
      Sum.inr ⟨x.1, x.2.2⟩
    else Sum.inl ⟨x.1, x.2.2⟩
  left_inv x := by
    cases x with
    | inl x => rfl
    | inr x => rfl
  right_inv x := by
    rcases x with ⟨w, ⟨b, i⟩⟩
    cases b <;> rfl

/-- The explicit iterated polynomial presentation
`Q[translational][angular] ≃ Q[angular,translational]`. -/
def splitEquiv {k V : Type*} [CommRing k] (root : V) :
    MvPolynomial (SpatialVariable root)
        (MvPolynomial (SpatialVariable root) k) ≃ₐ[k]
      MvPolynomial (GroundedTwistVariable root) k :=
  (MvPolynomial.sumAlgEquiv k
      (SpatialVariable root) (SpatialVariable root)).symm |>.trans
    (MvPolynomial.renameEquiv k (splitIndexEquiv root))

/-- Linear polynomial over an arbitrary commutative coefficient ring.  The
field-specialized version is `LinearFormIdeal.linearPolynomial`. -/
def coefficientLinearPolynomial
    {A I : Type*} [CommRing A] [Fintype I]
    (v : I → A) : MvPolynomial I A :=
  ∑ i, C (v i) * X i

@[simp] theorem splitEquiv_angular_X
    {k V : Type*} [CommRing k] (root : V)
    (x : SpatialVariable root) :
    splitEquiv (k := k) root (X x) =
      X ⟨x.1, ⟨false, x.2⟩⟩ := by
  change MvPolynomial.rename (splitIndexEquiv root)
    ((MvPolynomial.sumAlgEquiv k (SpatialVariable root)
      (SpatialVariable root)).symm (X x)) = _
  rw [MvPolynomial.sumAlgEquiv_symm_X, MvPolynomial.rename_X]
  rfl

@[simp] theorem splitEquiv_translational_C_X
    {k V : Type*} [CommRing k] (root : V)
    (x : SpatialVariable root) :
    splitEquiv (k := k) root (C (X x)) =
      X ⟨x.1, ⟨true, x.2⟩⟩ := by
  change MvPolynomial.rename (splitIndexEquiv root)
    ((MvPolynomial.sumAlgEquiv k (SpatialVariable root)
      (SpatialVariable root)).symm (C (X x))) = _
  rw [MvPolynomial.sumAlgEquiv_symm_C_X, MvPolynomial.rename_X]
  rfl

/-- One universal off-root twist in the iterated presentation. -/
def iteratedOffRootTwist
    {k V : Type*} [CommRing k] {root : V} (w : OffRoot root) :
    Twist (MvPolynomial (SpatialVariable root)
      (MvPolynomial (SpatialVariable root) k)) :=
  ⟨fun i ↦ X ⟨w, i⟩, fun i ↦ C (X ⟨w, i⟩)⟩

/-- Root-zero universal twists in the iterated presentation. -/
def iteratedGroundedTwist
    {k V : Type*} [CommRing k] [DecidableEq V] (root : V) :
    V → Twist (MvPolynomial (SpatialVariable root)
      (MvPolynomial (SpatialVariable root) k)) :=
  extendOffRoot root (iteratedOffRootTwist (k := k))

theorem map_iteratedOffRootTwist
    {V : Type*} {root : V} (w : OffRoot root) :
    mapTwist (splitEquiv (k := ℚ) root).toRingEquiv.toRingHom
        (iteratedOffRootTwist (k := ℚ) w) =
      coefficientOffRootTwist w := by
  apply Prod.ext <;> funext i <;> simp [iteratedOffRootTwist,
    coefficientOffRootTwist, mapTwist, mapVec3]

theorem map_iteratedGroundedTwist
    {V : Type*} [DecidableEq V] (root v : V) :
    mapTwist (splitEquiv (k := ℚ) root).toRingEquiv.toRingHom
        (iteratedGroundedTwist (k := ℚ) root v) =
      coefficientGroundedTwist root v := by
  by_cases hv : v = root
  · subst v
    simp [iteratedGroundedTwist, coefficientGroundedTwist,
      extendOffRoot, mapTwist_zero]
  · unfold iteratedGroundedTwist coefficientGroundedTwist extendOffRoot
    rw [dif_neg hv, dif_neg hv]
    exact map_iteratedOffRootTwist ⟨v, hv⟩

/-- The oriented occurrence direction row, restricted to non-root blocks. -/
def occurrenceDirectionRow
    {k V E : Type*} [CommRing k] [DecidableEq V]
    (root : V) (src dst : E → V) (a : V → Fin 3 → k) (e : E) :
    SpatialVariable root → k :=
  fun x ↦
    (if src e = x.1.1 then a (src e) x.2 - a (dst e) x.2 else 0) +
      (if dst e = x.1.1 then -(a (src e) x.2 - a (dst e) x.2) else 0)

/-- Universal translational placement in the coefficient polynomial ring. -/
def coefficientPlacement
    {k V : Type*} [CommRing k] [DecidableEq V] (root : V) :
    V → Fin 3 → MvPolynomial (SpatialVariable root) k :=
  fun v i ↦ if h : v = root then 0 else X ⟨⟨v, h⟩, i⟩

theorem coefficientPlacement_root
    {k V : Type*} [CommRing k] [DecidableEq V] (root : V) :
    coefficientPlacement (k := k) root root = 0 := by
  funext i
  simp [coefficientPlacement]

theorem iteratedGroundedTwist_fst
    {k V : Type*} [CommRing k] [DecidableEq V] (root v : V) (i : Fin 3) :
    (iteratedGroundedTwist (k := k) root v).1 i =
      if h : v = root then 0 else X ⟨⟨v, h⟩, i⟩ := by
  by_cases hv : v = root <;>
    simp [iteratedGroundedTwist, iteratedOffRootTwist,
      extendOffRoot, hv]

theorem iteratedGroundedTwist_snd
    {k V : Type*} [CommRing k] [DecidableEq V] (root v : V) (i : Fin 3) :
    (iteratedGroundedTwist (k := k) root v).2 i =
      C (coefficientPlacement (k := k) root v i) := by
  by_cases hv : v = root <;>
    simp [iteratedGroundedTwist, iteratedOffRootTwist,
      coefficientPlacement, extendOffRoot, hv]

/-- Universal angular coordinate, with the grounded body set to zero. -/
def angularCoordinate
    {k V : Type*} [CommRing k] [DecidableEq V] (root : V) :
    V → Fin 3 →
      MvPolynomial (SpatialVariable root)
        (MvPolynomial (SpatialVariable root) k) :=
  fun v i ↦ if h : v = root then 0 else X ⟨⟨v, h⟩, i⟩

theorem iteratedGroundedTwist_fst_eq_angularCoordinate
    {k V : Type*} [CommRing k] [DecidableEq V] (root v : V) :
    (iteratedGroundedTwist (k := k) root v).1 =
      angularCoordinate (k := k) root v := by
  funext i
  exact iteratedGroundedTwist_fst root v i

/-- A finite sum over the off-root subtype selects the unique term whose
underlying body is a prescribed non-root body. -/
theorem sum_X_C_if_eq_offRoot
    {k V : Type*} [CommRing k] [Fintype V] [DecidableEq V]
    (root v : V) (hv : v ≠ root) (j : Fin 3)
    (q : MvPolynomial (SpatialVariable root) k) :
    ∑ w : OffRoot root,
        (X (⟨w, j⟩ : SpatialVariable root) :
          MvPolynomial (SpatialVariable root)
            (MvPolynomial (SpatialVariable root) k)) *
          C (if v = w.1 then q else 0) =
      (X (⟨⟨v, hv⟩, j⟩ : SpatialVariable root) :
        MvPolynomial (SpatialVariable root)
          (MvPolynomial (SpatialVariable root) k)) * C q := by
  classical
  have hterm : ∀ w : OffRoot root,
      (if v = w.1 then q else 0) =
        if w = ⟨v, hv⟩ then q else 0 := by
    intro w
    by_cases h : v = w.1
    · have hw : w = ⟨v, hv⟩ := by
        apply Subtype.ext
        exact h.symm
      rw [if_pos h, if_pos hw]
    · have hw : w ≠ ⟨v, hv⟩ := by
        intro hw
        apply h
        simp [hw]
      rw [if_neg h, if_neg hw]
  have hprod : ∀ w : OffRoot root,
      (X (⟨w, j⟩ : SpatialVariable root) :
          MvPolynomial (SpatialVariable root)
            (MvPolynomial (SpatialVariable root) k)) *
          C (if w = ⟨v, hv⟩ then q else 0) =
        if w = ⟨v, hv⟩ then
          X (⟨w, j⟩ : SpatialVariable root) * C q else 0 := by
    intro w
    by_cases hw : w = ⟨v, hv⟩
    · rw [if_pos hw, if_pos hw]
    · rw [if_neg hw, if_neg hw]
      simp
  simp_rw [hterm, hprod]
  rw [Fintype.sum_ite_eq']

/-- No member of the off-root subtype has underlying body equal to the
root. -/
theorem sum_X_C_if_root_eq
    {k V : Type*} [CommRing k] [Fintype V] [DecidableEq V]
    (root : V) (j : Fin 3)
    (q : MvPolynomial (SpatialVariable root) k) :
    ∑ w : OffRoot root,
        (X (⟨w, j⟩ : SpatialVariable root) :
          MvPolynomial (SpatialVariable root)
            (MvPolynomial (SpatialVariable root) k)) *
          C (if root = w.1 then q else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro w _hw
  have hrw : root ≠ w.1 := fun h ↦ w.2 h.symm
  simp [hrw]

/-- One spatial-coordinate slice of the grounded occurrence row. -/
theorem sum_occurrenceDirectionRow_mul_X
    {k V E : Type*} [CommRing k] [Fintype V] [DecidableEq V]
    (root : V) (src dst : E → V) (e : E)
    (hLoop : src e ≠ dst e) (j : Fin 3) :
    ∑ w : OffRoot root,
        C (occurrenceDirectionRow root src dst
          (coefficientPlacement (k := k) root) e ⟨w, j⟩) * X ⟨w, j⟩ =
      (angularCoordinate (k := k) root (src e) j -
          angularCoordinate (k := k) root (dst e) j) *
        C (coefficientPlacement (k := k) root (src e) j -
          coefficientPlacement (k := k) root (dst e) j) := by
  classical
  simp only [occurrenceDirectionRow, map_add, add_mul,
    Finset.sum_add_distrib]
  by_cases hs : src e = root
  · have hd : dst e ≠ root := fun hd ↦ hLoop (hs.trans hd.symm)
    simp [angularCoordinate, coefficientPlacement, hs, hd, mul_comm,
      sum_X_C_if_root_eq, sum_X_C_if_eq_offRoot]
    ring
  · by_cases hd : dst e = root
    · simp [angularCoordinate, coefficientPlacement, hs, hd, mul_comm,
        sum_X_C_if_root_eq, sum_X_C_if_eq_offRoot]
    · simp [angularCoordinate, coefficientPlacement, hs, hd, mul_comm,
        sum_X_C_if_eq_offRoot]
      ring

/-- Summing one oriented row over grounded angular variables recovers the
corresponding angular/translational dot product. -/
theorem linearPolynomial_occurrenceDirectionRow
    {k V E : Type*} [CommRing k] [Fintype V] [DecidableEq V]
    (root : V) (src dst : E → V) (e : E)
    (hLoop : src e ≠ dst e) :
    coefficientLinearPolynomial
        (occurrenceDirectionRow root src dst
          (coefficientPlacement (k := k) root) e) =
      Twist.splitKlein
        (iteratedGroundedTwist (k := k) root (src e) -
          iteratedGroundedTwist (k := k) root (dst e)) := by
  classical
  simp only [coefficientLinearPolynomial, Twist.splitKlein, Vec3.dot,
    Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [sum_occurrenceDirectionRow_mul_X root src dst e hLoop j]
  rw [iteratedGroundedTwist_fst_eq_angularCoordinate,
    iteratedGroundedTwist_fst_eq_angularCoordinate,
    iteratedGroundedTwist_snd, iteratedGroundedTwist_snd]
  rw [map_sub]

/-- A grounded Split--Klein occurrence equation becomes the literal linear
form of its grounded direction row. -/
theorem splitEquiv_symm_splitKlein_coefficientRelativeTwist
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (src dst : E → V) (e : E)
    (hLoop : src e ≠ dst e) :
    (splitEquiv (k := ℚ) root).symm
        (Twist.splitKlein
          (coefficientRelativeTwist root src dst e)) =
      coefficientLinearPolynomial
        (occurrenceDirectionRow root src dst
          (coefficientPlacement (k := ℚ) root) e) := by
  apply (splitEquiv (k := ℚ) root).injective
  rw [(splitEquiv (k := ℚ) root).apply_symm_apply]
  rw [linearPolynomial_occurrenceDirectionRow root src dst e hLoop]
  change Twist.splitKlein (coefficientRelativeTwist root src dst e) =
    splitEquiv (k := ℚ) root
      (Twist.splitKlein
        (iteratedGroundedTwist (k := ℚ) root (src e) -
          iteratedGroundedTwist (k := ℚ) root (dst e)))
  let Z := iteratedGroundedTwist (k := ℚ) root (src e) -
    iteratedGroundedTwist (k := ℚ) root (dst e)
  calc
    Twist.splitKlein (coefficientRelativeTwist root src dst e) =
        Twist.splitKlein
          (mapTwist (splitEquiv (k := ℚ) root).toRingEquiv.toRingHom Z) := by
      congr 1
      simp only [Z, coefficientRelativeTwist, mapTwist_sub]
      rw [map_iteratedGroundedTwist, map_iteratedGroundedTwist]
    _ = (splitEquiv (k := ℚ) root) (Twist.splitKlein Z) :=
      (WittShear.map_splitKlein
        (splitEquiv (k := ℚ) root).toRingEquiv.toRingHom Z).symm

end

end GroundedTwistSplit

end RB31E2E


end
end BundleSource0033

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0033/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0033.json"

section BundleSource0034
/- Source: Papers/RigidityZheng_Incidence_UniversalActivePinHeightTransfer.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Incidence/UniversalActivePinHeightTransfer.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Universal active-pin height transfer

This file identifies the exact point at which the private-coordinate height
calculus meets the finite generic universal chart.

First, the base-changed chart ideal is split, without any hypothesis, into
the image of its active compatibility ideal and the image of its selected
null ideal.  The active summand is generated by the actual finite-generic
compatibility polynomials, with the occurrence/coordinate index retained.

Second, a generator-level coordinate presentation is enough to identify this
actual active summand with a provenance-labelled coordinate ideal.  Thus the
ideal equality (`hmap`) needed by the height machinery is a theorem, rather
than a separate ideal-level certificate.  The resulting relative theorem
says that the active occurrences add exactly the certified lower bound
`2 * active.card` above a selected-null coefficient prime.

After passage to `GenericPinCoefficientField`, the pin variables are
coefficients and the active relations are linear forms in the shared
body-twist variables.  The coordinate presentation therefore reduces the
height comparison to an explicit linear change of the twist coordinates.
-/

namespace RB31E2E

namespace UniversalActivePinHeightTransfer

noncomputable section

open MvPolynomial
open NullCellulePolynomial
open UniversalHomogeneousChart
open ActivePinPrimeHeight

/-! ## The actual finite-generic summands -/

/-- One actual active compatibility generator after extending the pin
parameters to their fraction field and finitely reindexing twist variables. -/
def finiteGenericActiveCompatibilityGenerator
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (a : ActiveCompatibilityIndex active chart) :
    FiniteGenericRelativeRing root E :=
  finiteGenericChartHom root
    (activeCompatibilityGenerator root src dst active chart a)

/-- The finite-generic active ideal, defined as the image of the literal
universal active ideal. -/
def finiteGenericActiveCompatibilityIdeal
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) :
    Ideal (FiniteGenericRelativeRing root E) :=
  Ideal.map (finiteGenericChartHom root)
    (activeCompatibilityIdeal root src dst active chart)

/-- The finite-generic image of the selected null equations. -/
def finiteGenericSelectedNullIdeal
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (selected : Finset active) :
    Ideal (FiniteGenericRelativeRing root E) :=
  Ideal.map (finiteGenericChartHom root)
    (Ideal.span (selectedNullGeneratorSet root src dst active selected))

/-- The active image is generated by the actual finite-generic compatibility
polynomials, not by an abstract replacement family. -/
theorem finiteGenericActiveCompatibilityIdeal_eq_span_range
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) :
    finiteGenericActiveCompatibilityIdeal root src dst active chart =
      Ideal.span (Set.range
        (finiteGenericActiveCompatibilityGenerator
          root src dst active chart)) := by
  rw [finiteGenericActiveCompatibilityIdeal, activeCompatibilityIdeal,
    Ideal.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨g, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨activeCompatibilityGenerator root src dst active chart a,
      ⟨a, rfl⟩, rfl⟩

/-- Exact base-changed decomposition of the universal chart ideal. -/
theorem finiteGenericUniversalChartIdeal_eq_active_sup_selectedNull
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active) :
    finiteGenericUniversalChartIdeal root src dst active chart selected =
      finiteGenericActiveCompatibilityIdeal root src dst active chart ⊔
        finiteGenericSelectedNullIdeal root src dst active selected := by
  rw [finiteGenericUniversalChartIdeal, universalChartIdeal,
    universalChartGeneratorSet, Ideal.span_union, Ideal.map_sup]
  rfl

/-! ## A general relative coordinate-height lemma -/

/-- Adjoining an injectively labelled finite family of polynomial
coordinates above a coefficient prime raises height by at least the size of
the family.  This is the all-cardinalities version of the two-coordinate
lemma in `ActivePinPrimeHeight`. -/
theorem basePrimeCoordinateIdeal_height_ge_add_card
    {R σ : Type*} [CommRing R] [IsNoetherianRing R] [Finite σ]
    (P : Ideal R) [P.IsPrime] {n : ℕ}
    (c : Fin n → σ) (hc : Function.Injective c) :
    P.height + n ≤
      (basePrimeCoordinateIdeal P (Set.range c)).height := by
  let I : Fin (n + 1) → Ideal (MvPolynomial σ R) := fun j ↦
    basePrimeCoordinateIdeal P (coordinatePrefixSet c j)
  have hprime (j : Fin (n + 1)) : (I j).IsPrime := by
    dsimp [I]
    exact basePrimeCoordinateIdeal_isPrime P (coordinatePrefixSet c j)
  have hstep {j l : Fin (n + 1)} (hjl : j < l) : I j < I l := by
    exact basePrimeCoordinatePrefix_lt P c hc hjl
  have hprefix : ∀ j : Fin (n + 1),
      (I 0).height + j.1 ≤ (I j).height := by
    intro j
    induction j using Fin.induction with
    | zero => simp
    | succ j ih =>
        letI : (I (Fin.castSucc j)).IsPrime := hprime (Fin.castSucc j)
        letI : (I j.succ).IsPrime := hprime j.succ
        have hlt : I (Fin.castSucc j) < I j.succ := by
          apply hstep
          simp
        have hone := Ideal.height_add_one_le_of_lt_of_isPrime hlt
        calc
          (I 0).height + (j.succ.1 : ℕ∞) =
              ((I 0).height + (j.1 : ℕ∞)) + 1 := by
                simp [add_assoc]
          _ ≤ (I (Fin.castSucc j)).height + 1 := by
                simpa [add_assoc, add_comm, add_left_comm] using
                  (add_le_add_right ih 1)
          _ ≤ (I j.succ).height := hone
  have hzero : I 0 =
      Ideal.map (C : R →+* MvPolynomial σ R) P := by
    simp [I, coordinatePrefixSet, basePrimeCoordinateIdeal,
      coordinateVariableIdeal]
  have hlast : I (Fin.last n) =
      basePrimeCoordinateIdeal P (Set.range c) := by
    change basePrimeCoordinateIdeal P
      (coordinatePrefixSet c (Fin.last n)) = _
    rw [coordinatePrefixSet_last]
  letI : (I 0).IsPrime := hprime 0
  letI : (I (Fin.last n)).IsPrime := hprime (Fin.last n)
  have h := hprefix (Fin.last n)
  rw [hzero, hlast,
    height_map_C_eq ( σ := σ) P] at h
  simpa using h

/-! ## Provenance-coordinate presentation of the actual active ideal -/

/-- The canonical private coordinate occupied by one active compatibility
provenance label; `ρ` indexes all remaining twist coordinates. -/
def activePrivateCoordinate
    {E ρ : Type*} [DecidableEq E] {active : Finset E}
    {chart : active → Fin 3} :
    ActiveCompatibilityIndex active chart →
      ActiveCompatibilityIndex active chart ⊕ ρ :=
  Sum.inl

/-- A generator-level coordinate presentation proves the desired ideal map.
No ideal equality is assumed. -/
theorem map_finiteGenericActiveCompatibilityIdeal_eq_coordinateIdeal
    {V E R ρ : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    [CommRing R]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (e : FiniteGenericRelativeRing root E ≃+*
      MvPolynomial (ActiveCompatibilityIndex active chart ⊕ ρ)
        R)
    (hgenerator : ∀ a : ActiveCompatibilityIndex active chart,
      e (finiteGenericActiveCompatibilityGenerator
        root src dst active chart a) = X (activePrivateCoordinate a)) :
    Ideal.map e
        (finiteGenericActiveCompatibilityIdeal
          root src dst active chart) =
      coordinateVariableIdeal
        (k := R)
        (Set.range (activePrivateCoordinate ( ρ := ρ))) := by
  rw [finiteGenericActiveCompatibilityIdeal_eq_span_range,
    Ideal.map_span, coordinateVariableIdeal]
  congr 1
  ext f
  constructor
  · rintro ⟨g, ⟨a, rfl⟩, rfl⟩
    exact ⟨activePrivateCoordinate a, ⟨a, rfl⟩, (hgenerator a).symm⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨finiteGenericActiveCompatibilityGenerator
        root src dst active chart a,
      ⟨a, rfl⟩, hgenerator a⟩

/-- Under the same concrete coordinate presentation, the actual active
summand has height at least two per active occurrence. -/
theorem finiteGenericActiveCompatibilityIdeal_height_ge_twice_card
    {V E ρ : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (e : FiniteGenericRelativeRing root E ≃+*
      MvPolynomial (ActiveCompatibilityIndex active chart ⊕ ρ)
        (GenericPinCoefficientField E))
    (hgenerator : ∀ a : ActiveCompatibilityIndex active chart,
      e (finiteGenericActiveCompatibilityGenerator
        root src dst active chart a) = X (activePrivateCoordinate a)) :
    (2 * active.card : ℕ) ≤
      (finiteGenericActiveCompatibilityIdeal
        root src dst active chart).height := by
  let b : ActiveCompatibilityIndex active chart ≃
      Fin (Fintype.card (ActiveCompatibilityIndex active chart)) :=
    Fintype.equivFin _
  let c : Fin (Fintype.card (ActiveCompatibilityIndex active chart)) →
      ActiveCompatibilityIndex active chart ⊕ ρ :=
    fun j ↦ activePrivateCoordinate (b.symm j)
  have hc : Function.Injective c := by
    exact Function.Injective.comp Sum.inl_injective b.symm.injective
  have hrange : Set.range c =
      Set.range (activePrivateCoordinate ( ρ := ρ)) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨b.symm j, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨b a, by simp [c, b]⟩
  rw [← e.height_map,
    map_finiteGenericActiveCompatibilityIdeal_eq_coordinateIdeal
      root src dst active chart e hgenerator,
    ← hrange, ← card_activeCompatibilityIndex]
  exact coordinateVariableIdeal_height_ge_card
    (k := GenericPinCoefficientField E) c hc

/-- Residual-free form of the preceding `hmap`: when all remaining twist
coordinates have been absorbed into the coefficient ring, the active
generators become the full coordinate ideal. -/
theorem map_finiteGenericActiveCompatibilityIdeal_eq_coordinateIdeal_univ
    {V E R : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    [CommRing R]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (e : FiniteGenericRelativeRing root E ≃+*
      MvPolynomial (ActiveCompatibilityIndex active chart) R)
    (hgenerator : ∀ a : ActiveCompatibilityIndex active chart,
      e (finiteGenericActiveCompatibilityGenerator
        root src dst active chart a) = X a) :
    Ideal.map e
        (finiteGenericActiveCompatibilityIdeal
          root src dst active chart) =
      coordinateVariableIdeal
        (k := R) (Set.univ : Set (ActiveCompatibilityIndex active chart)) := by
  rw [finiteGenericActiveCompatibilityIdeal_eq_span_range,
    Ideal.map_span, coordinateVariableIdeal]
  congr 1
  ext f
  constructor
  · rintro ⟨g, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, Set.mem_univ a, (hgenerator a).symm⟩
  · rintro ⟨a, _ha, rfl⟩
    exact ⟨finiteGenericActiveCompatibilityGenerator
        root src dst active chart a,
      ⟨a, rfl⟩, hgenerator a⟩

/-! ## Primewise relative height, without a selected-null presentation -/

/-- The coefficient prime below a prime of a coordinate presentation.  This
is a genuine contraction, so primality is inherited automatically. -/
def coefficientContraction
    {V E R : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    [CommRing R]
    {root : V} {active : Finset E} {chart : active → Fin 3}
    (e : FiniteGenericRelativeRing root E ≃+*
      MvPolynomial (ActiveCompatibilityIndex active chart) R)
    (Q : Ideal (FiniteGenericRelativeRing root E)) : Ideal R :=
  Ideal.comap (C : R →+*
    MvPolynomial (ActiveCompatibilityIndex active chart) R)
    (Ideal.map e Q)

/-- Parameter-free primewise increment after an explicit generator-level
coordinate change: every prime over the full chart has at least two height
units per active occurrence above its coefficient contraction.  No
presentation of the selected-null ideal and no ideal-level `hmap` is
assumed. -/
theorem prime_height_ge_coefficientContraction_add_twice_card
    {V E R : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    [CommRing R] [IsNoetherianRing R]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active)
    (e : FiniteGenericRelativeRing root E ≃+*
      MvPolynomial (ActiveCompatibilityIndex active chart) R)
    (hgenerator : ∀ a : ActiveCompatibilityIndex active chart,
      e (finiteGenericActiveCompatibilityGenerator
        root src dst active chart a) = X a)
    (Q : Ideal (FiniteGenericRelativeRing root E)) [Q.IsPrime]
    (hQ : finiteGenericUniversalChartIdeal
      root src dst active chart selected ≤ Q) :
    (coefficientContraction e Q).height + (2 * active.card : ℕ) ≤
      Q.height := by
  let Q' : Ideal (MvPolynomial
      (ActiveCompatibilityIndex active chart) R) := Ideal.map e Q
  let P : Ideal R := coefficientContraction e Q
  letI : Q'.IsPrime := by
    dsimp [Q']
    exact Ideal.map_isPrime_of_equiv e
  letI : P.IsPrime := by
    dsimp [P, coefficientContraction]
    exact Ideal.comap_isPrime _ _
  have hactive : finiteGenericActiveCompatibilityIdeal
      root src dst active chart ≤ Q := by
    apply le_trans _ hQ
    rw [finiteGenericUniversalChartIdeal_eq_active_sup_selectedNull]
    exact le_sup_left
  have hcoordinate : coordinateVariableIdeal
      (k := R) (Set.univ : Set (ActiveCompatibilityIndex active chart)) ≤ Q' := by
    rw [← map_finiteGenericActiveCompatibilityIdeal_eq_coordinateIdeal_univ
      root src dst active chart e hgenerator]
    exact Ideal.map_mono hactive
  have hbase : basePrimeCoordinateIdeal P
      (Set.univ : Set (ActiveCompatibilityIndex active chart)) ≤ Q' := by
    rw [basePrimeCoordinateIdeal]
    apply sup_le
    · change Ideal.map (C : R →+*
          MvPolynomial (ActiveCompatibilityIndex active chart) R)
          (Ideal.comap C Q') ≤ Q'
      exact Ideal.map_comap_le
    · exact hcoordinate
  let b : ActiveCompatibilityIndex active chart ≃
      Fin (Fintype.card (ActiveCompatibilityIndex active chart)) :=
    Fintype.equivFin _
  let c : Fin (Fintype.card (ActiveCompatibilityIndex active chart)) →
      ActiveCompatibilityIndex active chart := b.symm
  have hc : Function.Injective c := b.symm.injective
  have hrange : Set.range c =
      (Set.univ : Set (ActiveCompatibilityIndex active chart)) := by
    exact Set.range_eq_univ.mpr b.symm.surjective
  have hbaseHeight : P.height +
      (Fintype.card (ActiveCompatibilityIndex active chart) : ℕ) ≤
      (basePrimeCoordinateIdeal P
        (Set.univ : Set (ActiveCompatibilityIndex active chart))).height := by
    rw [← hrange]
    exact basePrimeCoordinateIdeal_height_ge_add_card P c hc
  letI : (basePrimeCoordinateIdeal P
      (Set.univ : Set (ActiveCompatibilityIndex active chart))).IsPrime :=
    basePrimeCoordinateIdeal_isPrime P Set.univ
  have hmono :
      (basePrimeCoordinateIdeal P
        (Set.univ : Set (ActiveCompatibilityIndex active chart))).height ≤
        Q'.height := by
    exact Ideal.height_mono hbase
  calc
    (coefficientContraction e Q).height + (2 * active.card : ℕ) =
        P.height +
          (Fintype.card (ActiveCompatibilityIndex active chart) : ℕ) := by
            rw [card_activeCompatibilityIndex]
    _ ≤ (basePrimeCoordinateIdeal P
          (Set.univ : Set (ActiveCompatibilityIndex active chart))).height :=
      hbaseHeight
    _ ≤ Q'.height := hmono
    _ = Q.height := by
      exact e.height_map Q

/-! ## Relative transfer above the selected-null prime -/

/-- If a concrete twist-coordinate change isolates all active compatibility
generators as the full provenance-indexed polynomial-variable family, and
the selected-null prior becomes a coefficient prime, then the actual full
universal chart ideal maps to the corresponding
`basePrimeCoordinateIdeal`.  This is the application-level `hmap`. -/
theorem map_finiteGenericUniversalChartIdeal_eq_basePrimeCoordinateIdeal
    {V E R : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    [CommRing R]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active)
    (e : FiniteGenericRelativeRing root E ≃+*
      MvPolynomial (ActiveCompatibilityIndex active chart) R)
    (P : Ideal R)
    (hprior : Ideal.map e
      (finiteGenericSelectedNullIdeal root src dst active selected) =
        Ideal.map (C : R →+*
          MvPolynomial (ActiveCompatibilityIndex active chart) R) P)
    (hgenerator : ∀ a : ActiveCompatibilityIndex active chart,
      e (finiteGenericActiveCompatibilityGenerator
        root src dst active chart a) = X a) :
    Ideal.map e
        (finiteGenericUniversalChartIdeal
          root src dst active chart selected) =
      basePrimeCoordinateIdeal P
        (Set.univ : Set (ActiveCompatibilityIndex active chart)) := by
  rw [finiteGenericUniversalChartIdeal_eq_active_sup_selectedNull,
    Ideal.map_sup, hprior, basePrimeCoordinateIdeal, sup_comm]
  congr 1
  rw [finiteGenericActiveCompatibilityIdeal_eq_span_range,
    Ideal.map_span, coordinateVariableIdeal]
  congr 1
  ext f
  constructor
  · rintro ⟨g, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, Set.mem_univ a, (hgenerator a).symm⟩
  · rintro ⟨a, _ha, rfl⟩
    exact ⟨finiteGenericActiveCompatibilityGenerator
        root src dst active chart a,
      ⟨a, rfl⟩, hgenerator a⟩

/-- End-to-end relative active-height theorem.  Once the displayed
generator-level change of coordinates has been constructed, active
occurrences contribute `2 * active.card` height above the selected-null
coefficient prime; no separate ideal-map hypothesis remains. -/
theorem finiteGenericUniversalChartIdeal_height_ge_prior_add_twice_card
    {V E R : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    [CommRing R] [IsNoetherianRing R]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active)
    (e : FiniteGenericRelativeRing root E ≃+*
      MvPolynomial (ActiveCompatibilityIndex active chart) R)
    (P : Ideal R) [P.IsPrime]
    (hprior : Ideal.map e
      (finiteGenericSelectedNullIdeal root src dst active selected) =
        Ideal.map (C : R →+*
          MvPolynomial (ActiveCompatibilityIndex active chart) R) P)
    (hgenerator : ∀ a : ActiveCompatibilityIndex active chart,
      e (finiteGenericActiveCompatibilityGenerator
        root src dst active chart a) = X a) :
    P.height + (2 * active.card : ℕ) ≤
      (finiteGenericUniversalChartIdeal
        root src dst active chart selected).height := by
  let b : ActiveCompatibilityIndex active chart ≃
      Fin (Fintype.card (ActiveCompatibilityIndex active chart)) :=
    Fintype.equivFin _
  let c : Fin (Fintype.card (ActiveCompatibilityIndex active chart)) →
      ActiveCompatibilityIndex active chart := b.symm
  have hc : Function.Injective c := b.symm.injective
  have hrange : Set.range c =
      (Set.univ : Set (ActiveCompatibilityIndex active chart)) := by
    exact Set.range_eq_univ.mpr b.symm.surjective
  rw [← e.height_map,
    map_finiteGenericUniversalChartIdeal_eq_basePrimeCoordinateIdeal
      root src dst active chart selected e P hprior hgenerator,
    ← hrange, ← card_activeCompatibilityIndex]
  exact basePrimeCoordinateIdeal_height_ge_add_card P c hc

end

end UniversalActivePinHeightTransfer

end RB31E2E


end
end BundleSource0034

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombinedPrepared/block_0034/Consolidated/RigidityCombinedPrepared.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombinedPrepared/checkpoint_0034.json"

