module

public import Recovery.Unimodular.NefBig.FanSchemeFoundations
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Order.Filter.ENNReal
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Tactic.Finiteness
public import Mathlib.Tactic.NormNum
public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.FanPurity
public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part09
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Recovery.Unimodular.NefBig.CartierGlobalGeneration
public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part12
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

@[expose] public section
noncomputable section

/-! Exact source bodies; see the accompanying sources manifest. -/

section Source_Continuation_Divisor_SectionVolume

namespace Unimodular.SectionGrowth


open scoped ENNReal

/-- Normalized asymptotic section dimension.  For actual section dimensions
in the actual scheme dimension this is volume divided by the factorial. -/
noncomputable def normalizedVolume (d : ℕ) (h : ℕ → ℕ) : ℝ≥0∞ :=
  Filter.limsup (fun m : ℕ => (h m : ℝ≥0∞) / (m : ℝ≥0∞) ^ d) Filter.atTop

theorem one_le_normalizedVolume (d : ℕ) (h : ℕ → ℕ)
    (hgrowth : ∀ m, m ^ d ≤ h m) :
    1 ≤ normalizedVolume d h := by
  refine Filter.le_limsup_of_frequently_le ?_
    (Filter.isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
  apply Filter.Eventually.frequently
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show m ≠ 0 by omega)
  rw [ENNReal.le_div_iff_mul_le
    (Or.inl (pow_ne_zero d hm0)) (Or.inl (by finiteness)), one_mul]
  exact_mod_cast hgrowth m

theorem normalizedVolume_pos (d : ℕ) (h : ℕ → ℕ)
    (hgrowth : ∀ m, m ^ d ≤ h m) :
    0 < normalizedVolume d h :=
  lt_of_lt_of_le (by norm_num) (one_le_normalizedVolume d h hgrowth)

/-- Growth along the powers of one fixed positive tensor power already
gives a positive lower bound for the ordinary limsup over all powers. -/
theorem inverse_scale_le_normalizedVolume (d : ℕ) (h : ℕ → ℕ)
    (M : ℕ) (hM : 0 < M) (hgrowth : ∀ m, m ^ d ≤ h (M * m)) :
    ((M : ℝ≥0∞) ^ d)⁻¹ ≤ normalizedVolume d h := by
  refine Filter.le_limsup_of_frequently_le ?_
    (Filter.isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
  apply Filter.frequently_atTop.mpr
  intro a
  let m := a + 1
  refine ⟨M * m, ?_, ?_⟩
  · dsimp [m]
    exact (Nat.le_succ a).trans (Nat.le_mul_of_pos_left _ hM)
  · have hm : m ≠ 0 := by dsimp [m]; omega
    have hMn : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
    have hmn : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hm
    have hden : ((M * m : ℕ) : ℝ≥0∞) ^ d ≠ 0 := by
      rw [Nat.cast_mul, mul_pow]
      exact mul_ne_zero (pow_ne_zero d hMn) (pow_ne_zero d hmn)
    rw [ENNReal.le_div_iff_mul_le (Or.inl hden) (Or.inl (by finiteness)),
      Nat.cast_mul, mul_pow,
      ENNReal.inv_mul_cancel_left (pow_ne_zero d hMn) (by finiteness)]
    exact_mod_cast hgrowth m

/-- The standard positive-volume test, with no monotonicity assumption on
the sequence of dimensions and with dimension zero included. -/
theorem normalizedVolume_pos_of_subsequence_growth (d : ℕ) (h : ℕ → ℕ)
    (M : ℕ) (hM : 0 < M) (hgrowth : ∀ m, m ^ d ≤ h (M * m)) :
    0 < normalizedVolume d h := by
  apply lt_of_lt_of_le _ (inverse_scale_le_normalizedVolume d h M hM hgrowth)
  exact ENNReal.inv_pos.mpr (by finiteness)

end Unimodular.SectionGrowth

#print axioms Unimodular.SectionGrowth.normalizedVolume_pos

end Source_Continuation_Divisor_SectionVolume

section Source_Recovery_Unimodular_NefBig_FanSmooth

/-!
# Smoothness of the actual glued fan scheme

A full regular cone has a genuine finite polynomial chart algebra. Every
other chart is an actual open subscheme of such a chart, by completeness
and the proved purity theorem. Scheme smoothness then follows from the
ordinary local-on-source criterion on the actual gluing cover.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace Unimodular.NefBig

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes PaperVerification.ToricCharacters
open PaperVerification.ToricGeometry

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n) (k : Type u) [Field k]

/-- The actual algebra of a full chart is a finite polynomial algebra over k. -/
def fullChartPolynomialEquivUniv (s : F.fullCones) :
    monoidChartAlgebra k (dualConeMonoid (s : Finset (Lattice n))) ≃ₐ[k]
      MvPolynomial (Finset.univ : Finset (Fin n)) k := by
  classical
  letI : IsEmpty (FreeCoordinate (Finset.univ : Finset (Fin n))) :=
    ⟨fun i => i.property (Finset.mem_univ i.val)⟩
  rw [F.fullConeBasis_ray_set, dualConeMonoid_basis_eq]
  exact (smoothChartAlgebraEquiv k (integralDualBasis (F.fullConeBasis s))
    (Finset.univ : Finset (Fin n))).trans
      (MvPolynomial.mapAlgEquiv (Finset.univ : Finset (Fin n))
        (AddMonoidAlgebra.uniqueAlgEquiv k
          (FreeCoordinate (Finset.univ : Finset (Fin n)) → ℤ)))

/-- Algebraic smoothness is transported along the genuine polynomial
algebra equivalence, not asserted from the name of the fan structure. -/
theorem fullChartAlgebra_smooth (s : F.fullCones) :
    Algebra.Smooth k (monoidChartAlgebra k (dualConeMonoid (s : Finset (Lattice n)))) :=
  Algebra.Smooth.of_equiv (fullChartPolynomialEquivUniv F k s).symm

/-- The actual full-chart structure morphism is smooth over the field. -/
theorem fullChart_smooth (s : F.fullCones) :
    Smooth (coneChart k (s : Finset (Lattice n)) ↘ Spec (CommRingCat.of k)) := by
  letI := fullChartAlgebra_smooth F k s
  change Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap k (monoidChartAlgebra k (dualConeMonoid (s : Finset (Lattice n)))))))
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)

/-- All actual cone charts are smooth: each is an open subscheme of an
actual full chart supplied by the proved purity of the complete fan. -/
theorem coneChart_smooth (s : Finset (Lattice n)) (hs : s ∈ F.cones) :
    Smooth (coneChart k s ↘ Spec (CommRingCat.of k)) := by
  obtain ⟨t, ht, hst, hcard⟩ := F.isPure s hs
  let t' : F.fullCones := ⟨t, Finset.mem_filter.mpr ⟨ht, hcard⟩⟩
  letI := fullChart_smooth F k t'
  letI := F.coneChartFaceMap_isOpenImmersion k t s ht hst
  rw [← comp_over (coneChartFaceMap k hst) (Spec (CommRingCat.of k))]
  infer_instance

/-- Standard scheme smoothness for the actual glued fan scheme over k. -/
theorem fanScheme_smoothViaAllCones :
    Smooth (F.fanScheme k ↘ Spec (CommRingCat.of k)) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth) (F.fanSchemeOpenCover k)
  intro s
  change Smooth (F.fanChartMap k s ≫ (F.fanScheme k ↘ Spec (CommRingCat.of k)))
  rw [comp_over]
  exact coneChart_smooth F k s.val s.property

#print axioms fullChartPolynomialEquivUniv
#print axioms fullChartAlgebra_smooth
#print axioms fullChart_smooth
#print axioms coneChart_smooth
#print axioms fanScheme_smoothViaAllCones

end Unimodular.NefBig

#check Unimodular.NefBig.fanScheme_smoothViaAllCones

end Source_Recovery_Unimodular_NefBig_FanSmooth

section Source_Recovery_Unimodular_NefBig_FanGlobalGeneration

/-!
# Convex integral support gives actual globally generated line bundles

The support hypothesis places each integral Cartier point in the actual
polytope. Its monomial is an actual global section of the constructed sheaf;
its rational value equals the specified generator on the corresponding affine
chart. The conclusion is standard stalkwise global generation and an actual
free-sheaf epimorphism, with no curve degree or nefness definition substituted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace Unimodular.NefBig

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes PaperVerification.ToricCharacters
open PaperVerification.ToricGeometry
open scoped BaseSections

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n) (k : Type u) [Field k]
  (a : Lattice n → ℤ)

/-- The integral Cartier points satisfy every actual ray inequality. -/
theorem cartierLatticePoint_mem_exponents (ha : F.IsNef (fun v => (a v : ℝ)))
    (s : F.fullCones) : F.cartierLatticePoint a s ∈ F.fanIntegralExponents a := by
  change PaperVerification.ToricGeometry.embed n (F.cartierLatticePoint a s) ∈ F.fanPolytope (fun v => (a v : ℝ))
  rw [F.embed_cartierLatticePoint]
  exact F.cartierPoint_mem_of_nef ha s

/-- The local Cartier generator is the actual rational value of a global
section; the section is obtained from the proved global-section isomorphism. -/
theorem fanCartier_global_generators (ha : F.IsNef (fun v => (a v : ℝ)))
    (i : (F.fanCartierCocycle k F.isPure a).index) :
    ∃ s : Γ((F.fanCartierCocycle k F.isPure a).sheaf, ⊤),
      (F.fanCartierCocycle k F.isPure a).toCartierData.sectionValue ⊤ s =
        ((F.fanCartierCocycle k F.isPure a).generator i : (F.fanScheme k).functionField) := by
  let m := F.cartierLatticePoint a i.down
  have hm : m ∈ F.fanIntegralExponents a := cartierLatticePoint_mem_exponents F a ha i.down
  let p : characterModule k (F.fanIntegralExponents a) :=
    ⟨AddMonoidAlgebra.single m 1, (single_mem_characterModule k _ m).mpr hm⟩
  let s := (F.fanCartierSectionCoordinates k F.isPure a).symm p
  refine ⟨s, ?_⟩
  change (F.fanCartierData k F.isPure a).globalSectionValue k s = _
  rw [← F.fanCartierSectionCoordinates_value k F.isPure a s]
  change F.torusRationalMap k
      (((F.fanCartierSectionCoordinates k F.isPure a)
        ((F.fanCartierSectionCoordinates k F.isPure a).symm p)).val) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The actual invertible sheaf of a convex integral support function is
globally generated in the standard stalkwise sense on the actual fan scheme. -/
theorem fanCartier_isGloballyGenerated (ha : F.IsNef (fun v => (a v : ℝ))) :
    (cocycleInvertibleSheaf (F.fanCartierCocycle k F.isPure a)).IsGloballyGenerated :=
  isGloballyGenerated_of_global_generators _ (fanCartier_global_generators F k a ha)

/-- Actual generating sections and their ordinary free-sheaf epimorphism. -/
theorem fanCartier_generatingSections (ha : F.IsNef (fun v => (a v : ℝ))) :
    Nonempty (F.fanCartierData k F.isPure a).sheaf.GeneratingSections :=
  (fanCartier_isGloballyGenerated F k a ha).nonempty_generatingSections

#print axioms cartierLatticePoint_mem_exponents
#print axioms fanCartier_global_generators
#print axioms fanCartier_isGloballyGenerated
#print axioms fanCartier_generatingSections

end Unimodular.NefBig

#check Unimodular.NefBig.fanCartier_isGloballyGenerated

end Source_Recovery_Unimodular_NefBig_FanGlobalGeneration

section Source_Continuation_Divisor_TypeAUnitBoundary

/-!
# Global generation of the anticanonical coefficients on every type-A fan

Use coordinates with the last simplex vertex at zero. A smooth fan cone
cannot contain two rays whose sum is another ray or zero: its primitive
ray vectors are part of a lattice basis, and the fan intersection axiom
would put that sum-ray among them. Thus the directed roots of each cone
have no directed path of length two. The indicator of their source set
is one on that cone and at most one on every root. This is the actual
support function needed by the proved global-generation theorem.

The proof includes dimension zero and makes no projectivity assumption.
-/

set_option autoImplicit false

namespace Unimodular.TypeABoundary

open PaperVerification.ToricGeometry
open scoped BigOperators Classical

variable {n : ℕ}

/-- The vertices of the unimodular simplex, with the distinguished vertex at zero. -/
def rootVertex : Option (Fin n) → Lattice n
  | none => 0
  | some i => Pi.single i 1

/-- All oriented roots in standard coordinates for the zero-sum root lattice. -/
def rootVector (i j : Option (Fin n)) : Lattice n := rootVertex i - rootVertex j

@[simp] theorem rootVector_self (i : Option (Fin n)) : rootVector i i = 0 := sub_self _

theorem rootVector_add (i j l : Option (Fin n)) :
    rootVector i j + rootVector j l = rootVector i l := by
  unfold rootVector
  abel

/-- The exact type-A ray set, retaining both orientations of every root. -/
def HasTypeARays (F : PaperVerification.ToricGeometry.SmoothCompleteFan n) : Prop :=
  ∀ u, u ∈ F.rays ↔ ∃ i j : Option (Fin n), i ≠ j ∧ u = rootVector i j

/-- A linear cut potential, normalized to vanish at the distinguished simplex vertex. -/
def cutLinear (S : Set (Option (Fin n))) : Ambient n →ₗ[ℝ] ℝ where
  toFun x := ∑ i, ((if some i ∈ S then (1 : ℝ) else 0) -
    (if none ∈ S then (1 : ℝ) else 0)) * x i
  map_add' x y := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

lemma cutLinear_vertex (S : Set (Option (Fin n))) (i : Option (Fin n)) :
    cutLinear S (PaperVerification.ToricGeometry.embed n (rootVertex i)) =
      (if i ∈ S then (1 : ℝ) else 0) - (if none ∈ S then (1 : ℝ) else 0) := by
  cases i with
  | none => simp [rootVertex, cutLinear, PaperVerification.ToricGeometry.embed]
  | some i => simp [rootVertex, cutLinear, PaperVerification.ToricGeometry.embed, Pi.single_apply]

lemma cutLinear_root (S : Set (Option (Fin n))) (i j : Option (Fin n)) :
    cutLinear S (PaperVerification.ToricGeometry.embed n (rootVector i j)) =
      (if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then (1 : ℝ) else 0) := by
  rw [rootVector, map_sub, map_sub, cutLinear_vertex, cutLinear_vertex]
  ring

lemma cutLinear_root_le (S : Set (Option (Fin n))) (i j : Option (Fin n)) :
    cutLinear S (PaperVerification.ToricGeometry.embed n (rootVector i j)) ≤ 1 := by
  rw [cutLinear_root]
  split_ifs <;> norm_num

variable (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)

/-- Every cone ray has coordinate sum one in an extending integral basis. -/
lemma exists_ray_sum_function {s : Finset (Lattice n)} (hs : s ∈ F.cones) :
    ∃ ℓ : Lattice n →ₗ[ℤ] ℤ, ∀ u ∈ s, ℓ u = 1 := by
  obtain ⟨b, I, hI⟩ := F.smooth s hs
  let ℓ : Lattice n →ₗ[ℤ] ℤ := ∑ i, b.coord i
  refine ⟨ℓ, ?_⟩
  intro u hu
  rw [hI] at hu
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  simp [ℓ, Module.Basis.coord_apply, Module.Basis.repr_self_apply]

/-- A sum of two cone generators can be neither zero nor another ray of the fan. -/
lemma sum_not_zero_or_ray {s : Finset (Lattice n)} (hs : s ∈ F.cones)
    {u v : Lattice n} (hu : u ∈ s) (hv : v ∈ s) :
    u + v ≠ 0 ∧ u + v ∉ F.rays := by
  obtain ⟨ℓ, hℓ⟩ := exists_ray_sum_function F hs
  have hvalue : ℓ (u + v) = 2 := by rw [map_add, hℓ u hu, hℓ v hv]; norm_num
  constructor
  · intro hzero
    rw [hzero, map_zero] at hvalue
    norm_num at hvalue
  · intro hray
    have hmem : PaperVerification.ToricGeometry.embed n (u + v) ∈ latticeRayCone s := by
      rw [map_add]
      exact (latticeRayCone s).add_mem (latticeRayCone_generator s hu)
        (latticeRayCone_generator s hv)
    have h := hℓ (u + v) ((F.ray_mem_cone_iff hs hray).mp hmem)
    omega

lemma no_two_edge_path (hroots : HasTypeARays F)
    {s : Finset (Lattice n)} (hs : s ∈ F.cones)
    {i j l : Option (Fin n)} (hij : i ≠ j) (hjl : j ≠ l)
    (hu : rootVector i j ∈ s) (hv : rootVector j l ∈ s) : False := by
  have h := sum_not_zero_or_ray F hs hu hv
  rw [rootVector_add] at h
  by_cases hil : i = l
  · subst l
    exact h.1 (rootVector_self i)
  · exact h.2 ((hroots _).mpr ⟨i, l, hil, rfl⟩)

/-- Source vertices of the directed roots occurring in one cone. -/
def coneSources (s : Finset (Lattice n)) : Set (Option (Fin n)) :=
  {i | ∃ j, i ≠ j ∧ rootVector i j ∈ s}

lemma cone_root_crosses_sources (hroots : HasTypeARays F)
    {s : Finset (Lattice n)} (hs : s ∈ F.cones)
    {i j : Option (Fin n)} (hij : i ≠ j) (hmem : rootVector i j ∈ s) :
    i ∈ coneSources s ∧ j ∉ coneSources s := by
  refine ⟨⟨j, hij, hmem⟩, ?_⟩
  rintro ⟨l, hjl, hl⟩
  exact no_two_edge_path F hroots hs hij hjl hmem hl

/-- The all-ones Cartier coefficients have convex support on every smooth
complete type-A fan, including the nonprojective fans. -/
theorem unitBoundary_convexSupport (hroots : HasTypeARays F) :
    F.IsNef (fun _ => 1) := by
  intro s hs
  refine ⟨cutLinear (coneSources s), ?_, ?_⟩
  · intro u hu
    obtain ⟨i, j, hij, rfl⟩ := (hroots u).mp (F.ray_mem_of_mem_cone hs hu)
    obtain ⟨hi, hj⟩ := cone_root_crosses_sources F hroots hs hij hu
    simp only [cutLinear_root, if_pos hi, if_neg hj, sub_zero]
  · intro u hu
    obtain ⟨i, j, hij, rfl⟩ := (hroots u).mp hu
    exact cutLinear_root_le _ i j

/-- Standard global generation of the actual unit-boundary line bundle. -/
theorem unitBoundary_isGloballyGenerated (k : Type*) [Field k]
    (hroots : HasTypeARays F) :
    (Unimodular.NefBig.cocycleInvertibleSheaf
      (F.fanCartierCocycle k F.isPure (fun _ => 1))).IsGloballyGenerated := by
  apply Unimodular.NefBig.fanCartier_isGloballyGenerated
  simpa using unitBoundary_convexSupport F hroots

#print axioms unitBoundary_convexSupport
#print axioms unitBoundary_isGloballyGenerated

end Unimodular.TypeABoundary

end Source_Continuation_Divisor_TypeAUnitBoundary

section Source_Continuation_Divisor_SectionFoundations

/-!
# The exact section-growth dependencies

These elementary bounded-lattice and Cartier-power proofs are isolated
from the independent Gröbner-basis and section-ring theories. They retain
the original actual sheaves, tensor powers, and bounded polyhedra.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace Unimodular.NefBig
open Set AlgebraicGeometry
open PaperVerification.ToricGeometry PaperVerification.ToricCharacters
open PaperVerification.ToricSchemes
open scoped BigOperators

variable {n : ℕ}

theorem finite_lattice_points_of_bounded (P : Set (Ambient n))
    (hP : Bornology.IsBounded P) :
    {x : Lattice n | PaperVerification.ToricGeometry.embed n x ∈ P}.Finite := by
  obtain ⟨R, hR⟩ := hP.subset_closedBall (0 : Ambient n)
  obtain ⟨N, hN⟩ := exists_nat_gt R
  apply (Set.Finite.pi (fun _ : Fin n => Set.finite_Icc (-(N : ℤ)) (N : ℤ))).subset
  intro x hx i _
  have hxR : ‖PaperVerification.ToricGeometry.embed n x‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR hx
  have hi : |(x i : ℝ)| ≤ (N : ℝ) :=
    (norm_le_pi_norm (PaperVerification.ToricGeometry.embed n x) i).trans (hxR.trans hN.le)
  have hib := abs_le.mp hi
  constructor
  · exact_mod_cast hib.1
  · exact_mod_cast hib.2

variable (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)

theorem fanPolytope_subset_convexHull_cartier (a : Lattice n → ℝ) :
    F.fanPolytope a ⊆ convexHull ℝ (Set.range (F.cartierPoint a)) := by
  intro x hx
  apply mem_finite_convexHull_of_lower_support (F.cartierPoint a) x
  intro f
  obtain ⟨s, hs⟩ := F.exists_cartierBasis_nonnegative F.isPure f
  exact ⟨s, linear_le_of_basis_coordinates (F.cartierBasis s) f (F.cartierPoint a s) x
    hs (F.cartierPoint_orthant s hx)⟩

theorem fanPolytope_isBounded (a : Lattice n → ℝ) : Bornology.IsBounded (F.fanPolytope a) :=
  ((Set.finite_range (F.cartierPoint a)).isCompact_convexHull ℝ).isBounded.subset
    (fanPolytope_subset_convexHull_cartier F a)

theorem fanIntegralExponents_finite (a : Lattice n → ℤ) : (F.fanIntegralExponents a).Finite :=
  finite_lattice_points_of_bounded (F.fanPolytope (fun u => (a u : ℝ)))
    (fanPolytope_isBounded F _)

theorem cartierLatticePoint_zero (s : F.fullCones) :
    F.cartierLatticePoint (0 : Lattice n → ℤ) s = 0 := by
  symm
  apply F.eq_cartierLatticePoint_of_pairings
  intro v hv
  simp [PaperVerification.ToricGeometry.integerPairing]

theorem cartierLatticePoint_nsmul (a : Lattice n → ℤ) (s : F.fullCones) (d : ℕ) :
    F.cartierLatticePoint (d • a) s = d • F.cartierLatticePoint a s := by
  induction d with
  | zero => simp [cartierLatticePoint_zero]
  | succ d ih => rw [succ_nsmul, F.cartierLatticePoint_add_coefficients, ih, succ_nsmul]

variable (k : Type u) [Field k]

theorem rationalCharacter_nsmul (m : Lattice n) (d : ℕ) :
    F.rationalCharacter k (d • m) = F.rationalCharacter k m ^ d := by
  induction d with
  | zero => simp
  | succ d ih => rw [succ_nsmul, F.rationalCharacter_add k, ih, pow_succ]

theorem fanCartierCocycle_pow (a : Lattice n → ℤ) (d : ℕ) :
    (F.fanCartierCocycle k F.isPure a).pow d =
      F.fanCartierCocycle k F.isPure (d • a) := by
  unfold RationalCartierCocycle.pow
    PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartierCocycle
  congr 1
  funext i
  rw [cartierLatticePoint_nsmul F, rationalCharacter_nsmul F k]

#print axioms fanIntegralExponents_finite
#print axioms fanCartierCocycle_pow
end Unimodular.NefBig

end Source_Continuation_Divisor_SectionFoundations

section Source_Recovery_Unimodular_NefBig_SectionDimensions

/-!
# Dimensions of actual toric global-section spaces

The basis is obtained from the proved global-section coordinate isomorphism
on the actual glued fan scheme. Its index set is the complete set of integral
points satisfying the divisor inequalities. Finiteness is proved from the
bounded polyhedron of a complete fan; no positivity hypothesis is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace Unimodular.NefBig

open AlgebraicGeometry
open PaperVerification.ToricSchemes PaperVerification.ToricCharacters
open PaperVerification.ToricGeometry
open scoped BaseSections

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n) (k : Type u) [Field k]

/-- Every integral allowed character gives one basis vector of the actual
global-section space of the actual Cartier sheaf. -/
def fanSectionsBasis (a : Lattice n → ℤ) :
    Module.Basis (F.fanIntegralExponents a) k
      Γ((F.fanCartierData k F.isPure a).sheaf, ⊤) where
  repr := (F.fanCartierSectionCoordinates k F.isPure a).trans
    (AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k) _)

/-- The actual global-section space is finite dimensional for every integral
Cartier coefficient function on the complete fan. -/
theorem fanSections_finite (a : Lattice n → ℤ) :
    Module.Finite k Γ((F.fanCartierData k F.isPure a).sheaf, ⊤) := by
  letI := (fanIntegralExponents_finite F a).fintype
  exact Module.Finite.of_basis (fanSectionsBasis F k a)

/-- Exact dimension, not only an inequality or a formal monomial count. -/
theorem fanSections_finrank (a : Lattice n → ℤ) :
    Module.finrank k Γ((F.fanCartierData k F.isPure a).sheaf, ⊤) =
      Nat.card (F.fanIntegralExponents a) :=
  Module.finrank_eq_nat_card_basis (fanSectionsBasis F k a)

#print axioms fanSectionsBasis
#print axioms fanSections_finite
#print axioms fanSections_finrank

end Unimodular.NefBig

#check Unimodular.NefBig.fanSections_finrank

end Source_Recovery_Unimodular_NefBig_SectionDimensions

section Source_Recovery_Unimodular_NefBig_SectionGrowth

/-!
# Polynomial growth of actual unit-boundary tensor-power sections

A fixed integer cube lies in a fixed dilation of the ray-inequality polytope.
Counting its distinct ordinary character sections gives a lower bound for
the dimension of the actual global sections of ordinary sheaf tensor powers.
This file proves the growth estimate itself. It does not identify the unit
boundary sheaf with the inverse canonical bundle, assert scheme projectivity,
or substitute a combinatorial definition for geometric bigness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace Unimodular.NefBig

open AlgebraicGeometry
open PaperVerification.ToricSchemes PaperVerification.ToricGeometry
open scoped BaseSections

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)

/-- One positive integral bound for all absolute primitive-ray coordinates. -/
def sectionGrowthScale : ℕ := 1 + ∑ u ∈ F.rays, ∑ i, (u i).natAbs

theorem sectionGrowthScale_pos : 0 < sectionGrowthScale F := by
  unfold sectionGrowthScale
  omega

/-- The integer point whose coordinates lie in the ordinary cube [0,d]^n. -/
def cubeExponent (d : ℕ) (v : Fin n → Fin (d + 1)) : Lattice n :=
  fun i => ((v i).val : ℤ)

theorem cubeExponent_injective (d : ℕ) :
    Function.Injective (cubeExponent (n := n) d) := by
  intro v w h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  change ((v i).val : ℤ) = ((w i).val : ℤ) at hi
  exact_mod_cast hi

theorem cubeExponent_pairing_lower (d : ℕ) (v : Fin n → Fin (d + 1))
    (u : Lattice n) (hu : u ∈ F.rays) :
    -((sectionGrowthScale F * d : ℕ) : ℤ) ≤ integerPairing u (cubeExponent d v) := by
  classical
  have hsize : (∑ i, (u i).natAbs) ≤ sectionGrowthScale F := by
    have h := Finset.single_le_sum (fun w (_ : w ∈ F.rays) =>
      Nat.zero_le (∑ i, (w i).natAbs)) hu
    exact h.trans (Nat.le_add_left _ _)
  have hterm (i : Fin n) :
      -((u i).natAbs : ℤ) * (d : ℤ) ≤ u i * ((v i).val : ℤ) := by
    have hv0 : (0 : ℤ) ≤ ((v i).val : ℤ) := by positivity
    have hvd : ((v i).val : ℤ) ≤ (d : ℤ) := by
      exact_mod_cast Nat.le_of_lt_succ (v i).isLt
    have hneg : -(u i) ≤ ((u i).natAbs : ℤ) := by
      simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -(u i)))
    have huLower : -((u i).natAbs : ℤ) ≤ u i := by omega
    calc
      -((u i).natAbs : ℤ) * (d : ℤ) ≤
          -((u i).natAbs : ℤ) * ((v i).val : ℤ) :=
        mul_le_mul_of_nonpos_left hvd (by omega)
      _ ≤ u i * ((v i).val : ℤ) := mul_le_mul_of_nonneg_right huLower hv0
  have hsizeZ : ((∑ i, (u i).natAbs : ℕ) : ℤ) ≤ (sectionGrowthScale F : ℤ) := by
    exact_mod_cast hsize
  have hd0 : (0 : ℤ) ≤ (d : ℤ) := by positivity
  calc
    -((sectionGrowthScale F * d : ℕ) : ℤ) ≤
        -((∑ i, (u i).natAbs : ℕ) : ℤ) * (d : ℤ) := by
      push_cast
      nlinarith
    _ = ∑ i, -((u i).natAbs : ℤ) * (d : ℤ) := by
      simp only [Nat.cast_sum, Finset.sum_neg_distrib, Finset.sum_mul, neg_mul]
    _ ≤ integerPairing u (cubeExponent d v) := by
      exact Finset.sum_le_sum fun i _ => hterm i

theorem cubeExponent_mem_exponents (d : ℕ) (v : Fin n → Fin (d + 1)) :
    cubeExponent d v ∈
      F.fanIntegralExponents (fun _ => ((sectionGrowthScale F * d : ℕ) : ℤ)) := by
  intro u hu
  rw [PaperVerification.ToricGeometry.SmoothCompleteFan.normalRay_pairing_lattice]
  change -(((sectionGrowthScale F * d : ℕ) : ℤ) : ℝ) ≤
    ((integerPairing u (cubeExponent d v) : ℤ) : ℝ)
  have h : (((-((sectionGrowthScale F * d : ℕ) : ℤ)) : ℤ) : ℝ) ≤
      ((integerPairing u (cubeExponent d v) : ℤ) : ℝ) :=
    Int.cast_le.mpr (cubeExponent_pairing_lower F d v u hu)
  simpa only [Int.cast_neg] using h

variable (k : Type u) [Field k]

/-- An actual global-section dimension estimate in every cube degree. -/
theorem unitBoundary_sections_finrank_growth (d : ℕ) :
    (d + 1) ^ n ≤
      Module.finrank k
        Γ((F.fanCartierData k F.isPure
          (fun _ => ((sectionGrowthScale F * d : ℕ) : ℤ))).sheaf, ⊤) := by
  classical
  let a : Lattice n → ℤ := fun _ => ((sectionGrowthScale F * d : ℕ) : ℤ)
  letI := (fanIntegralExponents_finite F a).fintype
  let f : (Fin n → Fin (d + 1)) → F.fanIntegralExponents a :=
    fun v => ⟨cubeExponent d v, cubeExponent_mem_exponents F d v⟩
  have hf : Function.Injective f := fun v w h =>
    cubeExponent_injective d (congrArg Subtype.val h)
  rw [fanSections_finrank]
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] using hc

/-- The lower bound for ordinary tensor powers, with the fixed fan-dependent scale. -/
theorem unitBoundary_tensorSections_finrank_growth (d : ℕ) :
    (d + 1) ^ n ≤ Module.finrank k Γ(tensorSheafPower
      (F.fanCartierData k F.isPure (fun _ => (1 : ℤ))).sheaf
      (sectionGrowthScale F * d), ⊤) := by
  let C := F.fanCartierCocycle k F.isPure (fun _ => (1 : ℤ))
  have he := (BaseSections.globalSectionsIso k
    (C.tensorSheafPowerIso (sectionGrowthScale F * d))).finrank_eq
  change (d + 1) ^ n ≤ Module.finrank k
    Γ(tensorSheafPower C.sheaf (sectionGrowthScale F * d), ⊤)
  rw [he]
  change (d + 1) ^ n ≤ Module.finrank k
    Γ(((F.fanCartierCocycle k F.isPure (fun _ => (1 : ℤ))).pow
      (sectionGrowthScale F * d)).sheaf, ⊤)
  rw [fanCartierCocycle_pow F k]
  have ha : (sectionGrowthScale F * d) • (fun _ : Lattice n => (1 : ℤ)) =
      (fun _ : Lattice n => ((sectionGrowthScale F * d : ℕ) : ℤ)) := by
    funext u
    simp only [Pi.smul_apply, nsmul_eq_mul, mul_one]
  rw [ha]
  change (d + 1) ^ n ≤ Module.finrank k
    Γ((F.fanCartierData k F.isPure
      (fun _ => ((sectionGrowthScale F * d : ℕ) : ℤ))).sheaf, ⊤)
  exact unitBoundary_sections_finrank_growth F k d

/-- A single positive scale works for every ordinary tensor power in the subsequence. -/
theorem unitBoundary_tensorSections_growth :
    ∃ M : ℕ, 0 < M ∧ ∀ d : ℕ, (d + 1) ^ n ≤
      Module.finrank k Γ(tensorSheafPower
        (F.fanCartierData k F.isPure (fun _ => (1 : ℤ))).sheaf (M * d), ⊤) :=
  ⟨sectionGrowthScale F, sectionGrowthScale_pos F,
    unitBoundary_tensorSections_finrank_growth F k⟩

#print axioms cubeExponent_mem_exponents
#print axioms unitBoundary_sections_finrank_growth
#print axioms unitBoundary_tensorSections_growth

end Unimodular.NefBig

#check Unimodular.NefBig.unitBoundary_tensorSections_growth

end Source_Recovery_Unimodular_NefBig_SectionGrowth

section Source_Continuation_Divisor_BoundaryVolume

/-!
# Positive section volume of the unit boundary

The sequence here is the dimension of global sections of the ordinary
sheaf tensor powers.  A single fixed scaling of the degree contains an
integer cube, so its normalized limsup is strictly positive.  This result
does not identify the unit boundary with the anticanonical sheaf; that
identification must compare it with the determinant of differentials.
-/

set_option autoImplicit false

universe u
namespace Unimodular.NefBig

open AlgebraicGeometry
open PaperVerification.ToricSchemes PaperVerification.ToricGeometry
open scoped BaseSections ENNReal

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
  (k : Type u) [Field k]

/-- The ordinary Hilbert function of the actual unit-boundary sheaf. -/
def unitBoundarySectionDimension (m : ℕ) : ℕ :=
  Module.finrank k Γ(tensorSheafPower
    (F.fanCartierData k F.isPure (fun _ => (1 : ℤ))).sheaf m, ⊤)

/-- A positive lower bound for the normalized limsup of actual section
dimensions, valid also in rank zero. -/
theorem unitBoundary_normalizedVolume_lower_bound :
    ((sectionGrowthScale F : ℝ≥0∞) ^ n)⁻¹ ≤
      SectionGrowth.normalizedVolume n (unitBoundarySectionDimension F k) := by
  apply SectionGrowth.inverse_scale_le_normalizedVolume
    n (unitBoundarySectionDimension F k) (sectionGrowthScale F)
    (sectionGrowthScale_pos F)
  intro d
  unfold unitBoundarySectionDimension
  exact (Nat.pow_le_pow_left (Nat.le_succ d) n).trans
    (unitBoundary_tensorSections_finrank_growth F k d)

theorem unitBoundary_normalizedVolume_pos :
    0 < SectionGrowth.normalizedVolume n (unitBoundarySectionDimension F k) := by
  have hfinite : (sectionGrowthScale F : ℝ≥0∞) ^ n ≠ ⊤ := by finiteness
  exact (ENNReal.inv_pos.mpr hfinite).trans_le
    (unitBoundary_normalizedVolume_lower_bound F k)

#print axioms unitBoundary_normalizedVolume_lower_bound
#print axioms unitBoundary_normalizedVolume_pos

end Unimodular.NefBig

end Source_Continuation_Divisor_BoundaryVolume

#eval "DIVISOR_GEOMETRY_BUNDLE_END"
