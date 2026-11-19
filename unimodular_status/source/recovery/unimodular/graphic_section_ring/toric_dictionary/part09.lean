module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part08
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.AlgebraicGeometry.Properties

@[expose] public section
set_option autoImplicit false

section
-- BEGIN PaperVerification.ToricPrincipalChartModules



/-!
# Rank-one principal chart modules and the actual transition units

The local module is a module over its genuine semigroup chart algebra.
Multiplication by its Laurent character gives an explicit linear
equivalence with that chart algebra. On overlaps, agreeing Cartier
pairings give an actual unit and its explicit inverse.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra
open scoped Classical

variable (k : Type*) [CommSemiring k]
variable {G : Type*} [AddCommGroup G]

def principalChartGeneratorMap (S : AddSubmonoid G) (v : G) :
    monoidChartAlgebra k S →ₗ[monoidChartAlgebra k S] AddMonoidAlgebra k G :=
  (LinearMap.mul (monoidChartAlgebra k S) (AddMonoidAlgebra k G)
    (single v (1 : k))).comp
      (Algebra.linearMap (monoidChartAlgebra k S) (AddMonoidAlgebra k G))

@[simp] theorem principalChartGeneratorMap_apply (S : AddSubmonoid G) (v : G)
    (f : monoidChartAlgebra k S) :
    principalChartGeneratorMap k S v f = single v (1 : k) * (f : AddMonoidAlgebra k G) := rfl

theorem principalChartGeneratorMap_injective (S : AddSubmonoid G) (v : G) :
    Function.Injective (principalChartGeneratorMap k S v) :=
  (characterTranslation k v).injective.comp Subtype.val_injective

def principalChartModule (S : AddSubmonoid G) (v : G) :
    Submodule (monoidChartAlgebra k S) (AddMonoidAlgebra k G) :=
  LinearMap.range (principalChartGeneratorMap k S v)

/-- Actual rank-one local triviality, over the chart algebra itself. -/
def principalChartTrivialization (S : AddSubmonoid G) (v : G) :
    monoidChartAlgebra k S ≃ₗ[monoidChartAlgebra k S] principalChartModule k S v :=
  LinearEquiv.ofInjective (principalChartGeneratorMap k S v)
    (principalChartGeneratorMap_injective k S v)

@[simp] theorem principalChartTrivialization_apply (S : AddSubmonoid G) (v : G)
    (f : monoidChartAlgebra k S) :
    ((principalChartTrivialization k S v f : principalChartModule k S v) :
      AddMonoidAlgebra k G) = single v (1 : k) * f := rfl

theorem principalChartModule_restrictScalars (S : AddSubmonoid G) (v : G) :
    (principalChartModule k S v).restrictScalars k =
      (characterModule k (S : Set G)).map (characterTranslation k v).toLinearMap := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨(g : AddMonoidAlgebra k G), ?_, rfl⟩
    rw [← monoidChartAlgebra_toSubmodule k S]
    exact g.property
  · rintro ⟨g, hg, rfl⟩
    have hg' : g ∈ monoidChartAlgebra k S := by
      change g ∈ (monoidChartAlgebra k S).toSubmodule
      rw [monoidChartAlgebra_toSubmodule]
      exact hg
    exact ⟨⟨g, hg'⟩, rfl⟩

/-- A character and its inverse both in the semigroup give an actual
unit of the chart algebra, not merely a unit in the ambient function field. -/
def chartCharacterUnit (S : AddSubmonoid G) (v : G)
    (hv : v ∈ S) (hneg : -v ∈ S) : (monoidChartAlgebra k S)ˣ where
  val := ⟨single v (1 : k), ⟨single ⟨v, hv⟩ (1 : k), by simp⟩⟩
  inv := ⟨single (-v) (1 : k), ⟨single ⟨-v, hneg⟩ (1 : k), by simp⟩⟩
  val_inv := by apply Subtype.ext; simp [← AddMonoidAlgebra.one_def]
  inv_val := by apply Subtype.ext; simp [← AddMonoidAlgebra.one_def]

@[simp] theorem chartCharacterUnit_val (S : AddSubmonoid G) (v : G)
    (hv : v ∈ S) (hneg : -v ∈ S) :
    (((chartCharacterUnit k S v hv hneg : (monoidChartAlgebra k S)ˣ) :
      monoidChartAlgebra k S) : AddMonoidAlgebra k G) = single v (1 : k) := rfl

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set AddMonoidAlgebra
open PaperVerification.ToricCharacters
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable (k : Type*) [CommSemiring k]

/-- The difference of two actual Cartier characters pairs to zero on
the intersection cone, so it and its negative are both regular there. -/
theorem cartier_difference_mem_overlap (a : Lattice n → ℤ) (s t : «Σ».fullCones) :
    «Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t ∈
      dualConeMonoid ((s : Finset (Lattice n)) ∩ t) ∧
    -(«Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t) ∈
      dualConeMonoid ((s : Finset (Lattice n)) ∩ t) := by
  have hz (u : Lattice n) (hu : u ∈ (s : Finset (Lattice n)) ∩ t) :
      integerPairing u («Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t) = 0 := by
    rw [integerPairing_sub,
      «Σ».cartierLatticePoint_pairing a s u (Finset.mem_inter.mp hu).1,
      «Σ».cartierLatticePoint_pairing a t u (Finset.mem_inter.mp hu).2, sub_self]
  constructor
  · intro u hu
    rw [hz u hu]
  · intro u hu
    have he : integerPairing u (-(«Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t)) =
        -integerPairing u («Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t) := by
      simp only [integerPairing, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [he, hz u hu, neg_zero]

def cartierTransitionUnit (a : Lattice n → ℤ) (s t : «Σ».fullCones) :
    (monoidChartAlgebra k (dualConeMonoid ((s : Finset (Lattice n)) ∩ t)))ˣ :=
  chartCharacterUnit k _ («Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t)
    («Σ».cartier_difference_mem_overlap a s t).1
    («Σ».cartier_difference_mem_overlap a s t).2

theorem cartierTransitionUnit_character (a : Lattice n → ℤ) (s t : «Σ».fullCones) :
    (((«Σ».cartierTransitionUnit k a s t :
      (monoidChartAlgebra k (dualConeMonoid ((s : Finset (Lattice n)) ∩ t)))ˣ) :
      monoidChartAlgebra k (dualConeMonoid ((s : Finset (Lattice n)) ∩ t))) :
      AddMonoidAlgebra k (Lattice n)) =
        single («Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t) (1 : k) := rfl

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricCharacters.principalChartTrivialization
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.cartierTransitionUnit
end
-- END PaperVerification.ToricPrincipalChartModules
end

section
-- BEGIN PaperVerification.ToricChartLocalization



/-!
# Localization of actual semigroup chart subalgebras

All maps below are the literal inclusions of subalgebras of k[M]. A
finite Laurent polynomial has one common character denominator whenever
each of its finitely many exponents does. This proves the localization
property, without replacing the inclusion by an abstract ring isomorphism.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra
open scoped BigOperators Classical

variable (k : Type*) [CommSemiring k]
variable {G : Type*} [AddCommGroup G]

theorem monoidChartAlgebra_mono {S T : AddSubmonoid G} (hST : S ≤ T) :
    monoidChartAlgebra k S ≤ monoidChartAlgebra k T := by
  intro f hf
  rw [mem_monoidChartAlgebra] at hf ⊢
  exact fun m hm => hST (hf hm)

def monoidChartInclusion {S T : AddSubmonoid G} (hST : S ≤ T) :
    monoidChartAlgebra k S →ₐ[k] monoidChartAlgebra k T :=
  Subalgebra.inclusion (monoidChartAlgebra_mono k hST)

@[simp] theorem monoidChartInclusion_coe {S T : AddSubmonoid G} (hST : S ≤ T)
    (f : monoidChartAlgebra k S) :
    ((monoidChartInclusion k hST f : monoidChartAlgebra k T) : AddMonoidAlgebra k G) = f := rfl

theorem monoidChartInclusion_injective {S T : AddSubmonoid G} (hST : S ≤ T) :
    Function.Injective (monoidChartInclusion k hST) :=
  Subalgebra.inclusion_injective (monoidChartAlgebra_mono k hST)

@[simp] theorem monoidChartInclusion_comp {S T U : AddSubmonoid G}
    (hST : S ≤ T) (hTU : T ≤ U) :
    (monoidChartInclusion k hTU).comp (monoidChartInclusion k hST) =
      monoidChartInclusion k (hST.trans hTU) := by
  ext f
  rfl

@[simp] theorem monoidChartInclusion_self (S : AddSubmonoid G) :
    monoidChartInclusion k (le_refl S) = AlgHom.id k (monoidChartAlgebra k S) := by
  ext f
  rfl

def chartCharacter (S : AddSubmonoid G) (v : G) (hv : v ∈ S) : monoidChartAlgebra k S :=
  ⟨single v (1 : k), ⟨single ⟨v, hv⟩ (1 : k), by simp⟩⟩

@[simp] theorem chartCharacter_coe (S : AddSubmonoid G) (v : G) (hv : v ∈ S) :
    ((chartCharacter k S v hv : monoidChartAlgebra k S) : AddMonoidAlgebra k G) =
      single v (1 : k) := rfl

@[simp] theorem monoidChartInclusion_character {S T : AddSubmonoid G}
    (hST : S ≤ T) (v : G) (hv : v ∈ S) :
    monoidChartInclusion k hST (chartCharacter k S v hv) =
      chartCharacter k T v (hST hv) := rfl

theorem finite_character_denominator {S T : AddSubmonoid G}
    (v : G) (hv : v ∈ S)
    (hclear : ∀ m ∈ T, ∃ N : ℕ, m + N • v ∈ S)
    (F : Finset G) (hF : ∀ m ∈ F, m ∈ T) :
    ∃ N : ℕ, ∀ m ∈ F, m + N • v ∈ S := by
  revert hF
  induction F using Finset.induction_on with
  | empty =>
      intro hF
      exact ⟨0, by simp⟩
  | @insert m F hm ih =>
      intro hF
      obtain ⟨N, hN⟩ := ih (fun z hz => hF z (Finset.mem_insert_of_mem hz))
      obtain ⟨L, hL⟩ := hclear m (hF m (Finset.mem_insert_self m F))
      refine ⟨L + N, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · simpa only [add_nsmul, add_assoc] using S.add_mem hL (S.nsmul_mem hv N)
      · have hh := S.add_mem (hN z hz) (S.nsmul_mem hv L)
        simpa only [add_nsmul, add_assoc, add_comm, add_left_comm] using hh

/-- One common monomial clears every denominator of the actual finite
Laurent polynomial, not only of each monomial separately. -/
theorem polynomial_character_denominator {S T : AddSubmonoid G}
    (v : G) (hv : v ∈ S)
    (hclear : ∀ m ∈ T, ∃ N : ℕ, m + N • v ∈ S)
    (f : monoidChartAlgebra k T) :
    ∃ N : ℕ, (f : AddMonoidAlgebra k G) * single (N • v) (1 : k) ∈
      monoidChartAlgebra k S := by
  have hf : ∀ m ∈ (f : AddMonoidAlgebra k G).coeff.support, m ∈ T :=
    (mem_monoidChartAlgebra k T f).mp f.property
  obtain ⟨N, hN⟩ := finite_character_denominator v hv hclear
    (f : AddMonoidAlgebra k G).coeff.support hf
  refine ⟨N, (mem_monoidChartAlgebra k S _).mpr ?_⟩
  intro z hz
  have hsupport := AddMonoidAlgebra.support_coeff_mul_single_subset
    (f : AddMonoidAlgebra k G) (1 : k) (N • v)
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp (hsupport hz)
  exact hN m hm

/-- The literal inclusion is a localization map at the specified
character. The kernel condition follows from actual injectivity. -/
theorem monoidChartInclusion_isLocalizationMap {S T : AddSubmonoid G}
    (hST : S ≤ T) (v : G) (hv : v ∈ S) (hneg : -v ∈ T)
    (hclear : ∀ m ∈ T, ∃ N : ℕ, m + N • v ∈ S) :
    (Submonoid.powers (chartCharacter k S v hv)).IsLocalizationMap
      (monoidChartInclusion k hST) := by
  have hunit : IsUnit (monoidChartInclusion k hST (chartCharacter k S v hv)) := by
    exact (chartCharacterUnit k T v (hST hv) hneg).isUnit
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨N, hN⟩ := (Submonoid.mem_powers_iff _ _).mp y.property
    rw [← hN, map_pow]
    exact hunit.pow N
  · intro f
    obtain ⟨N, hN⟩ := polynomial_character_denominator k v hv hclear f
    let g : monoidChartAlgebra k S :=
      ⟨(f : AddMonoidAlgebra k G) * single (N • v) (1 : k), hN⟩
    let y : Submonoid.powers (chartCharacter k S v hv) :=
      ⟨(chartCharacter k S v hv) ^ N, (Submonoid.mem_powers_iff _ _).mpr ⟨N, rfl⟩⟩
    refine ⟨(g, y), ?_⟩
    apply Subtype.ext
    change (f : AddMonoidAlgebra k G) * (single v (1 : k)) ^ N =
      (f : AddMonoidAlgebra k G) * single (N • v) (1 : k)
    simp only [AddMonoidAlgebra.single_pow, one_pow]
  · intro x y hxy
    have heq := monoidChartInclusion_injective k hST hxy
    subst y
    exact ⟨1, rfl⟩

end PaperVerification.ToricCharacters
end
-- END PaperVerification.ToricChartLocalization
end

section
-- BEGIN PaperVerification.ToricNormalConeIntersection
/-!
# Common primitive supporting normals at smooth vertices

An integral supporting coordinate at one smooth vertex, if it vanishes at
another, is exactly one of the second vertex's primitive supporting coordinates.
The proof uses positive edge lengths and integral change-of-basis coefficients;
no face-lattice or normal-fan intersection property is assumed.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

/-- Evaluate a linear functional in genuine basis coordinates. -/
theorem linear_apply_basis_coordinates {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (f : E →ₗ[ℝ] ℝ) (b : Module.Basis ι ℝ E) (x : E) :
    f x = ∑ i, b.repr x i * f (b i) := by
  have h := congrArg f (b.sum_repr x)
  simpa only [map_sum, map_smul, smul_eq_mul] using h.symm

/-- A positive coefficient in a nonnegative dual expansion forces its
corresponding coordinate to vanish whenever the whole functional vanishes. -/
theorem coordinate_zero_of_positive_dual_coefficient {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (f : E →ₗ[ℝ] ℝ) (b : Module.Basis ι ℝ E) (x : E)
    (hx : ∀ i, 0 ≤ b.repr x i) (hf : ∀ i, 0 ≤ f (b i))
    (hzero : f x = 0) (j : ι) (hj : 0 < f (b j)) : b.repr x j = 0 := by
  have hsum : (∑ i, b.repr x i * f (b i)) = 0 := by
    rw [← linear_apply_basis_coordinates f b x, hzero]
  have hle := Finset.single_le_sum (f := fun i => b.repr x i * f (b i))
    (fun i _ => mul_nonneg (hx i) (hf i)) (Finset.mem_univ j)
  rw [hsum] at hle
  have he : b.repr x j * f (b j) = 0 :=
    le_antisymm hle (mul_nonneg (hx j) (hf j))
  exact (mul_eq_zero.mp he).resolve_right hj.ne'

/-- A primitive supporting coordinate shared by two smooth vertices is one
of the second vertex's primitive supporting coordinates. -/
theorem shared_supporting_coordinate {n : ℕ} (P : Set (Ambient n))
    (v w : Ambient n) (hv : v ∈ P) (hw : w ∈ P)
    (b c : Module.Basis (Fin n) ℤ (Lattice n))
    (lb lc : Fin n → ℝ) (hlb : ∀ i, 0 < lb i) (hlc : ∀ i, 0 < lc i)
    (hedgeb : ∀ i, v + lb i • integralBasisReal b i ∈ P)
    (hedgec : ∀ i, w + lc i • integralBasisReal c i ∈ P)
    (hconeb : ∀ x ∈ P, ∀ i, 0 ≤ (integralBasisReal b).repr (x - v) i)
    (hconec : ∀ x ∈ P, ∀ i, 0 ≤ (integralBasisReal c).repr (x - w) i)
    (i : Fin n) (hzero : (integralBasisReal b).repr (w - v) i = 0) :
    ∃ j : Fin n, (integralBasisReal c).coord j = (integralBasisReal b).coord i := by
  let bR := integralBasisReal b
  let cR := integralBasisReal c
  let f : Ambient n →ₗ[ℝ] ℝ := bR.coord i
  have hfzero : f (w - v) = 0 := hzero
  have hbeta (k : Fin n) : 0 ≤ f (cR k) := by
    have h := hconeb (w + lc k • cR k) (hedgec k) i
    have he : w + lc k • cR k - v = (w - v) + lc k • cR k := by abel
    change 0 ≤ f (w + lc k • cR k - v) at h
    rw [he, map_add, map_smul, hfzero, zero_add, smul_eq_mul] at h
    exact nonneg_of_mul_nonneg_right h (hlc k)
  have hbetapos : ∃ j : Fin n, 0 < f (cR j) := by
    by_contra hnot
    push_neg at hnot
    have hall (j : Fin n) : f (cR j) = 0 := le_antisymm (hnot j) (hbeta j)
    have hf : f = 0 := by
      apply cR.ext
      intro j
      simp only [LinearMap.zero_apply, hall]
    have hself : f (bR i) = 1 := by simp [f, Module.Basis.coord_apply]
    rw [hf, LinearMap.zero_apply] at hself
    norm_num at hself
  obtain ⟨j, hj⟩ := hbetapos
  let g : Ambient n →ₗ[ℝ] ℝ := cR.coord j
  have hforce (x : Ambient n) (hx : x ∈ P) (hfx : f (x - w) = 0) :
      g (x - w) = 0 :=
    coordinate_zero_of_positive_dual_coefficient f cR (x - w) (hconec x hx)
      hbeta hfx j hj
  have hfv : f (v - w) = 0 := by
    have he : v - w = -(w - v) := by abel
    rw [he, map_neg, hfzero, neg_zero]
  have hgv : g (v - w) = 0 := hforce v hv hfv
  have hother (k : Fin n) (hki : k ≠ i) : g (bR k) = 0 := by
    have hfk : f (bR k) = 0 := by
      simp [f, Module.Basis.coord_apply, hki, Ne.symm hki]
    have hpoint : f (v + lb k • bR k - w) = 0 := by
      have he : v + lb k • bR k - w = (v - w) + lb k • bR k := by abel
      rw [he, map_add, map_smul, hfv, hfk]
      simp
    have hg := hforce (v + lb k • bR k) (hedgeb k) hpoint
    have he : v + lb k • bR k - w = (v - w) + lb k • bR k := by abel
    rw [he, map_add, map_smul, hgv, zero_add, smul_eq_mul] at hg
    exact (mul_eq_zero.mp hg).resolve_left (hlb k).ne'
  have hlinear : g = g (bR i) • f := by
    apply bR.ext
    intro k
    by_cases hki : k = i
    · subst k
      simp [f, Module.Basis.coord_apply]
    · simp [hother k hki, f, Module.Basis.coord_apply, hki, Ne.symm hki]
  have hproduct : g (bR i) * f (cR j) = 1 := by
    have h := congrArg (fun l : Ambient n →ₗ[ℝ] ℝ => l (cR j)) hlinear
    have hself : g (cR j) = 1 := by simp [g, Module.Basis.coord_apply]
    simpa only [LinearMap.smul_apply, smul_eq_mul, hself] using h.symm
  have ha : g (bR i) = (c.repr (b i) j : ℝ) := by
    change (integralBasisReal c).repr (integralBasisReal b i) j = _
    rw [integralBasisReal_apply, integralBasisReal_repr]
  have hb : f (cR j) = (b.repr (c j) i : ℝ) := by
    change (integralBasisReal b).repr (integralBasisReal c j) i = _
    rw [integralBasisReal_apply, integralBasisReal_repr]
  have hab : c.repr (b i) j * b.repr (c j) i = 1 := by
    rw [ha, hb] at hproduct
    exact_mod_cast hproduct
  have hbetaZ : 0 < b.repr (c j) i := by
    rw [hb] at hj
    exact_mod_cast hj
  have haone : c.repr (b i) j = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hab with h | h
    · exact h
    · rw [h] at hab
      omega
  have hgcoef : g (bR i) = 1 := by rw [ha, haone]; norm_num
  refine ⟨j, ?_⟩
  change g = f
  simpa only [hgcoef, one_smul] using hlinear

/-- Equality of primitive integer normal vectors is equivalent to equality of
the associated real supporting coordinate functionals. -/
theorem integralDualBasis_eq_iff_real_coord_eq {n : ℕ}
    (b c : Module.Basis (Fin n) ℤ (Lattice n)) (i j : Fin n) :
    integralDualBasis b i = integralDualBasis c j ↔
      (integralBasisReal b).coord i = (integralBasisReal c).coord j := by
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    have he := congrArg (fun z : Lattice n => ∑ k, embed n z k * x k) h
    simpa only [integralDualBasis_real_pairing, Module.Basis.coord_apply] using he
  · intro h
    apply embed_injective n
    rw [embed_integralDualBasis, embed_integralDualBasis, h]

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- Two actual smooth vertex normal cones intersect in the cone on their
literal common primitive integer rays. This proves the fan intersection
property from polytope geometry. -/
theorem normalCone_basis_common_rays
    (vZ wZ : Lattice n) (hv : embed n vZ ∈ P.carrier) (hw : embed n wZ ∈ P.carrier)
    (b c : Module.Basis (Fin n) ℤ (Lattice n)) (lb lc : Fin n → ℕ)
    (hedgeb : ∀ i, 0 < lb i ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (lb i : ℤ) • b i)))
    (hedgec : ∀ i, 0 < lc i ∧
      P.IsEdge (embed n wZ) (embed n (wZ + (lc i : ℤ) • c i)))
    (hconeb : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) i)
    (hconec : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal c).repr (x - embed n wZ) i) :
    latticeRayCone (Finset.univ.image (integralDualBasis b)) ⊓
      latticeRayCone (Finset.univ.image (integralDualBasis c)) =
      latticeRayCone ((Finset.univ.image (integralDualBasis b)) ∩
        (Finset.univ.image (integralDualBasis c))) := by
  classical
  let I := Finset.univ.filter (fun i : Fin n =>
    (integralBasisReal b).repr (embed n wZ - embed n vZ) i = 0)
  have hpointb (i : Fin n) :
      embed n vZ + (lb i : ℝ) • integralBasisReal b i ∈ P.carrier := by
    have h := (P.edge_endpoints_extreme (hedgeb i).2).2.1
    simpa only [map_add, embed_int_smul, Int.cast_natCast,
      integralBasisReal_apply] using h
  have hpointc (i : Fin n) :
      embed n wZ + (lc i : ℝ) • integralBasisReal c i ∈ P.carrier := by
    have h := (P.edge_endpoints_extreme (hedgec i).2).2.1
    simpa only [map_add, embed_int_smul, Int.cast_natCast,
      integralBasisReal_apply] using h
  have hactive : I.image (integralDualBasis b) =
      (Finset.univ.image (integralDualBasis b)) ∩
        (Finset.univ.image (integralDualBasis c)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hi0 := (Finset.mem_filter.mp hi).2
      obtain ⟨j, hj⟩ := shared_supporting_coordinate P.carrier
        (embed n vZ) (embed n wZ) hv hw b c
        (fun i => lb i) (fun i => lc i)
        (fun i => by exact_mod_cast (hedgeb i).1)
        (fun i => by exact_mod_cast (hedgec i).1)
        hpointb hpointc hconeb hconec i hi0
      refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩,
        Finset.mem_image.mpr ⟨j, Finset.mem_univ j, ?_⟩⟩
      exact (integralDualBasis_eq_iff_real_coord_eq c b j i).mpr hj
    · intro hz
      obtain ⟨hzb, hzc⟩ := Finset.mem_inter.mp hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hzb
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hzc
      have hcoord := (integralDualBasis_eq_iff_real_coord_eq c b j i).mp hji
      have hb0 := hconeb (embed n wZ) hw i
      have hc0 := hconec (embed n vZ) hv j
      change 0 ≤ (integralBasisReal c).coord j (embed n vZ - embed n wZ) at hc0
      rw [hcoord] at hc0
      have he : embed n vZ - embed n wZ = -(embed n wZ - embed n vZ) := by abel
      rw [he, map_neg] at hc0
      change 0 ≤ -(integralBasisReal b).repr (embed n wZ - embed n vZ) i at hc0
      have hi0 : (integralBasisReal b).repr (embed n wZ - embed n vZ) i = 0 := by
        linarith
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi0⟩, rfl⟩
  have hvcone := P.normalCone_eq_latticeRayCone vZ b lb hedgeb hconeb
  have hwcone := P.normalCone_eq_latticeRayCone wZ c lc hedgec hconec
  have hinter := P.normalCone_inter_eq_dual_coordinate_face vZ (embed n wZ) hv hw
    b lb hedgeb hconeb
  apply SetLike.coe_injective
  change ((latticeRayCone (Finset.univ.image (integralDualBasis b)) : Set (Ambient n)) ∩
      (latticeRayCone (Finset.univ.image (integralDualBasis c)) : Set (Ambient n))) = _
  rw [← hvcone, ← hwcone, hinter]
  change (latticeRayCone (I.image (integralDualBasis b)) : Set (Ambient n)) = _
  rw [hactive]

end LatticePolytope

end PaperVerification.ToricGeometry
end
-- END PaperVerification.ToricNormalConeIntersection
end

section
-- BEGIN PaperVerification.ToricBasisBoxFamily
/-!
# A finite family of genuine basis boxes

This packages the column-configuration form of the lattice-covering theorem
for a finite family of unrelated real bases. The selected column subsets are
proved to be genuine bases, and their zonotopes are identified with the
ordinary unit boxes in the given basis coordinates.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped BigOperators

variable {J : Type*} [Fintype J] {d : ℕ}

/-- A point in the convex hull of a finite family has a probability vector on
the whole index type, with zero coefficients on unused indices. -/
theorem exists_probability_of_mem_convexHull_range {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : J → E) {x : E}
    (hx : x ∈ convexHull ℝ (Set.range v)) :
    ∃ p : J → ℝ, (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧ ∑ j, p j • v j = x := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s, w, hw, hsum, hcomb⟩ := hx
  let p : J → ℝ := fun j => if j ∈ s then w j else 0
  have hp : ∀ j, 0 ≤ p j := by
    intro j
    by_cases hj : j ∈ s
    · simpa [p, hj] using hw j hj
    · simp [p, hj]
  refine ⟨p, hp, ?_, ?_⟩
  · simpa [p, Finset.sum_ite_mem] using hsum
  · rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum] at hcomb
    simpa [p, ite_smul, Finset.sum_ite_mem] using hcomb

def familyIndexEquiv : (J × Fin d) ≃ Fin (Fintype.card (J × Fin d)) :=
  Fintype.equivFin _

def familyMatrix (b : J → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) :
    Matrix (Fin d) (Fin (Fintype.card (J × Fin d))) ℝ :=
  fun i k => b (familyIndexEquiv.symm k).1 (familyIndexEquiv.symm k).2 i

def familySubset (j : J) : Finset (Fin (Fintype.card (J × Fin d))) :=
  Finset.univ.image (fun i : Fin d => familyIndexEquiv (j, i))

theorem familyIndex_injective (j : J) :
    Function.Injective (fun i : Fin d => familyIndexEquiv (j, i)) := by
  intro i k hik
  exact congrArg Prod.snd (familyIndexEquiv.injective hik)

@[simp] theorem familySubset_card (j : J) : (familySubset (d := d) j).card = d := by
  rw [familySubset, Finset.card_image_of_injective _ (familyIndex_injective j)]
  simp

theorem mem_familySubset (j : J) (k : Fin (Fintype.card (J × Fin d))) :
    k ∈ familySubset j ↔ ∃ i : Fin d, familyIndexEquiv (j, i) = k := by
  simp [familySubset]

@[simp] theorem familyMatrix_column
    (b : J → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (j : J) (i : Fin d) :
    matrixColumn (familyMatrix b) (familyIndexEquiv (j, i)) = b j i := by
  ext k
  simp [matrixColumn, familyMatrix, familyIndexEquiv]

/-- Each selected column subset is a genuine full real basis. -/
theorem familySubset_squaredMinor_pos
    (b : J → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (j : J) :
    0 < squaredMinor (familyMatrix b) (familySubset j) := by
  let s := familySubset (d := d) j
  have hs : s.card = d := familySubset_card j
  apply (squaredMinor_pos_iff (familyMatrix b) s).mpr
  refine ⟨hs, ?_⟩
  rw [column_minor_ne_zero_iff_linearIndependent]
  let φ : Fin d → Fin d := fun i => (familyIndexEquiv.symm (s.orderEmbOfFin hs i)).2
  have hfirst (i : Fin d) : (familyIndexEquiv.symm (s.orderEmbOfFin hs i)).1 = j := by
    have himem : s.orderEmbOfFin hs i ∈ familySubset j := s.orderEmbOfFin_mem hs i
    obtain ⟨k, hk⟩ := (mem_familySubset j _).mp himem
    rw [← hk]
    simp
  have hφ : Function.Injective φ := by
    intro i k hik
    apply (s.orderEmbOfFin hs).injective
    apply familyIndexEquiv.symm.injective
    exact Prod.ext (by rw [hfirst, hfirst]) hik
  have hvec (i : Fin d) :
      matrixColumn (familyMatrix b) (s.orderEmbOfFin hs i) = b j (φ i) := by
    have he : s.orderEmbOfFin hs i = familyIndexEquiv (j, φ i) := by
      apply familyIndexEquiv.symm.injective
      simp only [Equiv.symm_apply_apply]
      exact Prod.ext (hfirst i) rfl
    rw [he, familyMatrix_column]
  simpa only [Function.comp_def, hvec] using (b j).linearIndependent.comp φ hφ

/-- The selected global column box is the ordinary unit box in the original basis. -/
theorem familySubsetBox_coordinates
    (b : J → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (j : J)
    {z : EuclideanSpace ℝ (Fin d)}
    (hz : z ∈ SubsetBox (matrixColumn (familyMatrix b)) (familySubset j)) :
    ∃ t : Fin d → ℝ, (∀ i, |t i| ≤ 1 / 2) ∧ ∑ i, t i • b j i = z := by
  classical
  obtain ⟨u, hu, husum⟩ := hz
  let t : Fin d → ℝ := fun i => u (familyIndexEquiv (j, i))
  have ht (i : Fin d) : |t i| ≤ 1 / 2 := by
    have hi : familyIndexEquiv (j, i) ∈ familySubset j :=
      (mem_familySubset j _).mpr ⟨i, rfl⟩
    simpa only [hi, ite_true, t] using hu (familyIndexEquiv (j, i))
  refine ⟨t, ht, ?_⟩
  have hout (k : Fin (Fintype.card (J × Fin d))) (hk : k ∉ familySubset j) : u k = 0 := by
    have h := hu k
    simp only [hk, ite_false, zero_div] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  calc
    (∑ i, t i • b j i) =
        ∑ k ∈ familySubset j, u k • matrixColumn (familyMatrix b) k := by
      rw [familySubset, Finset.sum_image]
      · simp only [familyMatrix_column, t]
      · intro i _ k _ hik
        exact familyIndex_injective j hik
    _ = ∑ k, u k • matrixColumn (familyMatrix b) k := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      simp [hout k hk]
    _ = z := husum

/-- Arbitrary matched integral basis boxes yield a lattice decomposition whenever
the target is a convex combination of their matched centers. -/
theorem finite_basis_boxes_lattice_decomposition
    (b : J → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (Γ : AddSubgroup (EuclideanSpace ℝ (Fin d)))
    (hclosed : IsClosed (Γ : Set (EuclideanSpace ℝ (Fin d))))
    (hbΓ : ∀ j i, b j i ∈ Γ)
    (A B : Set (EuclideanSpace ℝ (Fin d))) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (a c : J → EuclideanSpace ℝ (Fin d))
    (hboxA : ∀ j (t : Fin d → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      a j + ∑ i, t i • b j i ∈ A)
    (hboxB : ∀ j (t : Fin d → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      c j + ∑ i, t i • b j i ∈ B)
    (m : EuclideanSpace ℝ (Fin d)) (hmΓ : m ∈ Γ)
    (hm : m = ∑ j, p j • (a j + c j)) :
    ∃ x ∈ A, ∃ y ∈ B, x ∈ Γ ∧ y ∈ Γ ∧ x + y = m := by
  have hVΓ (k : Fin (Fintype.card (J × Fin d))) : matrixColumn (familyMatrix b) k ∈ Γ := by
    obtain ⟨⟨j, i⟩, rfl⟩ := familyIndexEquiv.surjective k
    simpa only [familyMatrix_column] using hbΓ j i
  apply matched_boxes_lattice_decomposition (familyMatrix b) Γ hclosed hVΓ
    A B hA hB (familySubset (d := d)) (familySubset_squaredMinor_pos b)
    p hp hpsum a c ?_ ?_ m hmΓ hm
  · intro j z hz
    obtain ⟨t, ht, rfl⟩ := familySubsetBox_coordinates b j hz
    exact hboxA j t ht
  · intro j z hz
    obtain ⟨t, ht, rfl⟩ := familySubsetBox_coordinates b j hz
    exact hboxB j t ht

/-- The same finite-family theorem in ordinary real coordinate space. The
change from the Euclidean norm to the usual product norm is made by a genuine
continuous linear equivalence, preserving the subgroup and all box points. -/
theorem finite_basis_boxes_lattice_decomposition_pi
    (b : J → Module.Basis (Fin d) ℝ (Fin d → ℝ))
    (Γ : AddSubgroup (Fin d → ℝ))
    (hclosed : IsClosed (Γ : Set (Fin d → ℝ))) (hbΓ : ∀ j i, b j i ∈ Γ)
    (A B : Set (Fin d → ℝ)) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (a c : J → (Fin d → ℝ))
    (hboxA : ∀ j (t : Fin d → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      a j + ∑ i, t i • b j i ∈ A)
    (hboxB : ∀ j (t : Fin d → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      c j + ∑ i, t i • b j i ∈ B)
    (m : Fin d → ℝ) (hmΓ : m ∈ Γ)
    (hm : m = ∑ j, p j • (a j + c j)) :
    ∃ x ∈ A, ∃ y ∈ B, x ∈ Γ ∧ y ∈ Γ ∧ x + y = m := by
  let e : EuclideanSpace ℝ (Fin d) ≃L[ℝ] (Fin d → ℝ) :=
    EuclideanSpace.equiv (Fin d) ℝ
  let b' : J → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
    fun j => (b j).map e.symm.toLinearEquiv
  let Γ' : AddSubgroup (EuclideanSpace ℝ (Fin d)) :=
    Γ.comap e.toLinearMap.toAddMonoidHom
  have hclosed' : IsClosed (Γ' : Set (EuclideanSpace ℝ (Fin d))) :=
    hclosed.preimage e.continuous
  have hbΓ' (j : J) (i : Fin d) : b' j i ∈ Γ' := by
    change e (b' j i) ∈ Γ
    simpa [b', Module.Basis.map_apply] using hbΓ j i
  have hboxA' (j : J) (t : Fin d → ℝ) (ht : ∀ i, |t i| ≤ 1 / 2) :
      e.symm (a j) + ∑ i, t i • b' j i ∈ e ⁻¹' A := by
    change e (e.symm (a j) + ∑ i, t i • b' j i) ∈ A
    simpa [b', map_add, map_sum, map_smul, Module.Basis.map_apply] using hboxA j t ht
  have hboxB' (j : J) (t : Fin d → ℝ) (ht : ∀ i, |t i| ≤ 1 / 2) :
      e.symm (c j) + ∑ i, t i • b' j i ∈ e ⁻¹' B := by
    change e (e.symm (c j) + ∑ i, t i • b' j i) ∈ B
    simpa [b', map_add, map_sum, map_smul, Module.Basis.map_apply] using hboxB j t ht
  have hm' : e.symm m = ∑ j, p j • (e.symm (a j) + e.symm (c j)) := by
    apply e.injective
    simpa only [map_add, map_sum, map_smul, ContinuousLinearEquiv.apply_symm_apply] using hm
  have hmΓ' : e.symm m ∈ Γ' := by
    change e (e.symm m) ∈ Γ
    simpa using hmΓ
  obtain ⟨x, hx, y, hy, hxΓ, hyΓ, hxy⟩ :=
    finite_basis_boxes_lattice_decomposition b' Γ' hclosed' hbΓ'
      (e ⁻¹' A) (e ⁻¹' B) (hA.linear_preimage e.toLinearMap) (hB.linear_preimage e.toLinearMap)
      p hp hpsum (fun j => e.symm (a j)) (fun j => e.symm (c j))
      hboxA' hboxB' (e.symm m) hmΓ' hm'
  refine ⟨e x, hx, e y, hy, hxΓ, hyΓ, ?_⟩
  simpa only [map_add, ContinuousLinearEquiv.apply_symm_apply] using congrArg e hxy

end PaperVerification.Toric
end
-- END PaperVerification.ToricBasisBoxFamily
end

section
-- BEGIN PaperVerification.ToricFanConstruction
/-!
# The finite smooth complete fan of a smooth lattice polytope

The fan is built from all subsets of the genuine primitive normal basis at each
actual vertex. Its cone intersection and completeness fields are derived from
the actual normal cones of the polytope.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

/-- Indices of the basis vectors belonging to a specified ray set. -/
def basisRayIndices {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (s : Finset (Lattice n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => b i ∈ s)

theorem image_basisRayIndices {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (s : Finset (Lattice n)) (hs : s ⊆ Finset.univ.image b) :
    (basisRayIndices b s).image b = s := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hi).2
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hs hv)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hv⟩, rfl⟩

/-- Subcones generated by subsets of one integral basis intersect exactly in
their common rays. -/
theorem latticeRayCone_inter_of_subsets_basis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (s t : Finset (Lattice n))
    (hs : s ⊆ Finset.univ.image b) (ht : t ⊆ Finset.univ.image b) :
    latticeRayCone s ⊓ latticeRayCone t = latticeRayCone (s ∩ t) := by
  let I := basisRayIndices b s
  let J := basisRayIndices b t
  have hI : I.image b = s := image_basisRayIndices b s hs
  have hJ : J.image b = t := image_basisRayIndices b t ht
  have hIJ : (I ∩ J).image b = s ∩ t := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hiI, hiJ⟩ := Finset.mem_inter.mp hi
      exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hiI).2,
        (Finset.mem_filter.mp hiJ).2⟩
    · intro hv
      obtain ⟨hvs, hvt⟩ := Finset.mem_inter.mp hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hs hvs)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ i, hvs⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, hvt⟩⟩, rfl⟩
  calc
    latticeRayCone s ⊓ latticeRayCone t =
        latticeRayCone (I.image b) ⊓ latticeRayCone (J.image b) := by
      rw [hI, hJ]
    _ = latticeRayCone ((I ∩ J).image b) := by
      ext x
      simp only [Submodule.mem_inf, mem_latticeRayCone_basis_iff]
      constructor
      · rintro ⟨⟨hpos, hIz⟩, ⟨_, hJz⟩⟩
        refine ⟨hpos, ?_⟩
        intro i hi
        by_cases hiI : i ∈ I
        · exact hJz i (fun hiJ => hi (Finset.mem_inter.mpr ⟨hiI, hiJ⟩))
        · exact hIz i hiI
      · rintro ⟨hpos, hIJz⟩
        refine ⟨⟨hpos, ?_⟩, ⟨hpos, ?_⟩⟩
        · intro i hi
          exact hIJz i (fun h => hi (Finset.mem_inter.mp h).1)
        · intro i hi
          exact hIJz i (fun h => hi (Finset.mem_inter.mp h).2)
    _ = latticeRayCone (s ∩ t) := by rw [hIJ]

section BasisFamily

variable {n : ℕ} {J : Type*} [Fintype J]

/-- All subsets of a finite family's full integral bases. -/
def basisFamilyCones (b : J → Module.Basis (Fin n) ℤ (Lattice n)) :
    Finset (Finset (Lattice n)) :=
  Finset.univ.biUnion (fun j => (Finset.univ.image (b j)).powerset)

theorem mem_basisFamilyCones (b : J → Module.Basis (Fin n) ℤ (Lattice n))
    (s : Finset (Lattice n)) :
    s ∈ basisFamilyCones b ↔ ∃ j, s ⊆ Finset.univ.image (b j) := by
  simp [basisFamilyCones]

/-- A covering basis family whose full cones have the true common-ray
intersection property produces a genuine finite smooth complete fan. -/
def fanOfBasisFamily (b : J → Module.Basis (Fin n) ℤ (Lattice n))
    (hinter : ∀ j k,
      latticeRayCone (Finset.univ.image (b j)) ⊓ latticeRayCone (Finset.univ.image (b k)) =
        latticeRayCone ((Finset.univ.image (b j)) ∩ (Finset.univ.image (b k))))
    (hcover : ∀ x : Ambient n, ∃ j, x ∈ latticeRayCone (Finset.univ.image (b j))) :
    SmoothCompleteFan n where
  cones := basisFamilyCones b
  smooth := by
    intro s hs
    obtain ⟨j, hj⟩ := (mem_basisFamilyCones b s).mp hs
    exact ⟨b j, basisRayIndices (b j) s, (image_basisRayIndices (b j) s hj).symm⟩
  downward := by
    intro s hs t hts
    obtain ⟨j, hj⟩ := (mem_basisFamilyCones b s).mp hs
    exact (mem_basisFamilyCones b t).mpr ⟨j, hts.trans hj⟩
  intersection := by
    intro s hs t ht
    obtain ⟨j, hsj⟩ := (mem_basisFamilyCones b s).mp hs
    obtain ⟨k, htk⟩ := (mem_basisFamilyCones b t).mp ht
    let U := Finset.univ.image (b j)
    let V := Finset.univ.image (b k)
    have hsets : (s ∩ (U ∩ V)) ∩ t = s ∩ t := by
      ext v
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨⟨hvs, hvU, hvV⟩, hvt⟩
        exact ⟨hvs, hvt⟩
      · rintro ⟨hvs, hvt⟩
        exact ⟨⟨hvs, hsj hvs, htk hvt⟩, hvt⟩
    ext x
    constructor
    · rintro ⟨hxs, hxt⟩
      have hxUV : x ∈ latticeRayCone (U ∩ V) := by
        rw [← hinter j k]
        exact ⟨latticeRayCone_mono hsj hxs, latticeRayCone_mono htk hxt⟩
      have hxmid : x ∈ latticeRayCone (s ∩ (U ∩ V)) := by
        rw [← latticeRayCone_inter_of_subsets_basis (b j) s (U ∩ V) hsj
          Finset.inter_subset_left]
        exact ⟨hxs, hxUV⟩
      have hmidV : s ∩ (U ∩ V) ⊆ V :=
        Finset.inter_subset_right.trans Finset.inter_subset_right
      have hxfin : x ∈ latticeRayCone ((s ∩ (U ∩ V)) ∩ t) := by
        rw [← latticeRayCone_inter_of_subsets_basis (b k) (s ∩ (U ∩ V)) t hmidV htk]
        exact ⟨hxmid, hxt⟩
      simpa only [hsets] using hxfin
    · intro h
      exact ⟨latticeRayCone_mono Finset.inter_subset_left h,
        latticeRayCone_mono Finset.inter_subset_right h⟩
  complete := by
    intro x
    obtain ⟨j, hj⟩ := hcover x
    exact ⟨Finset.univ.image (b j), (mem_basisFamilyCones b _).mpr ⟨j, Finset.Subset.refl _⟩, hj⟩

theorem fanOfBasisFamily_isPure (b : J → Module.Basis (Fin n) ℤ (Lattice n))
    (hinter : ∀ j k,
      latticeRayCone (Finset.univ.image (b j)) ⊓ latticeRayCone (Finset.univ.image (b k)) =
        latticeRayCone ((Finset.univ.image (b j)) ∩ (Finset.univ.image (b k))))
    (hcover : ∀ x : Ambient n, ∃ j, x ∈ latticeRayCone (Finset.univ.image (b j))) :
    (fanOfBasisFamily b hinter hcover).IsPure := by
  intro s hs
  obtain ⟨j, hj⟩ := (mem_basisFamilyCones b s).mp hs
  refine ⟨Finset.univ.image (b j),
    (mem_basisFamilyCones b _).mpr ⟨j, Finset.Subset.refl _⟩, hj, ?_⟩
  rw [Finset.card_image_of_injective _ (b j).injective, Finset.card_fin]

end BasisFamily

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- A smooth lattice polytope determines a finite smooth complete fan from its
actual vertex cones. The fan's intersection and completeness properties are
proved, not included as assumptions on the polytope. -/
theorem exists_smooth_complete_normal_fan_exact_pure (hP : P.Smooth) :
    ∃ «Σ» : SmoothCompleteFan n, «Σ».realCones = P.normalFan ∧ «Σ».IsPure := by
  classical
  let J := P.carrier.extremePoints ℝ
  letI : Fintype J := P.finite_vertices.fintype
  have hdata (v : J) := P.smooth_vertex_basis_cone hP v v.property
  choose vZ b lengths hvZ hedges hcone using hdata
  let d : J → Module.Basis (Fin n) ℤ (Lattice n) := fun v => integralDualBasis (b v)
  have hedges' (v : J) : ∀ i, 0 < lengths v i ∧
      P.IsEdge (embed n (vZ v)) (embed n (vZ v + (lengths v i : ℤ) • b v i)) := by
    simpa only [hvZ v] using hedges v
  have hcone' (v : J) : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal (b v)).repr (x - embed n (vZ v)) i := by
    simpa only [hvZ v] using hcone v
  have hnormal (v : J) : P.normalCone v =
      (latticeRayCone (Finset.univ.image (d v)) : Set (Ambient n)) := by
    simpa only [hvZ v] using
      P.normalCone_eq_latticeRayCone (vZ v) (b v) (lengths v) (hedges' v) (hcone' v)
  have hinter (v w : J) :
      latticeRayCone (Finset.univ.image (d v)) ⊓ latticeRayCone (Finset.univ.image (d w)) =
        latticeRayCone ((Finset.univ.image (d v)) ∩ (Finset.univ.image (d w))) := by
    apply P.normalCone_basis_common_rays (vZ v) (vZ w)
      (by simpa only [hvZ v] using v.property.1)
      (by simpa only [hvZ w] using w.property.1)
      (b v) (b w) (lengths v) (lengths w) (hedges' v) (hedges' w) (hcone' v) (hcone' w)
  have hcover (u : Ambient n) : ∃ v : J, u ∈ latticeRayCone (Finset.univ.image (d v)) := by
    let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) u
    obtain ⟨v, hv, hmin⟩ := P.exists_minimizing_vertex f
    refine ⟨⟨v, hv⟩, ?_⟩
    change u ∈ (latticeRayCone (Finset.univ.image (d ⟨v, hv⟩)) : Set (Ambient n))
    rw [← hnormal ⟨v, hv⟩]
    intro x hx
    change 0 ≤ f (x - v)
    rw [map_sub]
    exact sub_nonneg.mpr (hmin x hx)
  let «Σ» := fanOfBasisFamily d hinter hcover
  refine ⟨«Σ», ?_, fanOfBasisFamily_isPure d hinter hcover⟩
  ext C
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨j, hj⟩ := (mem_basisFamilyCones d s).mp hs
    let I := basisRayIndices (d j) s
    have hI : I.image (d j) = s := image_basisRayIndices (d j) s hj
    have h := P.subbasis_mem_normalFan (vZ j)
      (by simpa only [hvZ j] using j.property.1)
      (b j) (lengths j) (hedges' j) (hcone' j) I
    change (latticeRayCone (I.image (d j)) : Set (Ambient n)) ∈ P.normalFan at h
    simpa only [hI] using h
  · rintro ⟨x, hx, rfl⟩
    have hrange : Set.range (fun j : J => (j : Ambient n)) = P.carrier.extremePoints ℝ := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        exact j.property
      · intro hy
        exact ⟨⟨y, hy⟩, rfl⟩
    have hxhull : x ∈ convexHull ℝ (Set.range (fun j : J => (j : Ambient n))) := by
      rw [hrange, P.hull_vertices]
      exact hx
    obtain ⟨p, hp, hpsum, hpm⟩ :=
      PaperVerification.Toric.exists_probability_of_mem_convexHull_range
        (fun j : J => (j : Ambient n)) hxhull
    let K := Finset.univ.filter (fun j : J => 0 < p j)
    have hK : K.Nonempty := by
      have hpos : 0 < ∑ j, p j := by rw [hpsum]; norm_num
      obtain ⟨j, hj, hpj⟩ :=
        (Finset.sum_pos_iff_of_nonneg (fun j _ => hp j)).mp hpos
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hpj⟩⟩
    have hcones (j : J) (hj : j ∈ K) : Finset.univ.image (d j) ∈ «Σ».cones :=
      (mem_basisFamilyCones d _).mpr ⟨j, Finset.Subset.refl _⟩
    obtain ⟨s, hs, hspec⟩ := «Σ».exists_cone_finite_intersection K
      (fun j => Finset.univ.image (d j)) hK hcones
    refine ⟨s, hs, ?_⟩
    ext u
    rw [← hpm, P.mem_normalCone_convex_average (fun j : J => (j : Ambient n)) p
      (fun j => j.property.1) hp hpsum u]
    change (∀ j : J, 0 < p j → u ∈ P.normalCone (j : Ambient n)) ↔
      u ∈ latticeRayCone s
    rw [hspec u]
    simp only [hnormal, K, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl

/-- The exact normal-fan identification, with purity available separately
from the stronger construction theorem above. -/
theorem exists_smooth_complete_normal_fan_exact (hP : P.Smooth) :
    ∃ «Σ» : SmoothCompleteFan n, «Σ».realCones = P.normalFan := by
  obtain ⟨«Σ», «hΣ», hpure⟩ := P.exists_smooth_complete_normal_fan_exact_pure hP
  exact ⟨«Σ», «hΣ»⟩

/-- In particular every actual vertex normal cone is one of the cones of the
constructed finite smooth complete fan. -/
theorem exists_smooth_complete_normal_fan (hP : P.Smooth) :
    ∃ «Σ» : SmoothCompleteFan n,
      ∀ v ∈ P.carrier.extremePoints ℝ,
        ∃ s ∈ «Σ».cones, P.normalCone v = (latticeRayCone s : Set (Ambient n)) := by
  obtain ⟨«Σ», «hΣ»⟩ := P.exists_smooth_complete_normal_fan_exact hP
  refine ⟨«Σ», ?_⟩
  intro v hv
  have h : P.normalCone v ∈ P.normalFan := ⟨v, hv.1, rfl⟩
  rw [← «hΣ»] at h
  exact h

end LatticePolytope

end PaperVerification.ToricGeometry
end
-- END PaperVerification.ToricFanConstruction
end

section
-- BEGIN PaperVerification.ToricChartFaceLocalization



/-!
# The denominator of a smooth cone face

Removing coordinate inequalities is exactly localization by the product
of the removed coordinate characters. The exponent is their sum in the
actual dual integral basis. This applies to every actual smooth fan cone
and every face ray subset.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open scoped BigOperators Classical

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℤ E]

theorem coordinateConeMonoid_antitone (b : Module.Basis ι ℤ E)
    {I J : Finset ι} (hIJ : I ⊆ J) :
    coordinateConeMonoid b J ≤ coordinateConeMonoid b I :=
  fun x hx i hi => hx i (hIJ hi)

def faceDenominatorExponent (b : Module.Basis ι ℤ E) (I J : Finset ι) : E :=
  ∑ j ∈ J \ I, b j

theorem faceDenominatorExponent_repr (b : Module.Basis ι ℤ E)
    (I J : Finset ι) (i : ι) :
    b.repr (faceDenominatorExponent b I J) i = if i ∈ J \ I then 1 else 0 := by
  simp [faceDenominatorExponent, map_sum, Finsupp.finsetSum_apply,
    Module.Basis.repr_self_apply, Finsupp.single_apply, eq_comm]

theorem faceDenominatorExponent_mem (b : Module.Basis ι ℤ E) (I J : Finset ι) :
    faceDenominatorExponent b I J ∈ coordinateConeMonoid b J := by
  intro i hi
  rw [faceDenominatorExponent_repr]
  split_ifs <;> norm_num

theorem neg_faceDenominatorExponent_mem (b : Module.Basis ι ℤ E) (I J : Finset ι) :
    -faceDenominatorExponent b I J ∈ coordinateConeMonoid b I := by
  intro i hi
  rw [map_neg, Finsupp.neg_apply, faceDenominatorExponent_repr,
    if_neg (fun hh => (Finset.mem_sdiff.mp hh).2 hi), neg_zero]

theorem faceDenominatorExponent_clears (b : Module.Basis ι ℤ E)
    {I J : Finset ι} (hIJ : I ⊆ J) (x : E)
    (hx : x ∈ coordinateConeMonoid b I) :
    ∃ N : ℕ, x + N • faceDenominatorExponent b I J ∈ coordinateConeMonoid b J := by
  let N := (J \ I).sup (fun i => (-b.repr x i).toNat)
  refine ⟨N, ?_⟩
  intro i hiJ
  have hrepr : b.repr (x + N • faceDenominatorExponent b I J) i =
      b.repr x i + (N : ℤ) * (if i ∈ J \ I then 1 else 0) := by
    simp only [map_add, map_nsmul, Finsupp.add_apply, Finsupp.smul_apply,
      nsmul_eq_mul, faceDenominatorExponent_repr]
  rw [hrepr]
  by_cases hiI : i ∈ I
  · rw [if_neg (fun hh => (Finset.mem_sdiff.mp hh).2 hiI), mul_zero, add_zero]
    exact hx i hiI
  · have hi : i ∈ J \ I := Finset.mem_sdiff.mpr ⟨hiJ, hiI⟩
    rw [if_pos hi, mul_one]
    have hle : (-b.repr x i).toNat ≤ N :=
      Finset.le_sup (f := fun j => (-b.repr x j).toNat) hi
    have hleZ : (((-b.repr x i).toNat : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast hle
    have hself := Int.self_le_toNat (-b.repr x i)
    omega

/-- After restricting to another face, the original denominator removes
exactly the inequalities not shared by the two faces. Coordinates already
invertible on the restricted chart cause no additional condition. -/
theorem faceDenominatorExponent_clears_intersection (b : Module.Basis ι ℤ E)
    {I K J : Finset ι} (hIJ : I ⊆ J) (x : E)
    (hx : x ∈ coordinateConeMonoid b (I ∩ K)) :
    ∃ N : ℕ, x + N • faceDenominatorExponent b K J ∈ coordinateConeMonoid b I := by
  let N := (I \ K).sup (fun i => (-b.repr x i).toNat)
  refine ⟨N, ?_⟩
  intro i hiI
  have hrepr : b.repr (x + N • faceDenominatorExponent b K J) i =
      b.repr x i + (N : ℤ) * (if i ∈ J \ K then 1 else 0) := by
    simp only [map_add, map_nsmul, Finsupp.add_apply, Finsupp.smul_apply,
      nsmul_eq_mul, faceDenominatorExponent_repr]
  rw [hrepr]
  by_cases hiK : i ∈ K
  · rw [if_neg (fun hh => (Finset.mem_sdiff.mp hh).2 hiK), mul_zero, add_zero]
    exact hx i (Finset.mem_inter.mpr ⟨hiI, hiK⟩)
  · have hi : i ∈ J \ K := Finset.mem_sdiff.mpr ⟨hIJ hiI, hiK⟩
    rw [if_pos hi, mul_one]
    have hle : (-b.repr x i).toNat ≤ N :=
      Finset.le_sup (f := fun j => (-b.repr x j).toNat)
        (Finset.mem_sdiff.mpr ⟨hiI, hiK⟩)
    have hleZ : (((-b.repr x i).toNat : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast hle
    have hself := Int.self_le_toNat (-b.repr x i)
    omega

variable (k : Type*) [CommSemiring k]

theorem coordinateChartInclusion_isLocalizationMap
    (b : Module.Basis ι ℤ E) {I J : Finset ι} (hIJ : I ⊆ J) :
    (Submonoid.powers (chartCharacter k (coordinateConeMonoid b J)
      (faceDenominatorExponent b I J) (faceDenominatorExponent_mem b I J))).IsLocalizationMap
        (monoidChartInclusion k (coordinateConeMonoid_antitone b hIJ)) :=
  monoidChartInclusion_isLocalizationMap k (coordinateConeMonoid_antitone b hIJ)
    _ (faceDenominatorExponent_mem b I J) (neg_faceDenominatorExponent_mem b I J)
    (faceDenominatorExponent_clears b hIJ)

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open scoped BigOperators Classical

theorem dualConeMonoid_antitone {n : ℕ} {s t : Finset (Lattice n)} (hts : t ⊆ s) :
    dualConeMonoid s ≤ dualConeMonoid t := fun m hm u hu => hm u (hts hu)

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Every actual smooth cone face has a single integral character whose
inversion removes precisely the discarded inequalities. -/
theorem exists_face_character_denominator
    (s t : Finset (Lattice n)) (hs : s ∈ «Σ».cones) (hts : t ⊆ s) :
    ∃ v : Lattice n, v ∈ dualConeMonoid s ∧ -v ∈ dualConeMonoid t ∧
      ∀ m ∈ dualConeMonoid t, ∃ N : ℕ, m + N • v ∈ dualConeMonoid s := by
  obtain ⟨b, J, rfl⟩ := «Σ».smooth s hs
  let I := basisRayIndices b t
  have hI : I.image b = t := image_basisRayIndices b t
    (hts.trans (Finset.image_subset_image (Finset.subset_univ J)))
  have hIJ : I ⊆ J := by
    intro i hi
    have hbi : b i ∈ t := hI ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp (hts hbi)
    exact b.injective hji ▸ hj
  refine ⟨faceDenominatorExponent (integralDualBasis b) I J, ?_, ?_, ?_⟩
  · rw [dualConeMonoid_basis_eq]
    exact faceDenominatorExponent_mem (integralDualBasis b) I J
  · rw [← hI, dualConeMonoid_basis_eq]
    exact neg_faceDenominatorExponent_mem (integralDualBasis b) I J
  · intro m hm
    rw [← hI, dualConeMonoid_basis_eq] at hm
    obtain ⟨N, hN⟩ := faceDenominatorExponent_clears (integralDualBasis b) hIJ m hm
    exact ⟨N, (dualConeMonoid_basis_eq b J).symm ▸ hN⟩

theorem chart_face_isLocalizationMap (k : Type*) [CommSemiring k]
    (s t : Finset (Lattice n)) (hs : s ∈ «Σ».cones) (hts : t ⊆ s) :
    ∃ (v : Lattice n) (hv : v ∈ dualConeMonoid s),
      (Submonoid.powers (chartCharacter k (dualConeMonoid s) v hv)).IsLocalizationMap
        (monoidChartInclusion k (dualConeMonoid_antitone hts)) := by
  obtain ⟨v, hv, hneg, hclear⟩ := «Σ».exists_face_character_denominator s t hs hts
  exact ⟨v, hv, monoidChartInclusion_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hneg hclear⟩

/-- The same character localizes both a cone chart to one face and another
face chart to their actual intersection. -/
theorem exists_intersection_character_denominator
    (q s t : Finset (Lattice n)) (hq : q ∈ «Σ».cones)
    (hs : s ⊆ q) (ht : t ⊆ q) :
    ∃ v : Lattice n, v ∈ dualConeMonoid q ∧ -v ∈ dualConeMonoid t ∧
      (∀ m ∈ dualConeMonoid t, ∃ N : ℕ, m + N • v ∈ dualConeMonoid q) ∧
      (∀ m ∈ dualConeMonoid (s ∩ t), ∃ N : ℕ, m + N • v ∈ dualConeMonoid s) := by
  obtain ⟨b, J, rfl⟩ := «Σ».smooth q hq
  let I := basisRayIndices b s
  let K := basisRayIndices b t
  have hI : I.image b = s := image_basisRayIndices b s
    (hs.trans (Finset.image_subset_image (Finset.subset_univ J)))
  have hK : K.image b = t := image_basisRayIndices b t
    (ht.trans (Finset.image_subset_image (Finset.subset_univ J)))
  have hIJ : I ⊆ J := (Finset.image_subset_image_iff b.injective).mp (hI.symm ▸ hs)
  have hKJ : K ⊆ J := (Finset.image_subset_image_iff b.injective).mp (hK.symm ▸ ht)
  have hIK : (I ∩ K).image b = s ∩ t := by
    rw [Finset.image_inter I K b.injective, hI, hK]
  let v := faceDenominatorExponent (integralDualBasis b) K J
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · rw [dualConeMonoid_basis_eq]
    exact faceDenominatorExponent_mem (integralDualBasis b) K J
  · rw [← hK, dualConeMonoid_basis_eq]
    exact neg_faceDenominatorExponent_mem (integralDualBasis b) K J
  · intro m hm
    rw [← hK, dualConeMonoid_basis_eq] at hm
    obtain ⟨N, hN⟩ := faceDenominatorExponent_clears (integralDualBasis b) hKJ m hm
    exact ⟨N, (dualConeMonoid_basis_eq b J).symm ▸ hN⟩
  · intro m hm
    rw [← hIK, dualConeMonoid_basis_eq] at hm
    obtain ⟨N, hN⟩ := faceDenominatorExponent_clears_intersection
      (integralDualBasis b) hIJ m hm
    refine ⟨N, ?_⟩
    rw [← hI, dualConeMonoid_basis_eq]
    exact hN

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
-- END PaperVerification.ToricChartFaceLocalization
end

section
-- BEGIN PaperVerification.ToricChartOpenImmersions



/-!
# Actual affine chart maps and their open images

The schemes are spectra of the semigroup subalgebras inside the character
ring. Every morphism is induced by their literal inclusion. Localization
therefore gives an actual open immersion, with its specified principal
open image. The final lemma is the categorical pullback statement for
two localizations with the same character denominator.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

variable (k : Type*) [CommRing k]
variable {G : Type*} [AddCommGroup G]

def monoidChartScheme (S : AddSubmonoid G) : Scheme :=
  Spec (CommRingCat.of (monoidChartAlgebra k S))

def monoidChartSpecMap {S T : AddSubmonoid G} (hST : S ≤ T) :
    monoidChartScheme k T ⟶ monoidChartScheme k S :=
  Spec.map (CommRingCat.ofHom (monoidChartInclusion k hST).toRingHom)

@[simp] theorem monoidChartSpecMap_comp {S T U : AddSubmonoid G}
    (hST : S ≤ T) (hTU : T ≤ U) :
    monoidChartSpecMap k hTU ≫ monoidChartSpecMap k hST =
      monoidChartSpecMap k (hST.trans hTU) := by
  dsimp only [monoidChartSpecMap, monoidChartScheme]
  rw [← Spec.map_comp]
  congr 1

@[simp] theorem monoidChartSpecMap_self (S : AddSubmonoid G) :
    monoidChartSpecMap k (le_refl S) = 𝟙 (monoidChartScheme k S) := by
  have heq : CommRingCat.ofHom (monoidChartInclusion k (le_refl S)).toRingHom =
      𝟙 (CommRingCat.of (monoidChartAlgebra k S)) := by
    ext f
    rfl
  exact (congrArg Spec.map heq).trans (Spec.map_id _)

theorem monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap
    {S T : AddSubmonoid G} (hST : S ≤ T) (v : G) (hv : v ∈ S)
    (hloc : (Submonoid.powers (chartCharacter k S v hv)).IsLocalizationMap
      (monoidChartInclusion k hST)) :
    IsOpenImmersion (monoidChartSpecMap k hST) := by
  letI : Algebra (monoidChartAlgebra k S) (monoidChartAlgebra k T) :=
    (monoidChartInclusion k hST).toRingHom.toAlgebra
  letI : IsLocalization.Away (chartCharacter k S v hv) (monoidChartAlgebra k T) :=
    (isLocalization_iff_isLocalizationMap _ _).mpr hloc
  exact IsOpenImmersion.of_isLocalization (chartCharacter k S v hv)

theorem monoidChartSpecMap_opensRange_of_isLocalizationMap
    {S T : AddSubmonoid G} (hST : S ≤ T) (v : G) (hv : v ∈ S)
    (hloc : (Submonoid.powers (chartCharacter k S v hv)).IsLocalizationMap
      (monoidChartInclusion k hST))
    [IsOpenImmersion (monoidChartSpecMap k hST)] :
    (monoidChartSpecMap k hST).opensRange =
      PrimeSpectrum.basicOpen (chartCharacter k S v hv) := by
  letI : Algebra (monoidChartAlgebra k S) (monoidChartAlgebra k T) :=
    (monoidChartInclusion k hST).toRingHom.toAlgebra
  letI : IsLocalization.Away (chartCharacter k S v hv) (monoidChartAlgebra k T) :=
    (isLocalization_iff_isLocalizationMap _ _).mpr hloc
  exact SetLike.coe_injective
    (PrimeSpectrum.localization_away_comap_range (monoidChartAlgebra k T)
      (chartCharacter k S v hv))

/-- An actual square of chart inclusions is a pullback when its two
vertical arrows invert the same character before and after restriction.
No abstract replacement of any chart algebra is used. -/
theorem monoidChartSquare_isPullback
    {S T U V : AddSubmonoid G}
    (hST : S ≤ T) (hSU : S ≤ U) (hTV : T ≤ V) (hUV : U ≤ V)
    (v : G) (hv : v ∈ S)
    (hlocSU : (Submonoid.powers (chartCharacter k S v hv)).IsLocalizationMap
      (monoidChartInclusion k hSU))
    (hlocTV : (Submonoid.powers (chartCharacter k T v (hST hv))).IsLocalizationMap
      (monoidChartInclusion k hTV)) :
    IsPullback (monoidChartSpecMap k hUV) (monoidChartSpecMap k hTV)
      (monoidChartSpecMap k hSU) (monoidChartSpecMap k hST) := by
  letI := monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k hSU v hv hlocSU
  letI := monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k hTV v (hST hv) hlocTV
  apply IsOpenImmersion.isPullback
  · simp only [monoidChartSpecMap_comp]
  · rw [monoidChartSpecMap_opensRange_of_isLocalizationMap k hSU v hv hlocSU,
      monoidChartSpecMap_opensRange_of_isLocalizationMap k hTV v (hST hv) hlocTV]
    change Spec.map (CommRingCat.ofHom (monoidChartInclusion k hST).toRingHom) ⁻¹ᵁ
      PrimeSpectrum.basicOpen (chartCharacter k S v hv) =
        PrimeSpectrum.basicOpen (chartCharacter k T v (hST hv))
    rw [SpecMap_preimage_basicOpen]
    rfl

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory

variable (k : Type*) [CommRing k] {n : ℕ}

def coneChart (s : Finset (Lattice n)) : Scheme :=
  monoidChartScheme k (dualConeMonoid s)

def coneChartFaceMap {s t : Finset (Lattice n)} (hts : t ⊆ s) :
    coneChart k t ⟶ coneChart k s :=
  monoidChartSpecMap k (dualConeMonoid_antitone hts)

@[simp] theorem coneChartFaceMap_comp {s t u : Finset (Lattice n)}
    (hts : t ⊆ s) (hut : u ⊆ t) :
    coneChartFaceMap k hut ≫ coneChartFaceMap k hts =
      coneChartFaceMap k (hut.trans hts) :=
  monoidChartSpecMap_comp k (dualConeMonoid_antitone hts) (dualConeMonoid_antitone hut)

@[simp] theorem coneChartFaceMap_self (s : Finset (Lattice n)) :
    coneChartFaceMap k (Finset.Subset.refl s) = 𝟙 (coneChart k s) :=
  monoidChartSpecMap_self k (dualConeMonoid s)

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n)

theorem coneChartFaceMap_isOpenImmersion (s t : Finset (Lattice n))
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) :
    IsOpenImmersion (coneChartFaceMap k hts) := by
  obtain ⟨v, hv, hloc⟩ := «Σ».chart_face_isLocalizationMap k s t hs hts
  exact monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hloc

theorem coneChartFaceMap_principal_open (s t : Finset (Lattice n))
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s)
    [IsOpenImmersion (coneChartFaceMap k hts)] :
    ∃ (v : Lattice n) (hv : v ∈ dualConeMonoid s),
      (coneChartFaceMap k hts).opensRange =
        PrimeSpectrum.basicOpen (chartCharacter k (dualConeMonoid s) v hv) := by
  obtain ⟨v, hv, hloc⟩ := «Σ».chart_face_isLocalizationMap k s t hs hts
  letI := monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hloc
  exact ⟨v, hv, monoidChartSpecMap_opensRange_of_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hloc⟩

/-- The affine chart of the actual common face is the scheme-theoretic
overlap of two face charts inside the original chart. -/
theorem coneChart_faces_isPullback (q s t : Finset (Lattice n))
    (hq : q ∈ «Σ».cones) (hs : s ⊆ q) (ht : t ⊆ q) :
    CategoryTheory.IsPullback
      (coneChartFaceMap k (Finset.inter_subset_right : s ∩ t ⊆ t))
      (coneChartFaceMap k (Finset.inter_subset_left : s ∩ t ⊆ s))
      (coneChartFaceMap k ht) (coneChartFaceMap k hs) := by
  obtain ⟨v, hv, hneg, hclear, hclearInter⟩ :=
    «Σ».exists_intersection_character_denominator q s t hq hs ht
  apply monoidChartSquare_isPullback k
    (dualConeMonoid_antitone hs) (dualConeMonoid_antitone ht)
    (dualConeMonoid_antitone Finset.inter_subset_left)
    (dualConeMonoid_antitone Finset.inter_subset_right) v hv
  · exact monoidChartInclusion_isLocalizationMap k (dualConeMonoid_antitone ht)
      v hv hneg hclear
  · exact monoidChartInclusion_isLocalizationMap k
      (dualConeMonoid_antitone Finset.inter_subset_left)
      v (dualConeMonoid_antitone hs hv)
      (dualConeMonoid_antitone Finset.inter_subset_right hneg) hclearInter

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
-- END PaperVerification.ToricChartOpenImmersions
end

section
-- BEGIN PaperVerification.ToricFanScheme



/-!
# The actual scheme obtained by gluing a smooth fan

Every cone supplies its actual affine semigroup chart. Face inclusions are
the previously proved open immersions. Their actual intersections prove
local directedness, so Mathlib's scheme gluing construction applies. The
result is a scheme with an actual affine open cover, not a structure whose
fields assume a toric dictionary.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PaperVerification.ToricCharacters
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [CommRing k]

abbrev ConeIndex := {s : Finset (Lattice n) // s ∈ «Σ».cones}

def coneDiagram : «Σ».ConeIndex ⥤ Scheme.{u} where
  obj s := coneChart k s.val
  map f := coneChartFaceMap k (leOfHom f)
  map_id s := coneChartFaceMap_self k s.val
  map_comp f g := (coneChartFaceMap_comp k (leOfHom g) (leOfHom f)).symm

instance coneDiagram_map_isOpenImmersion {s t : «Σ».ConeIndex} (f : s ⟶ t) :
    IsOpenImmersion ((«Σ».coneDiagram k).map f) :=
  «Σ».coneChartFaceMap_isOpenImmersion k t.val s.val t.property (leOfHom f)

/-- The local directedness condition is proved from the actual common-face
pullback, including the underlying point lifting. -/
instance coneDiagram_isLocallyDirected :
    («Σ».coneDiagram k ⋙ Scheme.forget).IsLocallyDirected where
  cond := by
    intro i j q fi fj xi xj h
    let l : «Σ».ConeIndex :=
      ⟨i.val ∩ j.val, «Σ».downward i.val i.property _ Finset.inter_subset_left⟩
    let fli : l ⟶ i := homOfLE Finset.inter_subset_left
    let flj : l ⟶ j := homOfLE Finset.inter_subset_right
    letI := «Σ».coneChartFaceMap_isOpenImmersion k q.val i.val q.property (leOfHom fi)
    letI := «Σ».coneChartFaceMap_isOpenImmersion k q.val j.val q.property (leOfHom fj)
    have H := «Σ».coneChart_faces_isPullback k q.val i.val j.val
      q.property (leOfHom fi) (leOfHom fj)
    change coneChartFaceMap k (leOfHom fi) xi =
      coneChartFaceMap k (leOfHom fj) xj at h
    have hx : xi ∈ Set.range (pullback.snd
        (coneChartFaceMap k (leOfHom fj)) (coneChartFaceMap k (leOfHom fi))) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact ⟨xj, h.symm⟩
    obtain ⟨z, hz⟩ := hx
    let x := H.isoPullback.inv z
    have hxi : coneChartFaceMap k (Finset.inter_subset_left : i.val ∩ j.val ⊆ i.val) x =
        xi := by
      exact (congrArg (fun f => f z) H.isoPullback_inv_snd).trans hz
    have hxj : coneChartFaceMap k (Finset.inter_subset_right : i.val ∩ j.val ⊆ j.val) x =
        xj := by
      apply (coneChartFaceMap k (leOfHom fj)).isOpenEmbedding.injective
      calc
        coneChartFaceMap k (leOfHom fj)
            (coneChartFaceMap k (Finset.inter_subset_right : i.val ∩ j.val ⊆ j.val) x) =
          coneChartFaceMap k (leOfHom fi)
            (coneChartFaceMap k (Finset.inter_subset_left : i.val ∩ j.val ⊆ i.val) x) :=
          congrArg (fun f => f x) H.w
        _ = coneChartFaceMap k (leOfHom fi) xi := by rw [hxi]
        _ = coneChartFaceMap k (leOfHom fj) xj := h
    exact ⟨l, fli, flj, x, hxi, hxj⟩

/-- Genuine Mathlib gluing data, with all its cocycle obligations derived
by locally directed scheme gluing. -/
def fanGlueData : Scheme.GlueData.{u} :=
  Scheme.IsLocallyDirected.glueData («Σ».coneDiagram k)

/-- The actual colimit scheme of the affine charts. -/
def fanScheme : Scheme.{u} := colimit («Σ».coneDiagram k)

def fanChartMap (s : «Σ».ConeIndex) : coneChart k s.val ⟶ «Σ».fanScheme k :=
  colimit.ι («Σ».coneDiagram k) s

instance fanChartMap_isOpenImmersion (s : «Σ».ConeIndex) :
    IsOpenImmersion («Σ».fanChartMap k s) := by
  exact inferInstanceAs (IsOpenImmersion (colimit.ι («Σ».coneDiagram k) s))

def fanSchemeOpenCover : («Σ».fanScheme k).OpenCover :=
  Scheme.IsLocallyDirected.openCover («Σ».coneDiagram k)

@[reassoc (attr := simp)] theorem fanChartMap_naturality
    {s t : «Σ».ConeIndex} (hst : s.val ⊆ t.val) :
    coneChartFaceMap k hst ≫ «Σ».fanChartMap k t = «Σ».fanChartMap k s :=
  colimit.w («Σ».coneDiagram k) (homOfLE hst)

theorem fanChartMap_jointly_surjective (x : «Σ».fanScheme k) :
    ∃ (s : «Σ».ConeIndex) (y : coneChart k s.val), «Σ».fanChartMap k s y = x :=
  Scheme.IsLocallyDirected.ι_jointly_surjective («Σ».coneDiagram k) x

/-- Equality of two points in the glued scheme is witnessed in the actual
intersection cone chart. No larger relation is imposed by the gluing. -/
theorem fanChartMap_eq_iff (s t : «Σ».ConeIndex)
    (x : coneChart k s.val) (y : coneChart k t.val) :
    «Σ».fanChartMap k s x = «Σ».fanChartMap k t y ↔
      ∃ z : coneChart k (s.val ∩ t.val),
        coneChartFaceMap k Finset.inter_subset_left z = x ∧
        coneChartFaceMap k Finset.inter_subset_right z = y := by
  constructor
  · intro h
    obtain ⟨l, fls, flt, z, hzs, hzt⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff («Σ».coneDiagram k)).mp h
    have hl : l.val ⊆ s.val ∩ t.val :=
      Finset.subset_inter (leOfHom fls) (leOfHom flt)
    let z' : coneChart k l.val := z
    have hzs' : coneChartFaceMap k (leOfHom fls) z' = x := hzs
    have hzt' : coneChartFaceMap k (leOfHom flt) z' = y := hzt
    refine ⟨coneChartFaceMap k hl z', ?_, ?_⟩
    · exact (congrArg (fun f : coneChart k l.val ⟶ coneChart k s.val => f z')
        (coneChartFaceMap_comp k
          (Finset.inter_subset_left : s.val ∩ t.val ⊆ s.val) hl)).trans hzs'
    · exact (congrArg (fun f : coneChart k l.val ⟶ coneChart k t.val => f z')
        (coneChartFaceMap_comp k
          (Finset.inter_subset_right : s.val ∩ t.val ⊆ t.val) hl)).trans hzt'
  · rintro ⟨z, rfl, rfl⟩
    let l : «Σ».ConeIndex :=
      ⟨s.val ∩ t.val, «Σ».downward s.val s.property _ Finset.inter_subset_left⟩
    change (coneChartFaceMap k (show l.val ⊆ s.val from Finset.inter_subset_left) ≫
      «Σ».fanChartMap k s) z =
      (coneChartFaceMap k (show l.val ⊆ t.val from Finset.inter_subset_right) ≫
        «Σ».fanChartMap k t) z
    rw [«Σ».fanChartMap_naturality, «Σ».fanChartMap_naturality]

/-- The affine overlap in the glued scheme is the common-face chart as
a scheme-theoretic pullback, not merely as a set of points. -/
theorem fanChart_inter_isPullback (s t : «Σ».ConeIndex) :
    IsPullback
      (coneChartFaceMap k (Finset.inter_subset_right : s.val ∩ t.val ⊆ t.val))
      (coneChartFaceMap k (Finset.inter_subset_left : s.val ∩ t.val ⊆ s.val))
      («Σ».fanChartMap k t) («Σ».fanChartMap k s) := by
  let l : «Σ».ConeIndex :=
    ⟨s.val ∩ t.val, «Σ».downward s.val s.property _ Finset.inter_subset_left⟩
  letI := «Σ».coneChartFaceMap_isOpenImmersion k s.val l.val s.property Finset.inter_subset_left
  apply IsOpenImmersion.isPullback
  · exact («Σ».fanChartMap_naturality k (s := l) (t := s)
      Finset.inter_subset_left).trans
        («Σ».fanChartMap_naturality k (s := l) (t := t)
          Finset.inter_subset_right).symm
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨z, hz, _⟩ := («Σ».fanChartMap_eq_iff k s t x y).mp hy.symm
      exact ⟨z, hz⟩
    · rintro ⟨z, rfl⟩
      refine ⟨coneChartFaceMap k Finset.inter_subset_right z, ?_⟩
      exact («Σ».fanChartMap_eq_iff k s t _ _).mpr ⟨z, rfl, rfl⟩ |>.symm

/-- The zero cone is the actual open torus chart. -/
def zeroConeIndex : «Σ».ConeIndex := ⟨∅, «Σ».empty_mem⟩

def torusOpenMap : coneChart k (∅ : Finset (Lattice n)) ⟶ «Σ».fanScheme k :=
  «Σ».fanChartMap k «Σ».zeroConeIndex

instance torusOpenMap_isOpenImmersion : IsOpenImmersion («Σ».torusOpenMap k) :=
  inferInstanceAs (IsOpenImmersion («Σ».fanChartMap k «Σ».zeroConeIndex))

set_option maxHeartbeats 1000000 in
@[reassoc (attr := simp)] theorem torusOpenMap_chart (s : «Σ».ConeIndex) :
    coneChartFaceMap k (Finset.empty_subset s.val) ≫ «Σ».fanChartMap k s =
      «Σ».torusOpenMap k :=
  «Σ».fanChartMap_naturality k (s := «Σ».zeroConeIndex) (t := s)
    (Finset.empty_subset s.val)

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
-- END PaperVerification.ToricFanScheme
end

section
-- BEGIN PaperVerification.ToricChartFactorization



/-! # Unique factorization on every actual smooth affine chart -/

noncomputable section

namespace PaperVerification.ToricCharacters

variable (k : Type*) [Field k]

def finiteLatticeCoordinates (J : Type*) [Fintype J] :
    (J → ℤ) ≃+ (Fin (Fintype.card J) → ℤ) where
  toFun x i := x ((Fintype.equivFin J).symm i)
  invFun x j := x (Fintype.equivFin J j)
  left_inv x := by funext j; simp
  right_inv x := by funext i; simp
  map_add' _ _ := rfl

def finiteCharacterRingEquiv (J : Type*) [Fintype J] :
    AddMonoidAlgebra k (J → ℤ) ≃ₐ[k] torusCoordinateRing k (Fintype.card J) :=
  AddMonoidAlgebra.domCongr k k (finiteLatticeCoordinates J)

theorem finiteCharacterRing_isDomain (J : Type*) [Fintype J] :
    IsDomain (AddMonoidAlgebra k (J → ℤ)) := by
  letI := torusCoordinateRing_isDomain k (Fintype.card J)
  exact MulEquiv.isDomain _ (finiteCharacterRingEquiv k J).toMulEquiv

theorem finiteCharacterRing_uniqueFactorization (J : Type*) [Fintype J] :
    UniqueFactorizationMonoid (AddMonoidAlgebra k (J → ℤ)) :=
  (finiteCharacterRingEquiv k J).symm.toMulEquiv.uniqueFactorizationMonoid
    (torusCoordinateRing_uniqueFactorization k (Fintype.card J))

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricCharacters

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type*) [Field k]

theorem chartRing_isDomain (s : Finset (Lattice n)) (hs : s ∈ «Σ».cones) :
    IsDomain (monoidChartAlgebra k (dualConeMonoid s)) := by
  obtain ⟨b, I, hI, ⟨e⟩⟩ := «Σ».smooth_chart_algebra k s hs
  letI := finiteCharacterRing_isDomain k (FreeCoordinate I)
  exact MulEquiv.isDomain _ e.toMulEquiv

/-- Factoriality is proved from the actual chart algebra equivalence;
it is not an extra hypothesis on a smooth fan. -/
theorem chartRing_uniqueFactorization (s : Finset (Lattice n)) (hs : s ∈ «Σ».cones) :
    UniqueFactorizationMonoid (monoidChartAlgebra k (dualConeMonoid s)) := by
  obtain ⟨b, I, hI, ⟨e⟩⟩ := «Σ».smooth_chart_algebra k s hs
  letI := finiteCharacterRing_isDomain k (FreeCoordinate I)
  letI := finiteCharacterRing_uniqueFactorization k (FreeCoordinate I)
  exact e.symm.toMulEquiv.uniqueFactorizationMonoid inferInstance

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.chartRing_uniqueFactorization
end
-- END PaperVerification.ToricChartFactorization
end

section
-- BEGIN PaperVerification.ToricFanSchemeIntegral



/-!
# Integrality and the dense torus of the glued fan scheme

The actual affine chart rings are domains. Their zero prime ideals agree
under all face restrictions, and yield a generic point of the glued
scheme. Reducedness is local on the proved affine open cover. Together
these prove integrality and density of the actual zero-cone chart.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

theorem coneChart_isIntegral (s : «Σ».ConeIndex) : IsIntegral (coneChart k s.val) := by
  letI := «Σ».chartRing_isDomain k s.val s.property
  exact inferInstanceAs
    (IsIntegral (Spec (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s.val)))))

def fanChartGenericPoint (s : «Σ».ConeIndex) : coneChart k s.val := by
  letI := «Σ».chartRing_isDomain k s.val s.property
  exact ⟨⊥, inferInstance⟩

theorem fanChartGenericPoint_isGenericPoint (s : «Σ».ConeIndex) :
    IsGenericPoint («Σ».fanChartGenericPoint k s) Set.univ := by
  letI := «Σ».chartRing_isDomain k s.val s.property
  change closure ({(⟨⊥, inferInstance⟩ :
    PrimeSpectrum (monoidChartAlgebra k (dualConeMonoid s.val)))} :
    Set (PrimeSpectrum (monoidChartAlgebra k (dualConeMonoid s.val)))) = Set.univ
  rw [PrimeSpectrum.closure_singleton]
  exact PrimeSpectrum.zeroLocus_bot

@[simp] theorem fanChartGenericPoint_faceMap {s t : «Σ».ConeIndex}
    (hst : s.val ⊆ t.val) :
    coneChartFaceMap k hst («Σ».fanChartGenericPoint k s) = «Σ».fanChartGenericPoint k t := by
  apply PrimeSpectrum.ext
  change Ideal.comap (monoidChartInclusion k (dualConeMonoid_antitone hst)).toRingHom ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _
    (monoidChartInclusion_injective k (dualConeMonoid_antitone hst))

def fanGenericPoint : «Σ».fanScheme k :=
  «Σ».torusOpenMap k («Σ».fanChartGenericPoint k «Σ».zeroConeIndex)

@[simp] theorem fanChartMap_genericPoint (s : «Σ».ConeIndex) :
    «Σ».fanChartMap k s («Σ».fanChartGenericPoint k s) = «Σ».fanGenericPoint k := by
  have hface := «Σ».fanChartGenericPoint_faceMap k
    (s := «Σ».zeroConeIndex) (t := s) (Finset.empty_subset s.val)
  have h := congrArg
    (fun f : coneChart k (∅ : Finset (Lattice n)) ⟶ «Σ».fanScheme k =>
      f («Σ».fanChartGenericPoint k «Σ».zeroConeIndex))
    («Σ».torusOpenMap_chart k s)
  exact (congrArg (fun z : coneChart k s.val => «Σ».fanChartMap k s z) hface).symm.trans h

theorem fanGenericPoint_isGenericPoint : IsGenericPoint («Σ».fanGenericPoint k) Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro x hx
  obtain ⟨s, y, rfl⟩ := «Σ».fanChartMap_jointly_surjective k x
  have hclosed : IsClosed ((«Σ».fanChartMap k s) ⁻¹' closure {«Σ».fanGenericPoint k}) :=
    isClosed_closure.preimage («Σ».fanChartMap k s).continuous
  have hmem : «Σ».fanChartGenericPoint k s ∈
      («Σ».fanChartMap k s) ⁻¹' closure {«Σ».fanGenericPoint k} := by
    change «Σ».fanChartMap k s («Σ».fanChartGenericPoint k s) ∈ closure {«Σ».fanGenericPoint k}
    rw [«Σ».fanChartMap_genericPoint]
    exact subset_closure (Set.mem_singleton _)
  exact ((«Σ».fanChartGenericPoint_isGenericPoint k s).mem_closed_set_iff hclosed).mp hmem
    (Set.mem_univ y)

instance fanScheme_irreducibleSpace : IrreducibleSpace («Σ».fanScheme k) :=
  (irreducibleSpace_def _).mpr («Σ».fanGenericPoint_isGenericPoint k).isIrreducible

instance fanScheme_isReduced : IsReduced («Σ».fanScheme k) := by
  letI (i : («Σ».fanSchemeOpenCover k).I₀) :
      IsReduced ((«Σ».fanSchemeOpenCover k).X i) := by
    let s : «Σ».ConeIndex := i
    change IsReduced (coneChart k s.val)
    letI := «Σ».coneChart_isIntegral k s
    infer_instance
  exact IsReduced.of_openCover («Σ».fanScheme k) («Σ».fanSchemeOpenCover k)

instance fanScheme_isIntegral : IsIntegral («Σ».fanScheme k) :=
  isIntegral_of_irreducibleSpace_of_isReduced («Σ».fanScheme k)

/-- The actual open zero-cone chart is dense in the actual glued scheme. -/
theorem torusOpenMap_denseRange : DenseRange («Σ».torusOpenMap k) := by
  intro x
  have hsub : ({«Σ».fanGenericPoint k} : Set («Σ».fanScheme k)) ⊆
      Set.range («Σ».torusOpenMap k) := by
    rintro y rfl
    exact ⟨«Σ».fanChartGenericPoint k «Σ».zeroConeIndex, rfl⟩
  have hcl := closure_mono hsub
  rw [(«Σ».fanGenericPoint_isGenericPoint k).def] at hcl
  exact hcl (Set.mem_univ x)

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
-- END PaperVerification.ToricFanSchemeIntegral
end

#eval "TORIC_DICTIONARY_PART_09_EOF"
