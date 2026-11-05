import Characterizations.Resolution.HomogeneousFree
import CommAlg.KoszulComplex.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Actual linear free resolutions

The definition records a genuine exact augmented complex of finite free polynomial
modules. The grading condition is that every matrix entry of a differential is a
linear form, while the augmentation has degree `d`. It contains no homology or
Betti-vanishing assertion.
-/

noncomputable section
local instance (priority := 2000) classicalBasisDecidableEqBasic (α : Type*) [Fintype α] : DecidableEq α := Classical.decEq α
set_option backward.isDefEq.respectTransparency false
namespace Characterizations
open Classical CategoryTheory CategoryTheory.Limits HomologicalComplex
open Resolution
universe u
variable {V k : Type u} [CommRing k]

structure LinearResolution (I : Ideal (MvPolynomial V k)) (d : ℕ) where
  Index : ℕ → Type
  finite : ∀ n, Fintype (Index n)
  differential : ∀ n, (Index (n + 1) → MvPolynomial V k) →ₗ[MvPolynomial V k]
    (Index n → MvPolynomial V k)
  augmentation : (Index 0 → MvPolynomial V k) →ₗ[MvPolynomial V k] MvPolynomial V k
  augmentation_range : LinearMap.range augmentation = I
  exact_zero : LinearMap.range (differential 0) = LinearMap.ker augmentation
  exact_succ : ∀ n, LinearMap.range (differential (n + 1)) = LinearMap.ker (differential n)
  linear : ∀ n, letI := finite n; letI := finite (n + 1)
    IsHomogeneousMap (differential n) 1
  augmentation_homogeneous : ∀ b, (augmentation (Pi.single b 1)).IsHomogeneous d

attribute [instance] LinearResolution.finite

namespace LinearResolution
variable {I : Ideal (MvPolynomial V k)} {d : ℕ} (P : LinearResolution I d)

lemma differential_comp (n : ℕ) :
    P.differential n ∘ₗ P.differential (n + 1) = 0 := by
  apply LinearMap.ext
  intro x
  change P.differential n (P.differential (n + 1) x) = 0
  apply LinearMap.mem_ker.mp
  rw [← P.exact_succ n]
  exact LinearMap.mem_range_self _ x

lemma augmentation_comp : P.augmentation ∘ₗ P.differential 0 = 0 := by
  apply LinearMap.ext
  intro x
  change P.augmentation (P.differential 0 x) = 0
  apply LinearMap.mem_ker.mp
  rw [← P.exact_zero]
  exact LinearMap.mem_range_self _ x

/-- The actual complex of finite free polynomial modules. -/
def complex : ChainComplex (ModuleCat.{u} (MvPolynomial V k)) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of _ (P.Index n → MvPolynomial V k))
    (fun n => ModuleCat.ofHom (P.differential n))
    (fun n => ModuleCat.hom_ext (P.differential_comp n))

@[simp] lemma complex_d (n : ℕ) : P.complex.d (n + 1) n = ModuleCat.ofHom (P.differential n) := by
  exact ChainComplex.of_d (fun j => ModuleCat.of (MvPolynomial V k) (P.Index j → MvPolynomial V k))
    (fun j => ModuleCat.ofHom (P.differential j)) n

/-- The augmentation takes values in the original ideal itself. -/
def augmentationToIdeal : (P.Index 0 → MvPolynomial V k) →ₗ[MvPolynomial V k] I :=
  P.augmentation.codRestrict I (fun x => by
    exact Eq.mp (congrArg (fun J : Submodule (MvPolynomial V k) (MvPolynomial V k) =>
      P.augmentation x ∈ J) P.augmentation_range) (LinearMap.mem_range_self _ x))

lemma augmentationToIdeal_surjective : Function.Surjective P.augmentationToIdeal := by
  intro y
  have hy : y.val ∈ LinearMap.range P.augmentation := by
    rw [P.augmentation_range]
    exact y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

lemma augmentationToIdeal_ker : LinearMap.ker P.augmentationToIdeal = LinearMap.ker P.augmentation := by
  ext x
  simp [augmentationToIdeal, LinearMap.mem_ker, Subtype.ext_iff]

lemma complex_exactAt_succ (n : ℕ) : P.complex.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (ModuleCat.Hom.hom (P.complex.d ((n + 1) + 1) (n + 1))) =
    LinearMap.ker (ModuleCat.Hom.hom (P.complex.d (n + 1) n))
  rw [P.complex_d, P.complex_d]
  exact P.exact_succ n

/-- The conventional categorical projective resolution obtained from the concrete data. -/
def toProjectiveResolution : ProjectiveResolution (ModuleCat.of (MvPolynomial V k) I) where
  complex := P.complex
  projective n := by
    change Projective (ModuleCat.of (MvPolynomial V k) (P.Index n → MvPolynomial V k))
    infer_instance
  π := (ChainComplex.toSingle₀Equiv P.complex _).symm
    ⟨ModuleCat.ofHom P.augmentationToIdeal, by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact LinearMap.congr_fun P.augmentation_comp x⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        simp only [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
        refine ⟨?_, ?_⟩
        · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
          change LinearMap.range (ModuleCat.Hom.hom (P.complex.d 1 0)) = LinearMap.ker P.augmentationToIdeal
          rw [P.augmentationToIdeal_ker]
          rw [P.complex_d]
          exact P.exact_zero
        · exact (ModuleCat.epi_iff_surjective _).mpr P.augmentationToIdeal_surjective
      · exact P.complex.shape 0 0 (by simp)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact P.complex_exactAt_succ n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

end LinearResolution

/-- Existence of an exact finite-free resolution with shifts `d + i`. -/
def HasLinearResolution (I : Ideal (MvPolynomial V k)) : Prop :=
  ∃ d, Nonempty (LinearResolution I d)

end Characterizations
