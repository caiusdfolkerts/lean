module

public import Continuation.CycleBounds.GraphicFunctionals
public import Continuation.CycleBounds.IntegralIncidence
public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part12

@[expose] public section

/-! # The numerical wall bound for the actual smooth complete fan

The coefficient function is the literal ceiling representative of the Thomsen
class. The left side is the actual integral Cartier wall slack. All ray labels,
all full cones, and all real representatives are retained.
-/

noncomputable section
open scoped BigOperators
namespace PaperVerification.ToricGeometry.SmoothCompleteFan
open Unimodular.CycleBounds Unimodular.SeriesParallel
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (F : SmoothCompleteFan n)

def thomsenRayFamily (u : F.rays) : Ambient n := embed n u.val

def thomsenCoefficients (_F : SmoothCompleteFan n) (θ : Module.Dual ℝ (Ambient n)) (u : Lattice n) : ℤ :=
  ⌈θ (embed n u)⌉

/-- The genuine direction space cut out by all active integral ray equations. -/
def thomsenDirection (θ : Module.Dual ℝ (Ambient n)) :
    Submodule ℝ (Module.Dual ℝ (Ambient n)) :=
  activeDirections F.thomsenRayFamily {u | ∃ z : ℤ, θ (F.thomsenRayFamily u) = (z : ℝ)}

/-- The negative Cartier point functional interpolates the divisor's coefficients
on the chosen full cone. -/
def negativeCartierForm (a : Lattice n → ℤ) (s : F.fullCones) :
    Module.Dual ℝ (Ambient n) :=
  -(dotProductEquiv ℝ (Fin n) (embed n (F.cartierLatticePoint a s)))

theorem negativeCartierForm_apply (a : Lattice n → ℤ) (s : F.fullCones)
    (u : Lattice n) :
    F.negativeCartierForm a s (embed n u) = -(integerPairing u (F.cartierLatticePoint a s) : ℝ) := by
  simp only [negativeCartierForm, LinearMap.neg_apply, normalRay_pairing_lattice]
  congr 1
  simp only [integerPairing, mul_comm]

def fullConeLabels (s : F.fullCones) : Finset F.rays := Finset.univ.image (F.activeRay s)

theorem activeRay_injective (s : F.fullCones) : Function.Injective (F.activeRay s) := by
  intro i j hij
  exact (F.fullConeBasis s).injective (congrArg Subtype.val hij)

theorem mem_fullConeLabels (s : F.fullCones) (u : F.rays) :
    u ∈ F.fullConeLabels s ↔ u.val ∈ s.val := by
  classical
  rw [F.fullConeBasis_ray_set s]
  simp only [fullConeLabels, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Subtype.ext hi⟩

theorem fullConeLabels_linearIndep (s : F.fullCones) :
    LinearIndepOn ℝ F.thomsenRayFamily (F.fullConeLabels s : Set F.rays) := by
  have hset : (F.fullConeLabels s : Set F.rays) = Set.range (F.activeRay s) := by
    ext u
    simp [fullConeLabels]
  rw [hset]
  apply (linearIndepOn_range_iff (F.activeRay_injective s) F.thomsenRayFamily).mpr
  have heq : F.thomsenRayFamily ∘ F.activeRay s =
      integralBasisReal (F.fullConeBasis s) := by
    funext i
    exact (integralBasisReal_apply (F.fullConeBasis s) i).symm
  rw [heq]
  exact (integralBasisReal (F.fullConeBasis s)).linearIndependent

theorem fullConeLabels_span (s : F.fullCones) :
    Submodule.span ℝ (F.thomsenRayFamily '' (F.fullConeLabels s : Set F.rays)) = ⊤ := by
  have hset : F.thomsenRayFamily '' (F.fullConeLabels s : Set F.rays) =
      Set.range (integralBasisReal (F.fullConeBasis s)) := by
    ext x
    simp only [Set.mem_image, Finset.mem_coe, fullConeLabels, Finset.mem_image,
      Finset.mem_univ, true_and, Set.mem_range]
    constructor
    · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by simp [thomsenRayFamily, activeRay]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨F.activeRay s i, ⟨i, rfl⟩, by simp [thomsenRayFamily, activeRay]⟩
  rw [hset]
  exact (integralBasisReal (F.fullConeBasis s)).span_eq

/-- The numerical conclusion of Proposition6.8 for every actual full cone and
ray, under a faithful incidence presentation of the complete ray family. -/
theorem thomsen_wall_slack_le_direction_real {V : Type*} [Fintype V]
    (G : IncidenceGraph V F.rays) (hG : G.edges = Set.univ) (hK : ¬G.HasK4Minor)
    (ι : Ambient n →ₗ[ℝ] (V → ℝ)) (hinj : Function.Injective ι)
    (hι : ∀ u, ι (F.thomsenRayFamily u) =
      Pi.single (G.source u) 1 - Pi.single (G.target u) 1)
    (θ : Module.Dual ℝ (Ambient n)) (s : F.fullCones) (w : F.rays) :
    F.thomsenCoefficients θ w.val +
      integerPairing w.val (F.cartierLatticePoint (F.thomsenCoefficients θ) s) ≤
        (Module.finrank ℝ (F.thomsenDirection θ) : ℤ) := by
  classical
  let a := F.thomsenCoefficients θ
  by_cases hws : w.val ∈ s.val
  · rw [F.cartierLatticePoint_pairing a s w.val hws]
    change a w.val + -a w.val ≤ _
    simp
  have hwB : w ∉ F.fullConeLabels s := by rwa [F.mem_fullConeLabels]
  have hnonzero : F.thomsenRayFamily w ≠ 0 := by
    intro hz
    exact F.ray_ne_zero w.property ((embed_injective n) (by simpa [thomsenRayFamily] using hz))
  have hspan : F.thomsenRayFamily w ∈
      Submodule.span ℝ (F.thomsenRayFamily '' (F.fullConeLabels s : Set F.rays)) := by
    rw [F.fullConeLabels_span]
    trivial
  have hℓ (u : F.rays) (hu : u ∈ F.fullConeLabels s) :
      F.negativeCartierForm a s (F.thomsenRayFamily u) = (⌈θ (F.thomsenRayFamily u)⌉ : ℝ) := by
    rw [thomsenRayFamily, F.negativeCartierForm_apply,
      F.cartierLatticePoint_pairing a s u.val ((F.mem_fullConeLabels s u).mp hu)]
    simp [a, thomsenCoefficients, thomsenRayFamily]
  have hb := graphic_wall_bound_all_parameters G hK F.thomsenRayFamily ι hinj hι θ
    (F.negativeCartierForm a s) (F.fullConeLabels s) (by rw [hG]; exact Set.subset_univ _)
    (F.fullConeLabels_linearIndep s) w (by rw [hG]; trivial) hwB hnonzero hspan hℓ
  rw [thomsenRayFamily, F.negativeCartierForm_apply] at hb
  have hA : {e | e ∈ G.edges ∧ ∃ z : ℤ, θ (F.thomsenRayFamily e) = (z : ℝ)} =
      {e | ∃ z : ℤ, θ (F.thomsenRayFamily e) = (z : ℝ)} := by
    rw [hG]
    ext e
    simp
  rw [hA] at hb
  simp only [sub_neg_eq_add] at hb
  change (⌈θ (embed n w.val)⌉ : ℝ) +
      (integerPairing w.val (F.cartierLatticePoint a s) : ℝ) ≤
        (Module.finrank ℝ (F.thomsenDirection θ) : ℝ) at hb
  exact_mod_cast hb

/-- An actual injective integral incidence map implies the real presentation,
with no restriction on the number or connectedness of graph vertices. -/
theorem thomsen_wall_slack_le_direction_integral {V : Type*} [Fintype V]
    (G : IncidenceGraph V F.rays) (hG : G.edges = Set.univ) (hK : ¬G.HasK4Minor)
    (δ : Lattice n →ₗ[ℤ] (V → ℤ)) (hinj : Function.Injective δ)
    (hδ : ∀ u : F.rays, δ u.val = Pi.single (G.source u) 1 - Pi.single (G.target u) 1)
    (θ : Module.Dual ℝ (Ambient n)) (s : F.fullCones) (w : F.rays) :
    F.thomsenCoefficients θ w.val +
      integerPairing w.val (F.cartierLatticePoint (F.thomsenCoefficients θ) s) ≤
        (Module.finrank ℝ (F.thomsenDirection θ) : ℤ) := by
  classical
  apply F.thomsen_wall_slack_le_direction_real G hG hK (realExtension δ)
    (realExtension_injective δ hinj) _ θ s w
  intro u
  rw [thomsenRayFamily]
  change realExtension δ (fun i ↦ (u.val i : ℝ)) = _
  rw [realExtension_intCast, hδ]
  ext a
  simp [Pi.single_apply]

#print axioms thomsen_wall_slack_le_direction_integral
end PaperVerification.ToricGeometry.SmoothCompleteFan
