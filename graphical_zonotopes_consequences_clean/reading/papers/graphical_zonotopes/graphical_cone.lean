module

public import Papers.GraphicalZonotopes.Indecomposable
public import Papers.GraphicalZonotopes.Mobius
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vanishing of every elemental difference on the graph's nonedges. -/
def Graphical (G : SimpleGraph V) (z : SetFunction V) : Prop :=
  ∀ u v, u ≠ v → ¬G.Adj u v → ∀ S, u ∉ S → v ∉ S → delta z u v S = 0

/-- Möbius support on cliques of cardinality at least two. -/
def CliqueSupported (G : SimpleGraph V) (y : SetFunction V) : Prop :=
  y ∅ = 0 ∧ (∀ v, y {v} = 0) ∧
    ∀ C u v, u ∈ C → v ∈ C → u ≠ v → ¬G.Adj u v → y C = 0

theorem cliqueSupported_iff (G : SimpleGraph V) (y : SetFunction V) :
    CliqueSupported G y ↔ TranslationNormalized (zeta y) ∧ Graphical G (zeta y) := by
  constructor
  · rintro ⟨he, hs, hn⟩
    refine ⟨(zeta_normalized_iff y).mpr ⟨he, hs⟩, ?_⟩
    intro u v huv hG
    exact (nonedge_coefficients_zero_iff y huv).mpr (fun C hu hv => hn C u v hu hv huv hG)
  · rintro ⟨hz, hG⟩
    obtain ⟨he, hs⟩ := (zeta_normalized_iff y).mp hz
    refine ⟨he, hs, ?_⟩
    intro C u v hu hv huv hnon
    exact (nonedge_coefficients_zero_iff y huv).mp (hG u v huv hnon) C hu hv

theorem mobius_cliqueSupported_iff (G : SimpleGraph V) (z : SetFunction V) :
    CliqueSupported G (mobius z) ↔ TranslationNormalized z ∧ Graphical G z := by
  simpa using cliqueSupported_iff G (mobius z)

/-- No graphical-support hypothesis on the summands is needed: nonnegativity
and a vanishing sum force it automatically. -/
theorem Graphical.summands {G : SimpleGraph V} {z f g : SetFunction V}
    (hG : Graphical G z) (hf : Supermodular f) (hg : Supermodular g)
    (he : f + g = z) : Graphical G f ∧ Graphical G g := by
  have hall : ∀ u v, u ≠ v → ¬G.Adj u v → ∀ S, u ∉ S → v ∉ S →
      delta f u v S = 0 ∧ delta g u v S = 0 := by
    intro u v huv hnon S hu hv
    have h1 := hf.elemental u v huv S hu hv
    have h2 := hg.elemental u v huv S hu hv
    have h3 := hG u v huv hnon S hu hv
    rw [← he, delta_add] at h3
    constructor <;> linarith
  exact ⟨fun u v huv hnon S hu hv => (hall u v huv hnon S hu hv).1,
    fun u v huv hnon S hu hv => (hall u v huv hnon S hu hv).2⟩

/-- An actual nonzero normalized supermodular function has a positive slack. -/
theorem exists_positive_delta {z : SetFunction V} (hn : TranslationNormalized z)
    (hs : Supermodular z) (hne : z ≠ 0) :
    ∃ u v, u ≠ v ∧ ∃ S, u ∉ S ∧ v ∉ S ∧ 0 < delta z u v S := by
  by_contra h
  push_neg at h
  apply hne
  apply normalized_zero_elemental_eq_zero hn
  intro u v huv S hu hv
  exact le_antisymm (h u v huv S hu hv) (hs.elemental u v huv S hu hv)

/-- The common-tight-equation criterion is sufficient for extremality, without
assuming a positive coefficient for the putative scalar in advance. -/
theorem extremeSupermodular_of_tightEquations {z : SetFunction V}
    (hn : TranslationNormalized z) (hs : Supermodular z) (hne : z ≠ 0)
    (hker : ∀ f : SetFunction V, TranslationNormalized f →
      (∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S →
        delta z u v S = 0 → delta f u v S = 0) →
      ∃ a : ℝ, f = a • z) : ExtremeSupermodular z := by
  refine ⟨hn, hs, hne, ?_⟩
  intro f g hnf hng hsf hsg he
  have hzeros : ∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S →
      delta z u v S = 0 → delta f u v S = 0 := by
    intro u v huv S hu hv hz
    have h1 := hsf.elemental u v huv S hu hv
    have h2 := hsg.elemental u v huv S hu hv
    rw [← he, delta_add] at hz
    linarith
  obtain ⟨a, ha⟩ := hker f hnf hzeros
  refine ⟨a, ?_, ha⟩
  obtain ⟨u, v, huv, S, hu, hv, hpos⟩ := exists_positive_delta hn hs hne
  have h := hsf.elemental u v huv S hu hv
  rw [ha, delta_smul] at h
  exact nonneg_of_mul_nonneg_left h hpos

end GraphicalZonotopes
