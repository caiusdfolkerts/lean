module

public import Papers.GraphicalZonotopes.ConeCorrespondence
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

def IsCliqueCoordinate (G : SimpleGraph V) (C : Finset V) : Prop :=
  2 ≤ C.card ∧ G.IsClique C

abbrev CliqueIndex (G : SimpleGraph V) := {C : Finset V // IsCliqueCoordinate G C}

noncomputable instance cliqueIndexFintype (G : SimpleGraph V) : Fintype (CliqueIndex G) := by
  classical
  infer_instance

def coefficientSpace (G : SimpleGraph V) : Submodule ℝ (SetFunction V) where
  carrier := {y | CliqueSupported G y}
  zero_mem' := by refine ⟨rfl,fun _ => rfl,?_⟩; intros; rfl
  add_mem' := by
    intro y y' hy hy'
    refine ⟨by simp [hy.1,hy'.1],fun v => by simp [hy.2.1 v,hy'.2.1 v],?_⟩
    intro C u v hu hv huv hnon
    simp [hy.2.2 C u v hu hv huv hnon,hy'.2.2 C u v hu hv huv hnon]
  smul_mem' := by
    intro a y hy
    refine ⟨by simp [hy.1],fun v => by simp [hy.2.1 v],?_⟩
    intro C u v hu hv huv hnon
    simp [hy.2.2 C u v hu hv huv hnon]

theorem coefficient_zero_of_not_clique {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) (C : Finset V) (hC : ¬IsCliqueCoordinate G C) : y C=0 := by
  classical
  by_cases hc : 2 ≤ C.card
  · by_contra hn
    apply hC
    refine ⟨hc,?_⟩
    intro u hu v hv huv
    by_contra hnon
    exact hn (hy.2.2 C u v hu hv huv hnon)
  · have hc' : C.card=0 ∨ C.card=1 := by omega
    rcases hc' with he | he
    · rw [card_eq_zero.mp he,hy.1]
    · obtain ⟨v,rfl⟩ := card_eq_one.mp he
      exact hy.2.1 v

def coefficientsFromCoordinates (G : SimpleGraph V) (c : CliqueIndex G → ℝ) : SetFunction V := by
  classical
  exact fun C => if h : IsCliqueCoordinate G C then c ⟨C,h⟩ else 0

theorem coefficientsFromCoordinates_supported (G : SimpleGraph V) (c : CliqueIndex G → ℝ) :
    CliqueSupported G (coefficientsFromCoordinates G c) := by
  classical
  refine ⟨?_,?_,?_⟩
  · simp [coefficientsFromCoordinates,IsCliqueCoordinate]
  · intro v
    simp [coefficientsFromCoordinates,IsCliqueCoordinate]
  · intro C u v hu hv huv hnon
    have hC : ¬IsCliqueCoordinate G C := by
      intro hc
      exact hnon (hc.2 hu hv huv)
    simp [coefficientsFromCoordinates,hC]

/-- Exactly all normalized clique coefficients, with no missing zero slots. -/
def cliqueCoefficientEquiv (G : SimpleGraph V) :
    (CliqueIndex G → ℝ) ≃ₗ[ℝ] coefficientSpace G where
  toFun c := ⟨coefficientsFromCoordinates G c,coefficientsFromCoordinates_supported G c⟩
  invFun y C := y.1 C.1
  left_inv c := by
    funext C
    simp [coefficientsFromCoordinates,C.2]
  right_inv y := by
    apply Subtype.ext
    funext C
    by_cases hC : IsCliqueCoordinate G C
    · simp [coefficientsFromCoordinates,hC]
    · simp [coefficientsFromCoordinates,hC,coefficient_zero_of_not_clique y.2 C hC]
  map_add' c d := by
    apply Subtype.ext
    funext C
    by_cases hC : IsCliqueCoordinate G C <;> simp [coefficientsFromCoordinates,hC]
  map_smul' a c := by
    apply Subtype.ext
    funext C
    by_cases hC : IsCliqueCoordinate G C <;> simp [coefficientsFromCoordinates,hC]

def graphicalFunctionSpace (G : SimpleGraph V) : Submodule ℝ (SetFunction V) where
  carrier := {z | TranslationNormalized z ∧ Graphical G z}
  zero_mem' := by
    refine ⟨⟨rfl,fun _ => rfl⟩,?_⟩
    intro u v huv hnon S hu hv
    simp [delta]
  add_mem' := by
    intro f g hf hg
    refine ⟨⟨?_,?_⟩,?_⟩
    · change f ∅+g ∅=0
      rw [hf.1.1,hg.1.1,add_zero]
    · intro v
      change f {v}+g {v}=0
      rw [hf.1.2 v,hg.1.2 v,add_zero]
    · intro u v huv hnon S hu hv
      rw [delta_add,hf.2 u v huv hnon S hu hv,hg.2 u v huv hnon S hu hv,add_zero]
  smul_mem' := by
    intro a f hf
    refine ⟨⟨?_,?_⟩,?_⟩
    · change a*f ∅=0
      rw [hf.1.1,mul_zero]
    · intro v
      change a*f {v}=0
      rw [hf.1.2 v,mul_zero]
    · intro u v huv hnon S hu hv
      rw [delta_smul,hf.2 u v huv hnon S hu hv,mul_zero]

/-- Möbius inversion restricted to the exact normalized graphical function
space. Its inverse is the actual finite lower-set sum. -/
def graphicalZetaEquiv (G : SimpleGraph V) :
    coefficientSpace G ≃ₗ[ℝ] graphicalFunctionSpace G where
  toFun y := ⟨zeta y.1,(cliqueSupported_iff G y.1).mp y.2⟩
  invFun z := ⟨mobius z.1,(mobius_cliqueSupported_iff G z.1).mpr z.2⟩
  left_inv y := Subtype.ext (mobius_zeta y.1)
  right_inv z := Subtype.ext (zeta_mobius z.1)
  map_add' y y' := Subtype.ext (zetaLinear.map_add y.1 y'.1)
  map_smul' a y := Subtype.ext (zetaLinear.map_smul a y.1)

def graphicalCoordinatesEquiv (G : SimpleGraph V) :
    (CliqueIndex G → ℝ) ≃ₗ[ℝ] graphicalFunctionSpace G :=
  (cliqueCoefficientEquiv G).trans (graphicalZetaEquiv G)

theorem graphicalFunctionSpace_finrank (G : SimpleGraph V) :
    Module.finrank ℝ (graphicalFunctionSpace G) = Fintype.card (CliqueIndex G) := by
  rw [← (graphicalCoordinatesEquiv G).finrank_eq,Module.finrank_fintype_fun_eq_card]

/-- The elemental-row map is injective on the normalized graphical space.
This also proves that its nonnegative cone is pointed. -/
theorem graphical_function_eq_zero_of_elemental_zero (G : SimpleGraph V)
    (z : graphicalFunctionSpace G)
    (hz : ∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S → delta z.1 u v S=0) : z=0 := by
  apply Subtype.ext
  exact normalized_zero_elemental_eq_zero z.2.1 hz

end GraphicalZonotopes
