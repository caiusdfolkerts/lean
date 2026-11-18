module

public import Papers.GraphicalZonotopes.CliqueCoordinates

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace FiniteMonomial
open Finset
open scoped BigOperators
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- A displayed finite list of genuine squarefree Boolean monomials. -/
def polynomial (C : I → Finset V) (x : I → ℝ) : SetFunction V :=
  ∑ i, x i • setMonomial (C i)

theorem polynomial_smul (C : I → Finset V) (x : I → ℝ) (a : ℝ) :
    polynomial C (a • x) = a • polynomial C x := by
  simp only [polynomial,smul_sum,Pi.smul_apply,smul_smul,smul_eq_mul]

theorem delta_polynomial (C : I → Finset V) (x : I → ℝ)
    {u v : V} (huv : u≠v) {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta (polynomial C x) u v S =
      ∑ i, if u∈C i ∧ v∈C i ∧ C i⊆insert u (insert v S) then x i else 0 := by
  rw [polynomial,delta_sum]
  apply sum_congr rfl
  intro i hi
  rw [delta_smul,delta_setMonomial huv hu hv]
  split_ifs <;> simp

/-- A complete injective clique enumeration recovers every actual normalized
graphical set function from its Möbius coordinates. -/
theorem graphical_eq_polynomial {G : SimpleGraph V} (C : I → Finset V)
    (hinj : Function.Injective C)
    (hcover : ∀ D : Finset V, IsCliqueCoordinate G D → ∃ i,C i=D)
    {f : SetFunction V} (hn : TranslationNormalized f) (hG : Graphical G f) :
    f=polynomial C (fun i => mobius f (C i)) := by
  have hy := (mobius_cliqueSupported_iff G f).mpr ⟨hn,hG⟩
  conv_lhs => rw [← zeta_mobius f,zeta_eq_sum_monomials]
  change (∑ D : Finset V,mobius f D • setMonomial D)=
    ∑ i : I,mobius f (C i) • setMonomial (C i)
  rw [← sum_image (f := fun D => mobius f D • setMonomial D)
    (fun i _ j _ hij => hinj hij)]
  symm
  apply sum_subset (subset_univ _)
  intro D hD hnot
  have hncl : ¬IsCliqueCoordinate G D := by
    intro hd
    obtain ⟨i,rfl⟩ := hcover D hd
    exact hnot (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
  rw [coefficient_zero_of_not_clique hy D hncl,zero_smul]

theorem polynomial_normalized (C : I → Finset V)
    (hcard : ∀ i,2≤(C i).card) (x : I → ℝ) :
    TranslationNormalized (polynomial C x) := by
  constructor
  · change (∑ i,x i • setMonomial (C i)) ∅=0
    rw [Finset.sum_apply]
    apply sum_eq_zero
    intro i hi
    have hne : ¬C i⊆∅ := by
      intro he
      have := card_le_card he
      have := hcard i
      simp only [card_empty] at *
      omega
    simp [setMonomial,hne]
  · intro v
    change (∑ i,x i • setMonomial (C i)) {v}=0
    rw [Finset.sum_apply]
    apply sum_eq_zero
    intro i hi
    have hne : ¬C i⊆{v} := by
      intro he
      have := card_le_card he
      have := hcard i
      simp only [card_singleton] at *
      omega
    simp [setMonomial,hne]

theorem polynomial_graphical {G : SimpleGraph V} (C : I → Finset V)
    (hclique : ∀ i,G.IsClique (C i)) (x : I → ℝ) :
    Graphical G (polynomial C x) := by
  intro u v huv hnon S hu hv
  rw [delta_polynomial C x huv hu hv]
  apply sum_eq_zero
  intro i hi
  have hfalse : ¬(u∈C i ∧ v∈C i ∧ C i⊆insert u (insert v S)) := by
    rintro ⟨huC,hvC,hsub⟩
    exact hnon (hclique i huC hvC huv)
  rw [if_neg hfalse]

end FiniteMonomial
end GraphicalZonotopes
