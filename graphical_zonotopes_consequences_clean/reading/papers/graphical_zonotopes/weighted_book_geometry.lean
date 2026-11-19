module

public import Papers.GraphicalZonotopes.IntegralBooleanResponse
public import Papers.GraphicalZonotopes.ConeCorrespondence

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise

/-- One branch depending on every hub joins all remaining nonconstant
branches. Other branches may ignore arbitrarily many of the hubs. -/
theorem essentialSpokeGraph_connected_of_anchor
    {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]
    [Nonempty H] (F : J → SetFunction H) (j₀ : J)
    (hanchor : ∀ a, Essential (F j₀) a)
    (hbranch : ∀ j, ∃ a, Essential (F j) a) :
    (essentialSpokeGraph F).Connected := by
  letI : Nonempty J := ⟨j₀⟩
  have hhub : ∀ a, (essentialSpokeGraph F).Reachable (Sum.inl a) (Sum.inr j₀) :=
    fun a => (show (essentialSpokeGraph F).Adj (Sum.inl a) (Sum.inr j₀)
      from hanchor a).reachable
  have hreach : ∀ x, (essentialSpokeGraph F).Reachable x (Sum.inr j₀) := by
    intro x
    cases x with
    | inl a => exact hhub a
    | inr j =>
      obtain ⟨a,ha⟩ := hbranch j
      exact (show (essentialSpokeGraph F).Adj (Sum.inl a) (Sum.inr j)
        from ha).reachable.symm.trans (hhub a)
  exact ⟨fun x y => (hreach x).trans (hreach y).symm⟩

/-- Integral complementary polytope for any integral dilation at least the
sum of the positive branch scales. The complement is constructed from its
supermodular set function, not merely inferred from numerical containment. -/
theorem assembled_lattice_complement_of_weight_sum_le {s k : ℕ}
    {z : SetFunction (Fin s)} (hz : TranslationNormalized z) (hzi : IntegerValued z)
    {F : Fin k → SetFunction (Fin s)} (hF : ∀ j, IsMonotoneBoolean (F j))
    (w : Fin k → ℤ) (hw : ∀ j, 0 ≤ w j)
    (hc : Compatible z F (fun j => (w j : ℝ)))
    (M : ℤ) (hM : ∑ j, w j ≤ M) :
    LatticePolytope (basePolytope (assembled z F (fun j => (w j : ℝ)))) ∧
    ∃ R : Set ((Fin s ⊕ Fin k) → ℝ), LatticePolytope R ∧ R.Nonempty ∧
      basePolytope (assembled z F (fun j => (w j : ℝ))) + R =
        (M : ℝ) • graphicalZonotope (cliqueBook s k) := by
  let f := assembled z F (fun j => (w j : ℝ))
  have hw' : ∀ j, 0 ≤ (w j : ℝ) := fun j => by exact_mod_cast hw j
  have hn := assembled_normalized hz F hF (fun j => (w j : ℝ))
  have hs := assembled_supermodular z F hF (fun j => (w j : ℝ)) hw' hc
  have hi := assembled_integerValued hzi F hF w
  have hG := assembled_graphical z F (fun j => (w j : ℝ))
  have hsum : (∑ j, (w j : ℝ)) ≤ (M : ℝ) := by exact_mod_cast hM
  have ha : 0 ≤ (M : ℝ) := (sum_nonneg (fun j _ => hw' j)).trans hsum
  have hbound : ∀ u v, u ≠ v → (cliqueBook s k).Adj u v → ∀ A,
      u ∉ A → v ∉ A → delta f u v A ≤ (M : ℝ) := by
    intro u v huv hedge A hu hv
    exact (assembled_delta_le_weight_sum hF hw' hc u v huv A hu hv).trans hsum
  let g : SetFunction (Fin s ⊕ Fin k) := (M : ℝ) • graphFunction (cliqueBook s k) - f
  have hgn : Normalized g := by
    change (M : ℝ) * graphFunction (cliqueBook s k) ∅ - f ∅ = 0
    have hf0 : f ∅ = 0 := hn.1
    rw [graphFunction_normalized, hf0, mul_zero, sub_self]
  have hgs : Supermodular g := graphical_complement_supermodular hG ha hbound
  have hgi : IntegerValued g :=
    ((graphFunction_integerValued (cliqueBook s k)).int_smul M).sub hi
  exact ⟨hi.basePolytope hn.1 hs, basePolytope g, hgi.basePolytope hgn hgs,
    basePolytope_nonempty hgn hgs,
    basePolytope_add_graphical_complement hn.1 hs hG ha hbound⟩

/-- A positive integral circuit in the actual response quotient yields a
full dimensional indecomposable lattice polytope and an integral complement.
Every ambient hub and every branch remains present in the dimension claim. -/
theorem lattice_book_of_weighted_modules {s k : ℕ} (hk : 0 < k)
    (F : Fin k → SetFunction (Fin s)) (hF : ∀ j, IsMonotoneBoolean (F j))
    (w : Fin k → ℤ) (hw : ∀ j, 0 < w j)
    (hconn : (essentialSpokeGraph F).Connected)
    (hrel : (fun j => (w j : ℝ)) ∈ LinearMap.ker (quotientRelation F))
    (huniq : UniqueIntegrableRelation F (fun j => (w j : ℝ)))
    (M : ℤ) (hM : ∑ j, w j ≤ M) :
    ∃ f : SetFunction (Fin s ⊕ Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s ⊕ Fin k) → ℝ), LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f + R = (M : ℝ) • graphicalZonotope (cliqueBook s k) := by
  obtain ⟨z,hzn,hzi,hc⟩ := integral_compatible_lift F hF w hrel
  have hw' : ∀ j, 0 < (w j : ℝ) := fun j => by exact_mod_cast hw j
  let f := assembled z F (fun j => (w j : ℝ))
  have hn : TranslationNormalized f := assembled_normalized hzn F hF _
  have hi : IntegerValued f := assembled_integerValued hzi F hF w
  have he : ExtremeSupermodular f := positive_circuit_extreme hzn hF
    (fun j => (hw' j).le) ⟨⟨0,hk⟩,ne_of_gt (hw' ⟨0,hk⟩)⟩ hc huniq
  have hd : FullDimension (basePolytope f) :=
    assembled_fullDimension hzn hF hw' hc hconn
  obtain ⟨hl,R,hR,hnR,hQR⟩ := assembled_lattice_complement_of_weight_sum_le
    hzn hzi hF w (fun j => (hw j).le) hc M hM
  exact ⟨f,hn,hi,he,assembled_graphical z F _,hd,
    he.minkowskiIndecomposable,hl,R,hR,hnR,hQR⟩

end BooleanModule
end GraphicalZonotopes
