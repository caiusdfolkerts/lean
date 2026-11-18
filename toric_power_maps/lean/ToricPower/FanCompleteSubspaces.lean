module

public import ToricPower.PolyhedralFoundations

/-!
# The finite family of complete subspace tests

The complete subspaces of a finite fan are covered by its cones contained in
the subspace. One such cone spans the entire subspace. Hence these subspaces
belong to a finite, explicitly described family of cone spans. The argument
does not require the ambient fan to be complete.

An auxiliary norm is transported from finite coordinates inside the proof;
the statements themselves have no topological or norm hypothesis. The final
lemma makes the finite maximum in the relative compactification argument
explicit. It does not assert the compactification or a cohomology limit theorem.

Candidate source awaiting ordinary compilation.
-/

@[expose] public noncomputable section

open Set TauCeti.Toric

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- Subspaces on which the cones of the given fan form a complete subfan.
No completeness hypothesis is imposed on the ambient fan. -/
def fanCompleteSubspaces (fan : Fan i) : Set (Submodule ℝ V) :=
  {W | ∀ x ∈ W, ∃ σ ∈ fan.cones, σ ≤ (W : PointedCone ℝ V) ∧ x ∈ σ}

/-- A complete subspace is the real span of an actual cone of the fan. -/
theorem fanCompleteSubspaces_exists_cone_span (fan : Fan i)
    {W : Submodule ℝ V} (hW : W ∈ fanCompleteSubspaces fan) :
    ∃ σ ∈ fan.cones, σ ≤ (W : PointedCone ℝ V) ∧
      Submodule.span ℝ (σ : Set V) = W := by
  letI := fan.lattice.finiteDimensional
  let coordinates := (Module.finBasis ℝ V).equivFun
  letI : NormedAddCommGroup V :=
    NormedAddCommGroup.induced V _ coordinates coordinates.injective
  letI : NormedSpace ℝ V := NormedSpace.induced ℝ V _ coordinates
  exact NormalFan.exists_full_span_cone_of_cover fan W hW

/-- The family of complete subspaces is finite, as a subset of the finite
family of spans of the fan's actual cones. -/
theorem fanCompleteSubspaces_finite (fan : Fan i) : (fanCompleteSubspaces fan).Finite := by
  apply (fan.finite_cones.image
    (fun σ : PointedCone ℝ V => Submodule.span ℝ (σ : Set V))).subset
  intro W hW
  obtain ⟨σ, hσ, _, hspan⟩ := fanCompleteSubspaces_exists_cone_span fan hW
  exact ⟨σ, hσ, hspan⟩

/-- Completeness of the subfan forces exactly the paper's linearity
condition; it is not supplied as an extra premise. -/
theorem fanCompleteSubspaces_linear (fan : Fan i)
    {W : Submodule ℝ V} (hW : W ∈ fanCompleteSubspaces fan) :
    NormalFan.IsLinearSubspace fan W :=
  NormalFan.isLinearSubspace_of_cone_cover fan W hW

/-- A complete subspace is rational: finitely many actual lattice vectors
span it over the reals. -/
theorem fanCompleteSubspaces_lattice_span (fan : Fan i)
    {W : Submodule ℝ V} (hW : W ∈ fanCompleteSubspaces fan) :
    ∃ s : Finset N, W = Submodule.span ℝ (i '' (s : Set N)) := by
  letI := fan.lattice.finiteDimensional
  let coordinates := (Module.finBasis ℝ V).equivFun
  letI : NormedAddCommGroup V :=
    NormedAddCommGroup.induced V _ coordinates coordinates.injective
  letI : NormedSpace ℝ V := NormedSpace.induced ℝ V _ coordinates
  exact NormalFan.exists_finite_lattice_span_of_cover fan W hW

/-- Universal tests over complete subspaces are exactly tests on the
qualifying members of a finite family of cone spans. -/
theorem forall_fanCompleteSubspaces_iff_cone_spans (fan : Fan i)
    (P : Submodule ℝ V → Prop) :
    (∀ W ∈ fanCompleteSubspaces fan, P W) ↔
      ∀ σ ∈ fan.cones,
        Submodule.span ℝ (σ : Set V) ∈ fanCompleteSubspaces fan →
          P (Submodule.span ℝ (σ : Set V)) := by
  constructor
  · intro h σ _ hσ
    exact h _ hσ
  · intro h W hW
    obtain ⟨σ, hσ, _, rfl⟩ := fanCompleteSubspaces_exists_cone_span fan hW
    exact h σ hσ hW

/-- Finitely many eventual statements have one common integer threshold.
This supplies the finite-maximum step in the Cartier-boundary argument. -/
theorem fanCompleteSubspaces_uniform_threshold (fan : Fan i)
    (P : Submodule ℝ V → ℕ → Prop)
    (h : ∀ W ∈ fanCompleteSubspaces fan, ∃ a : ℕ, ∀ b : ℕ, a ≤ b → P W b) :
    ∃ a : ℕ, ∀ W ∈ fanCompleteSubspaces fan, ∀ b : ℕ, a ≤ b → P W b := by
  classical
  let S := fanCompleteSubspaces fan
  letI : Fintype S := (fanCompleteSubspaces_finite fan).fintype
  choose threshold eventual using (fun W : S => h W.val W.property)
  let a := Finset.univ.sup threshold
  refine ⟨a, ?_⟩
  intro W hW b hab
  let j : S := ⟨W, hW⟩
  exact eventual j b ((Finset.le_sup (f := threshold) (Finset.mem_univ j)).trans hab)

end ToricPower

end
