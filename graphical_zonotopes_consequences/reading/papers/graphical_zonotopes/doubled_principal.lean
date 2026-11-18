module

public import Papers.GraphicalZonotopes.DoubledGeometry
public import Papers.GraphicalZonotopes.DoubledSymmetry

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open scoped Pointwise

/-- The full Theorem9.8, with both actual lattice summands, both geometric
indecomposabilities, their full dimensions and complete actual root-direction
graphs, every Boolean elemental slack, and the two parity-specific symmetry
conclusions. -/
def PrincipalBooleanPhaseClaim : Prop :=
  ∀ r : ℕ,4≤r → ∃ Q R : Set ((Fin r×Fin 2) → ℝ),
    LatticePolytope Q ∧ LatticePolytope R ∧
    MinkowskiIndecomposable Q ∧ MinkowskiIndecomposable R ∧
    FullDimension Q ∧ FullDimension R ∧
    Q+R=graphicalZonotope (doubledPartGraph r) ∧
    actualDirectionGraph Q=doubledPartGraph r ∧ actualDirectionGraph R=doubledPartGraph r ∧
    BooleanElemental Q ∧ BooleanElemental R ∧
    (Even r → CentrallySymmetricUpToTranslation Q ∧ CentrallySymmetricUpToTranslation R) ∧
    (Odd r → ∃ t,R=({t} : Set ((Fin r×Fin 2) → ℝ))+(-1 : ℝ) • Q) ∧
    (Odd r → graphicalZonotope (doubledPartGraph r)=
      Q+(-1 : ℝ) • Q+({fun _ : Fin r×Fin 2 => ((r-1 : ℕ) : ℝ)} : Set ((Fin r×Fin 2) → ℝ)))

/-- A uniform floor-half construction proves all parity cases without a
restriction on r. Its finite four-bit coefficient identity is applied to
every four-clique through the explicit Möbius formula. -/
theorem principal_boolean_phase_theorem : PrincipalBooleanPhaseClaim := by
  intro r hr
  have h4 : 4≤Fintype.card (Fin r) := by simpa using hr
  have h3 : 3≤Fintype.card (Fin r) := by simpa using (show 3≤r by omega)
  have hgraph : graph (Fin r)=doubledPartGraph r := rfl
  refine ⟨polytope (I := Fin r),complementPolytope (I := Fin r),
    polytope_lattice,complementPolytope_lattice,
    polytope_indecomposable h4,complementPolytope_indecomposable h4,
    polytope_fullDimension h3,complementPolytope_fullDimension h3,?_,?_,?_,
    polytope_booleanElemental,complementPolytope_booleanElemental,?_,?_,?_⟩
  · simpa only [hgraph] using (polytope_add_complement (I := Fin r))
  · exact (polytope_actualDirectionGraph h3).trans hgraph
  · exact (complementPolytope_actualDirectionGraph h3).trans hgraph
  · intro he
    have he' : Even (Fintype.card (Fin r)) := by simpa using he
    exact ⟨polytope_centrallySymmetric he',complementPolytope_centrallySymmetric he'⟩
  · intro ho
    exact ⟨differenceReflectionVector,
      complementPolytope_reflection (by simpa using ho)⟩
  · intro ho
    have he := complementPolytope_reflection (I := Fin r) (by simpa using ho)
    have ht : (differenceReflectionVector (I := Fin r))=
        (fun _ : Fin r×Fin 2 => ((r-1 : ℕ) : ℝ)) := by
      funext v
      simp only [differenceReflectionVector,Fintype.card_fin]
      rw [Nat.cast_sub (show 1≤r by omega),Nat.cast_one]
    rw [ht] at he
    rw [← hgraph,← polytope_add_complement,he]
    ac_rfl

end DoubledParts
end GraphicalZonotopes
