module

public import Papers.GraphicalZonotopes.TwoHubPrincipal
public import Papers.GraphicalZonotopes.PolytopalDimension

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.TwoHub
open scoped Pointwise

/-- The supremum in Theorem8.7 uses precisely the paper's convention that
indecomposability tests finite polytopal Minkowski decompositions. -/
theorem classification_polytopal (p b : ℕ) (hp : 1≤p) (hb : 1≤b) :
    (sSup {d : ℕ | ∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,b] i))→ℝ),
      IsFinitePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p b)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=d})=
      min (p+b+1) (2^(min p b)+2*min p b+1) := by
  rw [←maximumIndecomposableDimension_eq_polytopal_supremum]
  exact maximum_dimension p b hp hb

theorem full_polytopal_iff (p b : ℕ) (hp : 1≤p) (hb : 1≤b) :
    (∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,b] i))→ℝ),
      IsFinitePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p b))) ↔
      max p b≤2^(min p b)+min p b := by
  rw [←supportsFullIndecomposable_iff_polytopal_weak]
  exact supports_full_iff p b hp hb

theorem lattice_polytopal_attainment (p b : ℕ) (hp : 1≤p) (hb : 1≤b) :
    ∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,b] i))→ℝ),
      LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p b)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=min (p+b+1) (2^(min p b)+2*min p b+1) := by
  obtain ⟨Q,hQ,hl,hi,hw,hd⟩:=(all_attainment p b hp hb).polytope
  exact ⟨Q,hl,(weakSummand_indecomposable_iff_polytopal hQ hw).mp hi,hw,hd⟩

/-- The lattice witness in Theorem8.4 has an actual finite polytopal
complement at exactly the stated dilation. -/
theorem exponential_polytopal_summand (p : ℕ) (hp : 1≤p) :
    ∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,2^p+p] i))→ℝ),
      LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=2^p+2*p+1 ∧
      ∃ R : Set ((Σ i : Fin 4,Fin (![1,1,p,2^p+p] i))→ℝ),
        IsFinitePolytope R ∧ R.Nonempty ∧
        Q+R=((((p-1)*2^p+2 : ℕ) : ℝ) •
          graphicalZonotope (twoSingletonGraph p (2^p+p))) := by
  obtain ⟨Q,hl,hi,hd,hs⟩:=(exponential_lattice_summand p hp).polytope
  have hM : (0 : ℝ)<(((p-1)*2^p+2 : ℕ) : ℝ):=by positivity
  have hw : IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p (2^p+p))):=
    ⟨_,hM,hs⟩
  refine ⟨Q,hl,(weakSummand_indecomposable_iff_polytopal hl.finitePolytope hw).mp hi,hd,?_⟩
  exact (isMinkowskiSummand_graphical_iff_finite_complement hl.finitePolytope hM.le).mp hs

end GraphicalZonotopes.TwoHub
