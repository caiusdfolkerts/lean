module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part06
public import Unimodular.FanMaximalCones

/-!
# Purity of every actual finite smooth complete fan

The full-dimensional cones cover the real space by density and closedness.
Applying this to the positive sum of the rays of a cone places that cone in a
full-dimensional one. Purity is a consequence of the genuine fan axioms and
is not an additional geometric hypothesis on the section-ring theorem.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Topology
open Set

namespace PaperVerification.ToricGeometry

variable {n : ℕ}

theorem latticeRayCone_finitely_generated (s : Finset (Lattice n)) :
    (latticeRayCone s).FG := by
  refine ⟨s.image (embed n), ?_⟩
  exact (finiteRayCone_eq_hull _).symm

theorem latticeRayCone_closed (s : Finset (Lattice n)) :
    IsClosed (latticeRayCone s : Set (Ambient n)) :=
  Unimodular.ConeInterior.isClosed_of_fg (latticeRayCone_finitely_generated s)

namespace SmoothCompleteFan

variable (F : SmoothCompleteFan n)

/-- All full-dimensional cones already cover every real point. -/
theorem full_cones_cover (x : Ambient n) :
    ∃ s ∈ F.cones, Submodule.span ℝ (latticeRayCone s : Set (Ambient n)) = ⊤ ∧
      x ∈ latticeRayCone s := by
  classical
  let C := {s : Finset (Lattice n) // s ∈ F.cones}
  letI : Fintype C := Fintype.ofFinite C
  let P := {s : C // Submodule.span ℝ (latticeRayCone s.1 : Set (Ambient n)) ≠ ⊤}
  letI : Fintype P := Fintype.ofFinite P
  let Q := {s : C // Submodule.span ℝ (latticeRayCone s.1 : Set (Ambient n)) = ⊤}
  letI : Fintype Q := Fintype.ofFinite Q
  let T : Set (Ambient n) := ⋃ s : Q, (latticeRayCone s.1.1 : Set (Ambient n))
  have hclosed : IsClosed T := isClosed_iUnion_of_finite
    (fun s : Q => latticeRayCone_closed s.1.1)
  have hdense := Unimodular.FiniteSubspacePaths.dense_complement
    (fun s : P => Submodule.span ℝ (latticeRayCone s.1.1 : Set (Ambient n)))
    (fun s => s.2)
  have hsubset : {z : Ambient n | ∀ s : P,
      z ∉ Submodule.span ℝ (latticeRayCone s.1.1 : Set (Ambient n))} ⊆ T := by
    intro z hz
    obtain ⟨s, hs, hzs⟩ := F.complete z
    have hfull : Submodule.span ℝ (latticeRayCone s : Set (Ambient n)) = ⊤ := by
      by_contra hn
      exact hz ⟨⟨s, hs⟩, hn⟩ (Submodule.subset_span hzs)
    exact Set.mem_iUnion.mpr ⟨⟨⟨s, hs⟩, hfull⟩, hzs⟩
  have huniv : T = Set.univ :=
    hclosed.closure_eq.symm.trans (hdense.mono hsubset).closure_eq
  have hx : x ∈ T := by rw [huniv]; trivial
  obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hx
  exact ⟨s.1.1, s.1.2, s.2, hxs⟩

/-- A smooth full-dimensional cone contains exactly n basis rays. -/
theorem card_eq_of_full_span {s : Finset (Lattice n)} (hs : s ∈ F.cones)
    (hfull : Submodule.span ℝ (latticeRayCone s : Set (Ambient n)) = ⊤) : s.card = n := by
  classical
  obtain ⟨b, I, rfl⟩ := F.smooth s hs
  have hI : I = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    by_contra hi
    let l : Ambient n →ₗ[ℝ] ℝ := (integralBasisReal b).coord i
    have hker : Submodule.span ℝ (latticeRayCone (I.image b) : Set (Ambient n)) ≤
        LinearMap.ker l := by
      apply Submodule.span_le.mpr
      intro x hx
      exact (mem_latticeRayCone_basis_iff b I x).mp hx |>.2 i hi
    rw [hfull] at hker
    have hz : l (integralBasisReal b i) = 0 := hker Submodule.mem_top
    have hone : (1 : ℝ) = 0 := by
      simpa only [l, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_same] using hz
    exact one_ne_zero hone
  rw [hI, Finset.card_image_of_injective _ b.injective]
  simp

/-- Purity follows for every smooth complete fan, including dimension zero. -/
theorem isPure : F.IsPure := by
  intro s hs
  obtain ⟨t, ht, hfull, hx⟩ := F.full_cones_cover (∑ v ∈ s, embed n v)
  exact ⟨t, ht, F.sum_mem_cone_implies_subset hs ht hx, F.card_eq_of_full_span ht hfull⟩

end SmoothCompleteFan

#print axioms SmoothCompleteFan.full_cones_cover
#print axioms SmoothCompleteFan.card_eq_of_full_span
#print axioms SmoothCompleteFan.isPure

end PaperVerification.ToricGeometry

#check PaperVerification.ToricGeometry.SmoothCompleteFan.isPure
