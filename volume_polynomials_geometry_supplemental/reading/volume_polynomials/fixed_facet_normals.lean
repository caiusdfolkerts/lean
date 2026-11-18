module

public import VolumePolynomials.IrredundantHalfspaces
public import VolumePolynomials.FinitePolytope

@[expose] public section
set_option autoImplicit false

/-!
# One finite family of normals for every positive Minkowski sum

The proof uses finite V/H representation, removal of redundant inequalities,
and the invariant direction spaces of exposed faces. The resulting halfspace
formula is an exact equality of the original sets for every positive real
assignment of weights. Summands may have arbitrary affine dimension.
-/

noncomputable section
open Set
open scoped Pointwise RealInnerProductSpace BigOperators

namespace VolumePolynomials.PolytopeGeometry

open OAI.Paper092

theorem IsFiniteHull.has_halfspaces {d : ℕ} {C : Set (Euclidean d)}
    (hC : IsFiniteHull C) (hint : (interior C).Nonempty) :
    ∃ k : ℕ, ∃ P : HPolytope d (Fin k), P.body = C := by
  first
  | obtain ⟨S, rfl⟩ := hC.exists_finset
    exact finite_convex_hull_has_halfspaces S hint

theorem IsFiniteHull.has_irredundant_halfspaces {d : ℕ} {C : Set (Euclidean d)}
    (hC : IsFiniteHull C) (hint : (interior C).Nonempty) :
    ∃ k : ℕ, ∃ P : HPolytope d (Fin k),
      P.body = C ∧ ∀ i, P.IsEssential i := by
  first
  | obtain ⟨k, P, hP⟩ := hC.has_halfspaces hint
    obtain ⟨m, Q, hQ, he⟩ := P.exists_irredundant
    exact ⟨m, Q, hQ.trans hP, he⟩

theorem positive_sum_interior_nonempty_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (A : ι → Set E)
    (hc : ∀ i, Convex ℝ (A i)) (hne : ∀ i, (A i).Nonempty)
    (t : ι → ℝ) (ht : ∀ i, 0 < t i) :
    (interior (∑ i, t i • A i)).Nonempty ↔ (interior (∑ i, A i)).Nonempty := by
  first
  | have hneA : (∑ i, A i).Nonempty :=
      PolytopeFaces.nonempty_sum Finset.univ A (fun i _ => hne i)
    have hnet : (∑ i, t i • A i).Nonempty :=
      PolytopeFaces.nonempty_sum Finset.univ _ (fun i _ => (hne i).image _)
    have hconvA : Convex ℝ (∑ i, A i) := convex_sum A (fun i _ => hc i)
    have hconvt : Convex ℝ (∑ i, t i • A i) :=
      convex_sum _ (fun i _ => (hc i).smul (t i))
    rw [hconvt.interior_nonempty_iff_affineSpan_eq_top,
      hconvA.interior_nonempty_iff_affineSpan_eq_top,
      AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ E E hnet,
      AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ E E hneA,
      PolytopeFaces.vectorSpan_weighted_sum Finset.univ A t
        (fun i _ => hne i) (fun i _ => ht i)]

theorem support_positive_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (A : ι → Set E)
    (hA : ∀ i, IsCompact (A i)) (hne : ∀ i, (A i).Nonempty)
    (t : ι → ℝ) (ht : ∀ i, 0 < t i) (l : E →L[ℝ] ℝ) :
    SupportGeometry.support (∑ i, t i • A i) l =
      ∑ i, t i * SupportGeometry.support (A i) l := by
  first
  | have hcompact : ∀ i, IsCompact (t i • A i) := fun i =>
      (hA i).image (continuous_const.smul continuous_id)
    have hnonempty : ∀ i, (t i • A i).Nonempty := fun i =>
      (hne i).image (fun x => t i • x)
    rw [SupportGeometry.support_sum Finset.univ (fun i => t i • A i)
      (fun i _ => hcompact i) (fun i _ => hnonempty i)]
    apply Finset.sum_congr rfl
    intro i hi
    exact SupportGeometry.support_smul (A i) l (ht i).le

/-- Every positive sum has precisely the halfspaces determined by the normals
of any fixed H-representation of the unweighted total and its own supports. -/
theorem positive_sum_eq_support_halfspaces
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → Set (Euclidean d)) (hA : ∀ i, IsFiniteHull (A i))
    (hne : ∀ i, (A i).Nonempty) (hint : (interior (∑ i, A i)).Nonempty)
    (P : HPolytope d κ) (hP : P.body = ∑ i, A i)
    (t : ι → ℝ) (ht : ∀ i, 0 < t i) :
    (∑ i, t i • A i) =
      {x | ∀ i, ⟪P.normal i, x⟫ ≤
        SupportGeometry.support (∑ j, t j • A j) (innerSL ℝ (P.normal i))} := by
  first
  | have hCt := IsFiniteHull.weighted_sum Finset.univ A (fun i _ => hA i) t
    have hnt : (interior (∑ i, t i • A i)).Nonempty :=
      (positive_sum_interior_nonempty_iff A (fun i => (hA i).convex) hne t ht).mpr hint
    obtain ⟨m, Q, hQ, he⟩ := hCt.has_irredundant_halfspaces hnt
    ext x
    constructor
    · intro hx i
      exact SupportGeometry.le_support hCt.isCompact (innerSL ℝ (P.normal i)) hx
    · intro hx
      rw [← hQ]
      intro j
      have hneF : (Q.face j).Nonempty := by
        obtain ⟨y, hy, _⟩ := Q.exists_strict_face_point_of_essential j (he j)
        exact ⟨y, hy⟩
      have hface : Q.face j = exposedFace (∑ i, t i • A i) (Q.normal j) := by
        rw [Q.face_eq_exposedFace j hneF, hQ]
      have hdim : Module.finrank ℝ
          (vectorSpan ℝ (exposedFace (∑ i, t i • A i) (Q.normal j))) = d - 1 := by
        rw [← hface]
        exact Q.finrank_face_of_essential j (he j)
      obtain ⟨i, hi⟩ := positive_sum_facet_normals A (fun i => (hA i).isCompact)
        hne P hP t ht (Q.normal_unit j) hdim
      rw [Q.offset_eq_support j hneF, hQ, hi]
      exact hx i

/-- The fixed halfspace offsets are linear functions of the positive weights. -/
theorem positive_sum_eq_fixed_halfspaces
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → Set (Euclidean d)) (hA : ∀ i, IsFiniteHull (A i))
    (hne : ∀ i, (A i).Nonempty) (hint : (interior (∑ i, A i)).Nonempty)
    (P : HPolytope d κ) (hP : P.body = ∑ i, A i)
    (t : ι → ℝ) (ht : ∀ i, 0 < t i) :
    (∑ i, t i • A i) =
      {x | ∀ i, ⟪P.normal i, x⟫ ≤
        ∑ j, t j * SupportGeometry.support (A j) (innerSL ℝ (P.normal i))} := by
  first
  | rw [positive_sum_eq_support_halfspaces A hA hne hint P hP t ht]
    congr 1
    funext x
    apply propext
    simp_rw [support_positive_sum A (fun i => (hA i).isCompact) hne t ht]

end VolumePolynomials.PolytopeGeometry

namespace OAI.Paper092.HPolytope

open VolumePolynomials.PolytopeGeometry

theorem normal_injective_of_essential {d : ℕ} {ι : Type*} [Fintype ι]
    (P : HPolytope d ι) (he : ∀ i, P.IsEssential i) : Function.Injective P.normal := by
  first
  | intro i j hij
    have hnei : (P.face i).Nonempty := by
      obtain ⟨x, hx, _⟩ := P.exists_strict_face_point_of_essential i (he i)
      exact ⟨x, hx⟩
    have hnej : (P.face j).Nonempty := by
      obtain ⟨x, hx, _⟩ := P.exists_strict_face_point_of_essential j (he j)
      exact ⟨x, hx⟩
    apply P.distinct
    refine Prod.ext hij ?_
    change P.offset i = P.offset j
    rw [P.offset_eq_support i hnei, P.offset_eq_support j hnej, hij]

end OAI.Paper092.HPolytope
