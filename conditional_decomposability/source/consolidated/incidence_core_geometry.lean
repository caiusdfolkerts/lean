module
public import consolidated.deletion_geometry
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

set_option Elab.async false

section BundlePart0
/- Source: Papers/IncidenceCoreGeometry.lean -/




@[expose] public section

/-!
# Actual faces retained by an incidence core

These lemmas concern ordinary convex hulls and exposed faces.  They justify
replacing a selected set of vertices by its convex hull in the three-dimensional
point--facet incidence peeling argument.
-/

noncomputable section

namespace Papers.IncidenceCoreGeometry

open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

variable {d : ℕ}

theorem dimension_mono {A B : Set (E d)} (h : A ⊆ B) :
    faceDim A ≤ faceDim B :=
  Submodule.finrank_mono (vectorSpan_mono ℝ h)

/-- Any set containing three distinct actual extreme vertices has affine
dimension at least two. No independent-frame hypothesis is supplied. -/
theorem three_vertices_dimension_of_subset (P : ConvexPolytope d)
    (S : Finset (E d)) (hSP : S ⊆ P.vertices) (A : Set (E d))
    (hSA : ∀ x∈S, x∈A) (hcard : 3 ≤ S.card) :
    2 ≤ faceDim A := by
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ :=
    Finset.two_lt_card_iff.mp (show 2<S.card by omega)
  by_contra hd
  have hcol : Collinear ℝ A :=
    collinear_iff_finrank_le_one.mpr (show finrank ℝ (vectorSpan ℝ A)≤1 by
      change faceDim A≤1
      omega)
  have hsub : ({x,y,z} : Set (E d))⊆A := by
    intro w hw
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact hSA _ hx
    · exact hSA _ hy
    · exact hSA _ hz
  exact vertices_not_collinear P (hSP hx) (hSP hy) (hSP hz)
    hxy hxz hyz (hcol.subset hsub)

theorem three_vertices_dimension (P : ConvexPolytope d) (A : Set (E d))
    (hcard : 3 ≤ (P.vertices.filter (· ∈ A)).card) :
    2 ≤ faceDim A :=
  three_vertices_dimension_of_subset P _ (Finset.filter_subset _ _) A
    (fun _ h => (Finset.mem_filter.mp h).2) hcard

/-- Equal-dimensional exposed faces which contain a set spanning their full
dimension coincide. This uses the strict dimension increase of actual faces. -/
theorem faces_eq_of_full_dim_common_subset (P : ConvexPolytope d)
    {F G A : Set (E d)} (hF : P.IsFace F) (hG : P.IsFace G)
    (hA : A.Nonempty) (hAF : A⊆F) (hAG : A⊆G)
    (hFd : faceDim F≤faceDim A) (hGd : faceDim G≤faceDim A) : F=G := by
  have hAI : A⊆F∩G := fun x hx => ⟨hAF hx,hAG hx⟩
  have hI : P.IsFace (F∩G) := isFace_inter P hF hG (hA.mono hAI)
  have hd := dimension_mono hAI
  have hIF : F∩G=F := by
    by_contra hne
    have hlt := faceDim_lt_of_ssubset P hI hF
      (Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_left,hne⟩)
    omega
  have hIG : F∩G=G := by
    by_contra hne
    have hlt := faceDim_lt_of_ssubset P hI hG
      (Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_right,hne⟩)
    omega
  exact hIF.symm.trans hIG

/-- A two-face containing at least three retained vertices remains a
two-face of the smaller actual convex hull. -/
theorem retained_two_face (P Q : ConvexPolytope d)
    (hQP : Q.toSet⊆P.toSet) {F : Set (E d)}
    (hF : P.IsFace F) (hdF : faceDim F=2)
    (hcard : 3≤(Q.vertices.filter (· ∈ F)).card) :
    Q.IsFace (F∩Q.toSet) ∧ faceDim (F∩Q.toSet)=2 := by
  have hdim : 2≤faceDim (F∩Q.toSet) :=
    three_vertices_dimension_of_subset Q (Q.vertices.filter (·∈F))
      (Finset.filter_subset _ _) (F∩Q.toSet) (by
        intro x hx
        obtain ⟨hxQ,hxF⟩ := Finset.mem_filter.mp hx
        exact ⟨hxF,vertex_mem_body Q hxQ⟩) hcard
  have hle : faceDim (F∩Q.toSet)≤2 := by
    simpa only [hdF] using (dimension_mono (A:=F∩Q.toSet) Set.inter_subset_left)
  have hne : (F∩Q.toSet).Nonempty := by
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<(Q.vertices.filter (· ∈ F)).card by omega)
    obtain ⟨hxQ,hxF⟩ := Finset.mem_filter.mp hx
    exact ⟨x,hxF,vertex_mem_body Q hxQ⟩
  exact ⟨face_inter_subpolytope P Q hQP hF hne,le_antisymm hle hdim⟩

/-- Two different retained old facets force the active vertex hull to retain
dimension three. This excludes the lower-dimensional incidence-core case. -/
theorem dimension_three_of_two_retained_faces (P Q : ConvexPolytope d)
    (hdP : P.dim=3) (hQP : Q.toSet⊆P.toSet)
    {F G : Set (E d)} (hF : P.IsFace F) (hG : P.IsFace G)
    (hdF : faceDim F=2) (hdG : faceDim G=2) (hFG : F≠G)
    (hFc : 3≤(Q.vertices.filter (· ∈ F)).card)
    (hGc : 3≤(Q.vertices.filter (· ∈ G)).card) : Q.dim=3 := by
  obtain ⟨hRF,hdRF⟩ := retained_two_face P Q hQP hF hdF hFc
  obtain ⟨hRG,hdRG⟩ := retained_two_face P Q hQP hG hdG hGc
  have htop : Q.dim≤3 := by
    have hh := dimension_mono hQP
    change Q.dim≤P.dim at hh
    simpa only [hdP] using hh
  by_contra hdim
  have hQd : Q.dim≤2 := by omega
  have hQnonempty : Q.toSet.Nonempty := by
    obtain ⟨v,hv⟩ := Q.vertices_nonempty
    exact ⟨v,vertex_mem_body Q hv⟩
  have hRFeq : F∩Q.toSet=Q.toSet := by
    by_contra hne
    have hlt := faceDim_lt_of_ssubset Q hRF (toSet_isFace Q)
      (Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_right,hne⟩)
    change faceDim (F∩Q.toSet)<Q.dim at hlt
    omega
  have hRGeq : G∩Q.toSet=Q.toSet := by
    by_contra hne
    have hlt := faceDim_lt_of_ssubset Q hRG (toSet_isFace Q)
      (Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_right,hne⟩)
    change faceDim (G∩Q.toSet)<Q.dim at hlt
    omega
  apply hFG
  apply faces_eq_of_full_dim_common_subset P hF hG hQnonempty
  · intro x hx
    rw [←hRFeq] at hx
    exact hx.1
  · intro x hx
    rw [←hRGeq] at hx
    exact hx.1
  · rw [hdF,←hRFeq,hdRF]
  · rw [hdG,←hRGeq,hdRG]

end Papers.IncidenceCoreGeometry

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/BipartiteIncidencePeeling.lean -/






@[expose] public section

noncomputable section

namespace Papers.BipartiteIncidencePeeling

open scoped BigOperators

variable {V F : Type*} [DecidableEq V] [DecidableEq F]

def pointDegree (R : V → F → Prop) [DecidableRel R]
    (T : Finset F) (v : V) : ℕ := (T.filter (R v)).card

def faceDegree (R : V → F → Prop) [DecidableRel R]
    (S : Finset V) (f : F) : ℕ := (S.filter (fun v => R v f)).card

theorem sum_degrees (R : V → F → Prop) [DecidableRel R]
    (S : Finset V) (T : Finset F) :
    (∑ v ∈ S, pointDegree R T v) = ∑ f ∈ T, faceDegree R S f := by
  simp only [pointDegree,faceDegree,Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_comm

/-- The Euler incidence bound forces an eliminable point or face. This
lemma is purely finite counting; the geometric incidence bound is supplied
separately by the actual three-dimensional polytope argument. -/
theorem exists_degree_le_three
    (R : V → F → Prop) [DecidableRel R]
    (S : Finset V) (T : Finset F)
    (hbound : (∑ v ∈ S, (pointDegree R T v : ℤ)) <
      2*((S.card : ℤ)+T.card)) :
    (∃ v ∈ S, pointDegree R T v ≤ 3) ∨
      (∃ f ∈ T, faceDegree R S f ≤ 3) := by
  by_contra h
  have hv : ∀ v ∈ S, 4 ≤ pointDegree R T v := by
    intro v hv
    by_contra hd
    exact h (Or.inl ⟨v,hv,by omega⟩)
  have hf : ∀ f ∈ T, 4 ≤ faceDegree R S f := by
    intro f hf
    by_contra hd
    exact h (Or.inr ⟨f,hf,by omega⟩)
  have hleft : 4*(S.card : ℤ) ≤ ∑ v ∈ S, (pointDegree R T v : ℤ) := by
    calc
      4*(S.card : ℤ) = ∑ _v ∈ S, (4 : ℤ) := by simp [mul_comm]
      _ ≤ ∑ v ∈ S, (pointDegree R T v : ℤ) :=
        Finset.sum_le_sum (fun v hvS => by exact_mod_cast hv v hvS)
  have hright : 4*(T.card : ℤ) ≤ ∑ f ∈ T, (faceDegree R S f : ℤ) := by
    calc
      4*(T.card : ℤ) = ∑ _f ∈ T, (4 : ℤ) := by simp [mul_comm]
      _ ≤ ∑ f ∈ T, (faceDegree R S f : ℤ) :=
        Finset.sum_le_sum (fun f hfT => by exact_mod_cast hf f hfT)
  have hsum : (∑ v ∈ S, (pointDegree R T v : ℤ)) =
      ∑ f ∈ T, (faceDegree R S f : ℤ) := by
    exact_mod_cast sum_degrees R S T
  linarith

end Papers.BipartiteIncidencePeeling

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/SupportFormIndependence.lean -/









@[expose] public section

noncomputable section

/-!
# Independent affine supporting forms

Three distinct facets can be separated without constructing a polar body:
choose a point in each facet that is strictly inside the other two supporting
halfspaces. The evaluation matrix has zero diagonal and strictly positive
off-diagonal entries, hence positive determinant.

This file isolates the finite convexity and evaluation argument. The hypotheses
of the final lemma are concrete affine equalities and inequalities, not a
generic-rank assertion.
-/

namespace Papers.RationalityTen

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Finitely many nonnegative affine functions that are individually strictly
positive somewhere on a nonempty convex set are simultaneously strictly
positive at one point of that set. -/
theorem exists_all_affine_positive {ι : Type*} [Fintype ι]
    (S : Set V) (hS : Convex ℝ S) (hne : S.Nonempty)
    (f : ι → V →ᵃ[ℝ] ℝ)
    (hnonneg : ∀ i x, x ∈ S → 0 ≤ f i x)
    (hpositive : ∀ i, ∃ x ∈ S, 0 < f i x) :
    ∃ x ∈ S, ∀ i, 0 < f i x := by
  classical
  have hfinite : ∀ t : Finset ι, ∃ x ∈ S, ∀ i ∈ t, 0 < f i x := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        obtain ⟨x, hx⟩ := hne
        exact ⟨x, hx, by simp⟩
    | @insert i t hit ih =>
        obtain ⟨x, hx, hxp⟩ := ih
        obtain ⟨y, hy, hyp⟩ := hpositive i
        refine ⟨midpoint ℝ x y, hS.midpoint_mem hx hy, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          rw [AffineMap.map_midpoint]
          have hm := midpoint_add_self ℝ (f i x) (f i y)
          have hx0 := hnonneg i x hx
          linarith
        · rw [AffineMap.map_midpoint]
          have hm := midpoint_add_self ℝ (f j x) (f j y)
          have hy0 := hnonneg j y hy
          have hxpos := hxp j hj
          linarith
  obtain ⟨x, hx, hxp⟩ := hfinite Finset.univ
  exact ⟨x, hx, fun i => hxp i (Finset.mem_univ i)⟩

/-- A real three-by-three matrix with zero diagonal and positive off-diagonal
entries has positive determinant. -/
theorem det_pos_of_zero_diagonal_positive_offDiagonal
    (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hdiag : ∀ i, A i i = 0)
    (hoff : ∀ i j, i ≠ j → 0 < A i j) :
    0 < A.det := by
  have hformula :
      A.det = A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 := by
    rw [Matrix.det_fin_three, hdiag 0, hdiag 1, hdiag 2]
    ring
  rw [hformula]
  exact add_pos
    (mul_pos (mul_pos (hoff 0 1 (by decide)) (hoff 1 2 (by decide)))
      (hoff 2 0 (by decide)))
    (mul_pos (mul_pos (hoff 0 2 (by decide)) (hoff 1 0 (by decide)))
      (hoff 2 1 (by decide)))

/-- A nonsingular finite evaluation matrix certifies independence of affine
forms. The matrix rows are evaluation points and its columns are the forms. -/
theorem affineForms_independent_of_evaluationMatrix {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (f : ι → V →ᵃ[ℝ] ℝ) (p : ι → V)
    (hdet : (Matrix.of (fun i j => f j (p i))).det ≠ 0) :
    LinearIndependent ℝ f := by
  let ev : (V →ᵃ[ℝ] ℝ) →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun g i => g (p i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let A : Matrix ι ι ℝ := fun i j => f j (p i)
  apply LinearIndependent.of_comp ev
  change LinearIndependent ℝ A.col
  exact Matrix.linearIndependent_col_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet))

/-- A zero/nonzero separation witness proves independence of two affine
forms without assuming a generic matrix rank. -/
theorem two_affineForms_independent_of_separating_evaluations
    (f g : V →ᵃ[ℝ] ℝ) (x y : V)
    (hfx : f x = 0) (hgx : g x ≠ 0) (hfy : f y ≠ 0) :
    LinearIndependent ℝ ![f, g] := by
  apply affineForms_independent_of_evaluationMatrix ![f, g] ![x, y]
  simpa [Matrix.det_fin_two, hfx] using
    (neg_ne_zero.mpr (mul_ne_zero hgx hfy))

/-- Affine forms admitting a zero-diagonal, positive off-diagonal evaluation
pattern are linearly independent. -/
theorem three_affineForms_independent_of_evaluations
    (f : Fin 3 → V →ᵃ[ℝ] ℝ) (p : Fin 3 → V)
    (hzero : ∀ i, f i (p i) = 0)
    (hpositive : ∀ i j, i ≠ j → 0 < f j (p i)) :
    LinearIndependent ℝ f := by
  let ev : (V →ᵃ[ℝ] ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
    { toFun := fun g i => g (p i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let A : Matrix (Fin 3) (Fin 3) ℝ := fun i j => f j (p i)
  have hdet : 0 < A.det :=
    det_pos_of_zero_diagonal_positive_offDiagonal A hzero hpositive
  apply LinearIndependent.of_comp ev
  change LinearIndependent ℝ A.col
  exact Matrix.linearIndependent_col_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet.ne'))

/-- A concrete convex support criterion for independence of three affine forms.
For actual distinct facets, the final witness condition follows from their
maximality: no distinct facet contains another. -/
theorem three_affineForms_independent_of_convex_supports
    (f : Fin 3 → V →ᵃ[ℝ] ℝ) (S : Fin 3 → Set V)
    (hconvex : ∀ i, Convex ℝ (S i))
    (hne : ∀ i, (S i).Nonempty)
    (hzero : ∀ i x, x ∈ S i → f i x = 0)
    (hnonneg : ∀ i j x, x ∈ S i → 0 ≤ f j x)
    (hwitness : ∀ i j, i ≠ j → ∃ x ∈ S i, 0 < f j x) :
    LinearIndependent ℝ f := by
  classical
  have hp : ∀ i, ∃ p ∈ S i, ∀ j, i ≠ j → 0 < f j p := by
    intro i
    obtain ⟨p, hp, hpp⟩ := exists_all_affine_positive
      (S i) (hconvex i) (hne i)
      (fun j : {j : Fin 3 // i ≠ j} => f j.1)
      (fun j x hx => hnonneg i j.1 x hx)
      (fun j => hwitness i j.1 j.2)
    exact ⟨p, hp, fun j hij => hpp ⟨j, hij⟩⟩
  choose p hmem hpos using hp
  exact three_affineForms_independent_of_evaluations f p
    (fun i => hzero i (p i) (hmem i)) hpos

/-- The same positive evaluation criterion for ordinary linear forms on an
arbitrary real module. -/
theorem three_linearForms_independent_of_evaluations
    (f : Fin 3 → V →ₗ[ℝ] ℝ) (p : Fin 3 → V)
    (hzero : ∀ i, f i (p i) = 0)
    (hpositive : ∀ i j, i ≠ j → 0 < f j (p i)) :
    LinearIndependent ℝ f := by
  let toAffine : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] (V →ᵃ[ℝ] ℝ) :=
    { toFun := fun g => g.toAffineMap
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply LinearIndependent.of_comp toAffine
  exact three_affineForms_independent_of_evaluations
    (fun i => (f i).toAffineMap) p hzero hpositive


/-- A pair of independent equations together with a third equation that
does not vanish on their common witness is an independent triple.
This is the precise linear-algebra argument behind projection rule (iv). -/
theorem three_vectors_independent_of_pair_and_functional
    (x y z : V) (ell : V →ₗ[ℝ] ℝ)
    (hxy : LinearIndependent ℝ ![x,y])
    (hx : ell x = 0) (hy : ell y = 0) (hz : ell z ≠ 0) :
    LinearIndependent ℝ ![x,y,z] := by
  have hspan : Submodule.span ℝ (Set.range ![x,y]) ≤ ell.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact hx
    · exact hy
  have hzspan : z ∉ Submodule.span ℝ (Set.range ![x,y]) :=
    fun h => hz (hspan h)
  have hsnoc : Fin.snoc ![x,y] z = ![x,y,z] := by
    ext i
    fin_cases i <;> rfl
  simpa only [hsnoc] using hxy.finSnoc hzspan

/-- The same nonsingular evaluation matrix certifies independence of the
evaluated vectors, as well as independence of the evaluating forms. -/
theorem three_vectors_independent_of_evaluations
    (f : Fin 3 → V →ₗ[ℝ] ℝ) (p : Fin 3 → V)
    (hzero : ∀ i, f i (p i) = 0)
    (hpositive : ∀ i j, i ≠ j → 0 < f j (p i)) :
    LinearIndependent ℝ p := by
  let ev : V →ₗ[ℝ] (Fin 3 → ℝ) :=
    { toFun := fun x i => f i x
      map_add' := by intro x y; ext i; exact map_add (f i) x y
      map_smul' := by intro a x; ext i; exact map_smul (f i) a x }
  let A : Matrix (Fin 3) (Fin 3) ℝ := fun i j => f i (p j)
  have hdet : 0 < A.det :=
    det_pos_of_zero_diagonal_positive_offDiagonal A hzero
      (fun i j hij => hpositive j i hij.symm)
  apply LinearIndependent.of_comp ev
  change LinearIndependent ℝ A.col
  exact Matrix.linearIndependent_col_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet.ne'))

end Papers.RationalityTen

end
end
end BundlePart2

