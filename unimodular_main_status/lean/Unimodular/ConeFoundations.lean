module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Push
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Geometry.Convex.Cone.Face.Lattice
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Data.Real.Basic
public import Unimodular
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-! ## Tucker -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in LICENSE-TauCeti.
Authors: The Tau Ceti contributors

The two proof bodies below are reproduced from
TauCeti/Geometry/Convex/Cone/Alternative.lean at commit
06d5bb4e3ebb737dc6538567f5c53bf8800b9362.
Only the namespace and direct imports have been changed.
-/



namespace Unimodular.Tucker

variable {ι K V : Type*}
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup V] [Module K V]

private theorem exists_nonneg_sum_smul_eq_zero_and_coeff_add_dual_pos_at_of_finset [DecidableEq ι]
    (k : ι)
    (s : Finset ι) (a : ι → V) :
    ∃ x : ι → K, ∃ y : Module.Dual K V, (∀ j ∈ insert k s, 0 ≤ x j ∧ 0 ≤ y (a j)) ∧
      ∑ j ∈ insert k s, x j • a j = 0 ∧ 0 < x k + y (a k) := by
  induction s using Finset.induction_on generalizing a with
  | empty =>
    by_cases ha : a k = 0
    · exact ⟨Pi.single k 1, 0, by simp, by simp [ha], by simp⟩
    · obtain ⟨y, hy⟩ := Module.Projective.exists_dual_eq_one K ha
      exact ⟨0, y, by simp [hy], by simp, by simp [hy]⟩
  | insert n s hn ih =>
    by_cases hnk : n = k
    · subst hnk
      simpa only [Finset.insert_idem] using ih a
    have hn' : n ∉ insert k s := by simp [hn, hnk]
    have hne : ∀ j ∈ insert k s, j ≠ n := fun j hj h => hn' (h ▸ hj)
    rw [Finset.insert_comm]
    obtain ⟨x, y, hxy, hsum, hpos⟩ := ih a
    by_cases hy : 0 ≤ y (a n)
    · -- `y` is already nonnegative on the new vector: extend `x` by zero.
      refine ⟨Function.update x n 0, y, ?_, ?_, ?_⟩
      · rintro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · simp [hy]
        · simpa [Function.update_of_ne (hne j hj)] using hxy j hj
      · rw [Finset.sum_insert hn', Function.update_self, zero_smul, zero_add, ← hsum]
        exact Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (hne j hj)]
      · rwa [Function.update_of_ne (Ne.symm hnk)]
    · -- Otherwise project the old vectors along `a n` onto `ker y` and apply the induction
      -- hypothesis to the projected family `b j = a j + c j • a n`, where `y (b j) = 0`.
      push Not at hy
      set d := y (a n)
      have hd : d ≠ 0 := hy.ne
      set c : ι → K := fun j => -y (a j) / d
      have hc : ∀ j ∈ insert k s, 0 ≤ c j := fun j hj =>
        div_nonneg_of_nonpos (neg_nonpos.2 (hxy j hj).2) hy.le
      obtain ⟨u, z, huz, hsum', hpos'⟩ := ih fun j => a j + c j • a n
      set w : Module.Dual K V := z + (-z (a n) / d) • y
      have hw : ∀ j, w (a j) = z (a j + c j • a n) := fun j => by
        simp only [w, c, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
          smul_eq_mul]
        field_simp
      refine ⟨Function.update u n (∑ j ∈ insert k s, c j * u j), w, ?_, ?_, ?_⟩
      · rintro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · refine ⟨?_, ?_⟩
          · rw [Function.update_self]
            exact Finset.sum_nonneg fun i hi => mul_nonneg (hc i hi) (huz i hi).1
          · simp only [w, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
            rw [div_mul_cancel₀ _ hd, add_neg_cancel]
        · rw [Function.update_of_ne (hne j hj), hw]
          exact huz j hj
      · rw [Finset.sum_insert hn', Function.update_self, ← hsum', Finset.sum_smul]
        simp only [smul_add, smul_smul, Finset.sum_add_distrib]
        rw [add_comm]
        congr 1
        · exact Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (hne j hj)]
        · exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]
      · rw [Function.update_of_ne (Ne.symm hnk), hw]
        exact hpos'

/-- **Tucker's key lemma.** For a finite family of vectors `a j` and an index `k`, there are a
nonnegative linear relation `x` among the `a j` and a linear functional `y` that is nonnegative on
every `a j`, such that `x k + y (a k) > 0`: either `a k` occurs in a nonnegative relation, or some
functional nonnegative on the family is strictly positive on `a k`. -/
theorem exists_nonneg_sum_smul_eq_zero_and_coeff_add_dual_pos_at [Fintype ι] (a : ι → V) (k : ι) :
    ∃ x : ι → K, ∃ y : Module.Dual K V, 0 ≤ x ∧ ∑ j, x j • a j = 0 ∧ (∀ j, 0 ≤ y (a j)) ∧
      0 < x k + y (a k) := by
  classical
  obtain ⟨x, y, hxy, hsum, hpos⟩ :=
    exists_nonneg_sum_smul_eq_zero_and_coeff_add_dual_pos_at_of_finset (K := K) k
      (Finset.univ.erase k) a
  rw [Finset.insert_erase (Finset.mem_univ k)] at hxy hsum
  exact ⟨x, y, fun j => (hxy j (Finset.mem_univ j)).1, hsum,
    fun j => (hxy j (Finset.mem_univ j)).2, hpos⟩

end Unimodular.Tucker

/-! ## FiniteCone -/

namespace Unimodular.FiniteCone

open scoped BigOperators

variable {ι V : Type*} [Fintype ι]

section Algebraic

variable [AddCommGroup V] [Module ℝ V]

/-- A real linear functional nonnegative on the generators is nonnegative on their cone. -/
theorem nonneg_on_hull (a : ι → V) (f : V →ₗ[ℝ] ℝ)
    (hf : ∀ i, 0 ≤ f (a i)) :
    ∀ x ∈ PointedCone.hull ℝ (Set.range a), 0 ≤ f x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hf i
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_nonneg hx hy
  | smul c x _ hx =>
    rw [← Nonneg.coe_smul, map_smul, smul_eq_mul]
    exact mul_nonneg c.2 hx

/-- Farkas separation for a finite real conical hull, derived from Tucker's theorem. -/
theorem exists_nonneg_lt_zero_of_not_mem_hull (a : ι → V) {v : V}
    (hv : v ∉ PointedCone.hull ℝ (Set.range a)) :
    ∃ f : V →ₗ[ℝ] ℝ, (∀ i, 0 ≤ f (a i)) ∧ f v < 0 := by
  classical
  let A : Option ι → V := fun j => j.elim (-v) a
  obtain ⟨c, f, hc, hsum, hf, hpos⟩ :=
    Unimodular.Tucker.exists_nonneg_sum_smul_eq_zero_and_coeff_add_dual_pos_at
      (K := ℝ) A none
  have hrel : (∑ i, c (some i) • a i) = c none • v := by
    have hs : -(c none • v) + (∑ i, c (some i) • a i) = 0 := by
      simpa [A, Fintype.sum_option] using hsum
    have he := congrArg (fun z : V => c none • v + z) hs
    simpa [add_assoc] using he
  have hc0 : c none = 0 := by
    by_contra hne
    have hcpos : 0 < c none := lt_of_le_of_ne (hc none) (Ne.symm hne)
    have hm : c none • v ∈ PointedCone.hull ℝ (Set.range a) := by
      rw [← hrel]
      apply Submodule.sum_mem
      intro i _
      exact PointedCone.smul_mem _ (hc (some i))
        (PointedCone.subset_hull ⟨i, rfl⟩)
    have hs := PointedCone.smul_mem (PointedCone.hull ℝ (Set.range a))
      (inv_nonneg.mpr hcpos.le) hm
    apply hv
    simpa [smul_smul, inv_mul_cancel₀ hcpos.ne'] using hs
  refine ⟨f, fun i => ?_, ?_⟩
  · simpa [A] using hf (some i)
  · simpa [A, hc0] using hpos

theorem mem_hull_iff_forall_nonneg (a : ι → V) (v : V) :
    v ∈ PointedCone.hull ℝ (Set.range a) ↔
      ∀ f : V →ₗ[ℝ] ℝ, (∀ i, 0 ≤ f (a i)) → 0 ≤ f v := by
  constructor
  · intro hv f hf
    exact nonneg_on_hull a f hf v hv
  · intro h
    by_contra hv
    obtain ⟨f, hf, hfv⟩ := exists_nonneg_lt_zero_of_not_mem_hull a hv
    exact (not_lt_of_ge (h f hf)) hfv

end Algebraic

section Closed

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Finite conical hulls in finite-dimensional real normed spaces are closed. -/
theorem isClosed_hull (a : ι → V) :
    IsClosed (PointedCone.hull ℝ (Set.range a) : Set V) := by
  have he :
      (PointedCone.hull ℝ (Set.range a) : Set V) =
        ⋂ f : {f : V →ₗ[ℝ] ℝ // ∀ i, 0 ≤ f (a i)}, f.1 ⁻¹' Set.Ici 0 := by
    ext v
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Ici]
    change v ∈ PointedCone.hull ℝ (Set.range a) ↔ _
    rw [mem_hull_iff_forall_nonneg]
    exact ⟨fun h f => h f.1 f.2, fun h f hf => h ⟨f, hf⟩⟩
  rw [he]
  exact isClosed_iInter fun f =>
    isClosed_Ici.preimage f.1.continuous_of_finiteDimensional

end Closed

end Unimodular.FiniteCone

/-! ## QuotientFaces -/

namespace Unimodular.QuotientFaces

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

abbrev faceSpan (F : PointedCone ℝ V) : Submodule ℝ V :=
  Submodule.span ℝ (F : Set V)

abbrev quotientMap (F : PointedCone ℝ V) :
    V →ₗ[ℝ] V ⧸ faceSpan F :=
  (faceSpan F).mkQ

/-- A face contains precisely the points of its cone lying in its linear span. -/
theorem inf_span_eq {F C : PointedCone ℝ V} (hF : F.IsFaceOf C) :
    C ⊓ PointedCone.ofSubmodule (faceSpan F) = F := by
  apply le_antisymm
  · intro x hx
    obtain ⟨p, hp, n, hn, hxn⟩ := PointedCone.mem_span.mp hx.2
    apply hF.mem_of_add_mem_left hx.1 (hF.le hn)
    simpa [hxn] using hp
  · intro x hx
    exact ⟨hF.le hx, Submodule.subset_span hx⟩

theorem quotient_eq_zero_iff {F : PointedCone ℝ V} {x : V} :
    quotientMap F x = 0 ↔ x ∈ faceSpan F := by
  change x ∈ LinearMap.ker ((faceSpan F).mkQ) ↔ x ∈ faceSpan F
  rw [Submodule.ker_mkQ]

theorem quotient_eq_iff_sub_mem {F : PointedCone ℝ V} {x y : V} :
    quotientMap F x = quotientMap F y ↔ x - y ∈ faceSpan F := by
  rw [← quotient_eq_zero_iff, map_sub, sub_eq_zero]

theorem quotient_eq_zero_of_mem {F : PointedCone ℝ V} {x : V} (hx : x ∈ F) :
    quotientMap F x = 0 :=
  quotient_eq_zero_iff.mpr (Submodule.subset_span hx)

/-- Membership in a face above F is unchanged by identifying two points of C modulo span F. -/
theorem mem_face_of_quotient_eq {F G C : PointedCone ℝ V}
    (hG : G.IsFaceOf C) (hFG : F ≤ G) {x y : V}
    (hx : x ∈ C) (hy : y ∈ G)
    (heq : quotientMap F x = quotientMap F y) : x ∈ G := by
  obtain ⟨p, hp, n, hn, hdiff⟩ :=
    PointedCone.mem_span.mp (quotient_eq_iff_sub_mem.mp heq)
  have he : x + n = y + p := by
    have he := congrArg (fun z : V => z + (y + n)) hdiff
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using he
  apply hG.mem_of_add_mem_left hx (hG.le (hFG hn))
  rw [he]
  exact G.add_mem hy (hFG hp)

/-- Quotienting by the span of a face makes its cone salient. -/
theorem quotient_salient {F C : PointedCone ℝ V} (hF : F.IsFaceOf C) :
    ((C.map (quotientMap F)) : ConvexCone ℝ (V ⧸ faceSpan F)).Salient := by
  intro y hy hy0 hny
  obtain ⟨x, hx, rfl⟩ := PointedCone.mem_map.mp hy
  obtain ⟨z, hz, hzx⟩ := PointedCone.mem_map.mp hny
  have hsum0 : quotientMap F (x + z) = 0 := by
    rw [map_add, hzx, add_neg_cancel]
  have hsumF : x + z ∈ F := by
    rw [← inf_span_eq hF]
    exact ⟨C.add_mem hx hz, quotient_eq_zero_iff.mp hsum0⟩
  have hxF : x ∈ F := hF.mem_of_add_mem_left hx hz hsumF
  exact hy0 (quotient_eq_zero_of_mem hxF)

/-- A face containing F projects to a face of the quotient cone. -/
theorem map_isFaceOf {F G C : PointedCone ℝ V}
    (hG : G.IsFaceOf C) (hFG : F ≤ G) :
    (G.map (quotientMap F)).IsFaceOf (C.map (quotientMap F)) := by
  apply PointedCone.IsFaceOf.of_mem_of_add_mem_left
  · rintro y ⟨x, hx, rfl⟩
    exact PointedCone.mem_map.mpr ⟨x, hG.le hx, rfl⟩
  · intro x y hx hy hxy
    obtain ⟨a, ha, rfl⟩ := PointedCone.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := PointedCone.mem_map.mp hy
    obtain ⟨g, hg, he⟩ := PointedCone.mem_map.mp hxy
    have hab : a + b ∈ G :=
      mem_face_of_quotient_eq hG hFG (C.add_mem ha hb) hg
        (by simpa only [map_add] using he.symm)
    exact PointedCone.mem_map.mpr ⟨a, hG.mem_of_add_mem_left ha hb hab, rfl⟩

abbrev pullback (F C : PointedCone ℝ V)
    (H : PointedCone ℝ (V ⧸ faceSpan F)) : PointedCone ℝ V :=
  C ⊓ H.comap (quotientMap F)

/-- Pull a face of the quotient cone back to a face of the original cone. -/
theorem pullback_isFaceOf {F C : PointedCone ℝ V}
    {H : PointedCone ℝ (V ⧸ faceSpan F)}
    (hH : H.IsFaceOf (C.map (quotientMap F))) :
    (pullback F C H).IsFaceOf C := by
  apply PointedCone.IsFaceOf.of_mem_of_add_mem_left inf_le_left
  intro x y hx hy hxy
  refine ⟨hx, ?_⟩
  apply hH.mem_of_add_mem_left
    (PointedCone.mem_map.mpr ⟨x, hx, rfl⟩)
    (PointedCone.mem_map.mpr ⟨y, hy, rfl⟩)
  have hq : quotientMap F (x + y) ∈ H := hxy.2
  simpa only [map_add] using hq

theorem le_pullback {F C : PointedCone ℝ V} (hFC : F ≤ C)
    (H : PointedCone ℝ (V ⧸ faceSpan F)) :
    F ≤ pullback F C H := by
  intro x hx
  refine ⟨hFC hx, ?_⟩
  change quotientMap F x ∈ H
  rw [quotient_eq_zero_of_mem hx]
  exact H.zero_mem

theorem map_pullback {F C : PointedCone ℝ V}
    {H : PointedCone ℝ (V ⧸ faceSpan F)}
    (hH : H ≤ C.map (quotientMap F)) :
    (pullback F C H).map (quotientMap F) = H := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hx.2
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := PointedCone.mem_map.mp (hH hy)
    exact PointedCone.mem_map.mpr ⟨x, ⟨hx, hy⟩, rfl⟩

theorem pullback_map {F G C : PointedCone ℝ V}
    (hG : G.IsFaceOf C) (hFG : F ≤ G) :
    pullback F C (G.map (quotientMap F)) = G := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, heq⟩ := PointedCone.mem_map.mp hx.2
    exact mem_face_of_quotient_eq hG hFG hx.1 hy heq.symm
  · intro x hx
    exact ⟨hG.le hx, PointedCone.mem_map.mpr ⟨x, hx, rfl⟩⟩

/-- Face correspondence for a cone modulo the span of one of its faces. -/
def faceOrderIso {F C : PointedCone ℝ V} (hF : F.IsFaceOf C) :
    {G : C.Face // F ≤ G.toPointedCone} ≃o
      (C.map (quotientMap F)).Face where
  toFun G := ⟨G.1.toPointedCone.map (quotientMap F),
    map_isFaceOf G.1.isFaceOf G.2⟩
  invFun H := ⟨⟨pullback F C H.toPointedCone,
    pullback_isFaceOf H.isFaceOf⟩, le_pullback hF.le H.toPointedCone⟩
  left_inv G := by
    apply Subtype.ext
    apply PointedCone.Face.ext
    intro x
    change x ∈ pullback F C (G.1.toPointedCone.map (quotientMap F)) ↔
      x ∈ G.1.toPointedCone
    rw [pullback_map G.1.isFaceOf G.2]
  right_inv H := by
    apply PointedCone.Face.ext
    intro x
    change x ∈ (pullback F C H.toPointedCone).map (quotientMap F) ↔
      x ∈ H.toPointedCone
    rw [map_pullback H.isFaceOf.le]
  map_rel_iff' := by
    intro G H
    constructor
    · intro h x hx
      have hqx : quotientMap F x ∈ H.1.toPointedCone.map (quotientMap F) :=
        h (PointedCone.mem_map.mpr ⟨x, hx, rfl⟩)
      obtain ⟨y, hy, he⟩ := PointedCone.mem_map.mp hqx
      exact mem_face_of_quotient_eq H.1.isFaceOf H.2 (G.1.isFaceOf.le hx) hy he.symm
    · intro h y hy
      obtain ⟨x, hx, rfl⟩ := PointedCone.mem_map.mp hy
      exact PointedCone.mem_map.mpr ⟨x, h hx, rfl⟩

end Unimodular.QuotientFaces

/-! ## GenericPaths -/

noncomputable section

namespace Unimodular.GenericPaths

open scoped Pointwise

/-- Adjoining one line to a subspace of codimension at least two still leaves
an actual proper real subspace. -/
theorem sup_line_ne_top {n : ℕ} (L : Submodule ℝ (Ambient n))
    (hcodim : Module.finrank ℝ L + 2 ≤ n) (x : Ambient n) :
    L ⊔ ℝ ∙ x ≠ ⊤ := by
  have hline : Module.finrank ℝ (ℝ ∙ x) ≤ 1 := by
    by_cases hx : x = 0
    · subst x
      rw [Submodule.span_zero_singleton, finrank_bot]
      omega
    · exact (finrank_span_singleton hx).le
  have hsup := Submodule.finrank_add_le_finrank_add_finrank L (ℝ ∙ x)
  intro he
  rw [he, finrank_top] at hsup
  have hamb : Module.finrank ℝ (Ambient n) = n := by simp [Ambient]
  rw [hamb] at hsup
  omega

/-- Finitely many proper real subspaces cannot cover any nonempty open set.
This follows from their actual topological interiors and closedness. -/
theorem dense_complement {n : ℕ} {ι : Type*} [Fintype ι]
    (L : ι → Submodule ℝ (Ambient n)) (hproper : ∀ i, L i ≠ ⊤) :
    Dense {x : Ambient n | ∀ i, x ∉ L i} := by
  let f : ι → Set (Ambient n) := fun i => (L i : Set (Ambient n))ᶜ
  have hopen : ∀ i, IsOpen (f i) := fun i => (L i).closed_of_finiteDimensional.isOpen_compl
  have hdense : ∀ i, Dense (f i) := by
    intro i
    rw [← interior_eq_empty_iff_dense_compl]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hproper i ((L i).eq_top_of_nonempty_interior' ⟨x, hx⟩)
  have h := (Set.finite_range f).dense_sInter
    (by rintro t ⟨i, rfl⟩; exact hopen i)
    (by rintro t ⟨i, rfl⟩; exact hdense i)
  convert h using 1
  ext x
  simp [f]

/-- A segment from x to z avoids L when x avoids L and z avoids L plus the line
through x. No general-position or path condition is assumed without proof. -/
theorem segment_avoids {n : ℕ} (L : Submodule ℝ (Ambient n))
    {x z : Ambient n} (hx : x ∉ L) (hz : z ∉ L ⊔ ℝ ∙ x) :
    segment ℝ x z ⊆ (L : Set (Ambient n))ᶜ := by
  rintro q ⟨a, b, ha, hb, hab, rfl⟩ hq
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    apply hx
    simpa [hb0, ha1] using hq
  · let P := L ⊔ ℝ ∙ x
    have hxP : x ∈ P := (show ℝ ∙ x ≤ P from le_sup_right)
      (Submodule.subset_span (by simp))
    have habP : a • x + b • z ∈ P := (show L ≤ P from le_sup_left) hq
    have hbz : b • z ∈ P := by
      have h := P.sub_mem habP (P.smul_mem a hxP)
      simpa only [add_sub_cancel_left] using h
    apply hz
    have h := P.smul_mem b⁻¹ hbz
    simpa only [smul_smul, inv_mul_cancel₀ hb0, one_smul] using h

/-- Two points outside finitely many codimension-two subspaces can be joined
by two straight segments lying entirely outside those subspaces. -/
theorem exists_polygonal_join {n : ℕ} {ι : Type*} [Fintype ι]
    (L : ι → Submodule ℝ (Ambient n))
    (hcodim : ∀ i, Module.finrank ℝ (L i) + 2 ≤ n)
    {x y : Ambient n} (hx : ∀ i, x ∉ L i) (hy : ∀ i, y ∉ L i) :
    ∃ z : Ambient n,
      segment ℝ x z ⊆ {q | ∀ i, q ∉ L i} ∧
      segment ℝ y z ⊆ {q | ∀ i, q ∉ L i} := by
  let P : ι × Bool → Submodule ℝ (Ambient n) :=
    fun a => L a.1 ⊔ ℝ ∙ (if a.2 then x else y)
  have hproper : ∀ a, P a ≠ ⊤ := fun a => sup_line_ne_top (L a.1) (hcodim a.1) _
  obtain ⟨z, hz⟩ := (dense_complement P hproper).nonempty
  refine ⟨z, ?_, ?_⟩
  · intro q hq i
    exact segment_avoids (L i) (hx i) (by simpa [P] using hz (i, true)) hq
  · intro q hq i
    exact segment_avoids (L i) (hy i) (by simpa [P] using hz (i, false)) hq

/-- The actual real complement of finitely many subspaces of codimension at
least two is path connected, in every dimension where the hypotheses make sense. -/
theorem complement_pathConnected {n : ℕ} {ι : Type*} [Fintype ι]
    (L : ι → Submodule ℝ (Ambient n))
    (hcodim : ∀ i, Module.finrank ℝ (L i) + 2 ≤ n) :
    IsPathConnected {x : Ambient n | ∀ i, x ∉ L i} := by
  have hproper : ∀ i, L i ≠ ⊤ := by
    intro i he
    apply sup_line_ne_top (L i) (hcodim i) 0
    simp [he]
  obtain ⟨x, hx⟩ := (dense_complement L hproper).nonempty
  refine ⟨x, hx, ?_⟩
  intro y hy
  obtain ⟨z, hxz, hyz⟩ := exists_polygonal_join L hcodim hx hy
  exact (JoinedIn.of_segment_subset hxz).trans (JoinedIn.of_segment_subset hyz).symm

end Unimodular.GenericPaths

end

/-! Transitive axiom audit; this file is not verified until it exits without errors. -/
#print axioms Unimodular.Tucker.exists_nonneg_sum_smul_eq_zero_and_coeff_add_dual_pos_at_of_finset
#print axioms Unimodular.Tucker.exists_nonneg_sum_smul_eq_zero_and_coeff_add_dual_pos_at
#print axioms Unimodular.FiniteCone.nonneg_on_hull
#print axioms Unimodular.FiniteCone.exists_nonneg_lt_zero_of_not_mem_hull
#print axioms Unimodular.FiniteCone.mem_hull_iff_forall_nonneg
#print axioms Unimodular.FiniteCone.isClosed_hull
#print axioms Unimodular.QuotientFaces.faceSpan
#print axioms Unimodular.QuotientFaces.quotientMap
#print axioms Unimodular.QuotientFaces.inf_span_eq
#print axioms Unimodular.QuotientFaces.quotient_eq_zero_iff
#print axioms Unimodular.QuotientFaces.quotient_eq_iff_sub_mem
#print axioms Unimodular.QuotientFaces.quotient_eq_zero_of_mem
#print axioms Unimodular.QuotientFaces.mem_face_of_quotient_eq
#print axioms Unimodular.QuotientFaces.quotient_salient
#print axioms Unimodular.QuotientFaces.map_isFaceOf
#print axioms Unimodular.QuotientFaces.pullback
#print axioms Unimodular.QuotientFaces.pullback_isFaceOf
#print axioms Unimodular.QuotientFaces.le_pullback
#print axioms Unimodular.QuotientFaces.map_pullback
#print axioms Unimodular.QuotientFaces.pullback_map
#print axioms Unimodular.QuotientFaces.faceOrderIso
#print axioms Unimodular.GenericPaths.sup_line_ne_top
#print axioms Unimodular.GenericPaths.dense_complement
#print axioms Unimodular.GenericPaths.segment_avoids
#print axioms Unimodular.GenericPaths.exists_polygonal_join
#print axioms Unimodular.GenericPaths.complement_pathConnected
