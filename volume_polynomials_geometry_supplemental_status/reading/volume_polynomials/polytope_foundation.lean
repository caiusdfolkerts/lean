/-
Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Released under the Apache License 2.0; see vendor/openai-math/LICENSE.
Unused surface-measure definitions are omitted; two support proofs use direct compact maximizers.
All adaptations and exact unchanged source lines are recorded in audit/polytope-foundation-lines.json.
Original sources and hashes: audit/openai-polytope-provenance.json.
Regenerate with scripts/bundle-polytope-foundation.py. No checked status is implied.
-/
module
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Abel

@[expose] public section

/- UPSTREAM SOURCE: vendor/openai-math/ProjectionVolume/Model.lean -/
noncomputable section

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

namespace Paper092

noncomputable def simplexConstant (d : ℕ) : ℝ :=
  (d + 1) * (d : ℝ) ^ d / d.factorial

abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

def normalHyperplane {n : ℕ} (u : Euclidean n) : Submodule ℝ (Euclidean n) :=
  (Submodule.span ℝ ({u} : Set (Euclidean n)))ᗮ

def projectionVolume {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n) : ENNReal :=
  (volume : Measure (normalHyperplane u))
    ((normalHyperplane u).orthogonalProjectionOnto '' K)

def brightness {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n) : ℝ :=
  ‖u‖ * (projectionVolume K u).toReal

def projectionBody {n : ℕ} (K : Set (Euclidean n)) : Set (Euclidean n) :=
  {y | ∀ u, ⟪u, y⟫ ≤ brightness K u}

def normalizedProjectionVolume {n : ℕ} (K : Set (Euclidean n)) : ℝ :=
  (volume (projectionBody K)).toReal / (volume K).toReal ^ (n - 1)

def standardSimplex (n : ℕ) : Set (Euclidean n) :=
  convexHull ℝ (insert 0 (Set.range fun i : Fin n => EuclideanSpace.single i (1 : ℝ)))

def firstBlock (x : Euclidean 20) : Euclidean 10 :=
  WithLp.toLp 2 (fun i : Fin 10 => x (Fin.castAdd 10 i))

def secondBlock (x : Euclidean 20) : Euclidean 10 :=
  WithLp.toLp 2 (fun i : Fin 10 => x (Fin.natAdd 10 i))

def productWitness : Set (Euclidean 20) :=
  {x | firstBlock x ∈ standardSimplex 10 ∧ secondBlock x ∈ standardSimplex 10}

end Paper092

end

end OAI
end

/- UPSTREAM SOURCE: vendor/openai-math/ProjectionVolume/Basic.lean -/
noncomputable section

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Paper092

theorem normalHyperplane_volume_is_canonical {n : ℕ} (u : Euclidean n) :
    (volume : Measure (normalHyperplane u)) =
      (stdOrthonormalBasis ℝ (normalHyperplane u)).toBasis.addHaar := rfl

theorem normalHyperplane_finrank {n : ℕ} (u : Euclidean n) (hu : u ≠ 0) :
    Module.finrank ℝ (normalHyperplane u) = n - 1 := by
  have h := (Submodule.span ℝ ({u} : Set (Euclidean n))).finrank_add_finrank_orthogonal
  simp only [finrank_span_singleton hu, finrank_euclideanSpace_fin] at h
  change Module.finrank ℝ ((Submodule.span ℝ ({u} : Set (Euclidean n)))ᗮ) = n - 1
  omega

end Paper092

end

end OAI
end

/- UPSTREAM SOURCE: vendor/openai-math/ProjectionVolume/PolytopeDefinitions.lean -/
noncomputable section

namespace OAI

universe uι

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

noncomputable section

namespace Paper092

structure HPolytope (d : ℕ) (ι : Type uι) [Fintype ι] where
  normal : ι → Euclidean d
  offset : ι → ℝ
  normal_unit : ∀ i, ‖normal i‖ = 1
  compact : IsCompact {x : Euclidean d | ∀ i, ⟪normal i, x⟫ ≤ offset i}
  strict_feasible : ∃ x : Euclidean d, ∀ i, ⟪normal i, x⟫ < offset i
  distinct : Function.Injective (fun i => (normal i, offset i))

namespace HPolytope

def body {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι) : Set (Euclidean d) :=
  {x | ∀ i, ⟪P.normal i, x⟫ ≤ P.offset i}

def face {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι) (i : ι) :
    Set (Euclidean d) :=
  {x | x ∈ P.body ∧ ⟪P.normal i, x⟫ = P.offset i}

end HPolytope
end Paper092

end

end OAI
end

/- UPSTREAM SOURCE: vendor/openai-math/ProjectionVolume/PolytopeOperations.lean -/
noncomputable section

namespace OAI

universe uι uκ

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

noncomputable section
namespace Paper092.HPolytope

variable {d : ℕ} {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]

def reindex (P : HPolytope d ι) (e : κ ≃ ι) : HPolytope d κ where
  normal i := P.normal (e i)
  offset i := P.offset (e i)
  normal_unit i := P.normal_unit (e i)
  compact := by
    convert P.compact using 1
    ext x
    constructor
    · intro h i
      obtain ⟨j, rfl⟩ := e.surjective i
      exact h j
    · intro h j
      exact h (e j)
  strict_feasible := by
    obtain ⟨x, hx⟩ := P.strict_feasible
    exact ⟨x, fun i => hx (e i)⟩
  distinct := fun i j h => e.injective (P.distinct h)

theorem reindex_body (P : HPolytope d ι) (e : κ ≃ ι) :
    (P.reindex e).body = P.body := by
  ext x
  constructor
  · intro h i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact h j
  · intro h j
    exact h (e j)

def translate (P : HPolytope d ι) (v : Euclidean d) : HPolytope d ι where
  normal := P.normal
  offset i := P.offset i + ⟪P.normal i, v⟫
  normal_unit := P.normal_unit
  compact := by
    have heq : {x : Euclidean d | ∀ i, ⟪P.normal i, x⟫ ≤ P.offset i + ⟪P.normal i, v⟫} =
        (fun x => v + x) '' P.body := by
      ext x
      constructor
      · intro hx
        refine ⟨x - v, ?_, by abel_nf⟩
        intro i
        have := hx i
        simpa only [inner_sub_right, sub_le_iff_le_add] using this
      · rintro ⟨x, hx, rfl⟩ i
        simpa only [inner_add_right, add_comm] using add_le_add_right (hx i) ⟪P.normal i, v⟫
    rw [heq]
    exact P.compact.image (continuous_const.add continuous_id)
  strict_feasible := by
    obtain ⟨x, hx⟩ := P.strict_feasible
    refine ⟨v + x, fun i => ?_⟩
    simpa only [inner_add_right, add_comm] using add_lt_add_right (hx i) ⟪P.normal i, v⟫
  distinct := by
    intro i j h
    apply P.distinct
    have hn := congrArg Prod.fst h
    have ho := congrArg Prod.snd h
    dsimp at hn ho
    exact Prod.ext hn (by simpa only [hn, add_left_inj] using ho)

theorem translate_body (P : HPolytope d ι) (v : Euclidean d) :
    (P.translate v).body = v +ᵥ P.body := by
  ext x
  constructor
  · intro hx
    refine ⟨x - v, ?_, by dsimp; abel_nf⟩
    intro i
    have h := hx i
    change ⟪P.normal i, x⟫ ≤ P.offset i + ⟪P.normal i, v⟫ at h
    simpa only [inner_sub_right, sub_le_iff_le_add] using h
  · rintro ⟨x, hx, rfl⟩ i
    change ⟪P.normal i, v + x⟫ ≤ P.offset i + ⟪P.normal i, v⟫
    simpa only [inner_add_right, add_comm] using add_le_add_right (hx i) ⟪P.normal i, v⟫

end Paper092.HPolytope

end

end OAI
end

/- UPSTREAM SOURCE: vendor/openai-math/ProjectionVolume/FiniteVertices.lean -/
noncomputable section

namespace OAI

universe uι

open Set Filter Topology
open scoped RealInnerProductSpace

namespace Paper092
namespace HPolytope

variable {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι)

theorem extreme_active_unique {x y : Euclidean d}
    (hx : x ∈ P.body.extremePoints ℝ)
    (ha : ∀ i, ⟪P.normal i, x⟫ = P.offset i → ⟪P.normal i, y⟫ = P.offset i) :
    y = x := by
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ i,
      ⟪P.normal i, x⟫ < P.offset i →
        ⟪P.normal i, x + t • (y - x)⟫ < P.offset i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : ⟪P.normal i, x⟫ < P.offset i
    · have h : ∀ᶠ t : ℝ in 𝓝 0,
          ⟪P.normal i, x + t • (y - x)⟫ < P.offset i :=
        (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hi)
      filter_upwards [h] with t ht
      exact fun _ => ht
    · exact Filter.Eventually.of_forall fun _ h => (hi h).elim
  obtain ⟨ε, hε, hsmall⟩ := Metric.eventually_nhds_iff.mp hnear
  have hpert (t : ℝ) (ht : dist t 0 < ε) : x + t • (y - x) ∈ P.body := by
    intro i
    rcases (hx.1 i).lt_or_eq with hi | hi
    · exact (hsmall ht i hi).le
    · simp [inner_add_right, inner_smul_right, inner_sub_right, hi, ha i hi]
  have hp : dist (ε / 2) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  have hm : dist (-(ε / 2)) 0 < ε := by simpa using hp
  have hxplus := hx.2 (hpert (ε / 2) hp)
    (show x - (ε / 2) • (y - x) ∈ P.body by simpa only [neg_smul, ← sub_eq_add_neg] using hpert (-(ε / 2)) hm)
    (mem_openSegment_add_sub (𝕜 := ℝ) x ((ε / 2) • (y - x)))
  have hz : (ε / 2) • (y - x) = 0 := add_left_cancel (hxplus.trans (add_zero x).symm)
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (ne_of_gt (half_pos hε)))

theorem finite_extremePoints : (P.body.extremePoints ℝ).Finite := by
  classical
  let active (x : Euclidean d) : Finset ι :=
    Finset.univ.filter (fun i => ⟪P.normal i, x⟫ = P.offset i)
  have hi : Set.InjOn active (P.body.extremePoints ℝ) := by
    intro x hx y _ hxy
    apply (P.extreme_active_unique hx ?_).symm
    intro i hix
    have hm : i ∈ active x := by simp [active, hix]
    rw [hxy] at hm
    exact (Finset.mem_filter.mp hm).2
  exact (Set.toFinite (Set.univ : Set (Finset ι))).of_injOn
    (fun _ _ => Set.mem_univ _) hi

theorem eq_convexHull_extremePoints : P.body = convexHull ℝ (P.body.extremePoints ℝ) := by
  have hc : Convex ℝ P.body := by
    change Convex ℝ {x : Euclidean d | ∀ i, ⟪P.normal i, x⟫ ≤ P.offset i}
    simp only [Set.ofPred_forall]
    exact convex_iInter fun i => (convex_Iic (P.offset i)).linear_preimage
      (innerSL ℝ (P.normal i)).toLinearMap
  have h := closure_convexHull_extremePoints P.compact hc
  change closure (convexHull ℝ (P.body.extremePoints ℝ)) = P.body at h
  rw [P.finite_extremePoints.isClosed_convexHull ℝ |>.closure_eq] at h
  exact h.symm

end HPolytope

theorem halfspaces_are_finite_convex_hull {d : ℕ} {ι : Type uι} [Fintype ι]
    (P : HPolytope d ι) :
    ∃ S : Finset (Euclidean d), P.body = convexHull ℝ (S : Set (Euclidean d)) := by
  classical
  exact ⟨P.finite_extremePoints.toFinset, by simpa using P.eq_convexHull_extremePoints⟩
end Paper092

end OAI
end

/- UPSTREAM SOURCE: vendor/openai-math/ProjectionVolume/SupportGeometry.lean -/
noncomputable section

namespace OAI

universe uE uF uι uH

open Set
open scoped Pointwise

namespace Paper092.SupportGeometry

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def support (K : Set E) (f : E →L[ℝ] ℝ) : ℝ := sSup (f '' K)

theorem le_support {K : Set E} (hK : IsCompact K) (f : E →L[ℝ] ℝ)
    {x : E} (hx : x ∈ K) : f x ≤ support K f :=
  le_csSup (hK.image f.continuous).bddAbove (mem_image_of_mem f hx)

theorem support_le {K : Set E} (hK : K.Nonempty) (f : E →L[ℝ] ℝ)
    {a : ℝ} (ha : ∀ x ∈ K, f x ≤ a) : support K f ≤ a :=
  csSup_le (hK.image f) (by rintro _ ⟨x, hx, rfl⟩; exact ha x hx)

theorem exists_support {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (f : E →L[ℝ] ℝ) : ∃ x ∈ K, f x = support K f :=
  (hK.image f.continuous).sSup_mem (hne.image f)

theorem support_add {A B : Set E} (hA : IsCompact A) (hneA : A.Nonempty)
    (hB : IsCompact B) (hneB : B.Nonempty) (f : E →L[ℝ] ℝ) :
    support (A + B) f = support A f + support B f := by
  first
  | obtain ⟨a, ha, hea⟩ := exists_support hA hneA f
    obtain ⟨b, hb, heb⟩ := exists_support hB hneB f
    apply le_antisymm
    · apply support_le (hneA.add hneB) f
      rintro x ⟨u, hu, v, hv, rfl⟩
      simpa only [map_add] using add_le_add (le_support hA f hu) (le_support hB f hv)
    · have h := le_support (hA.add hB) f (show a + b ∈ A + B from ⟨a, ha, b, hb, rfl⟩)
      simpa only [map_add, hea, heb] using h

theorem support_smul (K : Set E) (f : E →L[ℝ] ℝ) {c : ℝ} (hc : 0 ≤ c) :
    support (c • K) f = c * support K f := by
  unfold support
  rw [image_smul_comm f c K (fun x => f.map_smul c x), Real.sSup_smul_of_nonneg hc]
  rfl

theorem support_prod {A : Set E} {B : Set F} (hA : IsCompact A) (hneA : A.Nonempty)
    (hB : IsCompact B) (hneB : B.Nonempty) (f : E →L[ℝ] ℝ) (g : F →L[ℝ] ℝ) :
    support (A ×ˢ B) (f.coprod g) = support A f + support B g := by
  first
  | obtain ⟨a, ha, hea⟩ := exists_support hA hneA f
    obtain ⟨b, hb, heb⟩ := exists_support hB hneB g
    apply le_antisymm
    · apply support_le (hneA.prod hneB) (f.coprod g)
      rintro ⟨u, v⟩ ⟨hu, hv⟩
      change f u + g v ≤ support A f + support B g
      exact add_le_add (le_support hA f hu) (le_support hB g hv)
    · have h := le_support (hA.prod hB) (f.coprod g)
        (show (a, b) ∈ A ×ˢ B from ⟨ha, hb⟩)
      change f a + g b ≤ support (A ×ˢ B) (f.coprod g) at h
      simpa only [hea, heb] using h

theorem support_sum {ι : Type uι} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hne : ∀ i ∈ s, (K i).Nonempty)
    (f : E →L[ℝ] ℝ) : support (∑ i ∈ s, K i) f = ∑ i ∈ s, support (K i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [support]
  | @insert i s hi ih =>
    have hKs : ∀ j ∈ s, IsCompact (K j) := fun j hj => hK j (Finset.mem_insert_of_mem hj)
    have hnes : ∀ j ∈ s, (K j).Nonempty := fun j hj => hne j (Finset.mem_insert_of_mem hj)
    have hcompact : IsCompact (∑ j ∈ s, K j) :=
      Finset.sum_induction K IsCompact (fun _ _ ha hb => ha.add hb)
        isCompact_singleton hKs
    have hnonempty : (∑ j ∈ s, K j).Nonempty :=
      Finset.sum_induction K Set.Nonempty (fun _ _ ha hb => ha.add hb)
        (singleton_nonempty 0) hnes
    rw [Finset.sum_insert hi,
      support_add (hK i (Finset.mem_insert_self i s)) (hne i (Finset.mem_insert_self i s))
        hcompact hnonempty, ih hKs hnes, Finset.sum_insert hi]

theorem mem_iff_le_support {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) {x : E} :
    x ∈ K ↔ ∀ f : E →L[ℝ] ℝ, f x ≤ support K f := by
  refine ⟨fun hx f => le_support hK f hx, fun h => ?_⟩
  by_contra hx
  obtain ⟨f, u, hu, hux⟩ := geometric_hahn_banach_closed_point hconv hK.isClosed hx
  exact (hux.trans_le ((h f).trans (support_le hne f fun y hy => (hu y hy).le))).false

theorem eq_of_support_eq {A B : Set E} (hA : IsCompact A) (hneA : A.Nonempty)
    (hconvA : Convex ℝ A) (hB : IsCompact B) (hneB : B.Nonempty)
    (hconvB : Convex ℝ B) (h : ∀ f : E →L[ℝ] ℝ, support A f = support B f) : A = B := by
  ext x
  simp only [mem_iff_le_support hA hneA hconvA, mem_iff_le_support hB hneB hconvB, h]

theorem isCompact_segment (x y : E) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

theorem support_segment (x y : E) (f : E →L[ℝ] ℝ) :
    support (segment ℝ x y) f = max (f x) (f y) := by
  unfold support
  rw [show f '' segment ℝ x y = segment ℝ (f x) (f y) from
    image_segment ℝ f.toLinearMap.toAffineMap x y]
  rw [segment_eq_Icc', csSup_Icc (min_le_max)]

theorem support_centered_segment (v : E) (f : E →L[ℝ] ℝ) :
    support (segment ℝ (-(1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v)) f = |f v| / 2 := by
  simp only [support_segment, map_smul, smul_eq_mul, neg_mul]
  rw [max_comm, ← abs_eq_max_neg, abs_mul]
  norm_num
  ring

theorem support_sum_centered_segments {ι : Type uι} (s : Finset ι) (v : ι → E)
    (f : E →L[ℝ] ℝ) :
    support (∑ i ∈ s, segment ℝ (-(1 / 2 : ℝ) • v i) ((1 / 2 : ℝ) • v i)) f =
      (1 / 2 : ℝ) * ∑ i ∈ s, |f (v i)| := by
  rw [support_sum s _ (fun _ _ => isCompact_segment _ _)
    (fun _ _ => ⟨_, left_mem_segment ℝ _ _⟩)]
  simp_rw [support_centered_segment, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  ring

theorem eq_sum_centered_segments_iff {ι : Type uι} {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hconv : Convex ℝ K) (s : Finset ι) (v : ι → E) :
    K = ∑ i ∈ s, segment ℝ (-(1 / 2 : ℝ) • v i) ((1 / 2 : ℝ) • v i) ↔
      ∀ f : E →L[ℝ] ℝ, support K f = (1 / 2 : ℝ) * ∑ i ∈ s, |f (v i)| := by
  constructor
  · intro h f
    rw [h, support_sum_centered_segments]
  · intro h
    apply eq_of_support_eq hK hne hconv
    · exact Finset.sum_induction _ IsCompact (fun _ _ ha hb => ha.add hb)
        isCompact_singleton (fun _ _ => isCompact_segment _ _)
    · exact Finset.sum_induction _ Set.Nonempty (fun _ _ ha hb => ha.add hb)
        (singleton_nonempty 0) (fun _ _ => ⟨_, left_mem_segment ℝ _ _⟩)
    · exact Finset.sum_induction _ (Convex ℝ) (fun _ _ ha hb => ha.add hb)
        (convex_singleton 0) (fun _ _ => convex_segment _ _)
    · intro f
      rw [h f, support_sum_centered_segments]

section InnerProduct

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem mem_iff_inner_le_support {K : Set H} (hK : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) {x : H} :
    x ∈ K ↔ ∀ u : H, inner ℝ u x ≤ support K (innerSL ℝ u) := by
  rw [mem_iff_le_support hK hne hconv]
  constructor
  · intro h u
    exact h (innerSL ℝ u)
  · intro h f
    obtain ⟨u, rfl⟩ := (InnerProductSpace.toDual ℝ H).surjective f
    exact h u

theorem halfSpaces_eq_of_eq_support {K : Set H} (hK : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) (p : H → ℝ) (hp : ∀ u, p u = support K (innerSL ℝ u)) :
    {x | ∀ u : H, inner ℝ u x ≤ p u} = K := by
  ext x
  simp_rw [mem_ofPred_eq, hp]
  exact (mem_iff_inner_le_support hK hne hconv).symm

theorem eq_of_inner_support_eq {A B : Set H} (hA : IsCompact A) (hneA : A.Nonempty)
    (hconvA : Convex ℝ A) (hB : IsCompact B) (hneB : B.Nonempty)
    (hconvB : Convex ℝ B)
    (h : ∀ u : H, support A (innerSL ℝ u) = support B (innerSL ℝ u)) : A = B := by
  ext x
  simp only [mem_iff_inner_le_support hA hneA hconvA,
    mem_iff_inner_le_support hB hneB hconvB, h]

end InnerProduct

end Paper092.SupportGeometry

end OAI
end

/- UPSTREAM SOURCE: vendor/openai-math/ProjectionVolume/PolarRepresentation.lean -/
noncomputable section

namespace OAI

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

noncomputable section
namespace Paper092

def halfspacePolar {d : ℕ} (K : Set (Euclidean d)) : Set (Euclidean d) :=
  {u | ∀ x ∈ K, ⟪u, x⟫ ≤ 1}

theorem halfspacePolar_convexHull {d : ℕ} (S : Set (Euclidean d)) :
    halfspacePolar (convexHull ℝ S) = halfspacePolar S := by
  ext u
  constructor
  · intro h x hx
    exact h x (subset_convexHull ℝ S hx)
  · intro h x hx
    have hc : Convex ℝ {y : Euclidean d | ⟪u, y⟫ ≤ 1} :=
      (convex_Iic (1 : ℝ)).linear_preimage (innerSL ℝ u).toLinearMap
    exact convexHull_min h hc hx

theorem halfspacePolar_isClosed {d : ℕ} (K : Set (Euclidean d)) :
    IsClosed (halfspacePolar K) := by
  unfold halfspacePolar
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_le (by fun_prop) continuous_const

theorem halfspacePolar_bipolar {d : ℕ} {K : Set (Euclidean d)}
    (hK : IsClosed K) (hc : Convex ℝ K) (h0 : (0 : Euclidean d) ∈ K) :
    halfspacePolar (halfspacePolar K) = K := by
  ext x
  constructor
  · intro hx
    by_contra hnot
    obtain ⟨f, r, hr, hxgt⟩ := geometric_hahn_banach_closed_point hc hK hnot
    have hr0 : 0 < r := by simpa using hr 0 h0
    obtain ⟨u, hu⟩ := (InnerProductSpace.toDual ℝ (Euclidean d)).surjective f
    have hf (z : Euclidean d) : ⟪u, z⟫ = f z := by
      exact congrArg (fun g : StrongDual ℝ (Euclidean d) => g z) hu
    have hp : r⁻¹ • u ∈ halfspacePolar K := by
      intro z hz
      rw [real_inner_smul_left, hf]
      have := mul_le_mul_of_nonneg_left (hr z hz).le (inv_nonneg.mpr hr0.le)
      simpa [hr0.ne'] using this
    have h := hx (r⁻¹ • u) hp
    rw [real_inner_smul_right, real_inner_comm u x, hf] at h
    have hh := mul_le_mul_of_nonneg_left h hr0.le
    have hle : f x ≤ r := by simpa [← mul_assoc, hr0.ne'] using hh
    exact (not_le_of_gt hxgt) hle
  · intro hx u hu
    simpa only [real_inner_comm] using hu x hx

theorem halfspacePolar_isCompact {d : ℕ} {K : Set (Euclidean d)}
    (h0 : (0 : Euclidean d) ∈ interior K) : IsCompact (halfspacePolar K) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨halfspacePolar_isClosed K, isBounded_iff_forall_norm_le.mpr ⟨2 / r, ?_⟩⟩
  intro y hy
  by_cases hz : y = 0
  · subst y
    simp only [norm_zero]
    positivity
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hz
  have hx : ((r / 2) / ‖y‖) • y ∈ K := by
    apply hball
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (div_pos (half_pos hr) hn), div_mul_cancel₀ _ hn.ne']
    linarith
  have h := hy _ hx
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq] at h
  have heq : (r / 2 / ‖y‖) * ‖y‖ ^ 2 = (r / 2) * ‖y‖ := by field_simp
  rw [heq] at h
  apply (le_div_iff₀ hr).mpr
  nlinarith

theorem finite_polar_has_halfspaces {d : ℕ} (S : Finset (Euclidean d))
    (hc : IsCompact (halfspacePolar (S : Set (Euclidean d)))) :
    ∃ (m : ℕ) (P : HPolytope d (Fin m)), P.body = halfspacePolar (S : Set (Euclidean d)) := by
  classical
  let T := S.filter (fun x => x ≠ 0)
  let J := {x // x ∈ T}
  have hn (i : J) : 0 < ‖(i : Euclidean d)‖ :=
    norm_pos_iff.mpr (Finset.mem_filter.mp i.property).2
  have heq : {x : Euclidean d | ∀ i : J,
      ⟪‖(i : Euclidean d)‖⁻¹ • (i : Euclidean d), x⟫ ≤ ‖(i : Euclidean d)‖⁻¹} =
      halfspacePolar (S : Set (Euclidean d)) := by
    ext x
    constructor
    · intro hx y hy
      by_cases hy0 : y = 0
      · simp [hy0]
      let i : J := ⟨y, Finset.mem_filter.mpr ⟨hy, hy0⟩⟩
      have h := mul_le_mul_of_nonneg_left (hx i) (hn i).le
      rw [real_inner_smul_left] at h
      dsimp only [i] at h
      simpa only [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy0), one_mul, real_inner_comm] using h
    · intro hx i
      have h := mul_le_mul_of_nonneg_left (hx i (Finset.mem_filter.mp i.property).1)
        (inv_nonneg.mpr (hn i).le)
      rw [real_inner_smul_left]
      simpa only [mul_one, real_inner_comm] using h
  let P : HPolytope d J := {
    normal := fun i => ‖(i : Euclidean d)‖⁻¹ • (i : Euclidean d)
    offset := fun i => ‖(i : Euclidean d)‖⁻¹
    normal_unit := fun i => by simp [norm_smul, (hn i).ne']
    compact := by rw [heq]; exact hc
    strict_feasible := ⟨0, fun i => by simpa using inv_pos.mpr (hn i)⟩
    distinct := by
      intro i j h
      have hnorm : ‖(i : Euclidean d)‖ = ‖(j : Euclidean d)‖ :=
        inv_inj.mp (congrArg Prod.snd h)
      have hv := congrArg Prod.fst h
      apply Subtype.ext
      have hs := congrArg (fun v : Euclidean d => ‖(i : Euclidean d)‖ • v) hv
      simpa only [smul_smul, ← hnorm, mul_inv_cancel₀ (hn i).ne', one_smul] using hs }
  refine ⟨Fintype.card J, P.reindex (Fintype.equivFin J).symm, ?_⟩
  rw [HPolytope.reindex_body]
  exact heq

theorem finite_convex_hull_has_halfspaces_centered {d : ℕ} (S : Finset (Euclidean d))
    (h0 : (0 : Euclidean d) ∈ interior (convexHull ℝ (S : Set (Euclidean d)))) :
    ∃ (m : ℕ) (P : HPolytope d (Fin m)), P.body = convexHull ℝ (S : Set (Euclidean d)) := by
  have hc : IsCompact (halfspacePolar (S : Set (Euclidean d))) := by
    rw [← halfspacePolar_convexHull]
    exact halfspacePolar_isCompact h0
  obtain ⟨m, P, hP⟩ := finite_polar_has_halfspaces S hc
  obtain ⟨T, hT⟩ := halfspaces_are_finite_convex_hull P
  have heq : halfspacePolar (T : Set (Euclidean d)) = convexHull ℝ (S : Set (Euclidean d)) := by
    calc
      halfspacePolar (T : Set (Euclidean d)) =
          halfspacePolar (convexHull ℝ (T : Set (Euclidean d))) := (halfspacePolar_convexHull _).symm
      _ = halfspacePolar P.body := by rw [hT]
      _ = halfspacePolar (halfspacePolar (S : Set (Euclidean d))) := by rw [hP]
      _ = halfspacePolar (halfspacePolar (convexHull ℝ (S : Set (Euclidean d)))) := by
        rw [halfspacePolar_convexHull]
      _ = convexHull ℝ (S : Set (Euclidean d)) := halfspacePolar_bipolar
        (S.finite_toSet.isClosed_convexHull ℝ) (convex_convexHull ℝ _) (interior_subset h0)
  obtain ⟨n, Q, hQ⟩ := finite_polar_has_halfspaces T
    (by rw [heq]; exact S.finite_toSet.isCompact_convexHull ℝ)
  exact ⟨n, Q, hQ.trans heq⟩

theorem finite_convex_hull_has_halfspaces {d : ℕ} (S : Finset (Euclidean d))
    (hint : (interior (convexHull ℝ (S : Set (Euclidean d)))).Nonempty) :
    ∃ (m : ℕ) (P : HPolytope d (Fin m)), P.body = convexHull ℝ (S : Set (Euclidean d)) := by
  classical
  obtain ⟨v, hv⟩ := hint
  let S₀ : Finset (Euclidean d) := S.image (fun x => x - v)
  have hS₀ : convexHull ℝ (S₀ : Set (Euclidean d)) =
      (-v) +ᵥ convexHull ℝ (S : Set (Euclidean d)) := by
    dsimp [S₀]
    rw [Finset.coe_image]
    have himage : (fun x : Euclidean d => x - v) '' (S : Set (Euclidean d)) =
        (-v) +ᵥ (S : Set (Euclidean d)) := by
      change (fun x : Euclidean d => x - v) '' (S : Set (Euclidean d)) =
        (fun x => -v + x) '' (S : Set (Euclidean d))
      congr 1
      funext x
      abel
    rw [himage, convexHull_vadd]
  have h0 : (0 : Euclidean d) ∈ interior (convexHull ℝ (S₀ : Set (Euclidean d))) := by
    rw [hS₀, interior_vadd]
    exact ⟨v, hv, by simp⟩
  obtain ⟨m, P, hP⟩ := finite_convex_hull_has_halfspaces_centered S₀ h0
  refine ⟨m, P.translate v, ?_⟩
  rw [HPolytope.translate_body, hP, hS₀]
  simp

end Paper092

end

end OAI
end
