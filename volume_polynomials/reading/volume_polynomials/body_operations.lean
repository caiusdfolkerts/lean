module
public import VolumePolynomials.Definitions
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

@[expose] public section

/-! Actual translations and linear changes of coordinates, including singular maps. -/

noncomputable section
open Set MeasureTheory Finset
open scoped Pointwise BigOperators

namespace VolumePolynomials

section General
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def bodySetHom : ConvexBody E →+ Set E where
  toFun := SetLike.coe
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem body_zero_smul (K : ConvexBody E) : (0 : ℝ) • K = 0 := by
  apply ConvexBody.ext
  exact Set.zero_smul_set K.nonempty

theorem body_add_smul (K : ConvexBody E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) • K = a • K + b • K := by
  apply ConvexBody.ext
  exact K.convex.add_smul ha hb

@[simp] theorem coe_sum_body {ι : Type*} (s : Finset ι) (K : ι → ConvexBody E) :
    ((∑ i ∈ s, K i : ConvexBody E) : Set E) = ∑ i ∈ s, (K i : Set E) :=
  map_sum (bodySetHom (E := E)) K s

theorem mem_sum_body {ι : Type*} [Fintype ι] (K : ι → ConvexBody E) (x : E) :
    x ∈ ∑ i, K i ↔ ∃ p : ι → E, (∀ i, p i ∈ K i) ∧ ∑ i, p i = x := by
  change x ∈ (((∑ i, K i : ConvexBody E) : Set E)) ↔ _
  rw [coe_sum_body]
  change x ∈ ∑ i, (K i : Set E) ↔
    ∃ p : ι → E, (∀ i, p i ∈ (K i : Set E)) ∧ ∑ i, p i = x
  simpa only [exists_prop] using Set.mem_fintype_sum (fun i => (K i : Set E)) x

theorem sum_body_mono {ι : Type*} [Fintype ι] {K L : ι → ConvexBody E}
    (h : ∀ i, K i ≤ L i) : (∑ i, K i) ≤ ∑ i, L i := by
  change (((∑ i, K i : ConvexBody E) : Set E)) ⊆ (((∑ i, L i : ConvexBody E) : Set E))
  simp only [coe_sum_body]
  exact Set.finsetSum_subset_finsetSum _ _ _ (fun i _ => h i)

theorem body_le_sum_of_zero_mem {ι : Type*} [Fintype ι] (K : ι → ConvexBody E)
    (h0 : ∀ i, (0 : E) ∈ K i) (i : ι) : K i ≤ ∑ j, K j := by
  classical
  intro x hx
  apply (mem_sum_body K x).mpr
  refine ⟨fun j => if j = i then x else 0, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · simpa [hji] using hx
    · simpa [hji] using h0 j
  · simp

def pointBody (x : E) : ConvexBody E :=
  ⟨{x}, convex_singleton x, isCompact_singleton, singleton_nonempty x⟩

@[simp] theorem coe_pointBody (x : E) : (pointBody x : Set E) = {x} := rfl

def pointBodyHom : E →+ ConvexBody E where
  toFun := pointBody
  map_zero' := rfl
  map_add' x y := ConvexBody.ext (by simp)

@[simp] theorem pointBody_smul (r : ℝ) (x : E) : pointBody (r • x) = r • pointBody x := by
  apply ConvexBody.ext
  simp

def translateBody (v : E) (K : ConvexBody E) : ConvexBody E := pointBody v + K

@[simp] theorem coe_translateBody (v : E) (K : ConvexBody E) :
    (translateBody v K : Set E) = v +ᵥ (K : Set E) := by
  simp [translateBody, Set.singleton_add, ← Set.image_vadd, vadd_eq_add]

theorem mem_translateBody (v : E) (K : ConvexBody E) (x : E) :
    x ∈ translateBody v K ↔ x - v ∈ K := by
  change x ∈ (translateBody v K : Set E) ↔ x - v ∈ (K : Set E)
  rw [coe_translateBody, Set.mem_vadd_set_iff_neg_vadd_mem]
  simp only [vadd_eq_add, sub_eq_add_neg, add_comm]

def mapBody (f : E →L[ℝ] F) (K : ConvexBody E) : ConvexBody F where
  carrier := f '' (K : Set E)
  convex' := K.convex.linear_image f.toLinearMap
  isCompact' := K.isCompact.image f.continuous
  nonempty' := K.nonempty.image f

@[simp] theorem coe_mapBody (f : E →L[ℝ] F) (K : ConvexBody E) :
    (mapBody f K : Set F) = f '' (K : Set E) := rfl

theorem mapBody_add (f : E →L[ℝ] F) (K L : ConvexBody E) :
    mapBody f (K + L) = mapBody f K + mapBody f L := by
  apply ConvexBody.ext
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases Set.mem_add.mp hw with ⟨x, hx, y, hy, rfl⟩
    exact Set.mem_add.mpr
      ⟨f x, ⟨x, hx, rfl⟩, f y, ⟨y, hy, rfl⟩, (map_add f x y).symm⟩
  · intro hz
    rcases Set.mem_add.mp hz with ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x + y, Set.mem_add.mpr ⟨x, hx, y, hy, rfl⟩, map_add f x y⟩

def mapBodyHom (f : E →L[ℝ] F) : ConvexBody E →+ ConvexBody F where
  toFun := mapBody f
  map_zero' := ConvexBody.ext (by
    change f '' {(0 : E)} = {(0 : F)}
    simp)
  map_add' := mapBody_add f

theorem mapBody_smul (f : E →L[ℝ] F) (r : ℝ) (K : ConvexBody E) :
    mapBody f (r • K) = r • mapBody f K := by
  apply ConvexBody.ext
  simp only [coe_mapBody, ConvexBody.coe_smul]
  exact Set.image_smul_comm f r (K : Set E) (fun x => f.map_smul r x)

@[simp] theorem mapBody_pointBody (f : E →L[ℝ] F) (v : E) :
    mapBody f (pointBody v) = pointBody (f v) := by
  apply ConvexBody.ext
  simp only [coe_mapBody, coe_pointBody, Set.image_singleton]

theorem mapBody_translate (f : E →L[ℝ] F) (v : E) (K : ConvexBody E) :
    mapBody f (translateBody v K) = translateBody (f v) (mapBody f K) := by
  simp only [translateBody, mapBody_add, mapBody_pointBody]

theorem translateBody_translate (v w : E) (K : ConvexBody E) :
    translateBody v (translateBody w K) = translateBody (v + w) K := by
  change pointBody v + (pointBody w + K) = pointBody (v + w) + K
  have h : pointBody (v + w) = pointBody v + pointBody w :=
    (pointBodyHom (E := E)).map_add v w
  rw [h, add_assoc]

theorem translateBody_add (v w : E) (K L : ConvexBody E) :
    translateBody v K + translateBody w L = translateBody (v + w) (K + L) := by
  change (pointBody v + K) + (pointBody w + L) = pointBody (v + w) + (K + L)
  have h : pointBody (v + w) = pointBody v + pointBody w :=
    (pointBodyHom (E := E)).map_add v w
  rw [h]
  ac_rfl

@[simp] theorem translateBody_zero (K : ConvexBody E) : translateBody 0 K = K :=
  zero_add K

theorem zero_mem_translateBody_neg {K : ConvexBody E} {x : E} (hx : x ∈ K) :
    (0 : E) ∈ translateBody (-x) K := by
  simpa only [mem_translateBody, zero_sub, neg_neg] using hx

end General

theorem mapBody_comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E →L[ℝ] F) (g : F →L[ℝ] G) (K : ConvexBody E) :
    mapBody g (mapBody f K) = mapBody (g.comp f) K := by
  apply ConvexBody.ext
  exact Set.image_image g f (K : Set E)

@[simp] theorem weightedSum_single {n d : ℕ} (K : Fin n → Body d)
    (i : Fin n) (a : ℝ) : weightedSum K (Pi.single i a) = a • K i := by
  classical
  simp [weightedSum, Pi.single_apply]

theorem weightedSum_add {n d : ℕ} (K : Fin n → Body d)
    (s t : Fin n → ℝ) (hs : ∀ i, 0 ≤ s i) (ht : ∀ i, 0 ≤ t i) :
    weightedSum K (s + t) = weightedSum K s + weightedSum K t := by
  simp only [weightedSum, Pi.add_apply,
    body_add_smul _ (hs _) (ht _), Finset.sum_add_distrib]

theorem weightedSum_translate {n d : ℕ} (K : Fin n → Body d)
    (v : Fin n → Space d) (t : Fin n → ℝ) :
    weightedSum (fun i => translateBody (v i) (K i)) t =
      translateBody (∑ i, t i • v i) (weightedSum K t) := by
  simp only [weightedSum, translateBody, smul_add, ← pointBody_smul, Finset.sum_add_distrib]
  congr 1
  exact (map_sum (pointBodyHom (E := Space d)) _ _).symm

@[simp] theorem bodyVolume_translate {d : ℕ} (v : Space d) (K : Body d) :
    bodyVolume (translateBody v K) = bodyVolume K := by
  simp [bodyVolume, Measure.real, measure_vadd]

theorem volumeFunction_translate {n d : ℕ} (K : Fin n → Body d)
    (v : Fin n → Space d) (t : Fin n → ℝ) :
    volumeFunction (fun i => translateBody (v i) (K i)) t = volumeFunction K t := by
  simp only [volumeFunction, weightedSum_translate, bodyVolume_translate]

theorem Realizes.translate {n d : ℕ} {K : Fin n → Body d} {c : Coefficients n d}
    (h : Realizes K c) (v : Fin n → Space d) :
    Realizes (fun i => translateBody (v i) (K i)) c := by
  intro t ht
  rw [h t ht]
  simp only [volumeFunction, weightedSum_translate, bodyVolume_translate]

theorem weightedSum_map {n d : ℕ} (f : Space d →L[ℝ] Space d)
    (K : Fin n → Body d) (t : Fin n → ℝ) :
    weightedSum (fun i => mapBody f (K i)) t = mapBody f (weightedSum K t) := by
  simp only [weightedSum]
  rw [show mapBody f (∑ i, t i • K i) = ∑ i, mapBody f (t i • K i) from
    map_sum (mapBodyHom f) _ _]
  simp only [mapBody_smul]

theorem bodyVolume_map {d : ℕ} (f : Space d →L[ℝ] Space d) (K : Body d) :
    bodyVolume (mapBody f K) = |LinearMap.det f.toLinearMap| * bodyVolume K := by
  simp only [bodyVolume, Measure.real, coe_mapBody]
  rw [Measure.addHaar_image_continuousLinearMap]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]

theorem volumeFunction_map {n d : ℕ} (f : Space d →L[ℝ] Space d)
    (K : Fin n → Body d) (t : Fin n → ℝ) :
    volumeFunction (fun i => mapBody f (K i)) t =
      |LinearMap.det f.toLinearMap| * volumeFunction K t := by
  simp only [volumeFunction, weightedSum_map, bodyVolume_map]

theorem Realizes.map {n d : ℕ} {K : Fin n → Body d} {c : Coefficients n d}
    (h : Realizes K c) (f : Space d →L[ℝ] Space d) :
    Realizes (fun i => mapBody f (K i)) (|LinearMap.det f.toLinearMap| • c) := by
  intro t ht
  simp only [evaluate, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  change |LinearMap.det f.toLinearMap| * evaluate c t = _
  rw [h t ht]
  simp only [volumeFunction, weightedSum_map, bodyVolume_map]

theorem Realizes.map_of_abs_det_one {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (h : Realizes K c) (f : Space d →L[ℝ] Space d)
    (hf : |LinearMap.det f.toLinearMap| = 1) : Realizes (fun i => mapBody f (K i)) c := by
  intro t ht
  rw [h t ht]
  simp only [volumeFunction, weightedSum_map, bodyVolume_map, hf, one_mul]

end VolumePolynomials
