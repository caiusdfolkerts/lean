module
public import PaperVerification.ToricFaces
public import Mathlib.Data.Finset.Max
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin
@[expose] public section
/-!
# Finite half-space representations by elimination

The missing representation theorem is developed through Fourier–Motzkin elimination.
No polyhedral representation assertion is taken as an axiom.
-/

noncomputable section

namespace PaperVerification.ToricExchange

open Set

/-- Elimination of one real unknown from a finite system of weak affine inequalities.
The retained constraints are the zero-coefficient rows and every lower/upper pair. -/
theorem exists_affine_inequality_variable_iff {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) :
    (∃ t : ℝ, ∀ i, 0 ≤ a i * t + b i) ↔
      (∀ i, a i = 0 → 0 ≤ b i) ∧
      (∀ i j, 0 < a i → a j < 0 → -b i / a i ≤ -b j / a j) := by
  classical
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun i hi => by simpa [hi] using ht i, ?_⟩
    intro i j hi hj
    have hlo : -b i / a i ≤ t := (div_le_iff₀ hi).mpr (by nlinarith [ht i])
    have hup : t ≤ -b j / a j := (le_div_iff_of_neg hj).mpr (by nlinarith [ht j])
    exact hlo.trans hup
  · rintro ⟨hz, hpairs⟩
    let L : Finset ι := Finset.univ.filter (fun i => 0 < a i)
    let U : Finset ι := Finset.univ.filter (fun i => a i < 0)
    have hrow (t : ℝ) (hlo : ∀ i, 0 < a i → -b i / a i ≤ t)
        (hup : ∀ i, a i < 0 → t ≤ -b i / a i) :
        ∀ i, 0 ≤ a i * t + b i := by
      intro i
      rcases lt_trichotomy (a i) 0 with hi | hi | hi
      · have := (le_div_iff_of_neg hi).mp (hup i hi)
        nlinarith
      · simpa [hi] using hz i hi
      · have := (div_le_iff₀ hi).mp (hlo i hi)
        nlinarith
    by_cases hL : L.Nonempty
    · obtain ⟨i, hi, hmax⟩ := L.exists_max_image (fun i => -b i / a i) hL
      have hi0 : 0 < a i := (Finset.mem_filter.mp hi).2
      refine ⟨-b i / a i, hrow _ ?_ ?_⟩
      · intro j hj
        exact hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
      · intro j hj
        exact hpairs i j hi0 hj
    · by_cases hU : U.Nonempty
      · obtain ⟨j, hj, hmin⟩ := U.exists_min_image (fun i => -b i / a i) hU
        refine ⟨-b j / a j, hrow _ ?_ ?_⟩
        · intro i hi
          exact False.elim (hL ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)
        · intro i hi
          exact hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
      · refine ⟨0, hrow _ ?_ ?_⟩
        · intro i hi
          exact False.elim (hL ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)
        · intro i hi
          exact False.elim (hU ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)

variable {V W ι : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

namespace AffineInequalities

/-- In finite dimension, every affine functional is continuous. -/
def ofSlack (f : ι → V →ᵃ[ℝ] ℝ) : AffineInequalities ι V where
  slack := f
  continuous_slack i := AffineMap.continuous_linear_iff.mp
    (f i).linear.continuous_of_finiteDimensional

/-- Pulling back finitely many half-spaces along an actual affine map. -/
def comap (H : AffineInequalities ι V) (f : W →ᵃ[ℝ] V) : AffineInequalities ι W :=
  ofSlack (fun i => (H.slack i).comp f)

@[simp] theorem mem_comap_region (H : AffineInequalities ι V) (f : W →ᵃ[ℝ] V) (x : W) :
    x ∈ (H.comap f).region ↔ f x ∈ H.region := Iff.rfl

/-- The coefficient of the variable that will be eliminated. -/
def lastCoefficient (H : AffineInequalities ι (V × ℝ)) (i : ι) : ℝ :=
  (H.slack i).linear (0, 1)

/-- The affine row remaining when the last variable is set to zero. -/
def zeroLast (H : AffineInequalities ι (V × ℝ)) (i : ι) : V →ᵃ[ℝ] ℝ :=
  (H.slack i).comp ((AffineMap.id ℝ V).prod (AffineMap.const ℝ V (0 : ℝ)))

theorem slack_prod (H : AffineInequalities ι (V × ℝ)) (i : ι) (x : V) (t : ℝ) :
    H.slack i (x, t) = H.lastCoefficient i * t + H.zeroLast i x := by
  have he : (x, t) = t • ((0, 1) : V × ℝ) +ᵥ ((x, 0) : V × ℝ) := by ext <;> simp
  rw [he, AffineMap.map_vadd, map_smul]
  simp [lastCoefficient, zeroLast, smul_eq_mul, mul_comm]

/-- The actual projected system. Inapplicable rows are represented by `0 ≥ 0`,
which leaves the represented set unchanged. -/
noncomputable def eliminateLast (H : AffineInequalities ι (V × ℝ)) :
    AffineInequalities (ι ⊕ (ι × ι)) V := by
  classical
  exact ofSlack (fun row => match row with
    | Sum.inl i => if H.lastCoefficient i = 0 then H.zeroLast i else 0
    | Sum.inr (i, j) => if 0 < H.lastCoefficient i ∧ H.lastCoefficient j < 0 then
        (H.lastCoefficient i)⁻¹ • H.zeroLast i -
          (H.lastCoefficient j)⁻¹ • H.zeroLast j else 0)

/-- Fourier–Motzkin elimination preserves exactly the existential projection. -/
theorem mem_eliminateLast_region [Fintype ι] (H : AffineInequalities ι (V × ℝ)) (x : V) :
    x ∈ H.eliminateLast.region ↔ ∃ t : ℝ, (x, t) ∈ H.region := by
  classical
  rw [show (∃ t : ℝ, (x, t) ∈ H.region) ↔
      ∃ t : ℝ, ∀ i, 0 ≤ H.lastCoefficient i * t + H.zeroLast i x by
    simp only [region, Set.mem_setOf_eq, H.slack_prod]]
  rw [exists_affine_inequality_variable_iff]
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro i hi
      simpa [eliminateLast, ofSlack, hi] using hx (Sum.inl i)
    · intro i j hi hj
      have hij : 0 < H.lastCoefficient i ∧ H.lastCoefficient j < 0 := ⟨hi, hj⟩
      have h := hx (Sum.inr (i, j))
      simp only [eliminateLast, ofSlack, if_pos hij, AffineMap.coe_sub, Pi.sub_apply,
        AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul] at h
      have hle := sub_nonneg.mp h
      simpa only [neg_div, div_eq_mul_inv, mul_comm, mul_neg] using (neg_le_neg hle)
  · rintro ⟨hz, hpairs⟩ row
    rcases row with i | ⟨i, j⟩
    · by_cases hi : H.lastCoefficient i = 0
      · simpa [eliminateLast, ofSlack, hi] using hz i hi
      · simp [eliminateLast, ofSlack, hi]
    · by_cases hij : 0 < H.lastCoefficient i ∧ H.lastCoefficient j < 0
      · have h := hpairs i j hij.1 hij.2
        simp only [eliminateLast, ofSlack, if_pos hij, AffineMap.coe_sub, Pi.sub_apply,
          AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]
        have h' : (H.lastCoefficient j)⁻¹ * H.zeroLast j x ≤
            (H.lastCoefficient i)⁻¹ * H.zeroLast i x := by
          simpa only [neg_div, div_eq_mul_inv, mul_comm, mul_neg, neg_le_neg_iff] using h
        exact sub_nonneg.mpr h'
      · simp [eliminateLast, ofSlack, hij]

end AffineInequalities

/-- The usual finite half-space representation property, with no geometric
conclusions encoded into the definition. -/
def HasFiniteHalfspaces (P : Set V) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (H : AffineInequalities ι V), P = H.region

namespace HasFiniteHalfspaces

variable {P : Set V}

theorem comap (hP : HasFiniteHalfspaces P) (f : W →ᵃ[ℝ] V) :
    HasFiniteHalfspaces (f ⁻¹' P) := by
  rcases hP with ⟨ι, hι, H, rfl⟩
  exact ⟨ι, hι, H.comap f, rfl⟩

theorem project_real {P : Set (V × ℝ)} (hP : HasFiniteHalfspaces P) :
    HasFiniteHalfspaces {x : V | ∃ t : ℝ, (x, t) ∈ P} := by
  rcases hP with ⟨ι, hι, H, rfl⟩
  letI := hι
  refine ⟨ι ⊕ (ι × ι), inferInstance, H.eliminateLast, ?_⟩
  ext x
  exact (H.mem_eliminateLast_region x).symm


/-- Moving the first coordinate of a finite tuple into the final real factor. -/
def insertCoordinate (n : ℕ) :
    ((V × (Fin n → ℝ)) × ℝ) →ₗ[ℝ] (V × (Fin (n + 1) → ℝ)) where
  toFun x := (x.1.1, Fin.cons x.2 x.1.2)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext i
      exact Fin.cases rfl (fun _ => rfl) i
  map_smul' c x := by
    apply Prod.ext
    · rfl
    · funext i
      exact Fin.cases rfl (fun _ => rfl) i

/-- Eliminating any finite tuple of real auxiliary variables. -/
theorem project_fin (n : ℕ) {P : Set (V × (Fin n → ℝ))}
    (hP : HasFiniteHalfspaces P) :
    HasFiniteHalfspaces {x : V | ∃ w : Fin n → ℝ, (x, w) ∈ P} := by
  induction n with
  | zero =>
    let f : V →ᵃ[ℝ] V × (Fin 0 → ℝ) :=
      (AffineMap.id ℝ V).prod (AffineMap.const ℝ V 0)
    convert hP.comap f using 1
    ext x
    constructor
    · rintro ⟨w, hw⟩
      have hw0 : w = 0 := Subsingleton.elim _ _
      simpa [f, hw0] using hw
    · intro hx
      exact ⟨0, hx⟩
  | succ n ih =>
    let Q : Set ((V × (Fin n → ℝ)) × ℝ) := (insertCoordinate (V := V) n) ⁻¹' P
    have hQ : HasFiniteHalfspaces Q := by
      change HasFiniteHalfspaces ((insertCoordinate (V := V) n).toAffineMap ⁻¹' P)
      exact hP.comap (insertCoordinate (V := V) n).toAffineMap
    have hR := hQ.project_real
    have hproj := ih hR
    convert hproj using 1
    ext x
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨Fin.tail w, w 0, ?_⟩
      simpa [Q, insertCoordinate, Fin.cons_self_tail] using hw
    · rintro ⟨w, t, ht⟩
      exact ⟨Fin.cons t w, ht⟩

/-- Projection over an arbitrary finite coordinate index set. -/
theorem project_fintype {κ : Type} [Fintype κ] {P : Set (V × (κ → ℝ))}
    (hP : HasFiniteHalfspaces P) :
    HasFiniteHalfspaces {x : V | ∃ w : κ → ℝ, (x, w) ∈ P} := by
  classical
  let e := Fintype.equivFin κ
  let f : (V × (Fin (Fintype.card κ) → ℝ)) →ₗ[ℝ] (V × (κ → ℝ)) :=
    { toFun := fun x => (x.1, fun i => x.2 (e i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h := (hP.comap f.toAffineMap).project_fin (Fintype.card κ)
  convert h using 1
  ext x
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨fun i => w (e.symm i), ?_⟩
    simpa [f] using hw
  · rintro ⟨w, hw⟩
    exact ⟨fun i => w (e i), hw⟩

end HasFiniteHalfspaces

section FiniteConvexHull

variable {n : ℕ} {κ : Type} [Fintype κ]

/-- The linear map sending weights to their weighted vector sum. -/
def weightedPointSum (v : κ → Fin n → ℝ) : (κ → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun w := ∑ i, w i • v i
  map_add' w z := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c w := by simp [smul_smul, Finset.smul_sum]

/-- Coordinate projections of the nonnegative weights. -/
def weightCoordinate (i : κ) : ((Fin n → ℝ) × (κ → ℝ)) →ₗ[ℝ] ℝ :=
  (LinearMap.proj i).comp (LinearMap.snd ℝ (Fin n → ℝ) (κ → ℝ))

/-- The affine equations defining a convex combination: total weight one, and
weighted vector sum equal to the displayed point. -/
def combinationEquation (v : κ → Fin n → ℝ) :
    Option (Fin n) → ((Fin n → ℝ) × (κ → ℝ)) →ᵃ[ℝ] ℝ
  | none => (∑ i : κ, weightCoordinate (n := n) i).toAffineMap -
      AffineMap.const ℝ ((Fin n → ℝ) × (κ → ℝ)) 1
  | some j => ((LinearMap.proj j).comp
      (LinearMap.fst ℝ (Fin n → ℝ) (κ → ℝ) -
        (weightedPointSum v).comp (LinearMap.snd ℝ (Fin n → ℝ) (κ → ℝ)))).toAffineMap

/-- A finite inequality description of the graph of all convex combinations. -/
def combinationGraph (v : κ → Fin n → ℝ) :
    AffineInequalities (κ ⊕ (Option (Fin n) × Bool)) ((Fin n → ℝ) × (κ → ℝ)) :=
  AffineInequalities.ofSlack (fun row => match row with
    | Sum.inl i => (weightCoordinate i).toAffineMap
    | Sum.inr (j, true) => combinationEquation v j
    | Sum.inr (j, false) => -(combinationEquation v j))

theorem mem_combinationGraph_region (v : κ → Fin n → ℝ) (x : Fin n → ℝ) (w : κ → ℝ) :
    (x, w) ∈ (combinationGraph v).region ↔
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ (∑ i, w i • v i) = x := by
  classical
  have heq (j : Option (Fin n)) :
      (0 ≤ combinationEquation v j (x, w) ∧ 0 ≤ -(combinationEquation v j (x, w))) ↔
        combinationEquation v j (x, w) = 0 := by
    constructor
    · rintro ⟨hp, hn⟩
      linarith
    · intro hz
      simp [hz]
  constructor
  · intro h
    have hz (j : Option (Fin n)) : combinationEquation v j (x, w) = 0 := by
      apply (heq j).mp
      exact ⟨h (Sum.inr (j, true)), h (Sum.inr (j, false))⟩
    refine ⟨fun i => h (Sum.inl i), ?_, ?_⟩
    · have h0 := hz none
      simpa [combinationEquation, weightCoordinate] using (sub_eq_zero.mp h0)
    · funext j
      have hj := hz (some j)
      simpa [combinationEquation, weightedPointSum] using (sub_eq_zero.mp hj).symm
  · rintro ⟨hw, hsum, hvec⟩ row
    rcases row with i | ⟨j, b⟩
    · exact hw i
    · have hz : combinationEquation v j (x, w) = 0 := by
        cases j with
        | none => simp [combinationEquation, weightCoordinate, hsum]
        | some j => simp [combinationEquation, weightedPointSum, hvec]
      cases b <;> simp [combinationGraph, AffineInequalities.ofSlack, hz]

/-- A finite convex hull is exactly the projection of the convex-combination graph. -/
theorem mem_finite_convexHull_iff_weights (s : Finset (Fin n → ℝ)) (x : Fin n → ℝ) :
    x ∈ convexHull ℝ (s : Set (Fin n → ℝ)) ↔
      ∃ w : s → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
        (∑ i, w i • (i : Fin n → ℝ)) = x := by
  classical
  constructor
  · intro hx
    obtain ⟨w, hw, hsum, hvec⟩ := Finset.mem_convexHull'.mp hx
    refine ⟨fun i => w i, fun i => hw i i.property, ?_, ?_⟩
    · simpa only [Finset.univ_eq_attach, Finset.sum_attach] using hsum
    · change (∑ i ∈ s.attach, w (i : Fin n → ℝ) • (i : Fin n → ℝ)) = x
      rw [Finset.sum_attach s (fun y => w y • y)]
      exact hvec
  · rintro ⟨w, hw, hsum, hvec⟩
    exact mem_convexHull_of_exists_fintype w (fun i : s => (i : Fin n → ℝ))
      hw hsum (fun i => i.property) hvec

/-- Every finite real convex hull has a finite affine half-space representation.
The proof explicitly eliminates its convex-combination weights. -/
theorem finite_convexHull_hasFiniteHalfspaces (s : Finset (Fin n → ℝ)) :
    HasFiniteHalfspaces (convexHull ℝ (s : Set (Fin n → ℝ))) := by
  classical
  let H := combinationGraph (fun i : s => (i : Fin n → ℝ))
  have hH : HasFiniteHalfspaces H.region :=
    ⟨s ⊕ (Option (Fin n) × Bool), inferInstance, H, rfl⟩
  convert hH.project_fintype using 1
  ext x
  rw [mem_finite_convexHull_iff_weights]
  exact exists_congr fun w => (mem_combinationGraph_region _ x w).symm

end FiniteConvexHull

end PaperVerification.ToricExchange
