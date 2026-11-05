module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Elab.Tactic.Omega
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring
public import paper_verification.toric001

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricElimination
section Source_ToricElimination

-- original header: module
-- original header: public import PaperVerification.ToricFaces
-- original header: public import Mathlib.Data.Finset.Max
-- original header: public import Mathlib.Analysis.Convex.Combination
-- original header: public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
-- original header: public import Mathlib.Data.Fin.Tuple.Basic
-- original header: public import Mathlib.Algebra.BigOperators.Fin
-- original header: @[expose] public section
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
end
end Source_ToricElimination
-- END ORIGINAL PaperVerification.ToricElimination


-- BEGIN ORIGINAL PaperVerification.ToricFaceGeometry
section Source_ToricFaceGeometry

-- original header: module
-- original header: public import PaperVerification.ToricElimination
-- original header: @[expose] public section
/-!
# Faces of finite convex hulls

Every actual convex face is the convex hull of the original generators lying on it.
This supplies the finite vertex data needed when passing to lower-dimensional faces.
-/

noncomputable section

namespace PaperVerification.ToricExchange

open Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The original finite generators lying on a specified geometric face. -/
noncomputable def faceGenerators (s : Finset V) (F : Set V) : Finset V := by
  classical
  exact s.filter (fun v => v ∈ F)

/-- An affine functional commutes with a weighted sum whose weights total one. -/
theorem affine_apply_weighted_sum {κ : Type*} (s : Finset κ) (w : κ → ℝ) (v : κ → V)
    (hsum : ∑ i ∈ s, w i = 1) (f : V →ᵃ[ℝ] ℝ) :
    f (∑ i ∈ s, w i • v i) = ∑ i ∈ s, w i * f (v i) := by
  have h := s.map_affineCombination v w hsum f
  simpa only [Finset.affineCombination_eq_linear_combination _ _ _ hsum,
    Function.comp_apply, smul_eq_mul] using h

/-- Injective affine maps preserve actual extreme points. -/
theorem affine_mem_extremePoints_image {W : Type*} [AddCommGroup W] [Module ℝ W]
    (f : V →ᵃ[ℝ] W) (hf : Function.Injective f) {S : Set V} {x : V}
    (hx : x ∈ S.extremePoints ℝ) : f x ∈ (f '' S).extremePoints ℝ := by
  refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hopen
  rw [← image_openSegment ℝ f a b] at hopen
  obtain ⟨z, hz, he⟩ := hopen
  have hzx := hf he
  subst z
  exact congrArg f (hx.2 ha hb hz)

/-- The left endpoint is an extreme point of a nondegenerate real segment. -/
theorem left_endpoint_extreme_segment {v w : V} (hvw : v ≠ w) :
    v ∈ (segment ℝ v w).extremePoints ℝ := by
  have h0 : (0 : ℝ) ∈ (Set.Icc (0 : ℝ) 1).extremePoints ℝ := by
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
    rintro x hx y hy ⟨a, b, ha, hb, hab, he⟩
    simp only [smul_eq_mul] at he
    have hax : a * x ≤ 0 := by nlinarith [mul_nonneg hb.le hy.1]
    have haz : a * x = 0 := le_antisymm hax (mul_nonneg ha.le hx.1)
    exact (mul_eq_zero.mp haz).resolve_left (ne_of_gt ha)
  rw [segment_eq_image_lineMap]
  have h := affine_mem_extremePoints_image (AffineMap.lineMap v w)
    (AffineMap.lineMap_injective ℝ hvw) h0
  simpa using h

/-- The right endpoint is also an extreme point of the segment. -/
theorem right_endpoint_extreme_segment {v w : V} (hvw : v ≠ w) :
    w ∈ (segment ℝ v w).extremePoints ℝ := by
  rw [segment_symm]
  exact left_endpoint_extreme_segment hvw.symm

namespace AffineInequalities

variable {ι : Type*} (H : AffineInequalities ι V)

/-- A face of a finite convex hull is generated by exactly those original generators
on which its defining constraints vanish. -/
theorem face_eq_convexHull_filter (s : Finset V)
    (hH : H.region = convexHull ℝ (s : Set V)) (J : Set ι) :
    H.face J = convexHull ℝ (faceGenerators s (H.face J) : Set V) := by
  classical
  change H.face J = convexHull ℝ ((s.filter (fun v => v ∈ H.face J)) : Set V)
  apply Set.Subset.antisymm
  · intro x hx
    have hxHull : x ∈ convexHull ℝ (s : Set V) := hH ▸ hx.1
    obtain ⟨w, hw, hsum, hvec⟩ := Finset.mem_convexHull'.mp hxHull
    have hgenerator (v : V) (hv : v ∈ s) : v ∈ H.region := by
      rw [hH]
      exact subset_convexHull ℝ (s : Set V) hv
    have hpositive (v : V) (hv : v ∈ s) (hwne : w v ≠ 0) : v ∈ H.face J := by
      refine ⟨hgenerator v hv, ?_⟩
      intro j hj
      have hterms : ∀ y ∈ s, 0 ≤ w y * H.slack j y :=
        fun y hy => mul_nonneg (hw y hy) (hgenerator y hy j)
      have hslacksum : (∑ y ∈ s, w y * H.slack j y) = 0 := by
        have hm := affine_apply_weighted_sum s w id hsum (H.slack j)
        simp only [id_eq] at hm
        rw [← hm, hvec]
        exact hx.2 j hj
      have hle := Finset.single_le_sum hterms hv
      rw [hslacksum] at hle
      have hzero : w v * H.slack j v = 0 := le_antisymm hle (hterms v hv)
      exact (mul_eq_zero.mp hzero).resolve_left hwne
    let t := s.filter (fun v => v ∈ H.face J)
    have hmissing (v : V) (hv : v ∈ s) (hvt : v ∉ t) : w v = 0 := by
      by_contra hne
      exact hvt (Finset.mem_filter.mpr ⟨hv, hpositive v hv hne⟩)
    have hsumt : ∑ v ∈ t, w v = 1 := by
      rw [Finset.sum_subset (Finset.filter_subset _ _) hmissing]
      exact hsum
    have hvect : ∑ v ∈ t, w v • v = x := by
      rw [Finset.sum_subset (Finset.filter_subset _ _) (fun v hv hvt => by rw [hmissing v hv hvt]; simp)]
      exact hvec
    exact Finset.mem_convexHull'.mpr ⟨w,
      fun v hv => hw v (Finset.mem_filter.mp hv).1, hsumt, hvect⟩
  · apply convexHull_min
    · exact fun v hv => (Finset.mem_filter.mp hv).2
    · exact H.convex_face J

end AffineInequalities

/-- Every actual convex face of a finite real polytope is the convex hull of the
original generators that it contains. No exposed-face assumption is added. -/
theorem convex_face_eq_convexHull_filter {n : ℕ} (s : Finset (Fin n → ℝ))
    (G : Set (Fin n → ℝ)) (hGconvex : Convex ℝ G)
    (hG : IsExtreme ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) G) :
    G = convexHull ℝ (faceGenerators s G : Set (Fin n → ℝ)) := by
  classical
  by_cases hGne : G.Nonempty
  · obtain ⟨ι, hι, H, hH⟩ := finite_convexHull_hasFiniteHalfspaces s
    letI := hι
    have hGH : IsExtreme ℝ H.region G := by simpa only [hH] using hG
    obtain ⟨x, hx, hxG⟩ := H.exists_activeFace_eq hGconvex hGH hGne
    rw [hxG]
    exact H.face_eq_convexHull_filter s hH.symm _
  · have hG0 : G = ∅ := Set.not_nonempty_iff_eq_empty.mp hGne
    simp [hG0, faceGenerators]


/-- The full exchange criterion for every finite real polytope, including those
of lower dimension in their ambient lattice. Integral vertices are not needed by
this reduction: all decomposition points are still actual points of the given lattice. -/
theorem finite_polytope_exchange_criterion {n : ℕ} {M : Type*} [AddCommGroup M]
    (embedding : M →+ (Fin n → ℝ)) (P : Set (Fin n → ℝ))
    (hpoly : ∃ s : Finset (Fin n → ℝ), P = convexHull ℝ (s : Set (Fin n → ℝ)))
    (hidp : IntegerDecompositionProperty embedding P)
    (hparity : FaceParity embedding P) (hadjoint : FaceAdjoint embedding P)
    (R : Type*) [CommRing R] :
    (∀ s t : Multiset (latticePoints embedding P), s.card = t.card →
      total (latticePoints embedding P) s = total (latticePoints embedding P) t →
      Connected (latticePoints embedding P) s t) ∧
    RingHom.ker (paperToricMap (latticePoints embedding P) R) =
      polynomialQuadraticIdeal (latticePoints embedding P) R := by
  obtain ⟨s, rfl⟩ := hpoly
  obtain ⟨ι, hι, H, hH⟩ := finite_convexHull_hasFiniteHalfspaces s
  letI := hι
  rw [hH] at hidp hparity hadjoint ⊢
  have hmid := midpointDecomposition_of_convex_idp embedding H.region H.convex_region hidp
  have htriple := tripleReduction_of_face_parity_adjoint H embedding hparity hadjoint
  exact ⟨all_fibers_connected _ hmid htriple, paper_kernel_eq_quadrics _ R hmid htriple⟩

end PaperVerification.ToricExchange
end
end Source_ToricFaceGeometry
-- END ORIGINAL PaperVerification.ToricFaceGeometry


-- BEGIN ORIGINAL PaperVerification.ToricStatements
section Source_ToricStatements

-- original header: module
-- original header: public import PaperVerification.ToricFaceGeometry
-- original header: public import Mathlib.Analysis.Convex.Extreme
-- original header: public import Mathlib.Analysis.Convex.Intrinsic
-- original header: public import Mathlib.Algebra.GCDMonoid.Finset
-- original header: public import Mathlib.LinearAlgebra.Basis.Defs
-- original header: public import Mathlib.Algebra.Group.Int.Units
-- original header: public import Mathlib.Data.Int.Basic
-- original header: @[expose] public section
/-!
# Faithful mathematical targets for the toric paper

The principal claims below are named propositions, not axioms and not claimed proofs.
The polytope, edges, smoothness, lattice lengths, sums, and kernel are all genuine
mathematical objects. No desired conclusion is included in a structure definition.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped Pointwise
open PaperVerification.ToricExchange

abbrev Lattice (n : ℕ) := Fin n → ℤ
abbrev Ambient (n : ℕ) := Fin n → ℝ

/-- The standard inclusion of the full lattice into its real vector space. -/
def embed (n : ℕ) : Lattice n →+ Ambient n where
  toFun z i := z i
  map_zero' := by ext i; simp
  map_add' z w := by ext i; simp

theorem embed_injective (n : ℕ) : Function.Injective (embed n) := by
  intro z w h
  funext i
  exact Int.cast_injective (congrFun h i)

/-- A vector in an integral basis is primitive: it is not a nonunit integer
multiple of another lattice vector. -/
theorem lattice_basis_vector_primitive {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n)
    (k : ℤ) (z : Lattice n) (h : b i = k • z) : k = 1 ∨ k = -1 := by
  have hc : b.repr (k • z) i = 1 := by
    rw [← h]
    simp
  have hsmul : b.repr (k • z) = k • b.repr z := b.repr.map_smul k z
  rw [hsmul] at hc
  have hk : k * b.repr z i = 1 := by
    simpa only [Finsupp.smul_apply, smul_eq_mul] using hc
  exact Int.eq_one_or_neg_one_of_mul_eq_one hk

/-- The coordinate gcd of a primitive integral basis vector is exactly one. -/
theorem lattice_basis_vector_gcd_one {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) :
    Finset.univ.gcd (fun j : Fin n => (b i j).natAbs) = 1 := by
  classical
  let g : ℕ := Finset.univ.gcd (fun j : Fin n => (b i j).natAbs)
  have hd (j : Fin n) : (g : ℤ) ∣ b i j :=
    Int.natCast_dvd.mpr (Finset.gcd_dvd (Finset.mem_univ j))
  choose z hz using hd
  have hv : b i = (g : ℤ) • z := by funext j; exact hz j
  rcases lattice_basis_vector_primitive b i g z hv with hg | hg
  · exact_mod_cast hg
  · have hg0 : (0 : ℤ) ≤ g := Int.natCast_nonneg g
    omega

/-- A full-dimensional lattice polytope, given by a finite generating set.
The generating set is not required to contain only vertices. -/
structure LatticePolytope (n : ℕ) where
  generators : Finset (Lattice n)
  nonempty : generators.Nonempty
  fullDimensional : affineSpan ℝ (convexHull ℝ ((embed n) '' (generators : Set (Lattice n)))) = ⊤

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- The ordinary convex hull defining the polytope. -/
def carrier : Set (Ambient n) := convexHull ℝ ((embed n) '' (P.generators : Set (Lattice n)))

/-- An edge is a nondegenerate line segment that is an actual face of the polytope. -/
def IsEdge (v w : Ambient n) : Prop :=
  v ≠ w ∧ IsExtreme ℝ P.carrier (segment ℝ v w)

/-- The endpoints of an actual edge are actual vertices of the polytope. -/
theorem edge_endpoints_extreme {v w : Ambient n} (h : P.IsEdge v w) :
    v ∈ P.carrier.extremePoints ℝ ∧ w ∈ P.carrier.extremePoints ℝ :=
  ⟨h.2.extremePoints_subset_extremePoints (left_endpoint_extreme_segment h.1),
    h.2.extremePoints_subset_extremePoints (right_endpoint_extreme_segment h.1)⟩

/-- Every vertex is one of the integral generators, regardless of whether the
original finite generating set contains redundant points. -/
theorem extreme_integral {v : Ambient n} (hv : v ∈ P.carrier.extremePoints ℝ) :
    ∃ z ∈ P.generators, embed n z = v := by
  obtain ⟨z, hz, he⟩ := extremePoints_convexHull_subset hv
  exact ⟨z, hz, he⟩

/-- The integral-endpoint clause of `EdgesAtLeast` is automatic for a lattice polytope. -/
theorem edge_endpoints_integral {v w : Ambient n} (h : P.IsEdge v w) :
    ∃ vZ wZ : Lattice n, embed n vZ = v ∧ embed n wZ = w := by
  obtain ⟨hv, hw⟩ := P.edge_endpoints_extreme h
  obtain ⟨vZ, _, hvZ⟩ := P.extreme_integral hv
  obtain ⟨wZ, _, hwZ⟩ := P.extreme_integral hw
  exact ⟨vZ, wZ, hvZ, hwZ⟩

/-- Lattice length in standard coordinates, the gcd of the coordinate differences. -/
def latticeLength (v w : Lattice n) : ℕ :=
  Finset.univ.gcd (fun i : Fin n => (w i - v i).natAbs)

/-- The gcd convention for lattice length agrees exactly with positive integer
multiplicity along a primitive basis direction, as used by the smoothness definition. -/
theorem latticeLength_basis_direction (v : Lattice n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (k : ℕ) :
    latticeLength v (v + (k : ℤ) • b i) = k := by
  simp only [latticeLength, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    add_sub_cancel_left, Int.natAbs_mul, Int.natAbs_natCast]
  rw [Finset.gcd_mul_left, lattice_basis_vector_gcd_one]
  simp

/-- Every actual edge has integral endpoints and at least the stated lattice length. -/
def EdgesAtLeast (bound : ℕ) : Prop :=
  ∀ v w : Ambient n, P.IsEdge v w →
    ∃ vZ wZ : Lattice n, embed n vZ = v ∧ embed n wZ = w ∧
      bound ≤ latticeLength vZ wZ

/-- Requiring integral endpoints adds no hypothesis: the edge bound can be
stated equivalently by quantifying only over lattice endpoints. -/
theorem edgesAtLeast_iff (bound : ℕ) :
    P.EdgesAtLeast bound ↔ ∀ v w : Lattice n,
      P.IsEdge (embed n v) (embed n w) → bound ≤ latticeLength v w := by
  constructor
  · intro h v w hvw
    obtain ⟨v', w', hv, hw, hlen⟩ := h (embed n v) (embed n w) hvw
    have hv' := embed_injective n hv
    have hw' := embed_injective n hw
    simpa only [hv', hw'] using hlen
  · intro h v w hvw
    obtain ⟨vZ, wZ, hvZ, hwZ⟩ := P.edge_endpoints_integral hvw
    refine ⟨vZ, wZ, hvZ, hwZ, ?_⟩
    apply h
    simpa only [hvZ, hwZ] using hvw

/-- The coordinate length of a basis-direction edge satisfies precisely the
geometric edge bound. -/
theorem edge_basis_length_bound {bound : ℕ} (hbound : P.EdgesAtLeast bound)
    (v : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (k : ℕ)
    (hedge : P.IsEdge (embed n v) (embed n (v + (k : ℤ) • b i))) : bound ≤ k := by
  have h := (P.edgesAtLeast_iff bound).mp hbound v (v + (k : ℤ) • b i) hedge
  simpa only [latticeLength_basis_direction] using h

/-- Smoothness exactly in terms of the primitive incident edge directions forming
a lattice basis. The final clause states that these are all incident edges. -/
def Smooth : Prop :=
  ∀ v ∈ P.carrier.extremePoints ℝ,
    ∃ (vZ : Lattice n) (basis : Module.Basis (Fin n) ℤ (Lattice n)) (lengths : Fin n → ℕ),
      embed n vZ = v ∧
      (∀ i, 0 < lengths i ∧
        P.IsEdge v (embed n (vZ + (lengths i : ℤ) • basis i))) ∧
      (∀ w : Ambient n, P.IsEdge v w →
        ∃ i, w = embed n (vZ + (lengths i : ℤ) • basis i))

/-- The ordinary normal cone at a point, using the standard pairing. -/
def normalCone (x : Ambient n) : Set (Ambient n) :=
  {u | ∀ y ∈ P.carrier, 0 ≤ ∑ i, u i * (y i - x i)}

/-- All cones of the normal fan, including the zero cone and boundary-face cones. -/
def normalFan : Set (Set (Ambient n)) :=
  {C | ∃ x ∈ P.carrier, C = P.normalCone x}

/-- Equality of the actual normal fans. -/
def SameNormalFan (Q : LatticePolytope n) : Prop := P.normalFan = Q.normalFan

/-- Ordinary Minkowski addition of the real polytopes. -/
def minkowskiSum (Q : LatticePolytope n) : Set (Ambient n) := P.carrier + Q.carrier

/-- Full IDP of the polytope, using every positive natural dilation. -/
def HasIDP : Prop := IntegerDecompositionProperty (embed n) P.carrier

/-- The actual polynomial-kernel quadratic-generation assertion over a coefficient ring. -/
def QuadraticallyGenerated (R : Type*) [CommRing R] : Prop :=
  RingHom.ker (paperToricMap (latticePoints (embed n) P.carrier) R) =
    polynomialQuadraticIdeal (latticePoints (embed n) P.carrier) R


/-- Every lattice polytope has a finite real affine-inequality presentation,
proved by eliminating its actual convex-combination weights. -/
theorem hasFiniteHalfspaces : HasFiniteHalfspaces P.carrier := by
  classical
  have h := finite_convexHull_hasFiniteHalfspaces (P.generators.image (embed n))
  simpa [carrier, Finset.coe_image] using h

/-- Proposition 2.1, with its literal face hypotheses, on every actual lattice
polytope and in every degree. The ideal equality uses precisely the paper's map. -/
theorem proposition2_1 (R : Type*) [CommRing R]
    (hidp : P.HasIDP) (hparity : FaceParity (embed n) P.carrier)
    (hadjoint : FaceAdjoint (embed n) P.carrier) :
    (∀ s t : Multiset (latticePoints (embed n) P.carrier),
      s.card = t.card → total (latticePoints (embed n) P.carrier) s =
        total (latticePoints (embed n) P.carrier) t →
      Connected (latticePoints (embed n) P.carrier) s t) ∧
      P.QuadraticallyGenerated R := by
  change _ ∧ RingHom.ker (paperToricMap (latticePoints (embed n) P.carrier) R) =
    polynomialQuadraticIdeal (latticePoints (embed n) P.carrier) R
  change IntegerDecompositionProperty (embed n) P.carrier at hidp
  obtain ⟨ι, hι, H, hP⟩ := P.hasFiniteHalfspaces
  letI := hι
  rw [hP] at hidp hparity hadjoint ⊢
  have hmid := midpointDecomposition_of_convex_idp (embed n) H.region H.convex_region hidp
  have htriple := tripleReduction_of_face_parity_adjoint H (embed n) hparity hadjoint
  exact ⟨all_fibers_connected _ hmid htriple, paper_kernel_eq_quadrics _ R hmid htriple⟩

end LatticePolytope

/-- The exact polytope claim of Theorem 1.1 over an arbitrary field.
This is only a target proposition; no proof is asserted by defining it. -/
def Theorem1_1Statement (R : Type*) [Field R] : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ P : LatticePolytope n,
    P.Smooth → P.EdgesAtLeast n → P.HasIDP ∧ P.QuadraticallyGenerated R

/-- The prescribed-parity geometric claim of Theorem 1.2. Representing a coset by
an arbitrary lattice vector is equivalent to quantifying over `M/2M`.
The correspondence with ample divisors uses the common normal fan dictionary. -/
def Theorem1_2PolytopeStatement : Prop :=
  ∀ n : ℕ, ∀ P Q : LatticePolytope n,
    P.Smooth → Q.Smooth → P.SameNormalFan Q → P.EdgesAtLeast n → Q.EdgesAtLeast n →
    ∀ m : Lattice n, embed n m ∈ interior (P.minkowskiSum Q) →
    ∀ parityRepresentative : Lattice n,
      ∃ a b : Lattice n, embed n a ∈ P.carrier ∧ embed n b ∈ Q.carrier ∧
        a + b = m ∧ SameParity a parityRepresentative

/-- The adjoint-multiplication geometric claim of Theorem 1.3, including both
inclusions in the stated equality of lattice-point sets. -/
def Theorem1_3PolytopeStatement : Prop :=
  ∀ n : ℕ, ∀ P Q : LatticePolytope n,
    P.Smooth → Q.Smooth → P.SameNormalFan Q →
    P.EdgesAtLeast (n + 1) → Q.EdgesAtLeast (n + 1) →
    ∀ m : Lattice n,
      embed n m ∈ interior (P.minkowskiSum Q) ↔
      ∃ a b : Lattice n, embed n a ∈ P.carrier ∧ embed n b ∈ interior Q.carrier ∧ a + b = m

end PaperVerification.ToricGeometry
end
end Source_ToricStatements
-- END ORIGINAL PaperVerification.ToricStatements


-- BEGIN ORIGINAL PaperVerification.ToricIntegralBasis
section Source_ToricIntegralBasis

-- original header: module
-- original header: public import PaperVerification.ToricStatements
-- original header: public import PaperVerification.ToricCornerBoxes
-- original header: public import Mathlib.Algebra.Module.ZLattice.Basic
-- original header: @[expose] public section
/-!
# Integral edge bases and real corner boxes

The integral basis appearing in the literal smoothness definition is extended to
an actual real basis. The extension preserves every lattice coordinate. Thus
integer supporting normals and the geometric edge lengths can be used directly
in the real box covering argument.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators

@[simp] theorem embed_int_smul {n : ℕ} (k : ℤ) (z : Lattice n) :
    embed n (k • z) = (k : ℝ) • embed n z := by
  ext i
  simp [embed, Int.cast_mul]

/-- The standard integral lattice as a genuine real-space submodule. -/
def standardIntegerLattice (n : ℕ) : Submodule ℤ (Ambient n) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

instance standardIntegerLattice_discreteTopology (n : ℕ) :
    DiscreteTopology (standardIntegerLattice n) := by
  exact ZSpan.discreteTopology_pi_basisFun (ι := Fin n)

instance standardIntegerLattice_isZLattice (n : ℕ) :
    IsZLattice ℝ (standardIntegerLattice n) := by
  dsimp [standardIntegerLattice]
  infer_instance

/-- The usual coordinate lattice and its embedded real submodule are linearly equivalent. -/
def standardLatticeEquiv (n : ℕ) : Lattice n ≃ₗ[ℤ] standardIntegerLattice n :=
  ((Pi.basisFun ℝ (Fin n)).restrictScalars ℤ).equivFun.symm

@[simp] theorem standardLatticeEquiv_coe {n : ℕ} (z : Lattice n) :
    ((standardLatticeEquiv n z : standardIntegerLattice n) : Ambient n) = embed n z := by
  classical
  change (((Pi.basisFun ℝ (Fin n)).restrictScalars ℤ).equivFun.symm z : Ambient n) = _
  rw [Module.Basis.equivFun_symm_apply]
  ext j
  simp [Submodule.coe_sum, Submodule.coe_smul_of_tower, Module.Basis.restrictScalars_apply,
    Finset.sum_apply, Pi.basisFun_apply, Pi.single_apply, embed]

/-- Every integral basis of the coordinate lattice gives the same vectors as a real basis. -/
def integralBasisReal {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Module.Basis (Fin n) ℝ (Ambient n) :=
  (b.map (standardLatticeEquiv n)).ofZLatticeBasis ℝ (standardIntegerLattice n)

@[simp] theorem integralBasisReal_apply {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) :
    integralBasisReal b i = embed n (b i) := by
  simp [integralBasisReal]

/-- Real coordinates of a lattice vector in an integral basis are exactly its integer coordinates. -/
@[simp] theorem integralBasisReal_repr {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (z : Lattice n) (i : Fin n) :
    (integralBasisReal b).repr (embed n z) i = (b.repr z i : ℝ) := by
  have h := (b.map (standardLatticeEquiv n)).ofZLatticeBasis_repr_apply
    ℝ (standardIntegerLattice n) (standardLatticeEquiv n z) i
  simpa only [integralBasisReal, standardLatticeEquiv_coe, Module.Basis.map_repr,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using h

/-- Each real dual basis functional is integral on the embedded coordinate lattice. -/
theorem integralBasisReal_coordinate_integral {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (z : Lattice n) :
    ∃ k : ℤ, (integralBasisReal b).repr (embed n z) i = k :=
  ⟨b.repr z i, integralBasisReal_repr b z i⟩

namespace LatticePolytope

/-- A specified integral edge basis with the required actual edge lengths
contains its entire unit corner box. This formulation keeps the chosen basis
fixed when matching two polytopes with the same normal fan. -/
theorem integral_edges_unit_corner_box {n : ℕ} (P : LatticePolytope n)
    (hlength : P.EdgesAtLeast n) (vZ : Lattice n)
    (hv : embed n vZ ∈ P.carrier)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (lengths : Fin n → ℕ)
    (hedges : ∀ i, P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)))
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    embed n vZ + ∑ i, t i • integralBasisReal b i ∈ P.carrier := by
  by_cases hn : n = 0
  · subst n
    exact (Subsingleton.elim (embed 0 vZ)
      (embed 0 vZ + ∑ i, t i • integralBasisReal b i)) ▸ hv
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    apply PaperVerification.Toric.unit_corner_box_of_long_segments hnpos P.carrier
      (convex_convexHull ℝ _) (embed n vZ) hv (integralBasisReal b)
      (fun i => (lengths i : ℝ)) ?_ ?_ t ht
    · intro i
      exact_mod_cast P.edge_basis_length_bound hlength vZ b i (lengths i) (hedges i)
    · intro i
      have hmem := (P.edge_endpoints_extreme (hedges i)).2.1
      simpa only [map_add, embed_int_smul, integralBasisReal_apply,
        Int.cast_natCast] using hmem

/-- The ordinary unit corner box supplied by every smooth vertex and the exact
edge-length bound of Theorem 1.1. This includes dimension zero. -/
theorem smooth_unit_corner_box {n : ℕ} (P : LatticePolytope n)
    (hP : P.Smooth) (hlength : P.EdgesAtLeast n)
    (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ) :
    ∃ (vZ : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n)),
      embed n vZ = v ∧
      ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) →
        v + ∑ i, t i • integralBasisReal b i ∈ P.carrier := by
  obtain ⟨vZ, b, lengths, hvZ, hedges, hall⟩ := hP v hv
  refine ⟨vZ, b, hvZ, ?_⟩
  intro t ht
  by_cases hn : n = 0
  · subst n
    exact (Subsingleton.elim v (v + ∑ i, t i • integralBasisReal b i)) ▸ hv.1
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    apply PaperVerification.Toric.unit_corner_box_of_long_segments hnpos P.carrier
      (convex_convexHull ℝ _) v hv.1 (integralBasisReal b)
      (fun i => (lengths i : ℝ)) ?_ ?_ t ht
    · intro i
      have hbound := P.edge_basis_length_bound hlength vZ b i (lengths i)
        (by simpa only [hvZ] using (hedges i).2)
      exact_mod_cast hbound
    · intro i
      have hmem := (P.edge_endpoints_extreme (hedges i).2).2.1
      have he : embed n (vZ + (lengths i : ℤ) • b i) =
          v + (lengths i : ℝ) • integralBasisReal b i := by
        rw [map_add, hvZ, integralBasisReal_apply]
        ext j
        simp [embed, Int.cast_mul]
      rwa [he] at hmem

end LatticePolytope

end PaperVerification.ToricGeometry
end
end Source_ToricIntegralBasis
-- END ORIGINAL PaperVerification.ToricIntegralBasis


-- BEGIN ORIGINAL PaperVerification.ToricFanFoundations
section Source_ToricFanFoundations

-- original header: module
-- original header: public import PaperVerification.ToricIntegralBasis
-- original header: public import Mathlib.Geometry.Convex.Cone.Face.Basic
-- original header: public import Mathlib.Tactic.Linarith
-- original header: @[expose] public section
/-!
# Actual finite smooth complete fans

Cones are genuine nonnegative real spans of finite lattice-vector sets.
The intersection axiom is equality of those actual cones, and smoothness
means that the ray generators form a subset of an integral basis. The
definition carries no primitive-relation or contraction conclusion.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical
open Set

section FiniteCones

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

/-- The genuine nonnegative real span of a finite vector family. -/
def finiteRayCone (s : Finset E) : PointedCone ℝ E :=
  PointedCone.ofConeComb
    {x | ∃ c : E → ℝ, (∀ v ∈ s, 0 ≤ c v) ∧ ∑ v ∈ s, c v • v = x}
    ⟨0, fun _ => 0, by simp⟩ (by
      rintro x ⟨c, hc, hcx⟩ y ⟨d, hd, hdy⟩ a ha b hb
      refine ⟨fun v => a * c v + b * d v, ?_, ?_⟩
      · intro v hv
        exact add_nonneg (mul_nonneg ha (hc v hv)) (mul_nonneg hb (hd v hv))
      · simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum,
          hcx, hdy])

theorem finiteRayCone_generator (s : Finset E) {v : E} (hv : v ∈ s) :
    v ∈ finiteRayCone s := by
  classical
  refine ⟨Pi.single v (1 : ℝ), ?_, ?_⟩
  · intro w hw
    by_cases hwv : w = v <;> simp [Pi.single_apply, hwv]
  · simp [Pi.single_apply, ite_smul, hv]

/-- The explicit finite-combination definition agrees with Mathlib's conic hull. -/
theorem finiteRayCone_eq_hull (s : Finset E) :
    finiteRayCone s = PointedCone.hull ℝ (s : Set E) := by
  apply le_antisymm
  · rintro x ⟨c, hc, hcx⟩
    rw [← hcx]
    exact Submodule.sum_mem _ (fun v hv =>
      PointedCone.smul_mem _ (hc v hv) (PointedCone.subset_hull hv))
  · exact Submodule.span_le.mpr (fun v hv => finiteRayCone_generator s hv)

theorem finiteRayCone_mono {s t : Finset E} (hst : s ⊆ t) :
    finiteRayCone s ≤ finiteRayCone t := by
  rw [finiteRayCone_eq_hull, finiteRayCone_eq_hull]
  exact Submodule.span_mono hst

@[simp] theorem finiteRayCone_empty : finiteRayCone (∅ : Finset E) = ⊥ := by
  rw [finiteRayCone_eq_hull, Finset.coe_empty]
  exact Submodule.span_empty (R := Nonneg ℝ) (M := E)

/-- Coordinates in a cone on a basis subset are nonnegative and vanish exactly
outside that subset. -/
theorem mem_finiteRayCone_basis_iff (b : Module.Basis ι ℝ E) (I : Finset ι) (x : E) :
    x ∈ finiteRayCone (I.image b) ↔
      (∀ i, 0 ≤ b.repr x i) ∧ (∀ i ∉ I, b.repr x i = 0) := by
  classical
  constructor
  · rintro ⟨c, hc, hcx⟩
    have hcoord (i : ι) : b.repr x i = if i ∈ I then c (b i) else 0 := by
      rw [← hcx, Finset.sum_image]
      · simp [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
          Finsupp.single_apply, smul_eq_mul]
      · exact fun a _ b' _ hab => b.injective hab
    constructor
    · intro i
      rw [hcoord]
      split_ifs with hi
      · exact hc (b i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      · exact le_rfl
    · intro i hi
      rw [hcoord, if_neg hi]
  · rintro ⟨hxpos, hxzero⟩
    let c : E → ℝ := fun z => ∑ j, b.repr x j * b.repr z j
    have hc (i : ι) : c (b i) = b.repr x i := by
      simp [c, Finsupp.single_apply, mul_ite]
    refine ⟨c, ?_, ?_⟩
    · rintro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      rw [hc]
      exact hxpos i
    · rw [Finset.sum_image]
      · simp only [hc]
        calc
          (∑ i ∈ I, b.repr x i • b i) = ∑ i, b.repr x i • b i := by
            apply Finset.sum_subset (Finset.subset_univ I)
            intro i _ hi
            rw [hxzero i hi, zero_smul]
          _ = x := b.sum_repr x
      · exact fun a _ b' _ hab => b.injective hab

/-- Every coordinate subcone is an actual face of the larger basis cone. -/
theorem finiteRayCone_basis_isFaceOf (b : Module.Basis ι ℝ E)
    {I J : Finset ι} (hIJ : I ⊆ J) :
    (finiteRayCone (I.image b)).IsFaceOf (finiteRayCone (J.image b)) := by
  refine ⟨finiteRayCone_mono (Finset.image_subset_image hIJ), ?_⟩
  intro x y a hx hy ha hxy
  obtain ⟨hxpos, hxzero⟩ := (mem_finiteRayCone_basis_iff b J x).mp hx
  obtain ⟨hypos, hyzero⟩ := (mem_finiteRayCone_basis_iff b J y).mp hy
  obtain ⟨hxypos, hxyzero⟩ := (mem_finiteRayCone_basis_iff b I (a • x + y)).mp hxy
  apply (mem_finiteRayCone_basis_iff b I x).mpr
  refine ⟨hxpos, ?_⟩
  intro i hi
  have hz := hxyzero i hi
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hz
  have hxi := hxpos i
  have hyi := hypos i
  nlinarith

/-- Intersections of coordinate cones in one basis are exactly the cones on
their common coordinates. -/
theorem finiteRayCone_basis_inter (b : Module.Basis ι ℝ E) (I J : Finset ι) :
    finiteRayCone (I.image b) ⊓ finiteRayCone (J.image b) =
      finiteRayCone ((I ∩ J).image b) := by
  ext x
  simp only [Submodule.mem_inf, mem_finiteRayCone_basis_iff]
  constructor
  · rintro ⟨⟨hx, hI⟩, ⟨_, hJ⟩⟩
    refine ⟨hx, ?_⟩
    intro i hi
    by_cases hiI : i ∈ I
    · exact hJ i (fun hiJ => hi (Finset.mem_inter.mpr ⟨hiI, hiJ⟩))
    · exact hI i hiI
  · rintro ⟨hx, hIJ⟩
    refine ⟨⟨hx, ?_⟩, ⟨hx, ?_⟩⟩
    · intro i hi
      exact hIJ i (fun h => hi (Finset.mem_inter.mp h).1)
    · intro i hi
      exact hIJ i (fun h => hi (Finset.mem_inter.mp h).2)

end FiniteCones

/-- The actual real cone generated by a finite set of integer rays. -/
def latticeRayCone {n : ℕ} (s : Finset (Lattice n)) : PointedCone ℝ (Ambient n) :=
  finiteRayCone (s.image (embed n))

theorem latticeRayCone_generator {n : ℕ} (s : Finset (Lattice n))
    {v : Lattice n} (hv : v ∈ s) : embed n v ∈ latticeRayCone s :=
  finiteRayCone_generator _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)

theorem latticeRayCone_mono {n : ℕ} {s t : Finset (Lattice n)} (hst : s ⊆ t) :
    latticeRayCone s ≤ latticeRayCone t :=
  finiteRayCone_mono (Finset.image_subset_image hst)

@[simp] theorem latticeRayCone_empty {n : ℕ} :
    latticeRayCone (∅ : Finset (Lattice n)) = ⊥ := by
  simp [latticeRayCone]

theorem latticeRayCone_basis {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) :
    latticeRayCone (I.image b) = finiteRayCone (I.image (integralBasisReal b)) := by
  change finiteRayCone ((I.image b).image (embed n)) = _
  congr 1
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨z, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, integralBasisReal_apply b i⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨b i, ⟨i, hi, rfl⟩, (integralBasisReal_apply b i).symm⟩

/-- Membership in a cone on an integral basis is exactly nonnegativity of
the real coordinates, with zero coordinates outside the chosen subset. -/
theorem mem_latticeRayCone_basis_iff {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (x : Ambient n) :
    x ∈ latticeRayCone (I.image b) ↔
      (∀ i, 0 ≤ (integralBasisReal b).repr x i) ∧
        (∀ i ∉ I, (integralBasisReal b).repr x i = 0) := by
  rw [latticeRayCone_basis]
  have hI : I.image (integralBasisReal b) =
      @Finset.image (Fin n) (Ambient n)
        (fun (a b : Ambient n) => Classical.propDecidable (a = b))
        (integralBasisReal b) I := by
    ext y
    simp only [Finset.mem_image]
  rw [hI]
  exact mem_finiteRayCone_basis_iff (integralBasisReal b) I x

/-- A finite smooth complete fan, stated entirely in terms of actual lattice
rays and actual cones. Every cone is a subset of a genuine integral basis;
intersections agree with their common-ray faces, and all real vectors are covered. -/
structure SmoothCompleteFan (n : ℕ) where
  cones : Finset (Finset (Lattice n))
  smooth : ∀ s ∈ cones, ∃ (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)), s = I.image b
  downward : ∀ s ∈ cones, ∀ t, t ⊆ s → t ∈ cones
  intersection : ∀ s ∈ cones, ∀ t ∈ cones,
    latticeRayCone s ⊓ latticeRayCone t = latticeRayCone (s ∩ t)
  complete : ∀ x : Ambient n, ∃ s ∈ cones, x ∈ latticeRayCone s

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Every cone is contained in a cone with the full ambient number of rays.
This property is derived for normal fans and preserved by subdivision; it
is not included as extra data in `SmoothCompleteFan`. -/
def IsPure : Prop :=
  ∀ s ∈ «Σ».cones, ∃ u ∈ «Σ».cones, s ⊆ u ∧ u.card = n

/-- A full-dimensional smooth cone has the whole of a genuine integral
basis as its ray set. -/
theorem full_cone_basis {s : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hcard : s.card = n) :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n), s = Finset.univ.image b := by
  obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
  rw [Finset.card_image_of_injective I b.injective] at hcard
  have hI : I = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ I)
    simpa only [Finset.card_fin, hcard] using (le_rfl : n ≤ n)
  exact ⟨b, by rw [hI]⟩

/-- The actual collection of real cones represented by the finite fan. -/
def realCones : Set (Set (Ambient n)) :=
  {C | ∃ s ∈ «Σ».cones, C = (latticeRayCone s : Set (Ambient n))}

/-- The finite set of primitive ray generators occurring in the fan. -/
def rays : Finset (Lattice n) := «Σ».cones.biUnion id

theorem mem_rays_iff (v : Lattice n) :
    v ∈ «Σ».rays ↔ ∃ s ∈ «Σ».cones, v ∈ s := by
  classical
  simp [rays]

theorem empty_mem : (∅ : Finset (Lattice n)) ∈ «Σ».cones := by
  obtain ⟨s, hs, hx⟩ := «Σ».complete 0
  exact «Σ».downward s hs ∅ (Finset.empty_subset s)

theorem singleton_mem_of_mem_rays {v : Lattice n} (hv : v ∈ «Σ».rays) :
    {v} ∈ «Σ».cones := by
  obtain ⟨s, hs, hvs⟩ := («Σ».mem_rays_iff v).mp hv
  exact «Σ».downward s hs {v} (Finset.singleton_subset_iff.mpr hvs)

/-- Every nonempty finite intersection of actual fan cones is an actual cone
of the same fan. The nonempty condition avoids introducing the whole ambient
space as an extra cone. -/
theorem exists_cone_finite_intersection {κ : Type*}
    (K : Finset κ) (t : κ → Finset (Lattice n)) :
    K.Nonempty → (∀ i ∈ K, t i ∈ «Σ».cones) →
      ∃ s ∈ «Σ».cones, ∀ x : Ambient n,
        x ∈ latticeRayCone s ↔ ∀ i ∈ K, x ∈ latticeRayCone (t i) := by
  classical
  induction K using Finset.induction_on with
  | empty => simp
  | @insert i K hi ih =>
    intro hne hmem
    have hti : t i ∈ «Σ».cones := hmem i (Finset.mem_insert_self i K)
    by_cases hK : K.Nonempty
    · obtain ⟨s, hs, hspec⟩ := ih hK
        (fun j hj => hmem j (Finset.mem_insert_of_mem hj))
      refine ⟨t i ∩ s, «Σ».downward (t i) hti _ Finset.inter_subset_left, ?_⟩
      intro x
      rw [← «Σ».intersection (t i) hti s hs]
      simp only [Submodule.mem_inf, hspec x, Finset.forall_mem_insert]
    · have hempty : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
      subst K
      exact ⟨t i, hti, by simp⟩

theorem ray_ne_zero {v : Lattice n} (hv : v ∈ «Σ».rays) : v ≠ 0 := by
  obtain ⟨s, hs, hvs⟩ := («Σ».mem_rays_iff v).mp hv
  obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hvs
  exact b.ne_zero i

/-- Every listed ray is primitive in the actual ambient integer lattice. -/
theorem ray_gcd_eq_one {v : Lattice n} (hv : v ∈ «Σ».rays) :
    Finset.univ.gcd (fun i : Fin n => (v i).natAbs) = 1 := by
  obtain ⟨s, hs, hvs⟩ := («Σ».mem_rays_iff v).mp hv
  obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hvs
  exact lattice_basis_vector_gcd_one b i

/-- A subset of the rays of a smooth cone generates an actual face of it. -/
theorem cone_subset_isFaceOf {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) :
    PointedCone.IsFaceOf (R := ℝ) (M := Ambient n)
      (latticeRayCone t) (latticeRayCone s) := by
  classical
  obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
  let J := I.filter (fun i => b i ∈ t)
  have hJ : J.image b = t := by
    ext v
    constructor
    · rintro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hi).2
    · intro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hts hv)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hv⟩, rfl⟩
  have hK (K : Finset (Fin n)) :
      finiteRayCone (@Finset.image (Fin n) (Ambient n)
        (fun (x y : Ambient n) => Classical.propDecidable (x = y))
        (integralBasisReal b) K) = latticeRayCone (K.image b) := by
    ext x
    exact (mem_finiteRayCone_basis_iff (integralBasisReal b) K x).trans
      (mem_latticeRayCone_basis_iff b K x).symm
  have hface := finiteRayCone_basis_isFaceOf (integralBasisReal b)
    (I := J) (J := I) (Finset.filter_subset (fun i => b i ∈ t) I)
  rw [hK J, hK I, hJ] at hface
  exact hface

/-- A ray of the fan lies in a fan cone precisely when it is one of that
cone's listed primitive rays. This follows from actual cone intersections. -/
theorem ray_mem_cone_iff {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones)
    {v : Lattice n} (hv : v ∈ «Σ».rays) : embed n v ∈ latticeRayCone s ↔ v ∈ s := by
  constructor
  · intro hvin
    by_contra hnot
    have hsing := «Σ».singleton_mem_of_mem_rays hv
    have hmeet : embed n v ∈ latticeRayCone ({v} ∩ s) := by
      rw [← «Σ».intersection {v} hsing s hs]
      exact ⟨latticeRayCone_generator {v} (Finset.mem_singleton_self v), hvin⟩
    have hempty : ({v} : Finset (Lattice n)) ∩ s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨hwv, hws⟩ := Finset.mem_inter.mp hw
      exact hnot ((Finset.mem_singleton.mp hwv) ▸ hws)
    rw [hempty, latticeRayCone_empty] at hmeet
    have hz : embed n v = 0 := (Submodule.mem_bot (Nonneg ℝ)).mp hmeet
    exact «Σ».ray_ne_zero hv ((embed_injective n) (by simpa using hz))
  · exact latticeRayCone_generator s

/-- The positive sum of all rays of a fan cone can lie in another cone only
when every one of those rays lies in the other cone. -/
theorem sum_mem_cone_implies_subset {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones)
    (hsum : (∑ v ∈ s, embed n v) ∈ latticeRayCone t) : s ⊆ t := by
  classical
  have hsumS : (∑ v ∈ s, embed n v) ∈ latticeRayCone s :=
    Submodule.sum_mem _ (fun v hv => latticeRayCone_generator s hv)
  have hmeet : (∑ v ∈ s, embed n v) ∈ latticeRayCone (s ∩ t) := by
    rw [← «Σ».intersection s hs t ht]
    exact ⟨hsumS, hsum⟩
  have hface := «Σ».cone_subset_isFaceOf hs (Finset.inter_subset_left : s ∩ t ⊆ s)
  intro v hv
  have hvmeet : embed n v ∈ latticeRayCone (s ∩ t) := by
    have hrest : (∑ w ∈ s.erase v, embed n w) ∈ latticeRayCone s :=
      Submodule.sum_mem _ (fun w hw =>
        latticeRayCone_generator s (Finset.mem_of_mem_erase hw))
    apply hface.mem_of_add_mem_left (latticeRayCone_generator s hv) hrest
    simpa only [Finset.add_sum_erase s (fun w => embed n w) hv] using hmeet
  have hvrays : v ∈ «Σ».rays := («Σ».mem_rays_iff v).mpr ⟨s, hs, hv⟩
  have hvin : v ∈ s ∩ t := («Σ».ray_mem_cone_iff
    («Σ».downward s hs (s ∩ t) Finset.inter_subset_left) hvrays).mp hvmeet
  exact (Finset.mem_inter.mp hvin).2

/-- The same support implication for every strictly positive real weighting
of the source cone's rays. This characterizes its relative interior support. -/
theorem positive_sum_mem_cone_implies_subset {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones) (c : Lattice n → ℝ)
    (hc : ∀ v ∈ s, 0 < c v)
    (hsum : (∑ v ∈ s, c v • embed n v) ∈ latticeRayCone t) : s ⊆ t := by
  classical
  have hsumS : (∑ v ∈ s, c v • embed n v) ∈ latticeRayCone s :=
    Submodule.sum_mem _ (fun v hv =>
      PointedCone.smul_mem _ (hc v hv).le (latticeRayCone_generator s hv))
  have hmeet : (∑ v ∈ s, c v • embed n v) ∈ latticeRayCone (s ∩ t) := by
    rw [← «Σ».intersection s hs t ht]
    exact ⟨hsumS, hsum⟩
  have hface := «Σ».cone_subset_isFaceOf hs (Finset.inter_subset_left : s ∩ t ⊆ s)
  intro v hv
  have hvmeet : embed n v ∈ latticeRayCone (s ∩ t) := by
    have hrest : (∑ w ∈ s.erase v, c w • embed n w) ∈ latticeRayCone s :=
      Submodule.sum_mem _ (fun w hw =>
        PointedCone.smul_mem _ (hc w (Finset.mem_of_mem_erase hw)).le
          (latticeRayCone_generator s (Finset.mem_of_mem_erase hw)))
    apply hface.mem_of_smul_add_mem (latticeRayCone_generator s hv) hrest (hc v hv)
    simpa only [Finset.add_sum_erase s (fun w => c w • embed n w) hv] using hmeet
  have hvrays : v ∈ «Σ».rays := («Σ».mem_rays_iff v).mpr ⟨s, hs, hv⟩
  have hvin : v ∈ s ∩ t := («Σ».ray_mem_cone_iff
    («Σ».downward s hs (s ∩ t) Finset.inter_subset_left) hvrays).mp hvmeet
  exact (Finset.mem_inter.mp hvin).2

/-- Every integer vector has a positive integral expansion on the rays of
some cone. The cone may be the zero cone. Integrality follows from an actual
integral basis; completeness alone would only supply real coefficients. -/
theorem exists_positive_integral_cone_expansion (z : Lattice n) :
    ∃ t ∈ «Σ».cones, ∃ c : Lattice n → ℕ,
      (∀ v ∈ t, 0 < c v) ∧ ∑ v ∈ t, (c v : ℤ) • v = z := by
  classical
  obtain ⟨s, hs, hz⟩ := «Σ».complete (embed n z)
  obtain ⟨b, I, hI⟩ := «Σ».smooth s hs
  have hz' : embed n z ∈ latticeRayCone (I.image b) := by
    rw [← hI]
    exact hz
  obtain ⟨hpos, hzero⟩ := (mem_latticeRayCone_basis_iff b I (embed n z)).mp hz'
  have hposZ (i : Fin n) : 0 ≤ b.repr z i := by
    have h := hpos i
    rw [integralBasisReal_repr] at h
    exact_mod_cast h
  have hzeroZ (i : Fin n) (hi : i ∉ I) : b.repr z i = 0 := by
    have h := hzero i hi
    rw [integralBasisReal_repr] at h
    exact Int.cast_eq_zero.mp h
  have hcast (i : Fin n) : ((b.repr z i).toNat : ℤ) = b.repr z i :=
    Int.toNat_of_nonneg (hposZ i)
  let J := I.filter (fun i => 0 < b.repr z i)
  let t := J.image b
  let c : Lattice n → ℕ := fun v => ∑ i, (b.repr z i).toNat * (b.repr v i).toNat
  have hc (i : Fin n) : c (b i) = (b.repr z i).toNat := by
    simp [c, Finsupp.single_apply, apply_ite, mul_ite]
  have ht : t ∈ «Σ».cones := by
    apply «Σ».downward s hs t
    rw [hI]
    exact Finset.image_subset_image (Finset.filter_subset _ _)
  refine ⟨t, ht, c, ?_, ?_⟩
  · intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    rw [hc]
    have h := (Finset.mem_filter.mp hi).2
    omega
  · rw [Finset.sum_image]
    · simp only [hc, hcast]
      calc
        (∑ i ∈ J, b.repr z i • b i) = ∑ i, b.repr z i • b i := by
          apply Finset.sum_subset (Finset.subset_univ J)
          intro i _ hi
          have hzi : b.repr z i = 0 := by
            by_cases hiI : i ∈ I
            · have hnot : ¬ 0 < b.repr z i := by
                intro hp
                exact hi (Finset.mem_filter.mpr ⟨hiI, hp⟩)
              exact le_antisymm (le_of_not_gt hnot) (hposZ i)
            · exact hzeroZ i hiI
          rw [hzi, zero_smul]
        _ = z := b.sum_repr z
    · exact fun i _ j _ hij => b.injective hij

/-- Smooth cones have at most the ambient dimension many rays. -/
theorem card_cone_le {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) : s.card ≤ n := by
  obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
  rw [Finset.card_image_of_injective I b.injective]
  calc
    I.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ I)
    _ = n := Finset.card_fin n

/-- A primitive collection is an inclusion-minimal collection of rays that
does not generate a cone of the fan. -/
def IsPrimitiveCollection (P : Finset (Lattice n)) : Prop :=
  P ⊆ «Σ».rays ∧ P ∉ «Σ».cones ∧ ∀ S, S ⊂ P → S ∈ «Σ».cones

theorem primitiveCollection_nonempty {P : Finset (Lattice n)}
    (hP : «Σ».IsPrimitiveCollection P) : P.Nonempty := by
  by_contra h
  have hzero := Finset.not_nonempty_iff_eq_empty.mp h
  exact hP.2.1 (hzero.symm ▸ «Σ».empty_mem)

theorem primitiveCollection_card_bounds {P : Finset (Lattice n)}
    (hP : «Σ».IsPrimitiveCollection P) : 2 ≤ P.card ∧ P.card ≤ n + 1 := by
  classical
  obtain ⟨v, hv⟩ := «Σ».primitiveCollection_nonempty hP
  have herase : P.erase v ∈ «Σ».cones := hP.2.2 _ (Finset.erase_ssubset hv)
  have hcard := «Σ».card_cone_le herase
  have hneone : P.card ≠ 1 := by
    intro hone
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hone
    have hwrays : w ∈ «Σ».rays := hP.1 (hw.symm ▸ Finset.mem_singleton_self w)
    exact hP.2.1 (hw.symm ▸ «Σ».singleton_mem_of_mem_rays hwrays)
  have hpos := Finset.card_pos.mpr ⟨v, hv⟩
  rw [Finset.card_erase_of_mem hv] at hcard
  omega

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricFanFoundations
-- END ORIGINAL PaperVerification.ToricFanFoundations


-- BEGIN ORIGINAL PaperVerification.ToricPrimitiveRelations
section Source_ToricPrimitiveRelations

-- original header: module
-- original header: public import PaperVerification.ToricFanFoundations
-- original header: public import Mathlib.Algebra.BigOperators.Ring.Finset
-- original header: public import Mathlib.Tactic.Ring
-- original header: @[expose] public section
/-!
# Primitive relations in actual smooth complete fans

A primitive relation is obtained by expanding the sum of a minimal noncone
collection in the unique positive cone of the fan. Positivity and integrality
are proved from completeness and smoothness. Disjointness of its positive and
negative rays is a theorem, not part of the definition.

The combinatorial contractibility condition below is precisely the cone
replacement condition in Casagrande, Theorem 2.2(ii). No equivalence with a
scheme-level contraction is asserted here without a separate proof.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- A primitive relation with genuine positive integral coefficients in its
focus cone. The ray sets need not be assumed disjoint. -/
structure PrimitiveRelation where
  positive : Finset (Lattice n)
  negative : Finset (Lattice n)
  coefficient : Lattice n → ℕ
  primitive : «Σ».IsPrimitiveCollection positive
  negative_cone : negative ∈ «Σ».cones
  coefficient_pos : ∀ v ∈ negative, 0 < coefficient v
  equation : ∑ v ∈ positive, v = ∑ v ∈ negative, (coefficient v : ℤ) • v

/-- Every primitive collection has a primitive relation; no relation is
postulated independently of the actual lattice vectors. -/
theorem exists_primitiveRelation {P : Finset (Lattice n)}
    (hP : «Σ».IsPrimitiveCollection P) :
    ∃ R : «Σ».PrimitiveRelation, R.positive = P := by
  obtain ⟨t, ht, c, hc, he⟩ := «Σ».exists_positive_integral_cone_expansion (∑ v ∈ P, v)
  exact ⟨⟨P, t, c, hP, ht, hc, he.symm⟩, rfl⟩

namespace PrimitiveRelation

variable {«Σ»} (R : «Σ».PrimitiveRelation)

/-- A primitive collection is disjoint from the focus of its relation
(Batyrev's primitive-collection disjointness lemma). -/
theorem disjoint : Disjoint R.positive R.negative := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxP hxT
  let P' := R.positive.erase x
  have hP' : P' ∈ «Σ».cones := R.primitive.2.2 _ (Finset.erase_ssubset hxP)
  let d : Lattice n → ℝ := fun v =>
    (R.coefficient v : ℝ) - if v = x then 1 else 0
  have hd (v : Lattice n) (hv : v ∈ R.negative) : 0 ≤ d v := by
    by_cases hvx : v = x
    · subst v
      have hx : (1 : ℝ) ≤ R.coefficient x := by exact_mod_cast R.coefficient_pos x hxT
      simp only [d, if_pos rfl, ite_true]
      linarith
    · simp only [d, if_neg hvx, sub_zero]
      exact Nat.cast_nonneg _
  have he : (∑ v ∈ R.negative, (R.coefficient v : ℝ) • embed n v) =
      ∑ v ∈ R.positive, embed n v := by
    have h := congrArg (embed n) R.equation
    simpa only [map_sum, embed_int_smul, Int.cast_natCast] using h.symm
  have hdsum : (∑ v ∈ R.negative, d v • embed n v) = ∑ v ∈ P', embed n v := by
    calc
      (∑ v ∈ R.negative, d v • embed n v) =
          (∑ v ∈ R.negative, (R.coefficient v : ℝ) • embed n v) - embed n x := by
        simp [d, sub_smul, Finset.sum_sub_distrib, ite_smul, hxT]
      _ = (∑ v ∈ R.positive, embed n v) - embed n x := by rw [he]
      _ = ∑ v ∈ P', embed n v := by
        rw [← Finset.sum_erase_add R.positive (fun v => embed n v) hxP]
        simp [P']
  have hsumCone : (∑ v ∈ P', embed n v) ∈ latticeRayCone R.negative := by
    rw [← hdsum]
    exact Submodule.sum_mem _ (fun v hv =>
      PointedCone.smul_mem _ (hd v hv) (latticeRayCone_generator R.negative hv))
  have hsubset : P' ⊆ R.negative :=
    «Σ».sum_mem_cone_implies_subset hP' R.negative_cone hsumCone
  have hall : R.positive ⊆ R.negative := by
    intro v hv
    by_cases hvx : v = x
    · simpa only [hvx] using hxT
    · exact hsubset (Finset.mem_erase.mpr ⟨hvx, hv⟩)
  exact R.primitive.2.1 («Σ».downward R.negative R.negative_cone R.positive hall)

/-- The positive focus cone is uniquely determined by the primitive collection. -/
theorem negative_unique (S : «Σ».PrimitiveRelation) (hPS : R.positive = S.positive) :
    R.negative = S.negative := by
  have hincl (R S : «Σ».PrimitiveRelation) (hPS : R.positive = S.positive) :
      R.negative ⊆ S.negative := by
    have he : (∑ v ∈ R.negative, (R.coefficient v : ℝ) • embed n v) =
        ∑ v ∈ S.negative, (S.coefficient v : ℝ) • embed n v := by
      have hZ : (∑ v ∈ R.negative, (R.coefficient v : ℤ) • v) =
          ∑ v ∈ S.negative, (S.coefficient v : ℤ) • v := by
        rw [← R.equation, ← S.equation, hPS]
      simpa only [map_sum, embed_int_smul, Int.cast_natCast] using congrArg (embed n) hZ
    apply «Σ».positive_sum_mem_cone_implies_subset R.negative_cone S.negative_cone
      (fun v => (R.coefficient v : ℝ)) (fun v hv => by exact_mod_cast R.coefficient_pos v hv)
    rw [he]
    exact Submodule.sum_mem _ (fun v hv => PointedCone.smul_mem _ (Nat.cast_nonneg _)
      (latticeRayCone_generator S.negative hv))
  exact Finset.Subset.antisymm (hincl R S hPS) (hincl S R hPS.symm)

/-- The positive integer coefficients on the focus are unique as well.
They are read off in a genuine integral basis containing that cone. -/
theorem coefficient_unique_on_negative (S : «Σ».PrimitiveRelation)
    (hPS : R.positive = S.positive) {v : Lattice n} (hv : v ∈ R.negative) :
    R.coefficient v = S.coefficient v := by
  have hN := R.negative_unique S hPS
  obtain ⟨b, I, hI⟩ := «Σ».smooth R.negative R.negative_cone
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (hI ▸ hv)
  have hsum (c : Lattice n → ℕ) :
      b.repr (∑ v ∈ R.negative, (c v : ℤ) • v) j = (c (b j) : ℤ) := by
    rw [hI, Finset.sum_image]
    · simp only [map_sum, LinearEquiv.map_smul, Finsupp.finsetSum_apply,
        Finsupp.smul_apply, Module.Basis.repr_self_apply]
      simp [hj, smul_eq_mul]
    · exact fun i _ k _ hik => b.injective hik
  have he : (∑ v ∈ R.negative, (R.coefficient v : ℤ) • v) =
      ∑ v ∈ R.negative, (S.coefficient v : ℤ) • v := by
    rw [R.equation.symm, hN, S.equation.symm, hPS]
  have hc := congrArg (fun z : Lattice n => b.repr z j) he
  rw [hsum, hsum] at hc
  exact_mod_cast hc

/-- The number `r` in the manuscript's relation `x₀+...+xᵣ = Σ aⱼyⱼ`. -/
def fiberDimension : ℕ := R.positive.card - 1

theorem fiberDimension_pos : 1 ≤ R.fiberDimension := by
  have h := («Σ».primitiveCollection_card_bounds R.primitive).1
  unfold fiberDimension
  omega

/-- The exact combinatorial replacement condition used in the contraction
theorem. It is a condition on all actual cones of the fan. -/
def IsCombinatoriallyContractible : Prop :=
  ∀ ν ∈ «Σ».cones, Disjoint ν (R.positive ∪ R.negative) →
    R.negative ∪ ν ∈ «Σ».cones → ∀ x ∈ R.positive,
      (R.positive.erase x) ∪ R.negative ∪ ν ∈ «Σ».cones

/-- The core negative rays and all but one positive ray form a genuine cone
for every combinatorially contractible relation. -/
theorem contractible_core_cone (hR : R.IsCombinatoriallyContractible)
    {x : Lattice n} (hx : x ∈ R.positive) :
    R.positive.erase x ∪ R.negative ∈ «Σ».cones := by
  simpa only [Finset.union_empty] using
    hR ∅ «Σ».empty_mem (Finset.disjoint_empty_left _) (by simpa using R.negative_cone) x hx

/-- The dimension inequality `r+q≤n` follows from a genuine smooth cone and
the proved disjointness, rather than being included as relation data. -/
theorem contractible_dimension_bound (hR : R.IsCombinatoriallyContractible) :
    R.fiberDimension + R.negative.card ≤ n := by
  obtain ⟨x, hx⟩ := «Σ».primitiveCollection_nonempty R.primitive
  have h := «Σ».card_cone_le (R.contractible_core_cone hR hx)
  rw [Finset.card_union_of_disjoint
    (R.disjoint.mono_left (Finset.erase_subset x R.positive)),
    Finset.card_erase_of_mem hx] at h
  exact h

/-- No cone contains the entire positive primitive collection. Consequently
it contains at most `r` positive rays. -/
theorem positive_rays_in_cone_bound {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) :
    (R.positive ∩ s).card ≤ R.fiberDimension := by
  have hproper : R.positive ∩ s ⊂ R.positive := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
    intro heq
    have hsub : R.positive ⊆ s := by
      rw [← heq]
      exact Finset.inter_subset_right
    exact R.primitive.2.1 («Σ».downward s hs R.positive hsub)
  have hcard := Finset.card_lt_card hproper
  unfold fiberDimension
  omega

/-- Pairing the primitive relation with arbitrary real invariant divisor
coefficients. This is the actual displayed coefficient pairing. -/
def degree (a : Lattice n → ℝ) : ℝ :=
  (∑ v ∈ R.positive, a v) - ∑ v ∈ R.negative, (R.coefficient v : ℝ) * a v

theorem degree_unique (S : «Σ».PrimitiveRelation) (hP : R.positive = S.positive)
    (a : Lattice n → ℝ) : R.degree a = S.degree a := by
  have hN := R.negative_unique S hP
  have hsum : (∑ v ∈ R.negative, (R.coefficient v : ℝ) * a v) =
      ∑ v ∈ R.negative, (S.coefficient v : ℝ) * a v := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [R.coefficient_unique_on_negative S hP hv]
  unfold degree
  rw [hsum, hP, hN]

theorem degree_add (a b : Lattice n → ℝ) : R.degree (a + b) = R.degree a + R.degree b := by
  simp only [degree, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem degree_sub (a b : Lattice n → ℝ) : R.degree (a - b) = R.degree a - R.degree b := by
  simp only [degree, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

theorem degree_smul (t : ℝ) (a : Lattice n → ℝ) :
    R.degree (t • a) = t * R.degree a := by
  simp only [degree, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  ring

/-- A selection of invariant divisors from a cone has relation degree at most
`r`: the cone omits at least one positive ray, and all negative contributions
can only lower the degree. This is the numerical bound in Lemma 3.1. -/
theorem degree_cone_selection_le {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) :
    R.degree (fun v => if v ∈ t then 1 else 0) ≤ R.fiberDimension := by
  have hnegative : 0 ≤ ∑ v ∈ R.negative,
      (R.coefficient v : ℝ) * (if v ∈ t then 1 else 0) := by
    apply Finset.sum_nonneg
    intro v hv
    split_ifs <;> simp
  have hpos : (∑ v ∈ R.positive, if v ∈ t then (1 : ℝ) else 0) =
      ((R.positive ∩ t).card : ℝ) := by
    rw [Finset.sum_boole]
    congr 1
  have hcard : (R.positive ∩ t).card ≤ R.fiberDimension :=
    (Finset.card_le_card (Finset.inter_subset_inter_left hts)).trans
      (R.positive_rays_in_cone_bound hs)
  have hcardR : ((R.positive ∩ t).card : ℝ) ≤ R.fiberDimension := by exact_mod_cast hcard
  unfold degree
  rw [hpos]
  linarith

/-- The corner-criterion hypothesis makes every selected-divisor subtraction
nonnegative on that primitive relation. -/
theorem degree_sub_corner_selection_nonneg {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) (a : Lattice n → ℝ) (side : ℝ)
    (hside : 0 ≤ side) (hdegree : side * R.fiberDimension ≤ R.degree a) :
    0 ≤ R.degree (a - side • (fun v => if v ∈ t then 1 else 0)) := by
  rw [R.degree_sub, R.degree_smul]
  have hbound := mul_le_mul_of_nonneg_left (R.degree_cone_selection_le hs hts) hside
  linarith

end PrimitiveRelation

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricPrimitiveRelations
-- END ORIGINAL PaperVerification.ToricPrimitiveRelations


-- BEGIN ORIGINAL PaperVerification.ToricContractionCones
section Source_ToricContractionCones

-- original header: module
-- original header: public import PaperVerification.ToricPrimitiveRelations
-- original header: public import Mathlib.Data.Finset.SDiff
-- original header: public import Lean.Elab.Tactic.Omega
-- original header: @[expose] public section
/-!
# Cone consequences of the actual contraction replacement condition

The hypotheses below are the explicit cone replacement condition in
Casagrande's theorem. In particular no geometric contraction, dimension
bound, or maximal-cone ray count is built into them.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

/-- A full-dimensional cone containing the negative focus of a contractible
primitive relation contains exactly `r` positive rays. This is the old-fan
part of Lemma 5.1(iii), with actual finite ray sets throughout. -/
theorem positive_count_in_full_cone (hR : R.IsCombinatoriallyContractible)
    {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (hcard : s.card = n)
    (hnegative : R.negative ⊆ s) :
    (R.positive ∩ s).card = R.fiberDimension := by
  let ν := s \ (R.positive ∪ R.negative)
  have hνs : ν ⊆ s := Finset.sdiff_subset
  have hνcone : ν ∈ «Σ».cones := «Σ».downward s hs ν hνs
  have hνdisjoint : Disjoint ν (R.positive ∪ R.negative) := by
    apply Finset.disjoint_left.mpr
    intro v hv hrest
    exact (Finset.mem_sdiff.mp hv).2 hrest
  have hnegativeν : R.negative ∪ ν ∈ «Σ».cones :=
    «Σ».downward s hs _ (Finset.union_subset hnegative hνs)
  obtain ⟨x, hx⟩ := «Σ».primitiveCollection_nonempty R.primitive
  have hexpanded := hR ν hνcone hνdisjoint hnegativeν x hx
  have hdim := «Σ».card_cone_le hexpanded
  have hposneg : Disjoint (R.positive.erase x) R.negative :=
    R.disjoint.mono_left (Finset.erase_subset x R.positive)
  have hcoreν : Disjoint (R.positive.erase x ∪ R.negative) ν := by
    apply Finset.disjoint_left.mpr
    intro v hv hvν
    apply (Finset.mem_sdiff.mp hvν).2
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (Finset.mem_of_mem_erase hv)
    · exact Finset.mem_union_right _ hv
  rw [Finset.card_union_of_disjoint hcoreν,
    Finset.card_union_of_disjoint hposneg,
    Finset.card_erase_of_mem hx] at hdim
  have hpartition : (R.positive ∩ s) ∪ R.negative ∪ ν = s := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · rcases Finset.mem_union.mp hv with hv | hv
        · exact (Finset.mem_inter.mp hv).2
        · exact hnegative hv
      · exact hνs hv
    · intro hv
      by_cases hvP : v ∈ R.positive
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvP, hv⟩))
      · by_cases hvT : v ∈ R.negative
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvT)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, by
            simpa only [Finset.mem_union, not_or] using And.intro hvP hvT⟩)
  have hPT : Disjoint (R.positive ∩ s) R.negative :=
    R.disjoint.mono_left Finset.inter_subset_left
  have hPTν : Disjoint ((R.positive ∩ s) ∪ R.negative) ν := by
    apply Finset.disjoint_left.mpr
    intro v hv hvν
    apply (Finset.mem_sdiff.mp hvν).2
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp hv).1
    · exact Finset.mem_union_right _ hv
  have hcounts : (R.positive ∩ s).card + R.negative.card + ν.card = n := by
    rw [← Finset.card_union_of_disjoint hPT,
      ← Finset.card_union_of_disjoint hPTν, hpartition, hcard]
  have hupper := R.positive_rays_in_cone_bound hs
  unfold fiberDimension at hupper ⊢
  omega

/-- There is a unique positive ray missing from every full cone over the
focus. The assertion is about the full ray set, not merely its cardinality. -/
theorem exists_unique_omitted_positive (hR : R.IsCombinatoriallyContractible)
    {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (hcard : s.card = n)
    (hnegative : R.negative ⊆ s) :
    ∃ x ∈ R.positive, R.positive \ s = {x} := by
  have hcount := R.positive_count_in_full_cone hR hs hcard hnegative
  have hsize := («Σ».primitiveCollection_card_bounds R.primitive).1
  have herase : (R.positive \ s).card = 1 := by
    have hsplit := Finset.card_sdiff_add_card_inter R.positive s
    unfold fiberDimension at hcount
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp herase
  refine ⟨x, ?_, hx⟩
  exact (Finset.mem_sdiff.mp (hx.symm ▸ Finset.mem_singleton_self x)).1

/-- The dimension of the negative focus is bounded by the complementary
fiber dimension, directly from the smooth cone supplied by replacement. -/
theorem focus_card_le_codimension (hR : R.IsCombinatoriallyContractible) :
    R.negative.card ≤ n - R.fiberDimension := by
  have h := R.contractible_dimension_bound hR
  omega

/-- A contraction with fiber dimension equal to the whole ambient dimension
has zero-dimensional focus; this is the numerical first step of the simplex
base case. No projective-space identification is claimed by this lemma. -/
theorem negative_eq_empty_of_fiberDimension_eq (hR : R.IsCombinatoriallyContractible)
    (hr : R.fiberDimension = n) : R.negative = ∅ := by
  apply Finset.card_eq_zero.mp
  have h := R.contractible_dimension_bound hR
  omega

end SmoothCompleteFan.PrimitiveRelation

end PaperVerification.ToricGeometry
end
end Source_ToricContractionCones
-- END ORIGINAL PaperVerification.ToricContractionCones


-- BEGIN ORIGINAL PaperVerification.ToricBasisBoxFamily
section Source_ToricBasisBoxFamily

-- original header: module
-- original header: public import PaperVerification.ToricBoxAverages
-- original header: public import Mathlib.LinearAlgebra.Basis.Defs
-- original header: public import Mathlib.Data.Fintype.EquivFin
-- original header: @[expose] public section
/-!
# A finite family of genuine basis boxes

This packages the column-configuration form of the lattice-covering theorem
for a finite family of unrelated real bases. The selected column subsets are
proved to be genuine bases, and their zonotopes are identified with the
ordinary unit boxes in the given basis coordinates.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped BigOperators

variable {J : Type*} [Fintype J] {d : ℕ}

/-- A point in the convex hull of a finite family has a probability vector on
the whole index type, with zero coefficients on unused indices. -/
theorem exists_probability_of_mem_convexHull_range {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : J → E) {x : E}
    (hx : x ∈ convexHull ℝ (Set.range v)) :
    ∃ p : J → ℝ, (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧ ∑ j, p j • v j = x := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s, w, hw, hsum, hcomb⟩ := hx
  let p : J → ℝ := fun j => if j ∈ s then w j else 0
  have hp : ∀ j, 0 ≤ p j := by
    intro j
    by_cases hj : j ∈ s
    · simpa [p, hj] using hw j hj
    · simp [p, hj]
  refine ⟨p, hp, ?_, ?_⟩
  · simpa [p, Finset.sum_ite_mem] using hsum
  · rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum] at hcomb
    simpa [p, ite_smul, Finset.sum_ite_mem] using hcomb

def familyIndexEquiv : (J × Fin d) ≃ Fin (Fintype.card (J × Fin d)) :=
  Fintype.equivFin _

def familyMatrix (b : J → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) :
    Matrix (Fin d) (Fin (Fintype.card (J × Fin d))) ℝ :=
  fun i k => b (familyIndexEquiv.symm k).1 (familyIndexEquiv.symm k).2 i

def familySubset (j : J) : Finset (Fin (Fintype.card (J × Fin d))) :=
  Finset.univ.image (fun i : Fin d => familyIndexEquiv (j, i))

theorem familyIndex_injective (j : J) :
    Function.Injective (fun i : Fin d => familyIndexEquiv (j, i)) := by
  intro i k hik
  exact congrArg Prod.snd (familyIndexEquiv.injective hik)

@[simp] theorem familySubset_card (j : J) : (familySubset (d := d) j).card = d := by
  rw [familySubset, Finset.card_image_of_injective _ (familyIndex_injective j)]
  simp

theorem mem_familySubset (j : J) (k : Fin (Fintype.card (J × Fin d))) :
    k ∈ familySubset j ↔ ∃ i : Fin d, familyIndexEquiv (j, i) = k := by
  simp [familySubset]

@[simp] theorem familyMatrix_column
    (b : J → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (j : J) (i : Fin d) :
    matrixColumn (familyMatrix b) (familyIndexEquiv (j, i)) = b j i := by
  ext k
  simp [matrixColumn, familyMatrix, familyIndexEquiv]

/-- Each selected column subset is a genuine full real basis. -/
theorem familySubset_squaredMinor_pos
    (b : J → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (j : J) :
    0 < squaredMinor (familyMatrix b) (familySubset j) := by
  let s := familySubset (d := d) j
  have hs : s.card = d := familySubset_card j
  apply (squaredMinor_pos_iff (familyMatrix b) s).mpr
  refine ⟨hs, ?_⟩
  rw [column_minor_ne_zero_iff_linearIndependent]
  let φ : Fin d → Fin d := fun i => (familyIndexEquiv.symm (s.orderEmbOfFin hs i)).2
  have hfirst (i : Fin d) : (familyIndexEquiv.symm (s.orderEmbOfFin hs i)).1 = j := by
    have himem : s.orderEmbOfFin hs i ∈ familySubset j := s.orderEmbOfFin_mem hs i
    obtain ⟨k, hk⟩ := (mem_familySubset j _).mp himem
    rw [← hk]
    simp
  have hφ : Function.Injective φ := by
    intro i k hik
    apply (s.orderEmbOfFin hs).injective
    apply familyIndexEquiv.symm.injective
    exact Prod.ext (by rw [hfirst, hfirst]) hik
  have hvec (i : Fin d) :
      matrixColumn (familyMatrix b) (s.orderEmbOfFin hs i) = b j (φ i) := by
    have he : s.orderEmbOfFin hs i = familyIndexEquiv (j, φ i) := by
      apply familyIndexEquiv.symm.injective
      simp only [Equiv.symm_apply_apply]
      exact Prod.ext (hfirst i) rfl
    rw [he, familyMatrix_column]
  simpa only [Function.comp_def, hvec] using (b j).linearIndependent.comp φ hφ

/-- The selected global column box is the ordinary unit box in the original basis. -/
theorem familySubsetBox_coordinates
    (b : J → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (j : J)
    {z : EuclideanSpace ℝ (Fin d)}
    (hz : z ∈ SubsetBox (matrixColumn (familyMatrix b)) (familySubset j)) :
    ∃ t : Fin d → ℝ, (∀ i, |t i| ≤ 1 / 2) ∧ ∑ i, t i • b j i = z := by
  classical
  obtain ⟨u, hu, husum⟩ := hz
  let t : Fin d → ℝ := fun i => u (familyIndexEquiv (j, i))
  have ht (i : Fin d) : |t i| ≤ 1 / 2 := by
    have hi : familyIndexEquiv (j, i) ∈ familySubset j :=
      (mem_familySubset j _).mpr ⟨i, rfl⟩
    simpa only [hi, ite_true, t] using hu (familyIndexEquiv (j, i))
  refine ⟨t, ht, ?_⟩
  have hout (k : Fin (Fintype.card (J × Fin d))) (hk : k ∉ familySubset j) : u k = 0 := by
    have h := hu k
    simp only [hk, ite_false, zero_div] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  calc
    (∑ i, t i • b j i) =
        ∑ k ∈ familySubset j, u k • matrixColumn (familyMatrix b) k := by
      rw [familySubset, Finset.sum_image]
      · simp only [familyMatrix_column, t]
      · intro i _ k _ hik
        exact familyIndex_injective j hik
    _ = ∑ k, u k • matrixColumn (familyMatrix b) k := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      simp [hout k hk]
    _ = z := husum

/-- Arbitrary matched integral basis boxes yield a lattice decomposition whenever
the target is a convex combination of their matched centers. -/
theorem finite_basis_boxes_lattice_decomposition
    (b : J → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (Γ : AddSubgroup (EuclideanSpace ℝ (Fin d)))
    (hclosed : IsClosed (Γ : Set (EuclideanSpace ℝ (Fin d))))
    (hbΓ : ∀ j i, b j i ∈ Γ)
    (A B : Set (EuclideanSpace ℝ (Fin d))) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (a c : J → EuclideanSpace ℝ (Fin d))
    (hboxA : ∀ j (t : Fin d → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      a j + ∑ i, t i • b j i ∈ A)
    (hboxB : ∀ j (t : Fin d → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      c j + ∑ i, t i • b j i ∈ B)
    (m : EuclideanSpace ℝ (Fin d)) (hmΓ : m ∈ Γ)
    (hm : m = ∑ j, p j • (a j + c j)) :
    ∃ x ∈ A, ∃ y ∈ B, x ∈ Γ ∧ y ∈ Γ ∧ x + y = m := by
  have hVΓ (k : Fin (Fintype.card (J × Fin d))) : matrixColumn (familyMatrix b) k ∈ Γ := by
    obtain ⟨⟨j, i⟩, rfl⟩ := familyIndexEquiv.surjective k
    simpa only [familyMatrix_column] using hbΓ j i
  apply matched_boxes_lattice_decomposition (familyMatrix b) Γ hclosed hVΓ
    A B hA hB (familySubset (d := d)) (familySubset_squaredMinor_pos b)
    p hp hpsum a c ?_ ?_ m hmΓ hm
  · intro j z hz
    obtain ⟨t, ht, rfl⟩ := familySubsetBox_coordinates b j hz
    exact hboxA j t ht
  · intro j z hz
    obtain ⟨t, ht, rfl⟩ := familySubsetBox_coordinates b j hz
    exact hboxB j t ht

/-- The same finite-family theorem in ordinary real coordinate space. The
change from the Euclidean norm to the usual product norm is made by a genuine
continuous linear equivalence, preserving the subgroup and all box points. -/
theorem finite_basis_boxes_lattice_decomposition_pi
    (b : J → Module.Basis (Fin d) ℝ (Fin d → ℝ))
    (Γ : AddSubgroup (Fin d → ℝ))
    (hclosed : IsClosed (Γ : Set (Fin d → ℝ))) (hbΓ : ∀ j i, b j i ∈ Γ)
    (A B : Set (Fin d → ℝ)) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (a c : J → (Fin d → ℝ))
    (hboxA : ∀ j (t : Fin d → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      a j + ∑ i, t i • b j i ∈ A)
    (hboxB : ∀ j (t : Fin d → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      c j + ∑ i, t i • b j i ∈ B)
    (m : Fin d → ℝ) (hmΓ : m ∈ Γ)
    (hm : m = ∑ j, p j • (a j + c j)) :
    ∃ x ∈ A, ∃ y ∈ B, x ∈ Γ ∧ y ∈ Γ ∧ x + y = m := by
  let e : EuclideanSpace ℝ (Fin d) ≃L[ℝ] (Fin d → ℝ) :=
    EuclideanSpace.equiv (Fin d) ℝ
  let b' : J → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
    fun j => (b j).map e.symm.toLinearEquiv
  let Γ' : AddSubgroup (EuclideanSpace ℝ (Fin d)) :=
    Γ.comap e.toLinearMap.toAddMonoidHom
  have hclosed' : IsClosed (Γ' : Set (EuclideanSpace ℝ (Fin d))) :=
    hclosed.preimage e.continuous
  have hbΓ' (j : J) (i : Fin d) : b' j i ∈ Γ' := by
    change e (b' j i) ∈ Γ
    simpa [b', Module.Basis.map_apply] using hbΓ j i
  have hboxA' (j : J) (t : Fin d → ℝ) (ht : ∀ i, |t i| ≤ 1 / 2) :
      e.symm (a j) + ∑ i, t i • b' j i ∈ e ⁻¹' A := by
    change e (e.symm (a j) + ∑ i, t i • b' j i) ∈ A
    simpa [b', map_add, map_sum, map_smul, Module.Basis.map_apply] using hboxA j t ht
  have hboxB' (j : J) (t : Fin d → ℝ) (ht : ∀ i, |t i| ≤ 1 / 2) :
      e.symm (c j) + ∑ i, t i • b' j i ∈ e ⁻¹' B := by
    change e (e.symm (c j) + ∑ i, t i • b' j i) ∈ B
    simpa [b', map_add, map_sum, map_smul, Module.Basis.map_apply] using hboxB j t ht
  have hm' : e.symm m = ∑ j, p j • (e.symm (a j) + e.symm (c j)) := by
    apply e.injective
    simpa only [map_add, map_sum, map_smul, ContinuousLinearEquiv.apply_symm_apply] using hm
  have hmΓ' : e.symm m ∈ Γ' := by
    change e (e.symm m) ∈ Γ
    simpa using hmΓ
  obtain ⟨x, hx, y, hy, hxΓ, hyΓ, hxy⟩ :=
    finite_basis_boxes_lattice_decomposition b' Γ' hclosed' hbΓ'
      (e ⁻¹' A) (e ⁻¹' B) (hA.linear_preimage e.toLinearMap) (hB.linear_preimage e.toLinearMap)
      p hp hpsum (fun j => e.symm (a j)) (fun j => e.symm (c j))
      hboxA' hboxB' (e.symm m) hmΓ' hm'
  refine ⟨e x, hx, e y, hy, hxΓ, hyΓ, ?_⟩
  simpa only [map_add, ContinuousLinearEquiv.apply_symm_apply] using congrArg e hxy

end PaperVerification.Toric
end
end Source_ToricBasisBoxFamily
-- END ORIGINAL PaperVerification.ToricBasisBoxFamily


-- BEGIN ORIGINAL PaperVerification.ToricShiftedPolytopes
section Source_ToricShiftedPolytopes

-- original header: module
-- original header: public import PaperVerification.ToricIntegralBasis
-- original header: public import Mathlib.Analysis.LocallyConvex.Separation
-- original header: public import Mathlib.Analysis.Convex.Topology
-- original header: @[expose] public section
/-!
# Shifted supporting halfspaces and matched corner centers

The following separation argument proves the center-polytope identity used in
Lemma 4.2. The hypotheses are actual supporting linear functionals and genuine
bases, and the conclusion is equality of ordinary subsets of a real vector space.
The remaining normal-fan construction is independent of this convex argument.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators

variable {E I J K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- The intersection of the specified closed supporting halfspaces. -/
def normalHalfspaces (u : I → E →ₗ[ℝ] ℝ) (a : I → ℝ) : Set E :=
  {x | ∀ i, a i ≤ u i x}

theorem convex_normalHalfspaces (u : I → E →ₗ[ℝ] ℝ) (a : I → ℝ) :
    Convex ℝ (normalHalfspaces u a) := by
  intro x hx y hy r s hr hs hrs i
  simp only [map_add, map_smul, smul_eq_mul]
  have hbound := add_le_add (mul_le_mul_of_nonneg_left (hx i) hr)
    (mul_le_mul_of_nonneg_left (hy i) hs)
  simpa only [← add_mul, hrs, one_mul] using hbound

/-- A finite convex hull is characterized by its lower support values. -/
theorem mem_finite_convexHull_of_lower_support [Finite J] (c : J → E) (x : E)
    (h : ∀ f : E →ₗ[ℝ] ℝ, ∃ j, f (c j) ≤ f x) :
    x ∈ convexHull ℝ (Set.range c) := by
  by_contra hx
  obtain ⟨f, t, hxt, ht⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (Set.range c))
    ((Set.finite_range c).isClosed_convexHull ℝ) hx
  obtain ⟨j, hj⟩ := h f.toLinearMap
  have hjt := ht (c j) (subset_convexHull ℝ _ (Set.mem_range_self j))
  exact (not_lt_of_ge hj) (hxt.trans hjt)

/-- Nonnegative coordinates in a basis cone give the expected lower bound
for every linear functional nonnegative on its generating vectors. -/
theorem linear_le_of_basis_coordinates [Fintype K]
    (b : Module.Basis K ℝ E) (f : E →ₗ[ℝ] ℝ) (c x : E)
    (hf : ∀ i, 0 ≤ f (b i)) (hx : ∀ i, 0 ≤ b.repr (x - c) i) :
    f c ≤ f x := by
  have hsum : f (x - c) = ∑ i, b.repr (x - c) i * f (b i) := by
    conv_lhs => rw [← b.sum_repr (x - c)]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hnonneg : 0 ≤ f (x - c) := by
    rw [hsum]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hx i) (hf i))
  simpa only [map_sub, sub_nonneg] using hnonneg

/-- Feasible Cartier points indexed by a complete collection of basis cones
generate precisely the shifted halfspace polytope. The active supporting
functionals are the dual coordinates of each basis. -/
theorem shifted_halfspaces_eq_convexHull [Finite J] [Fintype K]
    (u : I → E →ₗ[ℝ] ℝ) (a : I → ℝ)
    (b : J → Module.Basis K ℝ E) (active : J → K → I) (c : J → E)
    (hdual : ∀ j i x, u (active j i) x = (b j).repr x i)
    (hcomplete : ∀ f : E →ₗ[ℝ] ℝ, ∃ j, ∀ i, 0 ≤ f (b j i))
    (hactive : ∀ j i, u (active j i) (c j) = a (active j i))
    (hfeasible : ∀ j, c j ∈ normalHalfspaces u a) :
    normalHalfspaces u a = convexHull ℝ (Set.range c) := by
  apply Set.Subset.antisymm
  · intro x hx
    apply mem_finite_convexHull_of_lower_support c x
    intro f
    obtain ⟨j, hj⟩ := hcomplete f
    refine ⟨j, linear_le_of_basis_coordinates (b j) f (c j) x hj ?_⟩
    intro i
    rw [← hdual, map_sub, hactive]
    exact sub_nonneg.mpr (hx (active j i))
  · exact convexHull_min (by rintro _ ⟨j, rfl⟩; exact hfeasible j)
      (convex_normalHalfspaces u a)

/-- A nonzero supporting functional is strictly above its support value at
an interior point. The proof uses the open-map theorem for a surjective real
linear functional, so it applies to the actual topological interior. -/
theorem strict_support_of_interior (u : I → E →ₗ[ℝ] ℝ) (a : I → ℝ)
    (x : E) (hx : x ∈ interior (normalHalfspaces u a)) (i : I) (hi : u i ≠ 0) :
    a i < u i x := by
  have hne : ∃ v : E, u i v ≠ 0 := by
    by_contra h
    apply hi
    ext v
    by_contra hv
    exact h ⟨v, hv⟩
  obtain ⟨v, hv⟩ := hne
  have hsurj : Function.Surjective (u i) := by
    intro r
    refine ⟨(r / u i v) • v, ?_⟩
    simp only [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ r hv
  have hopen := (u i).isOpenMap_of_finiteDimensional hsurj
  have hmaps : Set.MapsTo (u i) (normalHalfspaces u a) (Set.Ici (a i)) :=
    fun y hy => hy i
  have h := hopen.mapsTo_interior hmaps hx
  simpa only [interior_Ici, Set.mem_Ioi] using h

/-- Integrality upgrades strict support to an entire unit of facet slack. -/
theorem integral_support_of_interior {n : ℕ}
    (u : I → Ambient n →ₗ[ℝ] ℝ) (a : I → ℤ)
    (hu : ∀ i z, ∃ k : ℤ, u i (embed n z) = k)
    (hne : ∀ i, u i ≠ 0) (m : Lattice n)
    (hm : embed n m ∈ interior (normalHalfspaces u (fun i => (a i : ℝ)))) :
    ∀ i, (a i : ℝ) + 1 ≤ u i (embed n m) := by
  intro i
  have hstrict := strict_support_of_interior u (fun i => (a i : ℝ))
    (embed n m) hm i (hne i)
  obtain ⟨k, hk⟩ := hu i m
  rw [hk] at hstrict ⊢
  have hki : a i < k := by exact_mod_cast hstrict
  have hki' : a i + 1 ≤ k := by omega
  exact_mod_cast hki'

/-- The center of the unit corner box at a specified vertex. -/
def cornerCenter [Fintype K] (v : E) (b : Module.Basis K ℝ E) : E :=
  v + ∑ i, (1 / 2 : ℝ) • b i

/-- Translation from corner coordinates in `[0,1]` to centered coordinates
in `[-1/2,1/2]` does not change the actual box. -/
theorem cornerCenter_box_mem [Fintype K] (P : Set E)
    (v : E) (b : Module.Basis K ℝ E)
    (hbox : ∀ t : K → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) →
      v + ∑ i, t i • b i ∈ P)
    (t : K → ℝ) (ht : ∀ i, |t i| ≤ 1 / 2) :
    cornerCenter v b + ∑ i, t i • b i ∈ P := by
  have hshift : ∀ i, 0 ≤ 1 / 2 + t i ∧ 1 / 2 + t i ≤ 1 := by
    intro i
    have h := abs_le.mp (ht i)
    constructor <;> linarith
  have h := hbox (fun i => 1 / 2 + t i) hshift
  simpa only [cornerCenter, add_smul, Finset.sum_add_distrib, add_assoc] using h

/-- A corner-box center satisfies all integral supporting inequalities shifted
inward by one half, including normals not incident to its own vertex. -/
theorem integral_cornerCenter_feasible [Fintype K]
    (u : I → E →ₗ[ℝ] ℝ) (a : I → ℝ)
    (v : E) (b : Module.Basis K ℝ E)
    (hu : ∀ i, u i ≠ 0)
    (hint : ∀ i k, ∃ z : ℤ, (z : ℝ) = u i (b k))
    (hbox : ∀ t : K → ℝ, (∀ k, 0 ≤ t k ∧ t k ≤ 1) →
      v + ∑ k, t k • b k ∈ normalHalfspaces u a) :
    cornerCenter v b ∈ normalHalfspaces u (fun i => a i + 1 / 2) := by
  classical
  intro i
  let f : E →ᵃ[ℝ] ℝ := (u i).toAffineMap - AffineMap.const ℝ E (a i)
  have hf : f.linear = u i := by simp [f]
  choose z hz using hint i
  have hboxf : ∀ t : K → ℝ, (∀ k, |t k| ≤ 1 / 2) →
      0 ≤ f (cornerCenter v b + ∑ k, t k • b k) := by
    intro t ht
    have hmem := cornerCenter_box_mem (normalHalfspaces u a) v b hbox t ht
    change 0 ≤ u i (cornerCenter v b + ∑ k, t k • b k) - a i
    exact sub_nonneg.mpr (hmem i)
  have h := PaperVerification.Toric.integral_unit_box_center_slack
    f (by simpa only [hf] using hu i) (cornerCenter v b) b z
    (by simpa only [hf] using hz) hboxf
  change (1 / 2 : ℝ) ≤ u i (cornerCenter v b) - a i at h
  linarith

/-- The active dual coordinate increases by precisely one half at a corner-box
center. This is the Cartier equation behind the shifted-polytope identity. -/
theorem cornerCenter_dual_coordinate [Fintype K] (v : E)
    (b : Module.Basis K ℝ E) (u : E →ₗ[ℝ] ℝ) (k : K)
    (hu : ∀ x, u x = b.repr x k) :
    u (cornerCenter v b) = u v + 1 / 2 := by
  classical
  simp only [cornerCenter, map_add, map_sum, map_smul, smul_eq_mul]
  rw [show (∑ i, (1 / 2 : ℝ) * u (b i)) = 1 / 2 by
    simp [hu, Module.Basis.repr_self, Finsupp.single_apply]]

/-- The exact shifted halfspace description of the convex hull of all unit-box
centers, with every geometric and integrality requirement displayed. -/
theorem corner_centers_convexHull [Finite J] [Fintype K]
    (u : I → E →ₗ[ℝ] ℝ) (a : I → ℝ)
    (v : J → E) (b : J → Module.Basis K ℝ E) (active : J → K → I)
    (hdual : ∀ j k x, u (active j k) x = (b j).repr x k)
    (hcomplete : ∀ f : E →ₗ[ℝ] ℝ, ∃ j, ∀ k, 0 ≤ f (b j k))
    (hactive : ∀ j k, u (active j k) (v j) = a (active j k))
    (hu : ∀ i, u i ≠ 0)
    (hint : ∀ i j k, ∃ z : ℤ, (z : ℝ) = u i (b j k))
    (hbox : ∀ (j : J) (t : K → ℝ), (∀ k, 0 ≤ t k ∧ t k ≤ 1) →
      v j + ∑ k, t k • b j k ∈ normalHalfspaces u a) :
    normalHalfspaces u (fun i => a i + 1 / 2) =
      convexHull ℝ (Set.range fun j => cornerCenter (v j) (b j)) := by
  apply shifted_halfspaces_eq_convexHull u (fun i => a i + 1 / 2)
    b active (fun j => cornerCenter (v j) (b j)) hdual hcomplete
  · intro j k
    rw [cornerCenter_dual_coordinate (v j) (b j) _ k (hdual j k), hactive]
  · intro j
    exact integral_cornerCenter_feasible u a (v j) (b j) hu
      (fun i k => hint i j k) (hbox j)

/-- Sums of matched feasible Cartier points generate the halfspace polytope
with summed support values. This is the normal-fan part of equation (7). -/
theorem matched_centers_convexHull [Finite J] [Fintype K]
    (u : I → E →ₗ[ℝ] ℝ) (a d : I → ℝ)
    (b : J → Module.Basis K ℝ E) (active : J → K → I) (c e : J → E)
    (hdual : ∀ j k x, u (active j k) x = (b j).repr x k)
    (hcomplete : ∀ f : E →ₗ[ℝ] ℝ, ∃ j, ∀ k, 0 ≤ f (b j k))
    (hcactive : ∀ j k, u (active j k) (c j) = a (active j k))
    (heactive : ∀ j k, u (active j k) (e j) = d (active j k))
    (hc : ∀ j, c j ∈ normalHalfspaces u a)
    (he : ∀ j, e j ∈ normalHalfspaces u d) :
    normalHalfspaces u (fun i => a i + d i) =
      convexHull ℝ (Set.range fun j => c j + e j) := by
  apply shifted_halfspaces_eq_convexHull u (fun i => a i + d i)
    b active (fun j => c j + e j) hdual hcomplete
  · intro j k
    rw [map_add, hcactive, heactive]
  · intro j i
    rw [map_add]
    exact add_le_add (hc j i) (he j i)

end PaperVerification.ToricGeometry
end
end Source_ToricShiftedPolytopes
-- END ORIGINAL PaperVerification.ToricShiftedPolytopes


-- BEGIN ORIGINAL PaperVerification.ToricVertexCone
section Source_ToricVertexCone

-- original header: module
-- original header: public import PaperVerification.ToricFaceGeometry
-- original header: public import Mathlib.Analysis.Convex.KreinMilman
-- original header: public import Mathlib.Analysis.Convex.Topology
-- original header: public import Mathlib.Analysis.LocallyConvex.Separation
-- original header: public import Mathlib.Data.Finset.Max
-- original header: public import Mathlib.Tactic.FieldSimp
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.Module
-- original header: public import Mathlib.Tactic.Ring
-- original header: @[expose] public section
/-!
# The tangent cone of a finite polytope at a vertex

This file proves the ordinary finite-polytope fact that a linear functional
which is nonnegative on all incident edge directions is nonnegative on every
direction from the vertex into the polytope. The proof uses an actual
height-one section and actual extreme segment faces; no face-lattice or
tangent-cone generation assertion is assumed.
-/

noncomputable section

namespace PaperVerification.ToricVertexCone

open scoped BigOperators
open Set
open PaperVerification.ToricExchange

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite convex hull is the convex hull of its actual extreme points. -/
theorem finite_hull_eq_hull_extremePoints (s : Finset E) :
    convexHull ℝ ((convexHull ℝ (s : Set E)).extremePoints ℝ) =
      convexHull ℝ (s : Set E) := by
  have hfinite : ((convexHull ℝ (s : Set E)).extremePoints ℝ).Finite :=
    s.finite_toSet.subset extremePoints_convexHull_subset
  have hclosed := (hfinite.isCompact_convexHull ℝ).isClosed
  simpa only [hclosed.closure_eq] using
    closure_convexHull_extremePoints (s.finite_toSet.isCompact_convexHull ℝ)
      (convex_convexHull ℝ (s : Set E))

/-- A vertex of a finite convex hull is not in the hull of the other generators. -/
theorem vertex_not_mem_hull_erase (s : Finset E) {v : E}
    (hv : v ∈ (convexHull ℝ (s : Set E)).extremePoints ℝ) :
    v ∉ convexHull ℝ ((s : Set E) \ {v}) := by
  have hv' := ((convex_convexHull ℝ (s : Set E)).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff).mp hv
  intro hmem
  apply hv'.2
  apply convexHull_mono (s := ((s : Set E) \ {v})) ?_ hmem
  intro x hx
  exact ⟨subset_convexHull ℝ (s : Set E) hx.1, hx.2⟩

/-- Every vertex of a finite polytope is strictly exposed on its other generators. -/
theorem exists_strict_vertex_functional (s : Finset E) {v : E}
    (hv : v ∈ (convexHull ℝ (s : Set E)).extremePoints ℝ) :
    ∃ h : E →L[ℝ] ℝ, ∀ w ∈ s, w ≠ v → 0 < h (w - v) := by
  classical
  obtain ⟨h, c, hvc, hc⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ ((s : Set E) \ {v}))
    ((s.finite_toSet.sdiff : ((s : Set E) \ {v}).Finite).isCompact_convexHull ℝ).isClosed
    (vertex_not_mem_hull_erase s hv)
  refine ⟨h, ?_⟩
  intro w hw hwv
  have hwc := hc w (subset_convexHull ℝ ((s : Set E) \ {v}) ⟨hw, hwv⟩)
  rw [map_sub]
  linarith

/-- Lower bounds of a linear functional on finite generators extend to their convex hull. -/
theorem linear_lower_bound_hull (s : Finset E) (f : E →ₗ[ℝ] ℝ) (c : ℝ)
    (h : ∀ w ∈ s, c ≤ f w) : ∀ x ∈ convexHull ℝ (s : Set E), c ≤ f x := by
  exact convexHull_min h ((convex_Ici c).linear_preimage f)

/-- The zero set of a nonnegative linear slack is an actual face. -/
theorem linear_minimum_face_extreme (P : Set E) (g : E →ₗ[ℝ] ℝ) (v : E)
    (hg : ∀ x ∈ P, g v ≤ g x) :
    IsExtreme ℝ P {x ∈ P | g x = g v} := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
  refine ⟨hx, ?_⟩
  have heq := hz.2
  simp only [map_add, map_smul, smul_eq_mul] at heq
  have hxg := hg x hx
  have hyg := hg y hy
  have hbalance : a * (g x - g v) + b * (g y - g v) = 0 := by
    calc
      a * (g x - g v) + b * (g y - g v) =
          (a * g x + b * g y) - (a + b) * g v := by ring
      _ = 0 := by rw [heq, hab, one_mul, sub_self]
  have hax_nonneg := mul_nonneg ha.le (sub_nonneg.mpr hxg)
  have hby_nonneg := mul_nonneg hb.le (sub_nonneg.mpr hyg)
  have hax : a * (g x - g v) = 0 := by
    linarith only [hbalance, hax_nonneg, hby_nonneg]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hax).resolve_left ha.ne')

/-- Normalize a ray from `v` to have height one. -/
def normalizedDirection (h : E →L[ℝ] ℝ) (v w : E) : E :=
  (h (w - v))⁻¹ • (w - v)

theorem scale_normalizedDirection (h : E →L[ℝ] ℝ) (v w : E)
    (hw : h (w - v) ≠ 0) :
    h (w - v) • normalizedDirection h v w = w - v := by
  simp only [normalizedDirection, smul_smul, mul_inv_cancel₀ hw, one_smul]

theorem height_normalizedDirection (h : E →L[ℝ] ℝ) (v w : E)
    (hw : h (w - v) ≠ 0) :
    h (normalizedDirection h v w) = 1 := by
  simp only [normalizedDirection, map_smul, smul_eq_mul, inv_mul_cancel₀ hw]

/-- Finite generators of the actual height-one section at a vertex. -/
def sectionGenerators (s : Finset E) (v : E) (h : E →L[ℝ] ℝ) : Finset E := by
  classical
  exact (s.erase v).image (normalizedDirection h v)

theorem mem_sectionGenerators (s : Finset E) (v : E) (h : E →L[ℝ] ℝ) (u : E) :
    u ∈ sectionGenerators s v h ↔
      ∃ w ∈ s, w ≠ v ∧ normalizedDirection h v w = u := by
  classical
  simp only [sectionGenerators, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨w, ⟨hwv, hws⟩, hwu⟩
    exact ⟨w, hws, hwv, hwu⟩
  · rintro ⟨w, hws, hwv, hwu⟩
    exact ⟨w, ⟨hwv, hws⟩, hwu⟩

/-- A vertex of the height-one section lies on an actual edge ray of the original
finite polytope. The resulting edge is a nondegenerate extreme segment. -/
theorem section_vertex_gives_edge {n : ℕ} (s : Finset (Fin n → ℝ))
    (v : Fin n → ℝ) (hv : v ∈ s) (h : (Fin n → ℝ) →L[ℝ] ℝ)
    (hpos : ∀ w ∈ s, w ≠ v → 0 < h (w - v))
    (u : Fin n → ℝ)
    (hu : u ∈ (convexHull ℝ (sectionGenerators s v h : Set (Fin n → ℝ))).extremePoints ℝ) :
    ∃ w ∈ s, v ≠ w ∧
      IsExtreme ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) (segment ℝ v w) ∧
      0 < h (w - v) ∧ w - v = h (w - v) • u := by
  classical
  let T := sectionGenerators s v h
  obtain ⟨f, hf⟩ := exists_strict_vertex_functional T hu
  have hfle (q : Fin n → ℝ) (hq : q ∈ T) : f u ≤ f q := by
    by_cases hqu : q = u
    · simp [hqu]
    · have hlt : 0 < f q - f u := by simpa only [map_sub] using hf q hq hqu
      linarith
  let g : (Fin n → ℝ) →ₗ[ℝ] ℝ := f.toLinearMap - (f u) • h.toLinearMap
  have hg_normal (w : Fin n → ℝ) (hw : w ∈ s) (hwv : w ≠ v) :
      g (w - v) = h (w - v) * (f (normalizedDirection h v w) - f u) := by
    have hheight := height_normalizedDirection h v w (hpos w hw hwv).ne'
    calc
      g (w - v) = g (h (w - v) • normalizedDirection h v w) :=
        congrArg g (scale_normalizedDirection h v w (hpos w hw hwv).ne').symm
      _ = h (w - v) * g (normalizedDirection h v w) := by rw [map_smul, smul_eq_mul]
      _ = _ := by simp [g, hheight]
  have hqmem (w : Fin n → ℝ) (hw : w ∈ s) (hwv : w ≠ v) :
      normalizedDirection h v w ∈ T :=
    (mem_sectionGenerators s v h _).mpr ⟨w, hw, hwv, rfl⟩
  have hgnonneg (w : Fin n → ℝ) (hw : w ∈ s) : 0 ≤ g (w - v) := by
    by_cases hwv : w = v
    · simp [hwv]
    · rw [hg_normal w hw hwv]
      exact mul_nonneg (hpos w hw hwv).le (sub_nonneg.mpr (hfle _ (hqmem w hw hwv)))
  have hqeq (w : Fin n → ℝ) (hw : w ∈ s) (hwv : w ≠ v)
      (hgw : g (w - v) = 0) : normalizedDirection h v w = u := by
    by_contra hne
    have hfpos := hf _ (hqmem w hw hwv) hne
    have hfpos' : 0 < f (normalizedDirection h v w) - f u := by
      simpa only [map_sub] using hfpos
    have hprod := mul_pos (hpos w hw hwv) hfpos'
    rw [← hg_normal w hw hwv, hgw] at hprod
    exact (lt_irrefl 0) hprod
  let P : Set (Fin n → ℝ) := convexHull ℝ (s : Set (Fin n → ℝ))
  let F : Set (Fin n → ℝ) := {x ∈ P | g x = g v}
  have hgmin : ∀ x ∈ P, g v ≤ g x := by
    apply linear_lower_bound_hull s g (g v)
    intro x hx
    have hxg := hgnonneg x hx
    simpa only [map_sub, sub_nonneg] using hxg
  have hFext : IsExtreme ℝ P F := linear_minimum_face_extreme P g v hgmin
  have hFconv : Convex ℝ F :=
    (convex_convexHull ℝ (s : Set (Fin n → ℝ))).inter
      ((convex_singleton (g v)).linear_preimage g)
  have hvF : v ∈ F := ⟨subset_convexHull ℝ (s : Set (Fin n → ℝ)) hv, rfl⟩
  have huT : u ∈ T := extremePoints_convexHull_subset hu
  obtain ⟨w₀, hw₀, hw₀v, hq₀⟩ := (mem_sectionGenerators s v h u).mp huT
  have hw₀g : g (w₀ - v) = 0 := by
    rw [hg_normal w₀ hw₀ hw₀v, hq₀, sub_self, mul_zero]
  have hw₀F : w₀ ∈ F :=
    ⟨subset_convexHull ℝ (s : Set (Fin n → ℝ)) hw₀,
      sub_eq_zero.mp (by simpa only [map_sub] using hw₀g)⟩
  let R := faceGenerators s F
  have hRmem (x : Fin n → ℝ) : x ∈ R ↔ x ∈ s ∧ x ∈ F := by
    simp [R, faceGenerators]
  obtain ⟨w, hwR, hmax⟩ := R.exists_max_image (fun x => h (x - v))
    ⟨w₀, (hRmem w₀).mpr ⟨hw₀, hw₀F⟩⟩
  have hws : w ∈ s := ((hRmem w).mp hwR).1
  have hwF : w ∈ F := ((hRmem w).mp hwR).2
  have hwp : 0 < h (w - v) :=
    (hpos w₀ hw₀ hw₀v).trans_le (hmax w₀ ((hRmem w₀).mpr ⟨hw₀, hw₀F⟩))
  have hwv : w ≠ v := by intro he; simp [he] at hwp
  have hscale (x : Fin n → ℝ) (hx : x ∈ R) : x - v = h (x - v) • u := by
    have hxs := ((hRmem x).mp hx).1
    have hxF := ((hRmem x).mp hx).2
    by_cases hxv : x = v
    · simp [hxv]
    · have hxg : g (x - v) = 0 := by simp only [map_sub, hxF.2, sub_self]
      calc
        x - v = h (x - v) • normalizedDirection h v x :=
          (scale_normalizedDirection h v x (hpos x hxs hxv).ne').symm
        _ = h (x - v) • u := by rw [hqeq x hxs hxv hxg]
  have hwscale := hscale w hwR
  have hRsegment : (R : Set (Fin n → ℝ)) ⊆ segment ℝ v w := by
    intro x hx
    have hxs := ((hRmem x).mp hx).1
    have hxheight : 0 ≤ h (x - v) := by
      by_cases hxv : x = v
      · simp [hxv]
      · exact (hpos x hxs hxv).le
    have hratio : h (x - v) / h (w - v) ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hxheight hwp.le, (div_le_one hwp).mpr (hmax x hx)⟩
    have hmul : (h (x - v) / h (w - v)) * h (w - v) = h (x - v) := by
      field_simp [hwp.ne']
    have hsmul : (h (x - v) / h (w - v)) • (w - v) = h (x - v) • u := by
      calc
        _ = (h (x - v) / h (w - v)) • (h (w - v) • u) :=
          congrArg (fun z => (h (x - v) / h (w - v)) • z) hwscale
        _ = ((h (x - v) / h (w - v)) * h (w - v)) • u := smul_smul _ _ _
        _ = h (x - v) • u := by rw [hmul]
    have hline : AffineMap.lineMap v w (h (x - v) / h (w - v)) = x := by
      rw [AffineMap.lineMap_apply_module', hsmul, ← hscale x hx, sub_add_cancel]
    simpa only [hline] using lineMap_mem_segment ℝ v w hratio
  have hFhull : F = convexHull ℝ (R : Set (Fin n → ℝ)) :=
    convex_face_eq_convexHull_filter s F hFconv hFext
  have hFsegment : F = segment ℝ v w := by
    apply Set.Subset.antisymm
    · rw [hFhull]
      exact convexHull_min hRsegment (convex_segment v w)
    · exact hFconv.segment_subset hvF hwF
  refine ⟨w, hws, hwv.symm, ?_, hwp, hwscale⟩
  simpa only [← hFsegment] using hFext

/-- A linear functional that is nonnegative on every actual incident edge
direction is nonnegative on every direction into the finite polytope. -/
theorem linear_nonneg_of_incident_edges {n : ℕ} (s : Finset (Fin n → ℝ))
    (v : Fin n → ℝ)
    (hv : v ∈ (convexHull ℝ (s : Set (Fin n → ℝ))).extremePoints ℝ)
    (f : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (hedges : ∀ w : Fin n → ℝ, v ≠ w →
      IsExtreme ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) (segment ℝ v w) →
      0 ≤ f (w - v)) :
    ∀ x ∈ convexHull ℝ (s : Set (Fin n → ℝ)), 0 ≤ f (x - v) := by
  classical
  obtain ⟨h, hpos⟩ := exists_strict_vertex_functional s hv
  have hvs : v ∈ s := extremePoints_convexHull_subset hv
  let T := sectionGenerators s v h
  have hext : ∀ u ∈ (convexHull ℝ (T : Set (Fin n → ℝ))).extremePoints ℝ,
      0 ≤ f u := by
    intro u hu
    obtain ⟨w, _, hvw, hwe, hwp, hwscale⟩ := section_vertex_gives_edge s v hvs h hpos u hu
    have hf := hedges w hvw hwe
    rw [hwscale, map_smul, smul_eq_mul] at hf
    exact nonneg_of_mul_nonneg_right hf hwp
  have hsection : ∀ u ∈ convexHull ℝ (T : Set (Fin n → ℝ)), 0 ≤ f u := by
    have hsub :
        convexHull ℝ ((convexHull ℝ (T : Set (Fin n → ℝ))).extremePoints ℝ) ⊆
          {u | 0 ≤ f u} :=
      convexHull_min hext ((convex_Ici (0 : ℝ)).linear_preimage f)
    rw [finite_hull_eq_hull_extremePoints T] at hsub
    exact hsub
  have hgenerators (w : Fin n → ℝ) (hw : w ∈ s) : f v ≤ f w := by
    have hfnonneg : 0 ≤ f (w - v) := by
      by_cases hwv : w = v
      · simp [hwv]
      · have hq : normalizedDirection h v w ∈ T :=
          (mem_sectionGenerators s v h _).mpr ⟨w, hw, hwv, rfl⟩
        have hfq := hsection _ (subset_convexHull ℝ (T : Set (Fin n → ℝ)) hq)
        rw [← scale_normalizedDirection h v w (hpos w hw hwv).ne',
          map_smul, smul_eq_mul]
        exact mul_nonneg (hpos w hw hwv).le hfq
    simpa only [map_sub, sub_nonneg] using hfnonneg
  intro x hx
  have hfx := linear_lower_bound_hull s f (f v) hgenerators x hx
  simpa only [map_sub, sub_nonneg] using hfx

/-- If every actual incident edge lies on a nonnegative basis ray, the whole
polytope lies in the nonnegative cone on that basis at the vertex. This is the
tangent-cone assertion needed to extract the integral dual facet normals at a
smooth vertex. -/
theorem nonnegative_basis_coordinates_of_incident_edges {n : ℕ}
    (s : Finset (Fin n → ℝ)) (v : Fin n → ℝ)
    (hv : v ∈ (convexHull ℝ (s : Set (Fin n → ℝ))).extremePoints ℝ)
    (b : Module.Basis (Fin n) ℝ (Fin n → ℝ))
    (hedges : ∀ w : Fin n → ℝ, v ≠ w →
      IsExtreme ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) (segment ℝ v w) →
      ∃ j : Fin n, ∃ a : ℝ, 0 ≤ a ∧ w - v = a • b j) :
    ∀ x ∈ convexHull ℝ (s : Set (Fin n → ℝ)),
      ∀ i : Fin n, 0 ≤ b.repr (x - v) i := by
  intro x hx i
  apply linear_nonneg_of_incident_edges s v hv (b.coord i) ?_ x hx
  intro w hvw hwedge
  obtain ⟨j, a, ha, hw⟩ := hedges w hvw hwedge
  rw [hw, map_smul]
  by_cases hij : i = j
  · subst j
    simpa using ha
  · simp [Module.Basis.coord_apply, hij, Ne.symm hij]

end PaperVerification.ToricVertexCone
end
end Source_ToricVertexCone
-- END ORIGINAL PaperVerification.ToricVertexCone


-- BEGIN ORIGINAL PaperVerification.ToricNormalFan
section Source_ToricNormalFan

-- original header: module
-- original header: public import PaperVerification.ToricIntegralBasis
-- original header: public import PaperVerification.ToricVertexCone
-- original header: public import PaperVerification.ToricShiftedPolytopes
-- original header: public import Mathlib.Data.Set.Finite.Lemmas
-- original header: @[expose] public section
/-!
# Actual vertices, basis cones, and normal-fan matching

All normal cones below are the ordinary supporting cones from the literal
polytope definition. The lemmas identify their dual basis coordinates and
show that equality of integral basis cones preserves primitive directions.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators
open PaperVerification.ToricVertexCone

/-- The coefficient vector representing a real linear functional in the
standard coordinate pairing used by the paper's normal cones. -/
def dualVector {n : ℕ} (f : Ambient n →ₗ[ℝ] ℝ) : Ambient n :=
  fun i => f (Pi.basisFun ℝ (Fin n) i)

@[simp] theorem dualVector_pairing {n : ℕ}
    (f : Ambient n →ₗ[ℝ] ℝ) (x y : Ambient n) :
    (∑ i, dualVector f i * (y i - x i)) = f (y - x) := by
  have h := congrArg f ((Pi.basisFun ℝ (Fin n)).sum_repr (y - x))
  simpa [dualVector, map_sum, map_smul, smul_eq_mul, mul_comm] using h

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- The actual vertex set is finite, independently of the chosen redundant generators. -/
theorem finite_vertices : (P.carrier.extremePoints ℝ).Finite := by
  exact (P.generators.finite_toSet.image (embed n)).subset extremePoints_convexHull_subset

/-- The convex hull of the actual vertices equals the whole polytope. -/
theorem hull_vertices : convexHull ℝ (P.carrier.extremePoints ℝ) = P.carrier := by
  classical
  have h := finite_hull_eq_hull_extremePoints (P.generators.image (embed n))
  simpa [carrier, Finset.coe_image] using h

/-- A lattice polytope has an actual vertex, also in dimension zero. -/
theorem vertices_nonempty : (P.carrier.extremePoints ℝ).Nonempty := by
  apply (convexHull_nonempty_iff (𝕜 := ℝ)).mp
  rw [P.hull_vertices]
  obtain ⟨z, hz⟩ := P.nonempty
  exact ⟨embed n z, subset_convexHull ℝ _ ⟨z, hz, rfl⟩⟩

/-- Every linear functional attains its minimum at an actual vertex. -/
theorem exists_minimizing_vertex (f : Ambient n →ₗ[ℝ] ℝ) :
    ∃ v ∈ P.carrier.extremePoints ℝ, ∀ x ∈ P.carrier, f v ≤ f x := by
  obtain ⟨v, hv, hmin⟩ := Set.exists_min_image (P.carrier.extremePoints ℝ)
    f P.finite_vertices P.vertices_nonempty
  refine ⟨v, hv, ?_⟩
  rw [← P.hull_vertices]
  exact convexHull_min hmin ((convex_Ici (f v)).linear_preimage f)

/-- A linear functional is in the actual normal cone precisely when it is
minimized at the selected point. -/
theorem dualVector_mem_normalCone_iff (f : Ambient n →ₗ[ℝ] ℝ) (v : Ambient n) :
    dualVector f ∈ P.normalCone v ↔ ∀ x ∈ P.carrier, f v ≤ f x := by
  simp only [normalCone, Set.mem_setOf_eq, dualVector_pairing, map_sub, sub_nonneg]

/-- Every smooth vertex has a supporting orthant in its actual primitive
integral edge basis. This is a consequence of the finite-polytope tangent-cone
argument, not an extra clause in the definition of smoothness. -/
theorem smooth_vertex_basis_cone (hP : P.Smooth)
    (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ) :
    ∃ (vZ : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n))
      (lengths : Fin n → ℕ),
      embed n vZ = v ∧
      (∀ i, 0 < lengths i ∧ P.IsEdge v (embed n (vZ + (lengths i : ℤ) • b i))) ∧
      (∀ x ∈ P.carrier, ∀ i, 0 ≤ (integralBasisReal b).repr (x - v) i) := by
  classical
  obtain ⟨vZ, b, lengths, hvZ, hedges, hall⟩ := hP v hv
  refine ⟨vZ, b, lengths, hvZ, hedges, ?_⟩
  let s := P.generators.image (embed n)
  have hcarrier : convexHull ℝ (s : Set (Ambient n)) = P.carrier := by
    simp [s, carrier, Finset.coe_image]
  have hv' : v ∈ (convexHull ℝ (s : Set (Ambient n))).extremePoints ℝ := by
    simpa only [hcarrier] using hv
  have hedgeRay : ∀ w : Ambient n, v ≠ w →
      IsExtreme ℝ (convexHull ℝ (s : Set (Ambient n))) (segment ℝ v w) →
      ∃ i : Fin n, ∃ a : ℝ, 0 ≤ a ∧ w - v = a • integralBasisReal b i := by
    intro w hvw hface
    have hedge : P.IsEdge v w := ⟨hvw, by simpa only [hcarrier] using hface⟩
    obtain ⟨i, rfl⟩ := hall w hedge
    refine ⟨i, (lengths i : ℝ), Nat.cast_nonneg _, ?_⟩
    rw [map_add, hvZ, integralBasisReal_apply, add_sub_cancel_left]
    ext j
    simp [embed, Int.cast_mul]
  have h := nonnegative_basis_coordinates_of_incident_edges s v hv'
    (integralBasisReal b) hedgeRay
  simpa only [hcarrier] using h

/-- A family containing the primitive edge basis at every actual vertex is
complete: every linear functional is nonnegative on one whole basis. -/
theorem smooth_basis_cones_complete
    (b : P.carrier.extremePoints ℝ → Module.Basis (Fin n) ℤ (Lattice n))
    (vZ : P.carrier.extremePoints ℝ → Lattice n)
    (lengths : P.carrier.extremePoints ℝ → Fin n → ℕ)
    (hvZ : ∀ v, embed n (vZ v) = (v : Ambient n))
    (hedges : ∀ v i, 0 < lengths v i ∧
      P.IsEdge v (embed n (vZ v + (lengths v i : ℤ) • b v i)))
    (f : Ambient n →ₗ[ℝ] ℝ) :
    ∃ v : P.carrier.extremePoints ℝ, ∀ i, 0 ≤ f (integralBasisReal (b v) i) := by
  obtain ⟨v, hv, hmin⟩ := P.exists_minimizing_vertex f
  refine ⟨⟨v, hv⟩, ?_⟩
  intro i
  let j : P.carrier.extremePoints ℝ := ⟨v, hv⟩
  have hedge := (hedges j i).2
  have hm := hmin _ (P.edge_endpoints_extreme hedge).2.1
  have he : embed n (vZ j + (lengths j i : ℤ) • b j i) =
      v + (lengths j i : ℝ) • integralBasisReal (b j) i := by
    rw [map_add, hvZ, integralBasisReal_apply]
    ext k
    simp [embed, Int.cast_mul, j]
  rw [he, map_add, map_smul, smul_eq_mul] at hm
  have hl : (0 : ℝ) < lengths j i := by exact_mod_cast (hedges j i).1
  nlinarith

/-- A point with a supporting real basis orthant is an actual vertex. -/
theorem extreme_of_supporting_basis (v : Ambient n) (hv : v ∈ P.carrier)
    (b : Module.Basis (Fin n) ℝ (Ambient n))
    (hcone : ∀ x ∈ P.carrier, ∀ i, 0 ≤ b.repr (x - v) i) :
    v ∈ P.carrier.extremePoints ℝ := by
  refine ⟨hv, ?_⟩
  intro x hx y hy hseg
  obtain ⟨r, s, hr, hs, hrs, he⟩ := hseg
  apply b.ext_elem
  intro i
  have hx0 := hcone x hx i
  have hy0 := hcone y hy i
  have he' := congrArg (fun z => b.repr z i) he
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at he'
  simp only [map_sub, Finsupp.sub_apply] at hx0 hy0
  have hbalance : r * (b.repr x i - b.repr v i) +
      s * (b.repr y i - b.repr v i) = 0 := by
    calc
      r * (b.repr x i - b.repr v i) + s * (b.repr y i - b.repr v i) =
          (r * b.repr x i + s * b.repr y i) - (r + s) * b.repr v i := by ring
      _ = 0 := by rw [he', hrs, one_mul, sub_self]
  have hrx := mul_nonneg hr.le hx0
  have hsy := mul_nonneg hs.le hy0
  have hzero : r * (b.repr x i - b.repr v i) = 0 := by
    linarith only [hbalance, hrx, hsy]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hr.ne')

/-- Equality of the genuine normal fans matches every supporting-basis vertex
with an actual vertex of the other polytope and preserves its supporting cone. -/
theorem exists_matched_vertex (Q : LatticePolytope n) (hfan : P.SameNormalFan Q)
    (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ)
    (b : Module.Basis (Fin n) ℝ (Ambient n))
    (hcone : ∀ x ∈ P.carrier, ∀ i, 0 ≤ b.repr (x - v) i) :
    ∃ w ∈ Q.carrier.extremePoints ℝ, P.normalCone v = Q.normalCone w ∧
      ∀ x ∈ Q.carrier, ∀ i, 0 ≤ b.repr (x - w) i := by
  have hmem : P.normalCone v ∈ P.normalFan := ⟨v, hv.1, rfl⟩
  rw [show P.normalFan = Q.normalFan from hfan] at hmem
  obtain ⟨w, hw, hcw⟩ := hmem
  have hnew : ∀ x ∈ Q.carrier, ∀ i, 0 ≤ b.repr (x - w) i := by
    intro x hx i
    have hi : dualVector (b.coord i) ∈ P.normalCone v := by
      intro y hy
      simpa only [dualVector_pairing, Module.Basis.coord_apply] using hcone y hy i
    rw [hcw] at hi
    have h := hi x hx
    simpa only [dualVector_pairing, Module.Basis.coord_apply] using h
  exact ⟨w, Q.extreme_of_supporting_basis w hw b hnew, hcw, hnew⟩

end LatticePolytope

/-- Two integral bases spanning the same positive orthant differ by a permutation,
with no rescaling. The proof uses nonnegative integer transition coefficients. -/
theorem integral_bases_perm_of_nonnegative_coordinates {K M : Type*}
    [Fintype K] [AddCommGroup M] [Module ℤ M]
    (b c : Module.Basis K ℤ M)
    (hbc : ∀ i j, 0 ≤ b.repr (c j) i)
    (hcb : ∀ i j, 0 ≤ c.repr (b j) i) :
    ∃ σ : Equiv.Perm K, ∀ i, b i = c (σ i) := by
  classical
  have hcoord (i k : K) :
      (∑ j, c.repr (b i) j * b.repr (c j) k) = if i = k then 1 else 0 := by
    have h := congrArg (fun x : M => b.repr x k) (c.sum_repr (b i))
    simpa only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul, Module.Basis.repr_self, Finsupp.single_apply] using h
  have hex (i : K) : ∃ j, c j = b i := by
    have hdiag : (∑ j, c.repr (b i) j * b.repr (c j) i) = 1 := by
      simpa using hcoord i i
    obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (show (∑ j, c.repr (b i) j * b.repr (c j) i) ≠ 0 by rw [hdiag]; norm_num)
    have ha0 := hcb j i
    have hb0 := hbc i j
    have ha1 : 1 ≤ c.repr (b i) j := by
      have hne := (mul_ne_zero_iff.mp hj).1
      omega
    have hb1 : 1 ≤ b.repr (c j) i := by
      have hne := (mul_ne_zero_iff.mp hj).2
      omega
    have hp := Finset.single_le_sum
      (fun k _ => mul_nonneg (hcb k i) (hbc i k)) (Finset.mem_univ j)
    rw [hdiag] at hp
    have ha_le : c.repr (b i) j ≤ c.repr (b i) j * b.repr (c j) i := by
      nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hb1)]
    have ha : c.repr (b i) j = 1 := by omega
    have hb : b.repr (c j) i = 1 := by rw [ha, one_mul] at hp; omega
    refine ⟨j, b.ext_elem (fun k => ?_)⟩
    by_cases hik : i = k
    · subst k
      simpa only [Module.Basis.repr_self, Finsupp.single_eq_same] using hb
    · have hpk := Finset.single_le_sum
        (fun l _ => mul_nonneg (hcb l i) (hbc k l)) (Finset.mem_univ j)
      rw [hcoord i k, if_neg hik, ha, one_mul] at hpk
      have hk : b.repr (c j) k = 0 := le_antisymm hpk (hbc k j)
      simpa only [Module.Basis.repr_self, Finsupp.single_apply, if_neg hik] using hk
  choose σ hσ using hex
  have hσinj : Function.Injective σ := by
    intro i j hij
    apply b.injective
    rw [← hσ i, ← hσ j, hij]
  exact ⟨Equiv.ofBijective σ
    ((Fintype.bijective_iff_injective_and_card σ).mpr ⟨hσinj, rfl⟩),
    fun i => (hσ i).symm⟩

/-- A positive-length integral edge contained in a basis orthant has
nonnegative integer coordinates in that basis. -/
theorem basis_coordinates_nonneg_of_edge {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (v z : Lattice n) (k : ℕ) (hk : 0 < k)
    (h : ∀ i, 0 ≤ (integralBasisReal b).repr
      (embed n (v + (k : ℤ) • z) - embed n v) i) :
    ∀ i, 0 ≤ b.repr z i := by
  intro i
  have hi := h i
  rw [map_add, add_sub_cancel_left, embed_int_smul, map_smul,
    Finsupp.smul_apply, smul_eq_mul, integralBasisReal_repr] at hi
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hn : (0 : ℝ) ≤ (b.repr z i : ℝ) := by
    push_cast at hi
    nlinarith
  exact_mod_cast hn

namespace LatticePolytope

/-- The actual common normal fan matches smooth vertices with the same
primitive lattice edge directions. Equality of the directions, rather than
merely equality of their rays, follows from integral-basis primitivity. -/
theorem sameNormalFan_matched_bases {n : ℕ} (P Q : LatticePolytope n)
    (hP : P.Smooth) (hQ : Q.Smooth) (hfan : P.SameNormalFan Q)
    (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ) :
    ∃ (w : Ambient n) (vZ wZ : Lattice n)
      (b : Module.Basis (Fin n) ℤ (Lattice n)) (p q : Fin n → ℕ),
      w ∈ Q.carrier.extremePoints ℝ ∧ embed n vZ = v ∧ embed n wZ = w ∧
      P.normalCone v = Q.normalCone w ∧
      (∀ i, 0 < p i ∧ P.IsEdge v (embed n (vZ + (p i : ℤ) • b i))) ∧
      (∀ i, 0 < q i ∧ Q.IsEdge w (embed n (wZ + (q i : ℤ) • b i))) ∧
      (∀ x ∈ P.carrier, ∀ i, 0 ≤ (integralBasisReal b).repr (x - v) i) ∧
      (∀ x ∈ Q.carrier, ∀ i, 0 ≤ (integralBasisReal b).repr (x - w) i) := by
  obtain ⟨vZ, b, p, hvZ, hp, hPb⟩ := P.smooth_vertex_basis_cone hP v hv
  obtain ⟨w, hw, hcones, hQb⟩ :=
    P.exists_matched_vertex Q hfan v hv (integralBasisReal b) hPb
  obtain ⟨wZ, c, q, hwZ, hq, hQc⟩ := Q.smooth_vertex_basis_cone hQ w hw
  have hPc : ∀ x ∈ P.carrier, ∀ i, 0 ≤ (integralBasisReal c).repr (x - v) i := by
    intro x hx i
    have hi : dualVector ((integralBasisReal c).coord i) ∈ Q.normalCone w := by
      intro y hy
      simpa only [dualVector_pairing, Module.Basis.coord_apply] using hQc y hy i
    rw [← hcones] at hi
    have h := hi x hx
    simpa only [dualVector_pairing, Module.Basis.coord_apply] using h
  have hbc : ∀ i j, 0 ≤ b.repr (c j) i := by
    intro i j
    apply basis_coordinates_nonneg_of_edge b wZ (c j) (q j) (hq j).1
    intro k
    have h := hQb _ (Q.edge_endpoints_extreme (hq j).2).2.1 k
    simpa only [hwZ] using h
  have hcb : ∀ i j, 0 ≤ c.repr (b j) i := by
    intro i j
    apply basis_coordinates_nonneg_of_edge c vZ (b j) (p j) (hp j).1
    intro k
    have h := hPc _ (P.edge_endpoints_extreme (hp j).2).2.1 k
    simpa only [hvZ] using h
  obtain ⟨σ, hσ⟩ := integral_bases_perm_of_nonnegative_coordinates b c hbc hcb
  refine ⟨w, vZ, wZ, b, p, fun i => q (σ i), hw, hvZ, hwZ, hcones, hp, ?_, hPb, hQb⟩
  intro i
  simpa only [hσ i] using hq (σ i)

end LatticePolytope

end PaperVerification.ToricGeometry
end
end Source_ToricNormalFan
-- END ORIGINAL PaperVerification.ToricNormalFan


-- BEGIN ORIGINAL PaperVerification.ToricDualNormalCone
section Source_ToricDualNormalCone

-- original header: module
-- original header: public import PaperVerification.ToricNormalFan
-- original header: public import PaperVerification.ToricFanFoundations
-- original header: public import Mathlib.LinearAlgebra.Matrix.Dual
-- original header: @[expose] public section
/-!
# Integral dual bases of actual smooth normal cones

The standard coordinate pairing identifies the dual lattice with the original
coordinate lattice. Under this genuine integral linear equivalence, the dual of
a primitive edge basis is again an integral basis. Its nonnegative real span is
exactly the ordinary supporting normal cone of the polytope.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators

/-- The dual integral basis, represented in the standard coordinate lattice by
the ordinary dot-product pairing. -/
def integralDualBasis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Module.Basis (Fin n) ℤ (Lattice n) :=
  b.dualBasis.map (dotProductEquiv ℤ (Fin n)).symm

/-- The defining duality holds for every lattice vector, without any
primitivity or index assumption beyond the genuine integral basis. -/
@[simp] theorem integralDualBasis_pairing {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (z : Lattice n) :
    (∑ j, integralDualBasis b i j * z j) = b.repr z i := by
  rw [integralDualBasis, Module.Basis.map_apply]
  change (dotProductEquiv ℤ (Fin n)
    ((dotProductEquiv ℤ (Fin n)).symm (b.dualBasis i))) z = _
  rw [LinearEquiv.apply_symm_apply]
  exact b.dualBasis_apply i z

/-- Coordinates in the dual integral basis are evaluations on the original
basis vectors. -/
@[simp] theorem integralDualBasis_repr {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (z : Lattice n) (i : Fin n) :
    (integralDualBasis b).repr z i = ∑ j, z j * b i j := by
  change b.dualBasis.repr ((dotProductEquiv ℤ (Fin n)) z) i = _
  rw [Module.Basis.dualBasis_repr]
  rfl

/-- Real extension of the integral duality. -/
@[simp] theorem integralDualBasis_real_pairing {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (x : Ambient n) :
    (∑ j, embed n (integralDualBasis b i) j * x j) =
      (integralBasisReal b).repr x i := by
  let f : Ambient n →ₗ[ℝ] ℝ :=
    dotProductEquiv ℝ (Fin n) (embed n (integralDualBasis b i))
  have hf : f = (integralBasisReal b).coord i := by
    apply (integralBasisReal b).ext
    intro k
    change (∑ j, embed n (integralDualBasis b i) j *
      integralBasisReal b k j) = (integralBasisReal b).repr (integralBasisReal b k) i
    rw [integralBasisReal_apply, integralBasisReal_repr]
    have hz := integralDualBasis_pairing b i (b k)
    change (∑ j, (integralDualBasis b i j : ℝ) * (b k j : ℝ)) =
      (b.repr (b k) i : ℝ)
    exact_mod_cast hz
  exact LinearMap.congr_fun hf x

/-- The primitive normal vector is precisely the coefficient vector of the
corresponding real dual coordinate functional. -/
theorem embed_integralDualBasis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) :
    embed n (integralDualBasis b i) = dualVector ((integralBasisReal b).coord i) := by
  funext j
  change embed n (integralDualBasis b i) j =
    (integralBasisReal b).repr (Pi.basisFun ℝ (Fin n) j) i
  calc
    embed n (integralDualBasis b i) j =
        embed n (integralDualBasis b i) ⬝ᵥ Pi.basisFun ℝ (Fin n) j := by
      rw [Pi.basisFun_apply, dotProduct_single_one]
    _ = _ := integralDualBasis_real_pairing b i (Pi.basisFun ℝ (Fin n) j)

/-- Coordinates in the real dual basis are ordinary pairings with the real
edge basis. This identifies nonnegative coordinates with supporting normals. -/
@[simp] theorem integralDualBasis_real_repr {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (u : Ambient n) (i : Fin n) :
    (integralBasisReal (integralDualBasis b)).repr u i =
      ∑ j, u j * integralBasisReal b i j := by
  let d := integralBasisReal (integralDualBasis b)
  let f : Ambient n →ₗ[ℝ] ℝ :=
    dotProductEquiv ℝ (Fin n) (integralBasisReal b i)
  have hf : d.coord i = f := by
    apply d.ext
    intro k
    change d.repr (d k) i = ∑ j, integralBasisReal b i j * d k j
    rw [Module.Basis.repr_self_apply]
    have hp := integralDualBasis_real_pairing b k (integralBasisReal b i)
    rw [Module.Basis.repr_self_apply] at hp
    simpa only [d, integralBasisReal_apply, mul_comm, eq_comm] using hp.symm
  have h := LinearMap.congr_fun hf u
  change d.repr u i = (integralBasisReal b i) ⬝ᵥ u at h
  simpa only [d, dotProduct, mul_comm] using h

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- Membership of the actual supporting normal cone is exactly
nonnegativity on a complete primitive edge basis. -/
theorem mem_normalCone_iff_basis_pairing
    (vZ : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n))
    (lengths : Fin n → ℕ)
    (hedges : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)))
    (hcone : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) i)
    (u : Ambient n) :
    u ∈ P.normalCone (embed n vZ) ↔
      ∀ i, 0 ≤ ∑ j, u j * integralBasisReal b i j := by
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) u
  have hnormal : u ∈ P.normalCone (embed n vZ) ↔
      ∀ x ∈ P.carrier, f (embed n vZ) ≤ f x := by
    change (∀ x ∈ P.carrier, 0 ≤ f (x - embed n vZ)) ↔ _
    simp only [map_sub, sub_nonneg]
  rw [hnormal]
  constructor
  · intro hu i
    have h := hu _ (P.edge_endpoints_extreme (hedges i).2).2.1
    rw [map_add, embed_int_smul, map_add, map_smul,
      smul_eq_mul, Int.cast_natCast, ← integralBasisReal_apply b i] at h
    have hl : (0 : ℝ) < lengths i := by exact_mod_cast (hedges i).1
    have hnonneg : 0 ≤ f (integralBasisReal b i) := by nlinarith
    exact hnonneg
  · intro hu x hx
    exact linear_le_of_basis_coordinates (integralBasisReal b) f
      (embed n vZ) x hu (hcone x hx)

/-- The actual normal cone is the nonnegative real cone generated by the
genuine primitive dual integral basis. -/
theorem normalCone_eq_latticeRayCone
    (vZ : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n))
    (lengths : Fin n → ℕ)
    (hedges : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)))
    (hcone : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) i) :
    P.normalCone (embed n vZ) =
      (latticeRayCone (Finset.univ.image (integralDualBasis b)) : Set (Ambient n)) := by
  ext u
  change (u ∈ P.normalCone (embed n vZ)) ↔
    u ∈ latticeRayCone (Finset.univ.image (integralDualBasis b))
  rw [P.mem_normalCone_iff_basis_pairing vZ b lengths hedges hcone u,
    mem_latticeRayCone_basis_iff]
  simp only [Finset.mem_univ, not_true_eq_false, false_implies, implies_true,
    and_true, integralDualBasis_real_repr]

/-- Every actual smooth vertex normal cone is generated by a complete
primitive integral basis of normals. No normal-fan smoothness is assumed. -/
theorem smooth_vertex_normalCone_basis (hP : P.Smooth)
    (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ) :
    ∃ d : Module.Basis (Fin n) ℤ (Lattice n),
      P.normalCone v = (latticeRayCone (Finset.univ.image d) : Set (Ambient n)) := by
  obtain ⟨vZ, b, lengths, hvZ, hedges, hcone⟩ := P.smooth_vertex_basis_cone hP v hv
  refine ⟨integralDualBasis b, ?_⟩
  have hedges' : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)) := by
    simpa only [hvZ] using hedges
  have hcone' : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) i := by
    simpa only [hvZ] using hcone
  simpa only [hvZ] using P.normalCone_eq_latticeRayCone vZ b lengths hedges' hcone'

end LatticePolytope

end PaperVerification.ToricGeometry

end
end Source_ToricDualNormalCone
-- END ORIGINAL PaperVerification.ToricDualNormalCone


-- BEGIN ORIGINAL PaperVerification.ToricNormalConeFaces
section Source_ToricNormalConeFaces

-- original header: module
-- original header: public import PaperVerification.ToricDualNormalCone
-- original header: @[expose] public section
/-!
# Intersections of actual normal cones

An intersection with another point's normal cone is the zero-coordinate face
cut out by the displacement to that point. The proof expands a normal in an
actual dual integral basis and uses nonnegativity of every summand.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.LatticePolytope

open Set
open scoped BigOperators

variable {n : ℕ} (P : LatticePolytope n)

/-- A normal supports two carrier points precisely when its support value
agrees at those points. -/
theorem mem_normalCone_inter_iff (v w : Ambient n)
    (hv : v ∈ P.carrier) (hw : w ∈ P.carrier) (u : Ambient n) :
    u ∈ P.normalCone v ∩ P.normalCone w ↔
      u ∈ P.normalCone v ∧ (∑ j, u j * (w j - v j)) = 0 := by
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) u
  have hmem (x : Ambient n) :
      u ∈ P.normalCone x ↔ ∀ y ∈ P.carrier, f x ≤ f y := by
    change (∀ y ∈ P.carrier, 0 ≤ f (y - x)) ↔ _
    simp only [map_sub, sub_nonneg]
  have hp : (∑ j, u j * (w j - v j)) = f w - f v := by
    change f (w - v) = _
    exact f.map_sub w v
  change (u ∈ P.normalCone v ∧ u ∈ P.normalCone w) ↔ _
  simp only [hmem v, hmem w, hp]
  constructor
  · rintro ⟨huv, huw⟩
    exact ⟨huv, sub_eq_zero.mpr (le_antisymm (huw v hv) (huv w hw))⟩
  · rintro ⟨huv, heq⟩
    refine ⟨huv, ?_⟩
    intro y hy
    rw [sub_eq_zero.mp heq]
    exact huv y hy

/-- In any genuine integral basis generating the normal cone at v, its
intersection with the cone at w is the coordinate face consisting of those
primitive normals that vanish on w-v. -/
theorem normalCone_inter_eq_latticeRayCone
    (v w : Ambient n) (hv : v ∈ P.carrier) (hw : w ∈ P.carrier)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hcone : P.normalCone v =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n))) :
    P.normalCone v ∩ P.normalCone w =
      (latticeRayCone ((Finset.univ.filter (fun i =>
        (∑ j, embed n (d i) j * (w j - v j)) = 0)).image d) : Set (Ambient n)) := by
  classical
  let b := integralBasisReal d
  let height : Fin n → ℝ := fun i => ∑ j, embed n (d i) j * (w j - v j)
  have hheight (i : Fin n) : 0 ≤ height i := by
    have hi : embed n (d i) ∈ P.normalCone v := by
      rw [hcone]
      exact latticeRayCone_generator _ (Finset.mem_image.mpr
        ⟨i, Finset.mem_univ i, rfl⟩)
    exact hi w hw
  have hmem (u : Ambient n) :
      u ∈ P.normalCone v ↔ ∀ i, 0 ≤ b.repr u i := by
    rw [hcone]
    change u ∈ latticeRayCone (Finset.univ.image d) ↔ _
    rw [mem_latticeRayCone_basis_iff]
    simp only [Finset.mem_univ, not_true_eq_false, false_implies, implies_true, and_true, b]
  have hpair (u : Ambient n) :
      (∑ j, u j * (w j - v j)) = ∑ i, b.repr u i * height i := by
    let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) (w - v)
    have hf (i : Fin n) : f (b i) = height i := by
      change ((w - v) ⬝ᵥ (b i)) = _
      rw [dotProduct_comm]
      rw [show b i = embed n (d i) from integralBasisReal_apply d i]
      rfl
    have hs := congrArg f (b.sum_repr u)
    have hsum : f u = ∑ i, b.repr u i * f (b i) := by
      simpa only [map_sum, map_smul, smul_eq_mul] using hs.symm
    calc
      (∑ j, u j * (w j - v j)) = f u := dotProduct_comm u (w - v)
      _ = ∑ i, b.repr u i * height i := by simpa only [hf] using hsum
  ext u
  rw [P.mem_normalCone_inter_iff v w hv hw u, hmem u, hpair u]
  change ((∀ i, 0 ≤ b.repr u i) ∧ (∑ i, b.repr u i * height i) = 0) ↔
    u ∈ latticeRayCone ((Finset.univ.filter (fun i => height i = 0)).image d)
  rw [mem_latticeRayCone_basis_iff]
  change ((∀ i, 0 ≤ b.repr u i) ∧ (∑ i, b.repr u i * height i) = 0) ↔
    (∀ i, 0 ≤ b.repr u i) ∧
      ∀ i ∉ Finset.univ.filter (fun i => height i = 0), b.repr u i = 0
  constructor
  · rintro ⟨hu, hsum⟩
    refine ⟨hu, ?_⟩
    intro i hi
    have hne : height i ≠ 0 := by simpa only [Finset.mem_filter, Finset.mem_univ,
      true_and] using hi
    have hp : b.repr u i * height i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg (hu j) (hheight j))).mp hsum i (Finset.mem_univ i)
    exact (mul_eq_zero.mp hp).resolve_right hne
  · rintro ⟨hu, hz⟩
    refine ⟨hu, Finset.sum_eq_zero (fun i _ => ?_)⟩
    by_cases hi : height i = 0
    · rw [hi, mul_zero]
    · have hnot : i ∉ Finset.univ.filter (fun i => height i = 0) := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
      rw [hz i hnot, zero_mul]

/-- For a primitive edge basis, the vanishing test above is exactly the
corresponding primal coordinate of the displacement. -/
theorem normalCone_inter_eq_dual_coordinate_face
    (vZ : Lattice n) (w : Ambient n)
    (hv : embed n vZ ∈ P.carrier) (hw : w ∈ P.carrier)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (lengths : Fin n → ℕ)
    (hedges : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)))
    (hcone : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) i) :
    P.normalCone (embed n vZ) ∩ P.normalCone w =
      (latticeRayCone ((Finset.univ.filter (fun i =>
        (integralBasisReal b).repr (w - embed n vZ) i = 0)).image
          (integralDualBasis b)) : Set (Ambient n)) := by
  have h := P.normalCone_inter_eq_latticeRayCone (embed n vZ) w hv hw
    (integralDualBasis b)
    (P.normalCone_eq_latticeRayCone vZ b lengths hedges hcone)
  have he (i : Fin n) :
      (∑ j, embed n (integralDualBasis b i) j * (w j - embed n vZ j)) =
        (integralBasisReal b).repr (w - embed n vZ) i :=
    integralDualBasis_real_pairing b i (w - embed n vZ)
  simpa only [he] using h

end PaperVerification.ToricGeometry.LatticePolytope

end
end Source_ToricNormalConeFaces
-- END ORIGINAL PaperVerification.ToricNormalConeFaces


-- BEGIN ORIGINAL PaperVerification.ToricNormalConeRealization
section Source_ToricNormalConeRealization

-- original header: module
-- original header: public import PaperVerification.ToricNormalConeFaces
-- original header: public import Mathlib.Analysis.Convex.Combination
-- original header: @[expose] public section
/-!
# Every coordinate subcone is an actual normal cone

A positive average of a vertex and the omitted incident edge endpoints
realizes any selected subset of primitive normals. This is a direct convex
argument, including the zero-dimensional case.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.LatticePolytope

open Set
open scoped BigOperators

variable {n : ℕ} (P : LatticePolytope n)

/-- The normal cone at an interior point of an actual chord is the
intersection of the endpoint normal cones. The midpoint suffices here. -/
theorem normalCone_midpoint (v w : Ambient n)
    (hv : v ∈ P.carrier) (hw : w ∈ P.carrier) :
    P.normalCone (AffineMap.lineMap v w (1 / 2 : ℝ)) =
      P.normalCone v ∩ P.normalCone w := by
  ext u
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) u
  have hmem (x : Ambient n) :
      u ∈ P.normalCone x ↔ ∀ y ∈ P.carrier, f x ≤ f y := by
    change (∀ y ∈ P.carrier, 0 ≤ f (y - x)) ↔ _
    simp only [map_sub, sub_nonneg]
  have hmid : f (AffineMap.lineMap v w (1 / 2 : ℝ)) = (f v + f w) / 2 := by
    simp only [AffineMap.lineMap_apply_module, map_add, map_smul, smul_eq_mul]
    ring
  change u ∈ P.normalCone _ ↔ u ∈ P.normalCone v ∧ u ∈ P.normalCone w
  simp only [hmem]
  constructor
  · intro hm
    have hmv := hm v hv
    have hmw := hm w hw
    constructor
    · intro z hz
      have hmz := hm z hz
      linarith
    · intro z hz
      have hmz := hm z hz
      linarith
  · rintro ⟨huv, huw⟩ z hz
    have hvz := huv z hz
    have hwz := huw z hz
    linarith

/-- Every subset of the primitive normal basis at a smooth corner is the
entire ordinary normal cone at an explicitly constructed carrier point. -/
theorem normalCone_subbasis_realized
    (vZ : Lattice n) (hv : embed n vZ ∈ P.carrier)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (lengths : Fin n → ℕ)
    (hedges : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)))
    (hcone : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) i)
    (I : Finset (Fin n)) :
    ∃ x ∈ P.carrier,
      P.normalCone x = (latticeRayCone (I.image (integralDualBasis b)) : Set (Ambient n)) := by
  classical
  let v := embed n vZ
  let bR := integralBasisReal b
  let t : ℝ := 1 / ((n : ℝ) + 1)
  let s : Fin n → ℝ := fun i => if i ∈ I then 0 else t
  let d : Fin n → Ambient n := fun i => (lengths i : ℝ) • bR i
  let y : Ambient n := v + ∑ i, s i • d i
  let x : Ambient n := AffineMap.lineMap v y (1 / 2 : ℝ)
  have ht : 0 < t := by dsimp [t]; positivity
  have hs (i : Fin n) : 0 ≤ s i ∧ s i ≤ t := by
    dsimp [s]
    split_ifs <;> constructor <;> linarith
  have hsum : ∑ i, s i ≤ (1 : ℝ) := by
    calc
      (∑ i, s i) ≤ ∑ _ : Fin n, t :=
        Finset.sum_le_sum (fun i _ => (hs i).2)
      _ = (n : ℝ) * t := by simp
      _ ≤ 1 := by
        have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        simpa only [t, div_eq_mul_inv, one_mul] using
          (div_le_one hn).mpr (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)
  have hd (i : Fin n) : v + (1 : ℝ) • d i ∈ P.carrier := by
    have he := (P.edge_endpoints_extreme (hedges i).2).2.1
    simpa only [v, d, bR, one_smul, map_add, embed_int_smul, Int.cast_natCast,
      integralBasisReal_apply] using he
  have hy : y ∈ P.carrier :=
    PaperVerification.Toric.corner_simplex_mem P.carrier (convex_convexHull ℝ _)
      v hv d 1 (by norm_num) hd s (fun i => (hs i).1) hsum
  have hx : x ∈ P.carrier :=
    (convex_convexHull ℝ _).lineMap_mem hv hy
      ⟨by norm_num, by norm_num⟩
  have hcy (i : Fin n) : bR.coord i (y - v) = s i * (lengths i : ℝ) := by
    dsimp [y]
    rw [add_sub_cancel_left, map_sum]
    simp [d, map_smul, Module.Basis.coord_apply,
      Module.Basis.repr_self_apply, Finsupp.single_apply, smul_eq_mul]
  have hcx (i : Fin n) :
      bR.repr (x - v) i = (1 / 2 : ℝ) * (s i * (lengths i : ℝ)) := by
    change bR.coord i (x - v) = _
    dsimp [x]
    rw [AffineMap.lineMap_apply_module', add_sub_cancel_right, map_smul,
      smul_eq_mul, hcy]
  have hzero (i : Fin n) : bR.repr (x - v) i = 0 ↔ i ∈ I := by
    rw [hcx]
    by_cases hi : i ∈ I
    · simp [s, hi]
    · have hlen : (0 : ℝ) < lengths i := by exact_mod_cast (hedges i).1
      have hp : (0 : ℝ) < (1 / 2 : ℝ) * (s i * (lengths i : ℝ)) := by
        rw [show s i = t by simp only [s, if_neg hi]]
        exact mul_pos (by norm_num) (mul_pos ht hlen)
      simp only [hi, iff_false]
      exact ne_of_gt hp
  have hsub : P.normalCone x ⊆ P.normalCone v := by
    change P.normalCone (AffineMap.lineMap v y (1 / 2 : ℝ)) ⊆ P.normalCone v
    rw [P.normalCone_midpoint v y hv hy]
    exact Set.inter_subset_left
  have hfilter : Finset.univ.filter
      (fun i => (integralBasisReal b).repr (x - embed n vZ) i = 0) = I := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hzero i
  have hinter := P.normalCone_inter_eq_dual_coordinate_face vZ x hv hx
    b lengths hedges hcone
  rw [Set.inter_eq_right.mpr hsub, hfilter] at hinter
  exact ⟨x, hx, hinter⟩

/-- Every subset of a primitive normal basis belongs to the actual normal fan. -/
theorem subbasis_mem_normalFan
    (vZ : Lattice n) (hv : embed n vZ ∈ P.carrier)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (lengths : Fin n → ℕ)
    (hedges : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)))
    (hcone : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) i)
    (I : Finset (Fin n)) :
    (latticeRayCone (I.image (integralDualBasis b)) : Set (Ambient n)) ∈ P.normalFan := by
  obtain ⟨x, hx, hnormal⟩ := P.normalCone_subbasis_realized vZ hv b lengths hedges hcone I
  exact ⟨x, hx, hnormal.symm⟩

end PaperVerification.ToricGeometry.LatticePolytope

end
end Source_ToricNormalConeRealization
-- END ORIGINAL PaperVerification.ToricNormalConeRealization


-- BEGIN ORIGINAL PaperVerification.ToricNormalConeAverages
section Source_ToricNormalConeAverages

-- original header: module
-- original header: public import PaperVerification.ToricNormalConeRealization
-- original header: @[expose] public section
/-!
# Normal cones of finite convex combinations

All support inequalities are the actual coordinate-pairing inequalities of
the lattice polytope. Zero weights are ignored; positive weights force equality
of the support value at every participating point.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.LatticePolytope

open Set
open scoped BigOperators

variable {n : ℕ} (P : LatticePolytope n)

/-- A normal supports a finite convex average exactly when it supports every
point with positive weight. The averaging family need not consist of vertices. -/
theorem mem_normalCone_convex_average {ι : Type*} [Fintype ι]
    (v : ι → Ambient n) (p : ι → ℝ)
    (hv : ∀ i, v i ∈ P.carrier)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (u : Ambient n) :
    u ∈ P.normalCone (∑ i, p i • v i) ↔
      ∀ i, 0 < p i → u ∈ P.normalCone (v i) := by
  classical
  let x : Ambient n := ∑ i, p i • v i
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) u
  have hmem (z : Ambient n) :
      u ∈ P.normalCone z ↔ ∀ y ∈ P.carrier, f z ≤ f y := by
    change (∀ y ∈ P.carrier, 0 ≤ f (y - z)) ↔ _
    simp only [map_sub, sub_nonneg]
  have hfx : f x = ∑ i, p i * f (v i) := by
    simp only [x, map_sum, map_smul, smul_eq_mul]
  change u ∈ P.normalCone x ↔ _
  simp only [hmem]
  constructor
  · intro hx i hi y hy
    have hnonneg (j : ι) : 0 ≤ p j * (f (v j) - f x) :=
      mul_nonneg (hp0 j) (sub_nonneg.mpr (hx (v j) (hv j)))
    have hsum : (∑ j, p j * (f (v j) - f x)) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul, ← hfx,
        sub_self]
    have hterm : p i * (f (v i) - f x) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hsum i
        (Finset.mem_univ i)
    have heq : f (v i) = f x :=
      sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left (ne_of_gt hi))
    rw [heq]
    exact hx y hy
  · intro h y hy
    have hterm (i : ι) : p i * f (v i) ≤ p i * f y := by
      by_cases hi : p i = 0
      · simp only [hi, zero_mul, le_refl]
      · have hip : 0 < p i := lt_of_le_of_ne (hp0 i) (Ne.symm hi)
        exact mul_le_mul_of_nonneg_left (h i hip y hy) (hp0 i)
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
    rw [← hfx, ← Finset.sum_mul, hp1, one_mul] at hs
    exact hs

/-- Set-valued form: the normal cone of a convex average is the intersection
of the actual normal cones at precisely its positive-weight points. -/
theorem normalCone_convex_average {ι : Type*} [Fintype ι]
    (v : ι → Ambient n) (p : ι → ℝ)
    (hv : ∀ i, v i ∈ P.carrier)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    P.normalCone (∑ i, p i • v i) =
      ⋂ i ∈ Finset.univ.filter (fun i => 0 < p i), P.normalCone (v i) := by
  classical
  ext u
  simp only [Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and,
    P.mem_normalCone_convex_average v p hv hp0 hp1 u]

end PaperVerification.ToricGeometry.LatticePolytope

end
end Source_ToricNormalConeAverages
-- END ORIGINAL PaperVerification.ToricNormalConeAverages


