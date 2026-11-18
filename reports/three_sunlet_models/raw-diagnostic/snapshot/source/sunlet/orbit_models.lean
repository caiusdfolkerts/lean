module

public import sunlet.partition_subgroups
public import sunlet.height_elimination
public import sunlet.main_dimension
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-! Actual identified-coordinate models: class orders, exceptional dimensions,
and the original six-family automorphism-orbit parameterization.
These are ordinary Lean proof bodies. Completion is established only by the
corresponding successful build records; provenance adds no proof constants. -/

@[expose] public section
noncomputable section
open scoped BigOperators

/- Source: GoodOrders.lean -/
namespace Sunlet.OrbitHeight.InverseStablePartition

variable {G C : Type*} [AddCommGroup G] [Fintype G] [Fintype C]
  [LinearOrder C] (P : InverseStablePartition G C)

/-- The literal three-part exceptional partition, with its actual index-two subgroup. -/
def IndexTwoException : Prop :=
  ∃ (H : AddSubgroup G) (d c : C), H.index = 2 ∧
    d ≠ P.zeroClass ∧ c ≠ P.zeroClass ∧ d ≠ c ∧
    (∀ a, P.classOf a = d ↔ a ∉ H) ∧
    (∀ a, P.classOf a = c ↔ a ∈ H ∧ a ≠ 0)

private theorem card_le_two_of_two_values (d : C)
    (h : ∀ i, i = P.zeroClass ∨ i = d) : Fintype.card C ≤ 2 := by
  classical
  have hs : (Finset.univ : Finset C) ⊆ {P.zeroClass, d} := by
    intro i _
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h i
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)

/-- A complement class placed first among nonzero classes forces every
nonzero coordinate of a nonnegative, nonzero height to be positive. -/
theorem positive_nonzero_of_first_complement {d : C} (hd : P.ComplementClass d)
    (hfirst : ∀ i, i ≠ P.zeroClass → d ≤ i)
    {x : C → ℚ} (hx : x ∈ P.heightSpace) (hn : ∀ i, 0 ≤ x i) (hx0 : x ≠ 0) :
    ∀ i, i ≠ P.zeroClass → 0 < x i := by
  obtain ⟨H, hH⟩ := hd
  have hdpos : 0 < x d := by
    by_contra h
    have hd0 : x d = 0 := le_antisymm (le_of_not_gt h) (hn d)
    obtain ⟨a, ha⟩ := P.surjective d
    have haH := (hH a).mpr ha
    have htop := subgroup_eq_top_of_contains_complement H (P.zeroSubgroup x hx hn)
      a haH (by intro b hb; change x (P.classOf b) = 0; rw [(hH b).mp hb, hd0])
    apply hx0
    funext i
    obtain ⟨b, rfl⟩ := P.surjective i
    have hb : b ∈ P.zeroSubgroup x hx hn := by rw [htop]; trivial
    exact hb
  intro i hi
  exact hdpos.trans_le (P.monotone_of_nonnegative hx hn (hfirst i hi))

/-- With at least three classes, a first complement class eliminates every
bad height except precisely the three-orbit index-two partition. -/
theorem good_of_first_complement {d : C} (hd : P.ComplementClass d)
    (hfirst : ∀ i, i ≠ P.zeroClass → d ≤ i)
    (hcard : 3 ≤ Fintype.card C) (hnot : ¬ P.IndexTwoException) : P.GoodHeightOrder := by
  intro x hx hn hx0 hbad
  obtain ⟨r, hr, hy, _, hlevels, hR⟩ := P.normalized_nonnegative_height hx hn hx0
  let y : C → ℚ := r • x
  change y ∈ P.heightSpace at hy
  change ∀ i, y i = 0 ∨ y i = 1 ∨ y i = 2 at hlevels
  have hyz : y P.zeroClass = 0 := hy.1
  have hy0 : y ≠ 0 := smul_ne_zero hr hx0
  have hyn : ∀ i, 0 ≤ y i := by
    intro i
    rcases hlevels i with h | h | h <;> rw [h] <;> norm_num
  have hpos := P.positive_nonzero_of_first_complement hd hfirst hy hyn hy0
  have hyr : 0 < r := by
    obtain ⟨i, hi⟩ : ∃ i, 0 < x i := by
      by_contra h
      push_neg at h
      apply hx0
      funext i
      exact le_antisymm (h i) (hn i)
    have hri : 0 ≤ r * x i := hyn i
    have hrn : 0 ≤ r := nonneg_of_mul_nonneg_left hri hi
    exact lt_of_le_of_ne hrn (Ne.symm hr)
  have hybad : P.BadHeight y := by
    intro i j hi hj hpi hpj
    apply hbad i j hi hj
    · exact pos_of_mul_pos_right hpi hyr.le
    · exact pos_of_mul_pos_right hpj hyr.le
  have hzero (i : C) : y i = 0 ↔ i = P.zeroClass := by
    constructor
    · intro hi
      by_contra hn
      exact (ne_of_gt (hpos i hn)) hi
    · rintro rfl
      exact hy.1
  have one_level (α : ℚ) (hl : ∀ i, y i = 0 ∨ y i = α) : False := by
    rcases P.one_level_structure hy hyn hl hy0 with ⟨i, hi⟩ | hindex
    · have hd' : P.ComplementClass i := ⟨_, hi⟩
      have hid := P.complementClass_unique hd' hd
      have htwo : ∀ j, j = P.zeroClass ∨ j = d := by
        intro j
        by_cases hj : j = P.zeroClass
        · exact Or.inl hj
        · right
          obtain ⟨a, ha⟩ := P.surjective j
          have hna : a ∉ P.zeroSubgroup y hy hyn := by
            change y (P.classOf a) ≠ 0
            rw [ha]
            exact ne_of_gt (hpos j hj)
          exact ha.symm.trans (((hi a).mp hna).trans hid)
      have hle := P.card_le_two_of_two_values d htwo
      omega
    · have hbot : P.zeroSubgroup y hy hyn = ⊥ := by
        ext a
        change y (P.classOf a) = 0 ↔ a = 0
        rw [hzero, P.zero_iff]
      rw [hbot, AddSubgroup.index_bot, Nat.card_eq_fintype_card] at hindex
      have hle := Fintype.card_le_of_surjective P.classOf P.surjective
      omega
  by_cases hone : ∃ a : G, y (P.classOf a) = 1
  · obtain ⟨a, ha⟩ := hone
    by_cases htwo : ∃ c : G, y (P.classOf c) = 2
    · obtain ⟨c, hc⟩ := htwo
      obtain ⟨H, hindex, hout, hupper⟩ :=
        P.two_level_bad_structure_index hy hyn hlevels hybad a c ha hc
      apply hnot
      refine ⟨H, P.classOf a, P.classOf c, hindex, ?_, ?_, ?_, ?_, ?_⟩
      · intro he
        rw [he, hyz] at ha
        norm_num at ha
      · intro he
        rw [he, hyz] at hc
        norm_num at hc
      · intro he
        rw [he, hc] at ha
        norm_num at ha
      · intro b
        exact (hout b).symm
      · intro b
        rw [← hupper b]
        constructor
        · intro hb
          constructor
          · by_contra hbn
            have he := (hout b).mp hbn
            rw [he, ha] at hb
            norm_num at hb
          · intro he
            rw [he, P.zero_class, hyz] at hb
            norm_num at hb
        · rintro ⟨hb, hb0⟩
          rcases hlevels (P.classOf b) with h | h | h
          · exact (hb0 ((P.zero_iff b).mp ((hzero _).mp h))).elim
          · have he := P.level_one_single_class hy hyn b a c h ha hc
            exact ((hout b).mpr he hb).elim
          · exact h
    · apply one_level 1
      intro i
      rcases hlevels i with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · obtain ⟨b, hb⟩ := P.surjective i
        exact (htwo ⟨b, by simpa only [hb] using h⟩).elim
  · apply one_level 2
    intro i
    rcases hlevels i with h | h | h
    · exact Or.inl h
    · obtain ⟨b, hb⟩ := P.surjective i
      exact (hone ⟨b, by simpa only [hb] using h⟩).elim
    · exact Or.inr h

/-- A nonzero class in the intersection of all relevant index-two subgroups,
placed last, excludes every bad height when no complement class exists. -/
theorem good_of_last_core (hno : ¬ ∃ i, P.ComplementClass i)
    (a : G) (ha : a ∈ P.indexTwoCore) (ha0 : a ≠ 0)
    (hlast : ∀ i, i ≤ P.classOf a) : P.GoodHeightOrder := by
  intro x hx hn hx0 hbad
  obtain ⟨r, hr, hy, hmono, hlevels, hR⟩ := P.normalized_nonnegative_height hx hn hx0
  let y : C → ℚ := r • x
  change y ∈ P.heightSpace at hy
  change ∀ i, y i = 0 ∨ y i = 1 ∨ y i = 2 at hlevels
  have hyz : y P.zeroClass = 0 := hy.1
  have hy0 : y ≠ 0 := smul_ne_zero hr hx0
  have hyn : ∀ i, 0 ≤ y i := by
    intro i
    rcases hlevels i with h | h | h <;> rw [h] <;> norm_num
  have hyr : 0 < r := by
    obtain ⟨i, hi⟩ : ∃ i, 0 < x i := by
      by_contra h
      push_neg at h
      apply hx0
      funext i
      exact le_antisymm (h i) (hn i)
    have hrn : 0 ≤ r := nonneg_of_mul_nonneg_left (hyn i) hi
    exact lt_of_le_of_ne hrn (Ne.symm hr)
  have hybad : P.BadHeight y := by
    intro i j hi hj hpi hpj
    exact hbad i j hi hj (pos_of_mul_pos_right hpi hyr.le) (pos_of_mul_pos_right hpj hyr.le)
  have hindex := (P.normalized_bad_obstruction hy hyn hy0 hlevels hybad).resolve_left hno
  have ham := (P.mem_indexTwoCore a).mp ha _ hindex (P.zeroSubgroup_saturated hy hyn)
  have haz : y (P.classOf a) = 0 := ham
  change Monotone y at hmono
  apply hy0
  funext i
  change y i = 0
  exact le_antisymm (by simpa only [haz] using hmono (hlast i)) (hyn i)

end Sunlet.OrbitHeight.InverseStablePartition

/- Source: OrderConstruction.lean -/
namespace Sunlet.OrbitHeight.InverseStablePartition

variable {G C : Type*} [AddCommGroup G] [Fintype G] [Fintype C]
  [LinearOrder C] (P : InverseStablePartition G C)

def priorityKey (d : C) (last : Bool) (i : C) : ℕ ×ₗ C :=
  toLex (if i = P.zeroClass then 0 else if i = d then (if last then 2 else 1)
    else (if last then 1 else 2), i)

abbrev priorityOrder (d : C) (last : Bool) : LinearOrder C :=
  LinearOrder.lift' (P.priorityKey d last) (by
    intro a b h
    exact congrArg (fun p : ℕ ×ₗ C => (ofLex p).2) h)

theorem priorityOrder_zero_le (d : C) (last : Bool) :
    ∀ i, @LE.le C (P.priorityOrder d last).toLE P.zeroClass i := by
  intro i
  change P.priorityKey d last P.zeroClass ≤ P.priorityKey d last i
  by_cases hi : i = P.zeroClass
  · subst i
    exact le_rfl
  · by_cases hid : i = d
    · subst i
      cases last <;> simp [priorityKey, Prod.Lex.toLex_le_toLex, hi]
    · cases last <;> simp [priorityKey, Prod.Lex.toLex_le_toLex, hi, hid]

theorem priorityOrder_first (d : C) (hd : d ≠ P.zeroClass) :
    ∀ i, i ≠ P.zeroClass → @LE.le C (P.priorityOrder d false).toLE d i := by
  intro i hi
  change P.priorityKey d false d ≤ P.priorityKey d false i
  by_cases hid : i = d
  · subst i
    exact le_rfl
  · simp [priorityKey, Prod.Lex.toLex_le_toLex, hd, hi, hid]

theorem priorityOrder_last (d : C) (hd : d ≠ P.zeroClass) :
    ∀ i, @LE.le C (P.priorityOrder d true).toLE i d := by
  intro i
  change P.priorityKey d true i ≤ P.priorityKey d true d
  by_cases hid : i = d
  · subst i
    exact le_rfl
  · by_cases hi : i = P.zeroClass <;>
      simp [priorityKey, Prod.Lex.toLex_le_toLex, hd, hi, hid]

/-- Every nonexceptional partition with at least three classes either has
singleton classes, or admits the exact good order required for the rank proof. -/
theorem good_order_or_singletons (hcard : 3 ≤ Fintype.card C)
    (hnot : ¬ P.IndexTwoException) :
    Function.Injective P.classOf ∨
      ∃ O : LinearOrder C,
        (∀ i, @LE.le C O.toLE P.zeroClass i) ∧
        @GoodHeightOrder G C _ O P := by
  classical
  by_cases hcomp : ∃ d, P.ComplementClass d
  · right
    obtain ⟨d, hd⟩ := hcomp
    let O := P.priorityOrder d false
    have hmin := P.priorityOrder_zero_le d false
    have hfirst := P.priorityOrder_first d (P.complementClass_ne_zero hd)
    refine ⟨P.priorityOrder d false, hmin, ?_⟩
    exact @good_of_first_complement G C _ _ _ (P.priorityOrder d false) P d hd hfirst hcard hnot
  · by_cases hbot : P.indexTwoCore = ⊥
    · exact Or.inl (P.classOf_injective_of_indexTwoCore_bot hbot)
    · right
      obtain ⟨a, ha, ha0⟩ : ∃ a : G, a ∈ P.indexTwoCore ∧ a ≠ 0 := by
        by_contra h
        push_neg at h
        apply hbot
        ext a
        constructor
        · intro ha
          exact h a ha
        · intro ha
          have hzero : a = 0 := ha
          rw [hzero]
          exact P.indexTwoCore.zero_mem
      have hd : P.classOf a ≠ P.zeroClass := fun h => ha0 ((P.zero_iff a).mp h)
      let O := P.priorityOrder (P.classOf a) true
      have hmin := P.priorityOrder_zero_le (P.classOf a) true
      have hlast := P.priorityOrder_last (P.classOf a) hd
      refine ⟨P.priorityOrder (P.classOf a) true, hmin, ?_⟩
      exact @good_of_last_core G C _ _ _ (P.priorityOrder (P.classOf a) true) P hcomp a ha ha0 hlast

end Sunlet.OrbitHeight.InverseStablePartition

/- Source: SingletonClasses.lean -/
namespace Sunlet.Identified

variable {K G C : Type*} [Field K] [AddCommGroup G] [Fintype G] [Fintype C]
  [DecidableEq C]

def parameterRename (q : G → C) : ParamVar G G → ParamVar C C
  | .s a => .s (q a)
  | .t a => .t (q a)
  | .h a => .h (q a)
  | .u a => .u (q a)
  | .v a => .v (q a)

theorem parameterRename_injective (q : G → C) (hq : Function.Injective q) :
    Function.Injective (parameterRename q) := by
  intro a b h
  cases a <;> cases b <;> simp_all [parameterRename, hq.eq_iff]

theorem rename_coordinatePolynomial (q : G → C) (ab : G × G) :
    MvPolynomial.rename (parameterRename q)
      (Sunlet.coordinatePolynomial (K := K) Sunlet.addTranslationPerm ab) =
      coordinatePolynomial (K := K) q ab := by
  simp [Sunlet.coordinatePolynomial, coordinatePolynomial,
    Sunlet.addTranslationPerm, parameterRename]

theorem comorphism_eq_rename (q : G → C) :
    PolynomialImage.comorphism (coordinatePolynomial (K := K) q) =
      (MvPolynomial.rename (parameterRename q)).comp
        (PolynomialImage.comorphism
          (Sunlet.coordinatePolynomial (K := K) Sunlet.addTranslationPerm)) := by
  ext1 ab
  simp only [AlgHom.comp_apply, PolynomialImage.comorphism, MvPolynomial.aeval_X]
  exact (rename_coordinatePolynomial (K := K) q ab).symm

theorem definingIdeal_eq_of_injective (q : G → C) (hq : Function.Injective q) :
    PolynomialImage.definingIdeal (coordinatePolynomial (K := K) q) =
      PolynomialImage.definingIdeal
        (Sunlet.coordinatePolynomial (K := K) Sunlet.addTranslationPerm) := by
  ext p
  change PolynomialImage.comorphism (coordinatePolynomial (K := K) q) p = 0 ↔ _
  rw [comorphism_eq_rename, AlgHom.comp_apply]
  exact (MvPolynomial.rename_injective (parameterRename q)
    (parameterRename_injective q hq)).eq_iff' (map_zero _)

/-- Singleton classes give the exact unrestricted dimension, on the original
pair-indexed coordinate ring, not merely an abstract isomorphic parameter count. -/
theorem imageClosure_dimension_of_bijective [IsAlgClosed K]
    (q : G → C) (hq : Function.Bijective q) (hm : 5 ≤ Fintype.card G) :
    ringKrullDim (MvPolynomial (G × G) K ⧸ MvPolynomial.vanishingIdeal K
      (PolynomialImage.closure (coordinatePolynomial (K := K) q))) =
        (5 * Fintype.card C - 4 : ℕ) := by
  classical
  rw [PolynomialImage.vanishingIdeal_imageClosure, definingIdeal_eq_of_injective q hq.1]
  have h := Sunlet.paper_theorem_1_1 (K := K) GroupCoordinates.translationLatinSystem hm
  rw [Sunlet.imageClosure, PolynomialImage.vanishingIdeal_imageClosure] at h
  have hc : Fintype.card G = Fintype.card C := Fintype.card_congr (Equiv.ofBijective q hq)
  change ringKrullDim (MvPolynomial (G × G) K ⧸ PolynomialImage.definingIdeal
    (Sunlet.coordinatePolynomial (K := K) Sunlet.addTranslationPerm)) =
      (5 * Fintype.card G - 4 : ℕ) at h
  rw [hc] at h
  exact h

end Sunlet.Identified

namespace Sunlet.OrbitHeight.InverseStablePartition

variable {K G C : Type*} [Field K] [IsAlgClosed K] [AddCommGroup G]
  [Fintype G] [Fintype C] [LinearOrder C] (P : InverseStablePartition G C)

/-- The complete nonexceptional inverse-stable partition result. It covers
all class counts at least three, with no extra rank or order hypothesis. -/
theorem nonexceptional_imageClosure_dimension
    (hm : 5 ≤ Fintype.card G) (hr : 3 ≤ Fintype.card C)
    (hnot : ¬ P.IndexTwoException) :
    ringKrullDim (MvPolynomial (G × G) K ⧸ MvPolynomial.vanishingIdeal K
      (PolynomialImage.closure (Identified.coordinatePolynomial (K := K) P.classOf))) =
        (5 * Fintype.card C - 4 : ℕ) := by
  classical
  rcases P.good_order_or_singletons hr hnot with hinj | ⟨O, hmin, hgood⟩
  · exact Identified.imageClosure_dimension_of_bijective P.classOf ⟨hinj, P.surjective⟩ hm
  · exact @imageClosure_dimension_of_good_order G C _ _ _ O P K _ _ hmin hgood

end Sunlet.OrbitHeight.InverseStablePartition

/- Source: FiniteCoordinateValues.lean -/
namespace PolynomialImage

variable {K σ X I : Type*} [Field K] [Fintype I]

/-- The hypothesis says that every coordinate is exactly one selected
coordinate polynomial. The conclusion concerns the actual substitution ideal. -/
theorem dimension_le_of_coordinate_representatives
    (f : X → MvPolynomial σ K) (r : I → X) (c : X → I)
    (hc : ∀ x, f (r (c x)) = f x) :
    ringKrullDim (MvPolynomial X K ⧸ definingIdeal f) ≤ (Fintype.card I : ℕ) := by
  let A := imageAlgebra f
  let g : I → A := fun i => ⟨f (r i), by
    refine ⟨MvPolynomial.X (r i), ?_⟩
    simp [comorphism]⟩
  let φ : MvPolynomial I K →ₐ[K] A := MvPolynomial.aeval g
  have hcomp : φ.comp (MvPolynomial.rename c) = (comorphism f).rangeRestrict := by
    ext1 x
    apply Subtype.ext
    simp only [AlgHom.comp_apply, MvPolynomial.rename_X, φ, MvPolynomial.aeval_X]
    change f (r (c x)) = (comorphism f) (MvPolynomial.X x)
    simpa only [comorphism, MvPolynomial.aeval_X] using hc x
  have hsurj : Function.Surjective φ := by
    intro a
    obtain ⟨p, hp⟩ := (comorphism f).rangeRestrict_surjective a
    refine ⟨MvPolynomial.rename c p, ?_⟩
    exact (AlgHom.congr_fun hcomp p).trans hp
  rw [ringKrullDim_eq_of_ringEquiv (coordinateRingEquivImage f).toRingEquiv]
  have h := ringKrullDim_le_of_surjective φ.toRingHom hsurj
  simpa using h

/-- The same bound for the full algebraic image closure. -/
theorem imageClosure_dimension_le_of_coordinate_representatives [Infinite K]
    (f : X → MvPolynomial σ K) (r : I → X) (c : X → I)
    (hc : ∀ x, f (r (c x)) = f x) :
    ringKrullDim (MvPolynomial X K ⧸ MvPolynomial.vanishingIdeal K (closure f)) ≤
      (Fintype.card I : ℕ) := by
  rw [vanishingIdeal_imageClosure]
  exact dimension_le_of_coordinate_representatives f r c hc

/-- A nonzero relation among the selected coordinate values lowers the upper
bound by one. Both the relation and its nonvanishing are explicit hypotheses
for this general algebraic lemma, and are proved for each model application. -/
theorem dimension_succ_le_of_coordinate_relation
    (f : X → MvPolynomial σ K) (r : I → X) (c : X → I)
    (hc : ∀ x, f (r (c x)) = f x)
    (p : MvPolynomial I K) (hp : p ≠ 0)
    (hrel : MvPolynomial.aeval (fun i => f (r i)) p = 0) :
    ringKrullDim (MvPolynomial X K ⧸ definingIdeal f) + 1 ≤ (Fintype.card I : ℕ) := by
  let A := imageAlgebra f
  let g : I → A := fun i => ⟨f (r i), by
    refine ⟨MvPolynomial.X (r i), ?_⟩
    simp [comorphism]⟩
  let φ : MvPolynomial I K →ₐ[K] A := MvPolynomial.aeval g
  have hcomp : φ.comp (MvPolynomial.rename c) = (comorphism f).rangeRestrict := by
    ext1 x
    apply Subtype.ext
    simp only [AlgHom.comp_apply, MvPolynomial.rename_X, φ, MvPolynomial.aeval_X]
    change f (r (c x)) = (comorphism f) (MvPolynomial.X x)
    simpa only [comorphism, MvPolynomial.aeval_X] using hc x
  have hsurj : Function.Surjective φ := by
    intro a
    obtain ⟨p, hp⟩ := (comorphism f).rangeRestrict_surjective a
    exact ⟨MvPolynomial.rename c p, (AlgHom.congr_fun hcomp p).trans hp⟩
  have hmap : A.val.comp φ = MvPolynomial.aeval (fun i => f (r i)) := by
    ext1 i
    simp [φ, g]
  have hzero : φ p = 0 := by
    apply Subtype.ext
    change A.val (φ p) = 0
    rw [← AlgHom.comp_apply, hmap, hrel]
  rw [ringKrullDim_eq_of_ringEquiv (coordinateRingEquivImage f).toRingEquiv]
  have h := ringKrullDim_succ_le_of_surjective φ.toRingHom hsurj
    (mem_nonZeroDivisors_iff_ne_zero.mpr hp) hzero
  simpa using h

end PolynomialImage

/- Source: TwoOrbitDimension.lean -/
namespace Sunlet.Identified.TwoClass

variable {K G C : Type*} [Field K] [AddCommGroup G] [Fintype G] [Fintype C]
  [LinearOrder C]

variable (q : G → C) (z d : C)
  (hq : ∀ a, q a = z ↔ a = 0)
  (hclasses : ∀ i, i = z ∨ i = d) (hzd : z < d)

include hq in
private theorem qzero : q 0 = z := (hq 0).mpr rfl

include hq hclasses in
private theorem qnonzero (a : G) (ha : a ≠ 0) : q a = d := by
  rcases hclasses (q a) with h | h
  · exact (ha ((hq a).mp h)).elim
  · exact h

def representatives (a c : G) : Fin 5 → G × G :=
  ![(0, 0), (a, a), (0, a), (a, 0), (a, c)]

def coordinateRepresentative (a c : G) (i : Fin 5) : G × G :=
  ((representatives a c i).2 - (representatives a c i).1, (representatives a c i).1)

def classify (bc : G × G) : Fin 5 := by
  classical
  exact if bc.1 = bc.2 then (if bc.1 = 0 then 0 else 1)
    else if bc.1 = 0 then 2 else if bc.2 = 0 then 3 else 4

include hq hclasses hzd in
private theorem selected_exponents (a c : G) (ha : a ≠ 0) (hc : c ≠ 0) (hca : c ≠ a) :
    (fun j i => (ClassSelection.selectedExponent q {d} (representatives a c j) i : ℚ)) =
      ![(fun i => (if i = .s z then 1 else 0) + (if i = .t z then 1 else 0) +
            (if i = .v z then 1 else 0) + (if i = .h z then 1 else 0)),
        (fun i => (if i = .s d then 1 else 0) + (if i = .t d then 1 else 0) +
            (if i = .v z then 1 else 0) + (if i = .h d then 1 else 0)),
        (fun i => (if i = .s z then 1 else 0) + (if i = .t d then 1 else 0) +
            (if i = .u d then 1 else 0) + (if i = .h d then 1 else 0)),
        (fun i => (if i = .s d then 1 else 0) + (if i = .t z then 1 else 0) +
            (if i = .v d then 1 else 0) + (if i = .h d then 1 else 0)),
        (fun i => (if i = .s d then 1 else 0) + (if i = .t d then 1 else 0) +
            (if i = .u d then 1 else 0) + (if i = .h d then 1 else 0))] := by
  have hz := qzero q z hq
  have had := qnonzero q z d hq hclasses a ha
  have hcd := qnonzero q z d hq hclasses c hc
  have hnd := qnonzero q z d hq hclasses (-a) (neg_ne_zero.mpr ha)
  have hcad := qnonzero q z d hq hclasses (c-a) (sub_ne_zero.mpr hca)
  have hne := ne_of_lt hzd
  funext j i
  fin_cases j <;>
    simp [representatives, ClassSelection.selectedExponent, ClassSelection.selectsU,
      ClassSelection.uExponent, ClassSelection.vExponent, Finsupp.single_apply, eq_comm,
      hz, had, hcd, hnd, hcad, hzd, hne, hne.symm, not_lt_of_ge hzd.le, add_assoc]

include hq hclasses hzd in
private theorem selected_independent (a c : G) (ha : a ≠ 0) (hc : c ≠ 0) (hca : c ≠ a) :
    LinearIndependent ℚ
      (fun j i => (ClassSelection.selectedExponent q {d} (representatives a c j) i : ℚ)) := by
  classical
  rw [selected_exponents q z d hq hclasses hzd a c ha hc hca]
  apply Fintype.linearIndependent_iff.mpr
  intro w hw
  have hne := ne_of_lt hzd
  have hs0 := congrFun hw (.s z)
  have ht0 := congrFun hw (.t z)
  have hv0 := congrFun hw (.v z)
  have hv1 := congrFun hw (.v d)
  have hu1 := congrFun hw (.u d)
  simp [Fin.sum_univ_succ, hne, hne.symm] at hs0 ht0 hv0 hv1 hu1
  have h0 : w 0 = 0 := by linarith only [ht0, hv1]
  have h1 : w 1 = 0 := by linarith only [hv0, h0]
  have h2 : w 2 = 0 := by linarith only [hs0, h0]
  have h3 : w 3 = 0 := hv1
  have h4 : w 4 = 0 := by linarith only [hu1, h2]
  intro j
  fin_cases j <;> assumption

include hq hclasses in
private theorem coordinate_classified (a c : G) (ha : a ≠ 0) (hc : c ≠ 0) (hca : c ≠ a)
    (ab : G × G) :
    coordinatePolynomial (K := K) q
      (coordinateRepresentative a c (classify (ab.2, ab.1 + ab.2))) =
        coordinatePolynomial (K := K) q ab := by
  have hz := qzero q z hq
  have had := qnonzero q z d hq hclasses a ha
  have hcd := qnonzero q z d hq hclasses c hc
  have hnd := qnonzero q z d hq hclasses (-a) (neg_ne_zero.mpr ha)
  have hcad := qnonzero q z d hq hclasses (c-a) (sub_ne_zero.mpr hca)
  rcases ab with ⟨u,b⟩
  by_cases hu : u = 0
  · subst u
    by_cases hb : b = 0
    · subst b
      simp [classify, coordinateRepresentative, representatives, coordinatePolynomial]
    · have hbd := qnonzero q z d hq hclasses b hb
      simp [classify, hb, coordinateRepresentative, representatives, coordinatePolynomial,
        hz, had, hbd]
  · have hud := qnonzero q z d hq hclasses u hu
    have hbe : b ≠ u + b := by intro h; exact hu (add_right_cancel (show u + b = 0 + b by simpa using h.symm))
    by_cases hb : b = 0
    · subst b
      simp [classify, hu, Ne.symm hu, hbe, coordinateRepresentative, representatives, coordinatePolynomial,
        hz, had, hud]
    · have hbd := qnonzero q z d hq hclasses b hb
      by_cases hs : u + b = 0
      · simp [classify, hbe, hb, hs, coordinateRepresentative, representatives,
          coordinatePolynomial, hz, had, hnd, hud, hbd]
      · have hsd := qnonzero q z d hq hclasses (u+b) hs
        simp [classify, hbe, hb, hs, coordinateRepresentative, representatives,
          coordinatePolynomial, hz, had, hcd, hcad, hud, hbd, hsd]

include hq hclasses hzd in
/-- Five actual coordinate functions are independent and exhaust all coordinate
values; hence this is an equality of genuine Krull dimensions in every characteristic. -/
theorem coordinateRing_dimension (a c : G) (ha : a ≠ 0) (hc : c ≠ 0) (hca : c ≠ a) :
    ringKrullDim (MvPolynomial (G × G) K ⧸
      PolynomialImage.definingIdeal (coordinatePolynomial (K := K) q)) = 5 := by
  classical
  apply le_antisymm
  · have h := PolynomialImage.dimension_le_of_coordinate_representatives
      (coordinatePolynomial (K := K) q) (coordinateRepresentative a c)
      (fun ab => classify (ab.2, ab.1 + ab.2))
      (coordinate_classified q z d hq hclasses a c ha hc hca)
    simpa using h
  · have halg := ClassSelection.coordinate_subfamily_algebraicIndependent (K := K) q {d}
      (representatives a c) (selected_independent q z d hq hclasses hzd a c ha hc hca)
    let A := PolynomialImage.imageAlgebra (coordinatePolynomial (K := K) q)
    let f : Fin 5 → A := fun i =>
      ⟨coordinatePolynomial q (coordinateRepresentative a c i), by
        refine ⟨MvPolynomial.X (coordinateRepresentative a c i), ?_⟩
        simp [PolynomialImage.comorphism]⟩
    have hf : AlgebraicIndependent K f := AlgebraicIndependent.of_comp A.val halg
    letI : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective
      (PolynomialImage.comorphism (coordinatePolynomial (K := K) q)).rangeRestrict
      (PolynomialImage.comorphism (coordinatePolynomial (K := K) q)).rangeRestrict_surjective
    have hd := DimensionAlgebra.card_le_ringKrullDim_of_algebraicIndependent K A f hf
    rw [ringKrullDim_eq_of_ringEquiv
      (PolynomialImage.coordinateRingEquivImage (coordinatePolynomial (K := K) q)).toRingEquiv]
    simpa using hd

end Sunlet.Identified.TwoClass

/- Source: ThreeOrbitDimension.lean -/
namespace Sunlet.Identified.ThreeClass

attribute [local instance 0] Classical.propDecidable

variable {K G C : Type*} [Field K] [AddCommGroup G] [Fintype G] [Fintype C]
  [LinearOrder C]
variable (q : G → C) (H : AddSubgroup G) (hindex : H.index = 2)
  (z d i : C) (hzd : z < d) (hdi : d < i)
  (hq0 : ∀ a, q a = z ↔ a = 0)
  (hqD : ∀ a, q a = d ↔ a ∉ H)
  (hqI : ∀ a, q a = i ↔ a ∈ H ∧ a ≠ 0)

include hindex in
private theorem diff_mem (a b : G) : a - b ∈ H ↔ (a ∈ H ↔ b ∈ H) := by
  rw [sub_eq_add_neg, AddSubgroup.add_mem_iff_of_index_two hindex, AddSubgroup.neg_mem_iff]

include hindex hqD hqI in
private theorem diff_class (a b : G) (hab : a ≠ b) :
    q (a - b) = if (a ∈ H ↔ b ∈ H) then i else d := by
  classical
  split_ifs with h
  · exact (hqI _).mpr ⟨(diff_mem H hindex a b).mpr h, sub_ne_zero.mpr hab⟩
  · exact (hqD _).mpr (fun hm => h ((diff_mem H hindex a b).mp hm))

def representatives (a c e : G) : Fin 11 → G × G :=
  ![(0,0), (a,a), (c,c), (0,a), (a,0), (c,a), (a,c), (0,c), (c,0), (c,e), (a,a+c)]

def lowerRepresentatives (a c e : G) : Fin 10 → G × G :=
  ![(0,0), (a,a), (c,c), (0,a), (a,0), (c,a), (a,c), (0,c), (c,0), (c,e)]

def coordinateRepresentative (a c e : G) (j : Fin 11) : G × G :=
  ((representatives a c e j).2 - (representatives a c e j).1,
    (representatives a c e j).1)

def classify (bc : G × G) : Fin 11 := by
  classical
  exact if bc.1 = bc.2 then (if bc.1 = 0 then 0 else if bc.1 ∈ H then 2 else 1)
    else if bc.1 = 0 then (if bc.2 ∈ H then 7 else 3)
    else if bc.2 = 0 then (if bc.1 ∈ H then 8 else 4)
    else if bc.1 ∈ H then (if bc.2 ∈ H then 9 else 5)
    else if bc.2 ∈ H then 6 else 10

def value (A B T : C) : MvPolynomial (ParamVar C C) K :=
  let x : ParamVar C C → MvPolynomial (ParamVar C C) K := MvPolynomial.X
  x (.s B) * x (.t T) * (x (.u A) * x (.h T) + x (.v A) * x (.h B))

def table : Fin 11 → MvPolynomial (ParamVar C C) K :=
  ![value z z z, value z d d, value z i i, value d z d, value d d z,
    value d i d, value d d i, value i z i, value i i z, value i i i, value i d d]

private theorem coordinate_endpoint (bc : G × G) :
    coordinatePolynomial (K := K) q (bc.2-bc.1, bc.1) =
      value (q (bc.2-bc.1)) (q bc.1) (q bc.2) := by
  simp [coordinatePolynomial, value]

include hindex hq0 hqD hqI in
private theorem representative_values (a c e : G)
    (ha : a ∉ H) (hc : c ∈ H) (hc0 : c ≠ 0)
    (he : e ∈ H) (he0 : e ≠ 0) (hec : e ≠ c) :
    (fun j => coordinatePolynomial (K := K) q (coordinateRepresentative a c e j)) =
      table (K := K) z d i := by
  have hz := (hq0 0).mpr rfl
  have had := (hqD a).mpr ha
  have hci := (hqI c).mpr ⟨hc,hc0⟩
  have hei := (hqI e).mpr ⟨he,he0⟩
  have ha0 : a ≠ 0 := fun h => ha (h ▸ H.zero_mem)
  have hna := (hqD (-a)).mpr (by simpa using ha)
  have hnc := (hqI (-c)).mpr ⟨H.neg_mem hc, neg_ne_zero.mpr hc0⟩
  have hac : a ≠ c := fun h => ha (h ▸ hc)
  have hdac : q (a-c) = d := by
    rw [diff_class q H hindex d i hqD hqI a c hac]
    simp [ha, hc]
  have hdca : q (c-a) = d := by
    rw [diff_class q H hindex d i hqD hqI c a (Ne.symm hac)]
    simp [ha, hc]
  have hdec : q (e-c) = i := by
    rw [diff_class q H hindex d i hqD hqI e c hec]
    simp [he, hc]
  have hacH : a+c ∉ H := by
    intro h
    exact ha (by simpa using H.sub_mem h hc)
  have hacd := (hqD (a+c)).mpr hacH
  have hcad' : q (c+a) = d := by simpa only [add_comm] using hacd
  funext j
  fin_cases j <;>
    simp [coordinateRepresentative, representatives, table, coordinate_endpoint,
      coordinatePolynomial, value, hz, had, hci, hei, hna, hnc, hdac, hdca, hdec, hacd, hcad']

include hindex hq0 hqD hqI in
private theorem coordinate_classified (bc : G × G) :
    coordinatePolynomial (K := K) q (bc.2-bc.1,bc.1) =
      table (K := K) z d i (classify H bc) := by
  classical
  have hz := (hq0 0).mpr rfl
  rcases bc with ⟨b,c⟩
  rw [coordinate_endpoint]
  by_cases hbc : b = c
  · subst c
    by_cases hb : b = 0
    · subst b
      simp [classify, table, hz]
    · by_cases hbH : b ∈ H
      · have hbi := (hqI b).mpr ⟨hbH,hb⟩
        simp [classify, table, hb, hbH, hz, hbi]
      · have hbd := (hqD b).mpr hbH
        simp [classify, table, hb, hbH, hz, hbd]
  · have hdif := diff_class q H hindex d i hqD hqI c b (Ne.symm hbc)
    by_cases hb : b = 0
    · subst b
      have hc : c ≠ 0 := Ne.symm hbc
      by_cases hcH : c ∈ H
      · have hci := (hqI c).mpr ⟨hcH,hc⟩
        simp [classify, table, hc, Ne.symm hc, hz, hcH, hci]
      · have hcd := (hqD c).mpr hcH
        simp [classify, table, hc, Ne.symm hc, hz, hcH, hcd]
    · by_cases hc : c = 0
      · subst c
        by_cases hbH : b ∈ H
        · have hbi := (hqI b).mpr ⟨hbH,hb⟩
          have hni := (hqI (-b)).mpr ⟨H.neg_mem hbH,neg_ne_zero.mpr hb⟩
          simp [classify, table, hb, hz, hbH, hbi, hni]
        · have hbd := (hqD b).mpr hbH
          have hnd := (hqD (-b)).mpr (by simpa using hbH)
          simp [classify, table, hb, hz, hbH, hbd, hnd]
      · by_cases hbH : b ∈ H <;> by_cases hcH : c ∈ H
        · have hbi := (hqI b).mpr ⟨hbH,hb⟩
          have hci := (hqI c).mpr ⟨hcH,hc⟩
          simp [classify, table, hbc, hb, hc, hbH, hcH, hbi, hci, hdif]
        · have hbi := (hqI b).mpr ⟨hbH,hb⟩
          have hcd := (hqD c).mpr hcH
          simp [classify, table, hbc, hb, hc, hbH, hcH, hbi, hcd, hdif]
        · have hbd := (hqD b).mpr hbH
          have hci := (hqI c).mpr ⟨hcH,hc⟩
          simp [classify, table, hbc, hb, hc, hbH, hcH, hbd, hci, hdif]
        · have hbd := (hqD b).mpr hbH
          have hcd := (hqD c).mpr hcH
          simp [classify, table, hbc, hb, hc, hbH, hcH, hbd, hcd, hdif]

/-- The two normalized inside-color coordinates obey this actual binomial. -/
def relation : MvPolynomial (Fin 11) K :=
  MvPolynomial.X 9 * MvPolynomial.X 1 - MvPolynomial.X 10 * MvPolynomial.X 2

theorem relation_nonzero : relation (K := K) ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval (fun j : Fin 11 => if j = 9 ∨ j = 1 then (1 : K) else 0)) h
  norm_num [relation] at he

theorem table_relation : MvPolynomial.aeval (table (K := K) z d i) (relation (K := K)) = 0 := by
  simp [relation, table, value]
  ring

include hindex hq0 hqD hqI in
/-- The exact eleven coordinate values have a proved nonzero relation. -/
theorem coordinateRing_dimension_le (a c e : G)
    (ha : a ∉ H) (hc : c ∈ H) (hc0 : c ≠ 0)
    (he : e ∈ H) (he0 : e ≠ 0) (hec : e ≠ c) :
    ringKrullDim (MvPolynomial (G × G) K ⧸
      PolynomialImage.definingIdeal (coordinatePolynomial (K := K) q)) ≤ 10 := by
  classical
  have hvalues := representative_values (K := K) q H hindex z d i hq0 hqD hqI
    a c e ha hc hc0 he he0 hec
  have hrep : ∀ ab, coordinatePolynomial (K := K) q
      (coordinateRepresentative a c e (classify H (ab.2,ab.1+ab.2))) =
        coordinatePolynomial (K := K) q ab := by
    intro ⟨a',b⟩
    rw [show coordinatePolynomial (K := K) q
      (coordinateRepresentative a c e (classify H (b,a'+b))) =
        table z d i (classify H (b,a'+b)) from congrFun hvalues _]
    simpa only [add_sub_cancel_right] using
      (coordinate_classified (K := K) q H hindex z d i hq0 hqD hqI (b,a'+b)).symm
  have hrel : MvPolynomial.aeval (fun j => coordinatePolynomial (K := K) q
      (coordinateRepresentative a c e j)) (relation (K := K)) = 0 := by
    rw [hvalues]
    exact table_relation (K := K) z d i
  have hbound := PolynomialImage.dimension_succ_le_of_coordinate_relation
    (coordinatePolynomial (K := K) q) (coordinateRepresentative a c e)
    (fun ab => classify H (ab.2,ab.1+ab.2)) hrep (relation (K := K)) (relation_nonzero (K := K)) hrel
  norm_num at hbound
  apply ENat.WithBot.add_le_add_one_right_iff.mp
  convert hbound using 1 <;> norm_num

include hindex hzd hdi hq0 hqD hqI in
private theorem selected_exponents (a c e : G)
    (ha : a ∉ H) (hc : c ∈ H) (hc0 : c ≠ 0)
    (he : e ∈ H) (he0 : e ≠ 0) (hec : e ≠ c) :
    (fun j p => (ClassSelection.selectedExponent q {i} (lowerRepresentatives a c e j) p : ℚ)) =
      ![
    (fun p => (if p = .s z then 1 else 0) + (if p = .t z then 1 else 0) + (if p = .v z then 1 else 0) + (if p = .h z then 1 else 0)),
    (fun p => (if p = .s d then 1 else 0) + (if p = .t d then 1 else 0) + (if p = .v z then 1 else 0) + (if p = .h d then 1 else 0)),
    (fun p => (if p = .s i then 1 else 0) + (if p = .t i then 1 else 0) + (if p = .v z then 1 else 0) + (if p = .h i then 1 else 0)),
    (fun p => (if p = .s z then 1 else 0) + (if p = .t d then 1 else 0) + (if p = .u d then 1 else 0) + (if p = .h d then 1 else 0)),
    (fun p => (if p = .s d then 1 else 0) + (if p = .t z then 1 else 0) + (if p = .v d then 1 else 0) + (if p = .h d then 1 else 0)),
    (fun p => (if p = .s i then 1 else 0) + (if p = .t d then 1 else 0) + (if p = .v d then 1 else 0) + (if p = .h i then 1 else 0)),
    (fun p => (if p = .s d then 1 else 0) + (if p = .t i then 1 else 0) + (if p = .u d then 1 else 0) + (if p = .h i then 1 else 0)),
    (fun p => (if p = .s z then 1 else 0) + (if p = .t i then 1 else 0) + (if p = .u i then 1 else 0) + (if p = .h i then 1 else 0)),
    (fun p => (if p = .s i then 1 else 0) + (if p = .t z then 1 else 0) + (if p = .v i then 1 else 0) + (if p = .h i then 1 else 0)),
    (fun p => (if p = .s i then 1 else 0) + (if p = .t i then 1 else 0) + (if p = .u i then 1 else 0) + (if p = .h i then 1 else 0))] := by
  have hz := (hq0 0).mpr rfl
  have had := (hqD a).mpr ha
  have hci := (hqI c).mpr ⟨hc,hc0⟩
  have hei := (hqI e).mpr ⟨he,he0⟩
  have ha0 : a ≠ 0 := fun h => ha (h ▸ H.zero_mem)
  have hna := (hqD (-a)).mpr (by simpa using ha)
  have hnc := (hqI (-c)).mpr ⟨H.neg_mem hc, neg_ne_zero.mpr hc0⟩
  have hac : a ≠ c := fun h => ha (h ▸ hc)
  have hdac : q (a-c) = d := by
    rw [diff_class q H hindex d i hqD hqI a c hac]
    simp [ha, hc]
  have hdca : q (c-a) = d := by
    rw [diff_class q H hindex d i hqD hqI c a (Ne.symm hac)]
    simp [ha, hc]
  have hdec : q (e-c) = i := by
    rw [diff_class q H hindex d i hqD hqI e c hec]
    simp [he, hc]
  have hacH : a+c ∉ H := by
    intro h
    exact ha (by simpa using H.sub_mem h hc)
  have hacd := (hqD (a+c)).mpr hacH
  have hcad' : q (c+a) = d := by simpa only [add_comm] using hacd
  have hzi := hzd.trans hdi
  funext j p
  fin_cases j <;>
    simp [lowerRepresentatives, ClassSelection.selectedExponent, ClassSelection.selectsU,
      ClassSelection.uExponent, ClassSelection.vExponent, Finsupp.single_apply, eq_comm,
      hz, had, hci, hei, hna, hnc, hdac, hdca, hdec, hacd, hcad',
      hzd, hdi, hzi, ne_of_lt hzd, ne_of_lt hdi, ne_of_lt hzi,
      (ne_of_lt hzd).symm, (ne_of_lt hdi).symm, (ne_of_lt hzi).symm,
      not_lt_of_ge hzd.le, not_lt_of_ge hdi.le, not_lt_of_ge hzi.le, add_assoc]

include hindex hzd hdi hq0 hqD hqI in
private theorem selected_independent (a c e : G)
    (ha : a ∉ H) (hc : c ∈ H) (hc0 : c ≠ 0)
    (he : e ∈ H) (he0 : e ≠ 0) (hec : e ≠ c) :
    LinearIndependent ℚ
      (fun j p => (ClassSelection.selectedExponent q {i} (lowerRepresentatives a c e j) p : ℚ)) := by
  classical
  rw [selected_exponents q H hindex z d i hzd hdi hq0 hqD hqI a c e ha hc hc0 he he0 hec]
  apply Fintype.linearIndependent_iff.mpr
  intro w hw
  have hzi := hzd.trans hdi
  have hv0 := congrFun hw (.s z)
  have hv1 := congrFun hw (.s d)
  have hv2 := congrFun hw (.s i)
  have hv3 := congrFun hw (.t z)
  have hv4 := congrFun hw (.t d)
  have hv5 := congrFun hw (.t i)
  have hv6 := congrFun hw (.h z)
  have hv7 := congrFun hw (.h d)
  have hv8 := congrFun hw (.h i)
  have hv9 := congrFun hw (.u z)
  have hv10 := congrFun hw (.u d)
  have hv11 := congrFun hw (.u i)
  have hv12 := congrFun hw (.v z)
  have hv13 := congrFun hw (.v d)
  have hv14 := congrFun hw (.v i)
  simp [Fin.sum_univ_succ, ne_of_lt hzd, ne_of_lt hdi, ne_of_lt hzi,
    (ne_of_lt hzd).symm, (ne_of_lt hdi).symm, (ne_of_lt hzi).symm] at hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
  have h0 : w 0 = 0 := hv6
  have h8 : w 8 = 0 := hv14
  have h4 : w 4 = 0 := by linarith only [hv3, h0, h8]
  have h5 : w 5 = 0 := by linarith only [hv13, h4]
  have h3 : w 3 = 0 := by linarith only [hv1, hv7, hv10, h4]
  have h1 : w 1 = 0 := by linarith only [hv7, h3, h4]
  have h6 : w 6 = 0 := by linarith only [hv10, h3]
  have h7 : w 7 = 0 := by linarith only [hv0, h0, h3]
  have h9 : w 9 = 0 := by linarith only [hv11, h7]
  have h2 : w 2 = 0 := by linarith only [hv12, h0, h1]
  intro j
  fin_cases j <;> assumption

include hindex hzd hdi hq0 hqD hqI in
/-- Ten actual coordinate functions have independent initial exponents over ℚ,
which proves algebraic independence over every ground field. -/
theorem coordinateRing_dimension_ge (a c e : G)
    (ha : a ∉ H) (hc : c ∈ H) (hc0 : c ≠ 0)
    (he : e ∈ H) (he0 : e ≠ 0) (hec : e ≠ c) :
    10 ≤ ringKrullDim (MvPolynomial (G × G) K ⧸
      PolynomialImage.definingIdeal (coordinatePolynomial (K := K) q)) := by
  classical
  have halg := ClassSelection.coordinate_subfamily_algebraicIndependent (K := K) q {i}
    (lowerRepresentatives a c e)
    (selected_independent q H hindex z d i hzd hdi hq0 hqD hqI a c e ha hc hc0 he he0 hec)
  let A := PolynomialImage.imageAlgebra (coordinatePolynomial (K := K) q)
  let f : Fin 10 → A := fun j =>
    ⟨coordinatePolynomial q
      ((lowerRepresentatives a c e j).2 - (lowerRepresentatives a c e j).1,
       (lowerRepresentatives a c e j).1), by
      refine ⟨MvPolynomial.X ((lowerRepresentatives a c e j).2 - (lowerRepresentatives a c e j).1, (lowerRepresentatives a c e j).1), ?_⟩
      simp [PolynomialImage.comorphism]⟩
  have hf : AlgebraicIndependent K f := AlgebraicIndependent.of_comp A.val halg
  letI : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective
    (PolynomialImage.comorphism (coordinatePolynomial (K := K) q)).rangeRestrict
    (PolynomialImage.comorphism (coordinatePolynomial (K := K) q)).rangeRestrict_surjective
  have hd := DimensionAlgebra.card_le_ringKrullDim_of_algebraicIndependent K A f hf
  rw [ringKrullDim_eq_of_ringEquiv
    (PolynomialImage.coordinateRingEquivImage (coordinatePolynomial (K := K) q)).toRingEquiv]
  simpa using hd

include hindex hzd hdi hq0 hqD hqI in
theorem coordinateRing_dimension (a c e : G)
    (ha : a ∉ H) (hc : c ∈ H) (hc0 : c ≠ 0)
    (he : e ∈ H) (he0 : e ≠ 0) (hec : e ≠ c) :
    ringKrullDim (MvPolynomial (G × G) K ⧸
      PolynomialImage.definingIdeal (coordinatePolynomial (K := K) q)) = 10 := by
  exact le_antisymm
    (coordinateRing_dimension_le q H hindex z d i hq0 hqD hqI a c e ha hc hc0 he he0 hec)
    (coordinateRing_dimension_ge q H hindex z d i hzd hdi hq0 hqD hqI a c e ha hc hc0 he he0 hec)

end Sunlet.Identified.ThreeClass

/- Source: ClassGroupCoordinates.lean -/
namespace Sunlet.ClassGroupCoordinates

variable {K G C : Type*} [Field K] [AddCommGroup G] [Fintype G] [Fintype C]
  [DecidableEq C]

abbrev Parameters := Fin 6 → C → K

def coordinate (q : G → C) (w : Parameters (K := K) (C := C)) (a b c : G) : K :=
  w 0 (q a) * w 1 (q b) * w 2 (q c) *
    (w 3 (q (a+b)) * w 4 (q a) + w 3 (q b) * w 5 (q a))

def parameterMap (q : G → C) (w : Parameters (K := K) (C := C)) (ab : G × G) : K :=
  coordinate q w ab.1 ab.2 (-(ab.1+ab.2))

def tripleParameterMap (q : G → C) (w : Parameters (K := K) (C := C))
    (abc : GroupCoordinates.FlowIndex G) : K :=
  coordinate q w abc.val.1 abc.val.2.1 abc.val.2.2

def collapse (negClass : C ≃ C) (w : Parameters (K := K) (C := C)) :
    Sunlet.Parameters K C C where
  s := w 1
  t i := w 2 (negClass i)
  h := w 3
  u i := w 0 i * w 4 i
  v i := w 0 i * w 5 i

def expand (negClass : C ≃ C) (p : Sunlet.Parameters K C C) :
    Parameters (K := K) (C := C) :=
  ![fun _ => 1, p.s, fun i => p.t (negClass.symm i), p.h, p.u, p.v]

theorem collapse_expand (negClass : C ≃ C) (p : Sunlet.Parameters K C C) :
    collapse negClass (expand negClass p) = p := by
  cases p
  simp [collapse, expand]

/-- Parameter negation is a genuine permutation of the orbit classes. No
class translation action is assumed, and no division is used in this bridge. -/
theorem parameterMap_eq_polynomialMap (q : G → C) (negClass : C ≃ C)
    (hneg : ∀ a, q (-a) = negClass (q a)) (w : Parameters (K := K) (C := C)) :
    parameterMap q w = PolynomialImage.parameterMap
      (Identified.coordinatePolynomial (K := K) q) (collapse negClass w).toCoordinates := by
  funext ab
  simp only [parameterMap, coordinate, PolynomialImage.parameterMap,
    Identified.coordinatePolynomial, map_mul, map_add, MvPolynomial.aeval_X,
    Sunlet.Parameters.toCoordinates, collapse, hneg]
  ring

/-- Equality of the complete affine images of the original six-family map
and the identified five-family polynomial map, including zero parameters. -/
theorem range_eq_polynomialMap (q : G → C) (negClass : C ≃ C)
    (hneg : ∀ a, q (-a) = negClass (q a)) :
    Set.range (parameterMap (K := K) q) =
      Set.range (PolynomialImage.parameterMap (Identified.coordinatePolynomial (K := K) q)) := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨(collapse negClass w).toCoordinates, (parameterMap_eq_polynomialMap q negClass hneg w).symm⟩
  · rintro ⟨p, rfl⟩
    refine ⟨expand negClass (Sunlet.Parameters.ofCoordinates p), ?_⟩
    rw [parameterMap_eq_polynomialMap q negClass hneg, collapse_expand,
      Sunlet.Parameters.toCoordinates_ofCoordinates]

def imageClosure (q : G → C) : Set (G × G → K) :=
  MvPolynomial.zeroLocus K
    (MvPolynomial.vanishingIdeal K (Set.range (parameterMap (K := K) q)))

def tripleImageClosure (q : G → C) : Set (GroupCoordinates.FlowIndex G → K) :=
  MvPolynomial.zeroLocus K
    (MvPolynomial.vanishingIdeal K (Set.range (tripleParameterMap (K := K) q)))

theorem imageClosure_eq_polynomial [Infinite K] (q : G → C) (negClass : C ≃ C)
    (hneg : ∀ a, q (-a) = negClass (q a)) :
    imageClosure (K := K) q = PolynomialImage.closure (Identified.coordinatePolynomial q) := by
  rw [imageClosure, range_eq_polynomialMap q negClass hneg,
    PolynomialImage.closure, PolynomialImage.definingIdeal_eq_vanishingIdeal]

theorem tripleParameterMap_eq (q : G → C) (w : Parameters (K := K) (C := C)) :
    tripleParameterMap q w = parameterMap q w ∘ GroupCoordinates.flowIndexEquiv := by
  funext abc
  have hc : abc.val.2.2 = -(abc.val.1+abc.val.2.1) :=
    eq_neg_of_add_eq_zero_right abc.property
  simp only [tripleParameterMap, parameterMap, Function.comp_apply,
    GroupCoordinates.flowIndexEquiv, Equiv.coe_fn_mk, hc]

theorem flowPolynomialEquiv_mem (q : G → C)
    (p : MvPolynomial (GroupCoordinates.FlowIndex G) K) :
    GroupCoordinates.flowPolynomialEquiv p ∈
        MvPolynomial.vanishingIdeal K (Set.range (parameterMap (K := K) q)) ↔
      p ∈ MvPolynomial.vanishingIdeal K (Set.range (tripleParameterMap (K := K) q)) := by
  simp only [MvPolynomial.mem_vanishingIdeal_iff, Set.forall_mem_range,
    GroupCoordinates.flowPolynomialEquiv, MvPolynomial.renameEquiv_apply,
    MvPolynomial.aeval_rename, tripleParameterMap_eq]

theorem flow_vanishingIdeal_map (q : G → C) :
    MvPolynomial.vanishingIdeal K (Set.range (parameterMap (K := K) q)) =
      (MvPolynomial.vanishingIdeal K (Set.range (tripleParameterMap (K := K) q))).map
        (GroupCoordinates.flowPolynomialEquiv (K := K) (G := G)).toRingHom := by
  ext p
  rw [Ideal.mem_map_iff_of_surjective
    (GroupCoordinates.flowPolynomialEquiv (K := K) (G := G)).toRingHom
    GroupCoordinates.flowPolynomialEquiv.surjective]
  constructor
  · intro hp
    refine ⟨GroupCoordinates.flowPolynomialEquiv.symm p, ?_,
      GroupCoordinates.flowPolynomialEquiv.apply_symm_apply p⟩
    apply (flowPolynomialEquiv_mem q _).mp
    simpa only [AlgEquiv.apply_symm_apply] using hp
  · rintro ⟨p,hp,rfl⟩
    exact (flowPolynomialEquiv_mem q p).mpr hp

def flowCoordinateRingEquiv (q : G → C) :
    (MvPolynomial (GroupCoordinates.FlowIndex G) K ⧸
      MvPolynomial.vanishingIdeal K (tripleImageClosure (K := K) q)) ≃ₐ[K]
    (MvPolynomial (G × G) K ⧸
      MvPolynomial.vanishingIdeal K (imageClosure (K := K) q)) := by
  rw [tripleImageClosure, imageClosure, GroupCoordinates.closure_vanishingIdeal,
    GroupCoordinates.closure_vanishingIdeal]
  exact Ideal.quotientEquivAlg _ _ GroupCoordinates.flowPolynomialEquiv (flow_vanishingIdeal_map q)

end Sunlet.ClassGroupCoordinates

/- Source: OrbitClasses.lean -/
namespace Sunlet.OrbitClasses

variable {G : Type*} [AddCommGroup G]

/-- In this Mathlib version `AddAut G` uses additive notation for composition.
An `AddSubgroup (AddAut G)` is an arbitrary subgroup of the full automorphism
group; no commutativity of that automorphism group is assumed. -/
def relation (B : AddSubgroup (AddAut G)) (a b : G) : Prop :=
  ∃ φ : B, (φ.val : G → G) a = b

def orbitSetoid (B : AddSubgroup (AddAut G)) : Setoid G where
  r := relation B
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨0, rfl⟩
    · rintro a b ⟨φ,hφ⟩
      refine ⟨-φ, ?_⟩
      change φ.val.symm b = a
      rw [← hφ]
      exact φ.val.symm_apply_apply a
    · rintro a b c ⟨φ,hφ⟩ ⟨ψ,hψ⟩
      refine ⟨ψ+φ, ?_⟩
      change ψ.val (φ.val a) = c
      rw [hφ,hψ]

abbrev Class (B : AddSubgroup (AddAut G)) := Quotient (orbitSetoid B)

def classOf (B : AddSubgroup (AddAut G)) (a : G) : Class B :=
  Quotient.mk (orbitSetoid B) a

theorem classOf_surjective (B : AddSubgroup (AddAut G)) :
    Function.Surjective (classOf B) := Quotient.mk_surjective

theorem classOf_eq_iff (B : AddSubgroup (AddAut G)) (a b : G) :
    classOf B a = classOf B b ↔ ∃ φ : B, (φ.val : G → G) a = b := Quotient.eq

theorem zero_class_iff (B : AddSubgroup (AddAut G)) (a : G) :
    classOf B a = classOf B 0 ↔ a = 0 := by
  rw [classOf_eq_iff]
  constructor
  · rintro ⟨φ,hφ⟩
    apply φ.val.injective
    simpa only [map_zero] using hφ
  · rintro rfl
    exact ⟨0,rfl⟩

def negClass (B : AddSubgroup (AddAut G)) : Class B ≃ Class B where
  toFun := Quotient.map' (fun a : G => -a) (by
    rintro a b ⟨φ,hφ⟩
    refine ⟨φ, ?_⟩
    change φ.val (-a) = -b
    rw [map_neg,hφ])
  invFun := Quotient.map' (fun a : G => -a) (by
    rintro a b ⟨φ,hφ⟩
    refine ⟨φ, ?_⟩
    change φ.val (-a) = -b
    rw [map_neg,hφ])
  left_inv a := Quotient.inductionOn a (fun a => by simp)
  right_inv a := Quotient.inductionOn a (fun a => by simp)

@[simp] theorem negClass_classOf (B : AddSubgroup (AddAut G)) (a : G) :
    negClass B (classOf B a) = classOf B (-a) := rfl

/-- The automorphism of an abelian group which sends each element to its inverse. -/
def negation : AddAut G where
  toFun := fun a => -a
  invFun := fun a => -a
  left_inv := neg_neg
  right_inv := neg_neg
  map_add' a b := neg_add a b

theorem classOf_neg (B : AddSubgroup (AddAut G)) (hneg : negation (G := G) ∈ B) (a : G) :
    classOf B (-a) = classOf B a := by
  rw [classOf_eq_iff]
  refine ⟨⟨negation,hneg⟩, ?_⟩
  exact neg_neg a

def inverseStablePartition (B : AddSubgroup (AddAut G)) (hneg : negation (G := G) ∈ B) :
    OrbitHeight.InverseStablePartition G (Class B) where
  classOf := classOf B
  surjective := classOf_surjective B
  zeroClass := classOf B 0
  zero_iff := zero_class_iff B
  neg_class := classOf_neg B hneg

instance [Fintype G] (B : AddSubgroup (AddAut G)) : Fintype (Class B) :=
  Fintype.ofFinite _

/-- A subgroup acts by automorphisms, so orbit classes are permuted by negation
whether or not negation itself lies in the subgroup. -/
theorem six_family_image_equality {K : Type*} [Field K] [Fintype G]
    (B : AddSubgroup (AddAut G)) :
    Set.range (ClassGroupCoordinates.parameterMap (K := K) (classOf B)) =
      Set.range (PolynomialImage.parameterMap
        (Identified.coordinatePolynomial (K := K) (classOf B))) := by
  classical
  exact ClassGroupCoordinates.range_eq_polynomialMap (classOf B) (negClass B)
    (fun a => (negClass_classOf B a).symm)

end Sunlet.OrbitClasses

/- Source: InverseStableClassification.lean -/
namespace Sunlet.OrbitHeight.InverseStablePartition

attribute [local instance 0] Classical.propDecidable

variable {K G C : Type*} [Field K] [AddCommGroup G] [Fintype G] [Fintype C]
  [LinearOrder C] (P : InverseStablePartition G C)

private theorem two_nonzero_distinct {A : Type*} [AddGroup A] [Fintype A]
    (hm : 3 ≤ Fintype.card A) : ∃ a c : A, a ≠ 0 ∧ c ≠ 0 ∧ c ≠ a := by
  classical
  haveI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a,ha⟩ := exists_ne (0 : A)
  by_contra h
  push_neg at h
  have hs : (Finset.univ : Finset A) ⊆ {0,a} := by
    intro c _
    by_cases hc : c = 0
    · simp [hc]
    · have he := h a c ha hc
      simp [he]
  have hle := Finset.card_le_card hs
  have hb := Finset.card_insert_le (0 : A) ({a} : Finset A)
  simp only [Finset.card_univ, Finset.card_singleton] at hle hb
  omega

private theorem classes_of_card_two (hr : Fintype.card C = 2) :
    ∃ d : C, d ≠ P.zeroClass ∧ ∀ i, i = P.zeroClass ∨ i = d := by
  classical
  obtain ⟨a,b,hab,hu⟩ := Finset.card_eq_two.mp (show (Finset.univ : Finset C).card = 2 from hr)
  have hz : P.zeroClass = a ∨ P.zeroClass = b := by
    have h := Finset.mem_univ P.zeroClass
    rw [hu] at h
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  rcases hz with hz | hz
  · refine ⟨b, by simpa only [hz] using Ne.symm hab, ?_⟩
    intro i
    have h := Finset.mem_univ i
    rw [hu] at h
    simpa only [Finset.mem_insert, Finset.mem_singleton, hz] using h
  · refine ⟨a, by simpa only [hz] using hab, ?_⟩
    intro i
    have h := Finset.mem_univ i
    rw [hu] at h
    simpa only [Finset.mem_insert, Finset.mem_singleton, hz, or_comm] using h

/-- The two-class model has dimension exactly five for every allowed group. -/
theorem two_class_imageClosure_dimension [Infinite K]
    (hm : 5 ≤ Fintype.card G) (hr : Fintype.card C = 2) :
    ringKrullDim (MvPolynomial (G × G) K ⧸ MvPolynomial.vanishingIdeal K
      (PolynomialImage.closure (Identified.coordinatePolynomial (K := K) P.classOf))) = 5 := by
  classical
  obtain ⟨d,hd,hclasses⟩ := P.classes_of_card_two hr
  obtain ⟨a,c,ha,hc,hca⟩ := two_nonzero_distinct (A := G) (by omega)
  have hzd : @LT.lt C (P.priorityOrder d false).toLT P.zeroClass d := by
    change P.priorityKey d false P.zeroClass < P.priorityKey d false d
    simp [priorityKey, Prod.Lex.toLex_lt_toLex, hd]
  rw [PolynomialImage.vanishingIdeal_imageClosure]
  exact @Identified.TwoClass.coordinateRing_dimension K G C _ _ _ _ (P.priorityOrder d false)
    P.classOf P.zeroClass d P.zero_iff hclasses hzd a c ha hc hca

/-- Every three-class index-two exception has enough representatives for the
uniform ten-coordinate rank proof; the group-order hypothesis excludes order four. -/
theorem index_two_imageClosure_dimension [Infinite K]
    (hm : 5 ≤ Fintype.card G) (hex : P.IndexTwoException) :
    ringKrullDim (MvPolynomial (G × G) K ⧸ MvPolynomial.vanishingIdeal K
      (PolynomialImage.closure (Identified.coordinatePolynomial (K := K) P.classOf))) = 10 := by
  classical
  obtain ⟨H,d,i,hindex,hd,hi,hdi,hout,hin⟩ := hex
  letI : Fintype H := Fintype.ofFinite H
  have hsize := H.card_mul_index
  rw [hindex, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hsize
  have hHcard : 3 ≤ Fintype.card H := by omega
  obtain ⟨c,e,hc0,he0,hec⟩ := two_nonzero_distinct (A := H) hHcard
  obtain ⟨a,ha,_⟩ := H.index_eq_two_iff_exists_notMem_and.mp hindex
  have hc0' : (c : G) ≠ 0 := fun h => hc0 (Subtype.ext h)
  have he0' : (e : G) ≠ 0 := fun h => he0 (Subtype.ext h)
  have hec' : (e : G) ≠ c := fun h => hec (Subtype.ext h)
  have hzd : @LT.lt C (P.priorityOrder d false).toLT P.zeroClass d := by
    change P.priorityKey d false P.zeroClass < P.priorityKey d false d
    simp [priorityKey, Prod.Lex.toLex_lt_toLex, hd]
  have hdi' : @LT.lt C (P.priorityOrder d false).toLT d i := by
    change P.priorityKey d false d < P.priorityKey d false i
    simp [priorityKey, Prod.Lex.toLex_lt_toLex, hd, hi, hdi, Ne.symm hdi]
  rw [PolynomialImage.vanishingIdeal_imageClosure]
  exact @Identified.ThreeClass.coordinateRing_dimension K G C _ _ _ _ (P.priorityOrder d false)
    P.classOf H hindex P.zeroClass d i hzd hdi' P.zero_iff hout hin
    a c e ha c.property hc0' e.property he0' hec'

/-- Full inverse-stable classification: neither representative elements nor a
good order nor a rank condition is an additional theorem hypothesis. -/
theorem inverse_stable_imageClosure_dimension [IsAlgClosed K]
    (hm : 5 ≤ Fintype.card G) :
    ringKrullDim (MvPolynomial (G × G) K ⧸ MvPolynomial.vanishingIdeal K
      (PolynomialImage.closure (Identified.coordinatePolynomial (K := K) P.classOf))) =
        (if Fintype.card C = 2 then (5 : ℕ)
          else if P.IndexTwoException then 10 else 5 * Fintype.card C - 4) := by
  classical
  by_cases hr : Fintype.card C = 2
  · simp only [if_pos hr]
    exact P.two_class_imageClosure_dimension hm hr
  · simp only [if_neg hr]
    by_cases hex : P.IndexTwoException
    · simp only [if_pos hex]
      exact P.index_two_imageClosure_dimension hm hex
    · simp only [if_neg hex]
      obtain ⟨a,c,ha,hc,hca⟩ := two_nonzero_distinct (A := G) (by omega)
      have hqa : P.classOf a ≠ P.zeroClass := fun h => ha ((P.zero_iff a).mp h)
      haveI : Nontrivial C := ⟨⟨P.classOf a,P.zeroClass,hqa⟩⟩
      have hcard := Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial C)
      exact P.nonexceptional_imageClosure_dimension hm (by omega) hex

/-- The exceptional condition has exactly the three classes stated in the paper. -/
theorem index_two_exception_card (hex : P.IndexTwoException) : Fintype.card C = 3 := by
  classical
  obtain ⟨H,d,i,hindex,hd,hi,hdi,hout,hin⟩ := hex
  have hu : (Finset.univ : Finset C) = {P.zeroClass,d,i} := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    obtain ⟨a,rfl⟩ := P.surjective j
    by_cases ha : a = 0
    · left; exact (P.zero_iff a).mpr ha
    · by_cases haH : a ∈ H
      · exact Or.inr (Or.inr ((hin a).mpr ⟨haH,ha⟩))
      · exact Or.inr (Or.inl ((hout a).mpr haH))
  have hz : P.zeroClass ≠ d := Ne.symm hd
  have hzi : P.zeroClass ≠ i := Ne.symm hi
  simpa only [Finset.card_univ, Finset.card_insert_of_notMem,
    Finset.mem_insert, Finset.mem_singleton, hz, hzi, hdi, or_false, not_false_eq_true,
    Finset.card_singleton] using congrArg Finset.card hu

/-- The complete inverse-stable clause in the manuscript's original six-family,
flow-indexed coordinates, with no restriction to nonzero parameter points. -/
theorem inverse_stable_original_coordinates [IsAlgClosed K]
    (hm : 5 ≤ Fintype.card G) :
    ringKrullDim (MvPolynomial (GroupCoordinates.FlowIndex G) K ⧸
      MvPolynomial.vanishingIdeal K
        (ClassGroupCoordinates.tripleImageClosure (K := K) P.classOf)) =
        (if Fintype.card C = 2 then (5 : ℕ)
          else if P.IndexTwoException then 10 else 5 * Fintype.card C - 4) := by
  rw [ringKrullDim_eq_of_ringEquiv
    (ClassGroupCoordinates.flowCoordinateRingEquiv (K := K) P.classOf).toRingEquiv]
  rw [ClassGroupCoordinates.imageClosure_eq_polynomial P.classOf (Equiv.refl C)
    (by intro a; exact P.neg_class a)]
  exact P.inverse_stable_imageClosure_dimension hm

end Sunlet.OrbitHeight.InverseStablePartition

namespace Sunlet.OrbitHeight

attribute [local instance 0] Classical.propDecidable

/-- Order-free statement of the full inverse-stable clause of Theorem 7.1.
The order used to select initial monomials is constructed from finiteness. -/
theorem inverse_stable_original_coordinates_order_free
    {K G C : Type*} [Field K] [IsAlgClosed K] [AddCommGroup G]
    [Fintype G] [Fintype C] (P : InverseStablePartition G C)
    (hm : 5 ≤ Fintype.card G) :
    ringKrullDim (MvPolynomial (GroupCoordinates.FlowIndex G) K ⧸
      MvPolynomial.vanishingIdeal K
        (ClassGroupCoordinates.tripleImageClosure (K := K) P.classOf)) =
      (if Fintype.card C = 2 then (5 : ℕ)
        else if P.IndexTwoException then 10 else 5 * Fintype.card C - 4) := by
  classical
  letI : LinearOrder C := LinearOrder.lift' (Fintype.equivFin C)
    (Fintype.equivFin C).injective
  exact P.inverse_stable_original_coordinates hm

end Sunlet.OrbitHeight

namespace Sunlet.OrbitClasses

attribute [local instance 0] Classical.propDecidable

/-- The automorphism-orbit specialization when the automorphism subgroup
contains inversion. The arbitrary subgroup case remains a separate obligation. -/
theorem paper_theorem_7_1_inverse_stable
    {K G : Type*} [Field K] [IsAlgClosed K] [AddCommGroup G] [Fintype G]
    (B : AddSubgroup (AddAut G)) (hneg : negation (G := G) ∈ B)
    (hm : 5 ≤ Fintype.card G) :
    ringKrullDim (MvPolynomial (GroupCoordinates.FlowIndex G) K ⧸
      MvPolynomial.vanishingIdeal K
        (ClassGroupCoordinates.tripleImageClosure (K := K) (classOf B))) =
      (if Fintype.card (Class B) = 2 then (5 : ℕ)
        else if (inverseStablePartition B hneg).IndexTwoException then 10
        else 5 * Fintype.card (Class B) - 4) :=
  OrbitHeight.inverse_stable_original_coordinates_order_free
    (inverseStablePartition B hneg) hm

end Sunlet.OrbitClasses

/- Source: StableSupport.lean -/
namespace Sunlet.StableSupport

open MvPolynomial
open scoped MonomialOrder

variable {K G C : Type*} [Field K] [AddCommGroup G] [Fintype G] [Fintype C]
  [DecidableEq G] [DecidableEq C]

local instance preimageDecidable (q : G → C) (σ : Set C) [DecidablePred (· ∈ σ)] :
    DecidablePred (· ∈ q ⁻¹' σ) := fun a => inferInstanceAs (Decidable (q a ∈ σ))

theorem translation_transitive (P : Set G) (hP : AddSubgroup.closure P = ⊤) :
    TransitiveFamily addTranslationPerm P := by
  have connected (g : G) (hg : g ∈ AddSubgroup.closure P) :
      ∀ x, ColorConnected addTranslationPerm P x (g + x) := by
    induction hg using AddSubgroup.closure_induction with
    | mem g hg => exact colorConnected_step addTranslationPerm P hg
    | zero => intro x; simpa using colorConnected_refl addTranslationPerm P x
    | add g h hg hh ihg ihh =>
        intro x
        simpa only [ColorConnected, add_assoc] using Relation.EqvGen.trans _ _ _ (ihh x) (ihg (h+x))
    | neg g hg ih =>
        intro x
        have hx := Relation.EqvGen.symm _ _ (ih (-g+x))
        simpa only [ColorConnected, add_neg_cancel_left] using hx
  intro x y
  have h := connected (y-x) (by rw [hP]; trivial) x
  simpa only [sub_add_cancel] using h

def selectedExponent (q : G → C) (σ : Set C) [DecidablePred (· ∈ σ)]
    (ab : G × G) : ParamVar C C →₀ ℕ :=
  if SelectedRelations.selectsU addTranslationPerm 0 0 (q ⁻¹' σ) ab.1 ab.2 then
    (Finsupp.single (.s (q ab.2)) 1 + Finsupp.single (.t (q (ab.1+ab.2))) 1) +
      (Finsupp.single (.u (q ab.1)) 1 + Finsupp.single (.h (q (ab.1+ab.2))) 1)
  else
    (Finsupp.single (.s (q ab.2)) 1 + Finsupp.single (.t (q (ab.1+ab.2))) 1) +
      (Finsupp.single (.v (q ab.1)) 1 + Finsupp.single (.h (q ab.2)) 1)

def relationMap (q : G → C) (σ : Set C) [DecidablePred (· ∈ σ)] :
    (ParamVar C C → ℚ) →ₗ[ℚ] (G × G → ℚ) where
  toFun w ab := w (.s (q ab.2)) + w (.t (q (ab.1+ab.2))) +
    if SelectedRelations.selectsU addTranslationPerm 0 0 (q ⁻¹' σ) ab.1 ab.2 then
      w (.u (q ab.1)) + w (.h (q (ab.1+ab.2)))
    else w (.v (q ab.1)) + w (.h (q ab.2))
  map_add' w z := by funext ab; dsimp; split_ifs <;> ring
  map_smul' r w := by funext ab; dsimp; split_ifs <;> ring

theorem relation_pullback (q : G → C) (σ : Set C) [DecidablePred (· ∈ σ)]
    (w : ParamVar C C → ℚ) (hw : w ∈ (relationMap q σ).ker) :
    SelectedRelations.IsRelation addTranslationPerm 0 0 (q ⁻¹' σ)
      (fun i => w (Identified.parameterRename q i)) := by
  intro a b
  have h := congrFun (LinearMap.mem_ker.mp hw) (a,b)
  simpa only [relationMap, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.zero_apply, SelectedRelations.RelationEquation, addTranslationPerm_apply,
    Identified.parameterRename] using h

theorem relation_canonical (q : G → C) (hq : Function.Surjective q) (z : C)
    (hq0 : ∀ a, q a = z ↔ a = 0)
    (σ τ : Set C) [DecidablePred (· ∈ σ)]
    (hzσ : z ∉ σ) (hzτ : z ∉ τ) (hστ : Disjoint σ τ)
    (hσ : AddSubgroup.closure (q ⁻¹' σ) = ⊤)
    (hτ : AddSubgroup.closure (q ⁻¹' τ) = ⊤)
    (hσtwo : ∃ a ∈ q ⁻¹' σ, ∃ b ∈ q ⁻¹' σ, a ≠ b)
    (hτtwo : ∃ a ∈ q ⁻¹' τ, ∃ b ∈ q ⁻¹' τ, a ≠ b)
    (w : ParamVar C C → ℚ) (hw : w ∈ (relationMap q σ).ker) :
    w = SelectedRelations.canonical z (w (.s z)) (w (.s z) + w (.h z))
      (w (.v z)) (w (.u z)) := by
  have hzero : q 0 = z := (hq0 0).mpr rfl
  have hder : ∀ a : G, a ≠ 0 → ∀ b, addTranslationPerm a b ≠ b := by
    intro a ha b hab
    exact ha (add_right_cancel (show a+b=0+b by simpa using hab))
  have hσne : ∀ a ∈ q ⁻¹' σ, a ≠ 0 := by
    intro a ha he; subst a; exact hzσ (by simpa only [Set.mem_preimage,hzero] using ha)
  have hτne : ∀ a ∈ q ⁻¹' τ, a ≠ 0 := by
    intro a ha he; subst a; exact hzτ (by simpa only [Set.mem_preimage,hzero] using ha)
  have hinj : Function.Injective (addTranslationPerm (G := G)) := by
    intro a b h
    have hh := Equiv.congr_fun h 0
    simpa using hh
  have hp := SelectedRelations.relation_canonical addTranslationPerm 0 0
    (q ⁻¹' σ) (q ⁻¹' τ) (by ext a; simp) (fun h => hσne 0 h rfl)
    (hστ.preimage q) hder hσne hτne
    (by obtain ⟨a,ha,b,hb,hab⟩ := hσtwo; exact ⟨a,ha,b,hb,hinj.ne hab⟩)
    (by obtain ⟨a,ha,b,hb,hab⟩ := hτtwo; exact ⟨a,ha,b,hb,hinj.ne hab⟩)
    (translation_transitive _ hσ) (translation_transitive _ hτ)
    (fun i => w (Identified.parameterRename q i)) (relation_pullback q σ w hw)
  funext j
  cases j with
  | s i =>
      obtain ⟨a,rfl⟩ := hq i
      simpa only [Identified.parameterRename, SelectedRelations.canonical,hzero] using congrFun hp (.s a)
  | t i =>
      obtain ⟨a,rfl⟩ := hq i
      simpa only [Identified.parameterRename, SelectedRelations.canonical,hzero] using congrFun hp (.t a)
  | h i =>
      obtain ⟨a,rfl⟩ := hq i
      simpa only [Identified.parameterRename, SelectedRelations.canonical,hzero] using congrFun hp (.h a)
  | v i =>
      obtain ⟨a,rfl⟩ := hq i
      simpa only [Identified.parameterRename, SelectedRelations.canonical,hzero] using congrFun hp (.v a)
  | u i =>
      obtain ⟨a,rfl⟩ := hq i
      simpa only [Identified.parameterRename, SelectedRelations.canonical,hzero,hq0] using congrFun hp (.u a)

def liftedU (q : G → C) (z : C) (σ : Set C) [DecidablePred (· ∈ σ)]
    (ab : G × G) : WithBot (ParamVar C C) →₀ ℕ :=
  (WeightedInitial.liftedVariable z σ (.s (q ab.2)) +
    WeightedInitial.liftedVariable z σ (.t (q (ab.1+ab.2)))) +
    (WeightedInitial.liftedVariable z σ (.u (q ab.1)) +
      WeightedInitial.liftedVariable z σ (.h (q (ab.1+ab.2))))

def liftedV (q : G → C) (z : C) (σ : Set C) [DecidablePred (· ∈ σ)]
    (ab : G × G) : WithBot (ParamVar C C) →₀ ℕ :=
  (WeightedInitial.liftedVariable z σ (.s (q ab.2)) +
    WeightedInitial.liftedVariable z σ (.t (q (ab.1+ab.2)))) +
    (WeightedInitial.liftedVariable z σ (.v (q ab.1)) +
      WeightedInitial.liftedVariable z σ (.h (q ab.2)))

def selectedLifted (q : G → C) (z : C) (σ : Set C) [DecidablePred (· ∈ σ)]
    (ab : G × G) : WithBot (ParamVar C C) →₀ ℕ :=
  if SelectedRelations.selectsU addTranslationPerm 0 0 (q ⁻¹' σ) ab.1 ab.2 then
    liftedU q z σ ab else liftedV q z σ ab

theorem weightHom_coordinate (q : G → C) (z : C) (σ : Set C)
    [DecidablePred (· ∈ σ)] (ab : G × G) :
    WeightedInitial.weightHom (K := K) z σ (Identified.coordinatePolynomial q ab) =
      monomial (liftedU q z σ ab) 1 + monomial (liftedV q z σ ab) 1 := by
  simp [WeightedInitial.weightHom, Identified.coordinatePolynomial,
    liftedU, liftedV, mul_add, monomial_mul]

theorem selectedLifted_coe (q : G → C) (z : C) (σ : Set C)
    [DecidablePred (· ∈ σ)] (ab : G × G) (j : ParamVar C C) :
    selectedLifted q z σ ab (j : WithBot (ParamVar C C)) = selectedExponent q σ ab j := by
  simp only [selectedLifted, selectedExponent]
  split_ifs <;> simp [liftedU, liftedV, WeightedInitial.liftedVariable, Finsupp.single_apply]

theorem strict_selected_weight (q : G → C) (z : C)
    (hq0 : ∀ a, q a = z ↔ a = 0) (σ : Set C) [DecidablePred (· ∈ σ)]
    (hzσ : z ∉ σ) (ab : G × G) :
    if SelectedRelations.selectsU addTranslationPerm 0 0 (q ⁻¹' σ) ab.1 ab.2 then
      liftedV q z σ ab ⊥ < liftedU q z σ ab ⊥
    else liftedU q z σ ab ⊥ < liftedV q z σ ab ⊥ := by
  have hzero : q 0 = z := (hq0 0).mpr rfl
  rcases ab with ⟨a,b⟩
  by_cases ha : a = 0
  · subst a
    simp [SelectedRelations.selectsU, Set.mem_preimage, hzero, hzσ,
      liftedU, liftedV, WeightedInitial.liftedVariable, WeightedInitial.reverseWeight,
      addTranslationPerm_apply]
  · have hfix : addTranslationPerm a 0 ≠ 0 := by simpa using ha
    have hpre : b = (addTranslationPerm a).symm 0 ↔ a+b=0 :=
      (addTranslationPerm a).eq_symm_apply
    by_cases haP : q a ∈ σ <;> by_cases hb : b = 0 <;> by_cases hp : a+b=0
    all_goals try { subst b; exact (ha (by simpa using hp)).elim }
    all_goals simp [SelectedRelations.selectsU, Set.mem_preimage, hpre, ha, haP,
      hb, hp, hfix, Equiv.eq_symm_apply, liftedU, liftedV,
      WeightedInitial.liftedVariable, WeightedInitial.reverseWeight, hq0,
      addTranslationPerm_apply]

section MonomialOrder

variable [LinearOrder (ParamVar C C)]

theorem weighted_leading (q : G → C) (z : C)
    (hq0 : ∀ a, q a = z ↔ a = 0) (σ : Set C) [DecidablePred (· ∈ σ)]
    (hzσ : z ∉ σ) (ab : G × G) :
    MonomialOrder.lex.degree
      (WeightedInitial.weightHom (K := K) z σ (Identified.coordinatePolynomial q ab)) =
        selectedLifted q z σ ab ∧
      MonomialOrder.lex.Monic
        (WeightedInitial.weightHom (K := K) z σ (Identified.coordinatePolynomial q ab)) := by
  classical
  let m : MonomialOrder (WithBot (ParamVar C C)) := MonomialOrder.lex
  have hw := strict_selected_weight q z hq0 σ hzσ ab
  rw [weightHom_coordinate, selectedLifted]
  by_cases hs : SelectedRelations.selectsU addTranslationPerm 0 0 (q ⁻¹' σ) ab.1 ab.2
  · simp only [if_pos hs] at hw ⊢
    have hlt : m.degree (monomial (liftedV q z σ ab) (1 : K)) ≺[m]
        m.degree (monomial (liftedU q z σ ab) (1 : K)) := by
      simpa [m.degree_monomial] using (WeightedInitial.lex_lt_of_bot hw)
    exact ⟨by simpa [m, m.degree_monomial] using m.degree_add_of_lt hlt,
      m.monic_monomial_one.add_of_lt hlt⟩
  · simp only [if_neg hs] at hw ⊢
    have hlt : m.degree (monomial (liftedU q z σ ab) (1 : K)) ≺[m]
        m.degree (monomial (liftedV q z σ ab) (1 : K)) := by
      simpa [m.degree_monomial] using (WeightedInitial.lex_lt_of_bot hw)
    rw [add_comm]
    exact ⟨by simpa [m, m.degree_monomial] using m.degree_add_of_lt hlt,
      m.monic_monomial_one.add_of_lt hlt⟩

end MonomialOrder

theorem coordinate_subfamily_algebraicIndependent {I : Type*} [Fintype I]
    (q : G → C) (z : C) (hq0 : ∀ a, q a = z ↔ a = 0)
    (σ : Set C) [DecidablePred (· ∈ σ)] (hzσ : z ∉ σ)
    (r : I → G × G)
    (hr : LinearIndependent ℚ (fun j i => (selectedExponent q σ (r j) i : ℚ))) :
    AlgebraicIndependent K (fun j => Identified.coordinatePolynomial (K := K) q (r j)) := by
  classical
  letI : LinearOrder (ParamVar C C) := LinearOrder.lift'
    (Fintype.equivFin (ParamVar C C)) (Fintype.equivFin (ParamVar C C)).injective
  let m : MonomialOrder (WithBot (ParamVar C C)) := MonomialOrder.lex
  let f : I → MvPolynomial (ParamVar C C) K := fun j => Identified.coordinatePolynomial q (r j)
  let φ := WeightedInitial.weightHom (K := K) z σ
  have hdegree (j : I) : m.degree (φ (f j)) = selectedLifted q z σ (r j) :=
    (weighted_leading q z hq0 σ hzσ (r j)).1
  have hn (j : I) : φ (f j) ≠ 0 := (weighted_leading q z hq0 σ hzσ (r j)).2.ne_zero
  have hlin : LinearIndependent ℚ (fun j i => (m.degree (φ (f j)) i : ℚ)) := by
    apply LinearIndependent.of_comp (WeightedInitial.forgetWeight (ι := C) (Ω := C))
    convert hr using 1
    funext j i
    simp only [Function.comp_apply, WeightedInitial.forgetWeight, LinearMap.coe_mk,
      AddHom.coe_mk, hdegree, selectedLifted_coe]
  exact AlgebraicIndependent.of_comp φ
    (InitialIndependence.algebraicIndependent_of_rational_leading_exponents m
      (fun j => φ (f j)) hn hlin)

theorem canonical_mem_ker (q : G → C) (z : C) (hq0 : ∀ a, q a = z ↔ a = 0)
    (σ : Set C) [DecidablePred (· ∈ σ)] (hzσ : z ∉ σ) (v : Fin 4 → ℚ) :
    ExponentRank.canonicalLinear z v ∈ (relationMap q σ).ker := by
  have hzero : q 0 = z := (hq0 0).mpr rfl
  apply LinearMap.mem_ker.mpr
  funext ab
  by_cases hs : SelectedRelations.selectsU addTranslationPerm 0 0 (q ⁻¹' σ) ab.1 ab.2
  · have ha : ab.1 ≠ 0 := by
      intro he
      have hh := hs
      rw [he] at hh
      exact SelectedRelations.selectsU_base
        (π := addTranslationPerm) (o := (0 : G))
        (by simpa only [Set.mem_preimage,hzero] using hzσ) ab.2 hh
    have hqa : q ab.1 ≠ z := fun h => ha ((hq0 _).mp h)
    simp only [relationMap, LinearMap.coe_mk, AddHom.coe_mk, ExponentRank.canonicalLinear,
      SelectedRelations.canonical, if_pos hs, if_neg hqa, Pi.zero_apply]
    ring
  · simp only [relationMap, LinearMap.coe_mk, AddHom.coe_mk, ExponentRank.canonicalLinear,
      SelectedRelations.canonical, if_neg hs, Pi.zero_apply]
    ring

def canonicalKer (q : G → C) (z : C) (hq0 : ∀ a, q a = z ↔ a = 0)
    (σ : Set C) [DecidablePred (· ∈ σ)] (hzσ : z ∉ σ) :
    (Fin 4 → ℚ) →ₗ[ℚ] (relationMap q σ).ker :=
  (ExponentRank.canonicalLinear z).codRestrict _ (canonical_mem_ker q z hq0 σ hzσ)

theorem dimension_of_generating_supports [Infinite K]
    (q : G → C) (hq : Function.Surjective q) (z : C) (hq0 : ∀ a, q a = z ↔ a = 0)
    (σ τ : Set C) [DecidablePred (· ∈ σ)]
    (hzσ : z ∉ σ) (hzτ : z ∉ τ) (hστ : Disjoint σ τ)
    (hσ : AddSubgroup.closure (q ⁻¹' σ) = ⊤)
    (hτ : AddSubgroup.closure (q ⁻¹' τ) = ⊤)
    (hσtwo : ∃ a ∈ q ⁻¹' σ, ∃ b ∈ q ⁻¹' σ, a ≠ b)
    (hτtwo : ∃ a ∈ q ⁻¹' τ, ∃ b ∈ q ⁻¹' τ, a ≠ b) :
    ringKrullDim (MvPolynomial (G × G) K ⧸ MvPolynomial.vanishingIdeal K
      (PolynomialImage.closure (Identified.coordinatePolynomial (K := K) q))) =
        (5 * Fintype.card C - 4 : ℕ) := by
  classical
  have hinj : Function.Injective (canonicalKer q z hq0 σ hzσ) := by
    intro a b h
    apply ExponentRank.canonical_injective z z
    exact congrArg Subtype.val h
  have hsurj : Function.Surjective (canonicalKer q z hq0 σ hzσ) := by
    intro w
    refine ⟨ExponentRank.decodeLinear z z w, ?_⟩
    apply Subtype.ext
    exact (relation_canonical q hq z hq0 σ τ hzσ hzτ hστ hσ hτ hσtwo hτtwo
      w w.property).symm
  have hk : Module.finrank ℚ (relationMap q σ).ker = 4 := by
    let e := LinearEquiv.ofBijective (canonicalKer q z hq0 σ hzσ) ⟨hinj,hsurj⟩
    simpa using e.finrank_eq.symm
  let M : Matrix (G × G) (ParamVar C C) ℚ := fun ab j => (selectedExponent q σ ab j : ℚ)
  have hM : M.mulVecLin = relationMap q σ := by
    apply LinearMap.ext
    intro w
    funext ab
    change (∑ j, (selectedExponent q σ ab j : ℚ) * w j) = _
    simp only [selectedExponent]
    split_ifs <;>
      simp [relationMap, *, Finsupp.add_apply, Nat.cast_add, add_mul,
        Finset.sum_add_distrib, Finsupp.single_apply, add_assoc]
  have hplus : M.rank + 4 = 5 * Fintype.card C := by
    change Module.finrank ℚ M.mulVecLin.range + 4 = _
    rw [hM]
    have h := (relationMap q σ).finrank_range_add_finrank_ker
    rw [hk] at h
    simp only [Module.finrank_pi, Module.finrank_self, mul_one, ExponentRank.card_paramVar] at h
    omega
  apply le_antisymm
  · apply Identified.imageClosure_dimension_le
    intro a
    simpa only [(hq0 0).mpr rfl] using hq0 a
  · rw [PolynomialImage.vanishingIdeal_imageClosure]
    obtain ⟨I, r, hrinj, hspan, hr⟩ := exists_linearIndependent' ℚ M.row
    letI : Fintype I := Fintype.ofInjective r hrinj
    have hcard : Fintype.card I = M.rank := by
      rw [M.rank_eq_finrank_span_row, ← hspan]
      exact (finrank_span_eq_card hr).symm
    have halg := coordinate_subfamily_algebraicIndependent (K := K) q z hq0 σ hzσ r hr
    let A := PolynomialImage.imageAlgebra (Identified.coordinatePolynomial (K := K) q)
    let f : I → A := fun j => ⟨Identified.coordinatePolynomial q (r j), by
      refine ⟨MvPolynomial.X (r j), ?_⟩
      simp [PolynomialImage.comorphism]⟩
    have hf : AlgebraicIndependent K f := AlgebraicIndependent.of_comp A.val halg
    letI : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective
      (PolynomialImage.comorphism (Identified.coordinatePolynomial (K := K) q)).rangeRestrict
      (PolynomialImage.comorphism (Identified.coordinatePolynomial (K := K) q)).rangeRestrict_surjective
    have hd := DimensionAlgebra.card_le_ringKrullDim_of_algebraicIndependent K A f hf
    have hsize : Fintype.card I = 5 * Fintype.card C - 4 := by omega
    rw [ringKrullDim_eq_of_ringEquiv
      (PolynomialImage.coordinateRingEquivImage
        (Identified.coordinatePolynomial (K := K) q)).toRingEquiv]
    simpa only [hsize] using hd

end Sunlet.StableSupport

/- Source: OddSupport.lean -/
namespace Sunlet.OddSupport

variable {G D : Type*} [AddCommGroup G] [Fintype G]

theorem zero_translate_positive (r : G → D) (f : G → ℚ)
    (hodd : ∀ a, f (-a) = - f a)
    (hpair : ∀ a b, r a = r b → f a = f b ∨ f a = -f b)
    (hcross : ∀ b c, r b ≠ r c → f (c-b) = f c - f b)
    (d g : G) (hd : 0 < f d) (hg : f g = 0) : 0 < f (d+g) := by
  have hne : r (-g) ≠ r d := by
    intro h
    rcases hpair (-g) d h with he | he <;> rw [hodd,hg] at he <;> linarith
  have he := hcross (-g) d hne
  rw [sub_neg_eq_add,hodd,hg,neg_zero,sub_zero] at he
  exact he.symm ▸ hd

theorem positive_generates (r : G → D) (f : G → ℚ)
    (hodd : ∀ a, f (-a) = - f a)
    (hpair : ∀ a b, r a = r b → f a = f b ∨ f a = -f b)
    (hcross : ∀ b c, r b ≠ r c → f (c-b) = f c - f b)
    (d : G) (hd : 0 < f d) : AddSubgroup.closure {a | 0 < f a} = ⊤ := by
  apply top_unique
  intro g _
  rcases lt_trichotomy (f g) 0 with hg | hg | hg
  · have hn : -g ∈ AddSubgroup.closure {a | 0 < f a} :=
      AddSubgroup.subset_closure (by change 0 < f (-g); rw [hodd]; linarith)
    simpa only [neg_neg] using (AddSubgroup.closure {a | 0 < f a}).neg_mem hn
  · have ht : d+g ∈ AddSubgroup.closure {a | 0 < f a} :=
      AddSubgroup.subset_closure (zero_translate_positive r f hodd hpair hcross d g hd hg)
    have hm : d ∈ AddSubgroup.closure {a | 0 < f a} := AddSubgroup.subset_closure hd
    simpa only [add_sub_cancel_left] using (AddSubgroup.closure {a | 0 < f a}).sub_mem ht hm
  · exact AddSubgroup.subset_closure hg

theorem positive_two (r : G → D) (f : G → ℚ)
    (hodd : ∀ a, f (-a) = - f a)
    (hpair : ∀ a b, r a = r b → f a = f b ∨ f a = -f b)
    (hcross : ∀ b c, r b ≠ r c → f (c-b) = f c - f b)
    (d : G) (hd : 0 < f d) (hm : 5 ≤ Fintype.card G) :
    ∃ a, 0 < f a ∧ ∃ b, 0 < f b ∧ a ≠ b := by
  classical
  by_contra htwo
  have huniq (g : G) (hg : 0 < f g) : g = d := by
    by_contra hgd
    exact htwo ⟨g,hg,d,hd,hgd⟩
  have hz (g : G) (hg : f g = 0) : g = 0 := by
    have he := huniq (d+g) (zero_translate_positive r f hodd hpair hcross d g hd hg)
    exact add_left_cancel (show d+g=d+0 by simpa using he)
  have hs : (Finset.univ : Finset G) ⊆ {0,d,-d} := by
    intro g _
    rcases lt_trichotomy (f g) 0 with hg | hg | hg
    · have hn : 0 < f (-g) := by rw [hodd]; linarith
      have he : g = -d := by simpa only [neg_neg] using congrArg Neg.neg (huniq (-g) hn)
      simp only [Finset.mem_insert,Finset.mem_singleton,he,or_true]
    · simp only [hz g hg,Finset.mem_insert,Finset.mem_singleton,true_or]
    · simp only [huniq g hg,Finset.mem_insert,Finset.mem_singleton,true_or,or_true]
  have hc := Finset.card_le_card hs
  have hb := Finset.card_insert_le (0 : G) ({d,-d} : Finset G)
  have hd' := Finset.card_insert_le d ({-d} : Finset G)
  simp only [Finset.card_univ,Finset.card_singleton] at hc hb hd'
  omega

theorem supports (r : G → D) (f : G → ℚ)
    (hodd : ∀ a, f (-a) = - f a)
    (hpair : ∀ a b, r a = r b → f a = f b ∨ f a = -f b)
    (hcross : ∀ b c, r b ≠ r c → f (c-b) = f c - f b)
    (hf : ∃ a, f a ≠ 0) (hm : 5 ≤ Fintype.card G) :
    AddSubgroup.closure {a | 0 < f a} = ⊤ ∧
    AddSubgroup.closure {a | f a < 0} = ⊤ ∧
    (∃ a, 0 < f a ∧ ∃ b, 0 < f b ∧ a ≠ b) ∧
    (∃ a, f a < 0 ∧ ∃ b, f b < 0 ∧ a ≠ b) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨d,hd⟩ : ∃ d, 0 < f d := by
    rcases lt_or_gt_of_ne ha with hn | hp
    · exact ⟨-a, by rw [hodd]; linarith⟩
    · exact ⟨a,hp⟩
  have hodd' : ∀ a, -f (-a) = -(-f a) := by intro a; rw [hodd]
  have hpair' : ∀ a b, r a = r b → -f a = -f b ∨ -f a = -(-f b) := by
    intro a b hab
    rcases hpair a b hab with h | h
    · exact Or.inl (congrArg Neg.neg h)
    · exact Or.inr (congrArg Neg.neg h)
  have hcross' : ∀ b c, r b ≠ r c → -f (c-b) = -f c - (-f b) := by
    intro b c h; rw [hcross b c h]; ring
  have hd' : 0 < -f (-d) := by rw [hodd]; linarith
  refine ⟨positive_generates r f hodd hpair hcross d hd, ?_,
    positive_two r f hodd hpair hcross d hd hm, ?_⟩
  · simpa only [neg_pos] using
      positive_generates r (fun a => -f a) hodd' hpair' hcross' (-d) hd'
  · simpa only [neg_pos] using
      positive_two r (fun a => -f a) hodd' hpair' hcross' (-d) hd' hm

end Sunlet.OddSupport
