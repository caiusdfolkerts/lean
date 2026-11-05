module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Basic
public import Mathlib.Order.WellQuasiOrder
public import Mathlib.Logic.Relation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Push
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Choose
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Data.Int.Order.Units
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

namespace Unimodular.Graver

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def ConformalLE (g h : ι → ℤ) : Prop :=
  ∀ i, (g i).toNat ≤ (h i).toNat ∧ (-g i).toNat ≤ (-h i).toNat

theorem conformalLE_iff (g h : ι → ℤ) :
    ConformalLE g h ↔
      ∀ i, (0 ≤ g i ∧ g i ≤ h i) ∨ (h i ≤ g i ∧ g i ≤ 0) := by
  constructor
  · intro H i
    obtain ⟨hp, hn⟩ := H i
    omega
  · intro H i
    rcases H i with hp | hn <;> constructor <;> omega

@[refl] theorem ConformalLE.refl (g : ι → ℤ) : ConformalLE g g :=
  fun _ => ⟨le_rfl, le_rfl⟩

@[trans] theorem ConformalLE.trans {f g h : ι → ℤ}
    (hfg : ConformalLE f g) (hgh : ConformalLE g h) : ConformalLE f h :=
  fun i => ⟨(hfg i).1.trans (hgh i).1, (hfg i).2.trans (hgh i).2⟩

@[simp] theorem zero_conformalLE (g : ι → ℤ) : ConformalLE 0 g := by
  intro i
  simp only [Pi.zero_apply, Int.toNat_zero, neg_zero]
  exact ⟨Nat.zero_le _, Nat.zero_le _⟩

theorem ConformalLE.antisymm {g h : ι → ℤ}
    (hgh : ConformalLE g h) (hhg : ConformalLE h g) : g = h := by
  funext i
  have hg := hgh i
  have hh := hhg i
  omega

theorem ConformalLE.sub {g h : ι → ℤ} (hgh : ConformalLE g h) :
    ConformalLE (h - g) h := by
  rw [conformalLE_iff] at hgh ⊢
  intro i
  have hi := hgh i
  simp only [Pi.sub_apply]
  omega

def mass (g : ι → ℤ) : ℕ :=
  ∑ i, ((g i).toNat + (-g i).toNat)

@[simp] theorem mass_zero : mass (0 : ι → ℤ) = 0 := by simp [mass]

@[simp] theorem mass_eq_zero_iff (g : ι → ℤ) : mass g = 0 ↔ g = 0 := by
  constructor
  · intro h
    funext i
    have hi : (g i).toNat + (-g i).toNat = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Nat.zero_le _)).mp h i (Finset.mem_univ i)
    change g i = 0
    omega
  · rintro rfl
    exact mass_zero

theorem mass_pos {g : ι → ℤ} (hg : g ≠ 0) : 0 < mass g := by
  have := (mass_eq_zero_iff g).not.mpr hg
  omega

theorem ConformalLE.mass_le {g h : ι → ℤ} (hgh : ConformalLE g h) :
    mass g ≤ mass h := by
  apply Finset.sum_le_sum
  intro i _
  exact Nat.add_le_add (hgh i).1 (hgh i).2

theorem ConformalLE.mass_lt {g h : ι → ℤ}
    (hgh : ConformalLE g h) (hne : g ≠ h) : mass g < mass h := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  apply Finset.sum_lt_sum
  · intro j _
    exact Nat.add_le_add (hgh j).1 (hgh j).2
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    have h := hgh i
    omega

theorem ConformalLE.mass_sub_add {g h : ι → ℤ} (hgh : ConformalLE g h) :
    mass (h - g) + mass g = mass h := by
  rw [mass, mass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := (conformalLE_iff g h).mp hgh i
  simp only [Pi.sub_apply]
  omega

theorem conformalLE_wellQuasiOrdered :
    WellQuasiOrdered (ConformalLE (ι := ι)) := by
  intro f
  let split (g : ι → ℤ) (p : ι × Bool) : ℕ :=
    if p.2 then (g p.1).toNat else (-g p.1).toNat
  obtain ⟨a, b, hab, hs⟩ :=
    (wellQuasiOrdered_le : WellQuasiOrdered (α := (ι × Bool) → ℕ) (· ≤ ·))
      (fun k => split (f k))
  refine ⟨a, b, hab, fun i => ?_⟩
  exact ⟨by simpa [split] using hs (i, true),
    by simpa [split] using hs (i, false)⟩

def Primitive (L : AddSubgroup (ι → ℤ)) (g : ι → ℤ) : Prop :=
  g ∈ L ∧ g ≠ 0 ∧
    ∀ h ∈ L, h ≠ 0 → ConformalLE h g → h = g

theorem primitive_finite (L : AddSubgroup (ι → ℤ)) :
    {g | Primitive L g}.Finite := by
  apply IsAntichain.finite_of_wellQuasiOrdered (r := ConformalLE)
    (s := {g | Primitive L g}) _ conformalLE_wellQuasiOrdered
  intro g hg h hh hne hgh
  exact hne (hh.2.2 g hg.1 hg.2.1 hgh)

theorem exists_primitive_conformal (L : AddSubgroup (ι → ℤ))
    {g : ι → ℤ} (hg : g ∈ L) (hne : g ≠ 0) :
    ∃ h, Primitive L h ∧ ConformalLE h g := by
  classical
  have hex : ∃ n : ℕ, ∃ h : ι → ℤ,
      h ∈ L ∧ h ≠ 0 ∧ ConformalLE h g ∧ mass h = n :=
    ⟨mass g, g, hg, hne, ConformalLE.refl _, rfl⟩
  obtain ⟨h, hhL, hh0, hhg, hmass⟩ := Nat.find_spec hex
  refine ⟨h, ⟨hhL, hh0, ?_⟩, hhg⟩
  intro k hkL hk0 hkh
  by_contra hne'
  have hklt := hkh.mass_lt hne'
  have hkmin : Nat.find hex ≤ mass k :=
    Nat.find_min' hex ⟨k, hkL, hk0, hkh.trans hhg, rfl⟩
  omega

def Between (c d x : ι → ℤ) : Prop :=
  ∀ i, min (c i) (d i) ≤ x i ∧ x i ≤ max (c i) (d i)

@[simp] theorem between_left (c d : ι → ℤ) : Between c d c := by
  intro i
  exact ⟨min_le_left _ _, le_max_left _ _⟩

@[simp] theorem between_right (c d : ι → ℤ) : Between c d d := by
  intro i
  exact ⟨min_le_right _ _, le_max_right _ _⟩

theorem Between.add_conformal {c d x g : ι → ℤ}
    (hx : Between c d x) (hg : ConformalLE g (d - x)) : Between c d (x + g) := by
  intro i
  have hxi := hx i
  have hgi := (conformalLE_iff g (d - x)).mp hg i
  simp only [Pi.add_apply, Pi.sub_apply] at hgi ⊢
  omega

def BoundedMove (L : AddSubgroup (ι → ℤ)) (c d x y : ι → ℤ) : Prop :=
  Primitive L (y - x) ∧ Between c d y

theorem primitive_connectivity (L : AddSubgroup (ι → ℤ))
    (c d : ι → ℤ) (hdc : d - c ∈ L) :
    Relation.ReflTransGen (BoundedMove L c d) c d := by
  classical
  have aux : ∀ n : ℕ, ∀ x : ι → ℤ, Between c d x → d - x ∈ L →
      mass (d - x) = n → Relation.ReflTransGen (BoundedMove L c d) x d := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro x hx hxL hmass
      by_cases heq : x = d
      · subst x
        exact Relation.ReflTransGen.refl
      have hdif : d - x ≠ 0 := by
        intro hzero
        exact heq (sub_eq_zero.mp hzero).symm
      obtain ⟨g, hg, hgconf⟩ := exists_primitive_conformal L hxL hdif
      let y := x + g
      have hy : Between c d y := hx.add_conformal hgconf
      have hdyeq : d - y = (d - x) - g := by dsimp [y]; abel
      have hyL : d - y ∈ L := by rw [hdyeq]; exact L.sub_mem hxL hg.1
      have hless : mass (d - y) < n := by
        rw [hdyeq]
        have he := hgconf.mass_sub_add
        have hp := mass_pos hg.2.1
        omega
      have hstep : BoundedMove L c d x y := by
        refine ⟨?_, hy⟩
        have he : y - x = g := by dsimp [y]; abel
        rwa [he]
      exact (Relation.ReflTransGen.single hstep).trans
        (ih (mass (d - y)) hless y hy hyL rfl)
  exact aux _ c (between_left _ _) hdc rfl

theorem Between.nonnegative {c d x : ι → ℤ} (hx : Between c d x)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i) : ∀ i, 0 ≤ x i := by
  intro i
  exact (le_min (hc i) (hd i)).trans (hx i).1

theorem Between.coordinate_zero {c d x : ι → ℤ} (hx : Between c d x)
    {i : ι} (hc : c i = 0) (hd : d i = 0) : x i = 0 := by
  have hi := hx i
  simp only [hc, hd, min_self, max_self] at hi
  omega

theorem kernel_primitive_connectivity {M : Type*} [AddCommGroup M]
    (A : (ι → ℤ) →+ M) (c d : ι → ℤ) (hcd : A c = A d) :
    Relation.ReflTransGen (BoundedMove A.ker c d) c d := by
  apply primitive_connectivity
  change A (d - c) = 0
  rw [map_sub, hcd, sub_self]

theorem reachable_fiber_and_box {M : Type*} [AddCommGroup M]
    (A : (ι → ℤ) →+ M) (c d : ι → ℤ) {x : ι → ℤ}
    (h : Relation.ReflTransGen (BoundedMove A.ker c d) c x) :
    A x = A c ∧ Between c d x := by
  induction h with
  | refl => exact ⟨rfl, between_left _ _⟩
  | @tail y z hprev hstep ih =>
    have hz : A (z - y) = 0 := hstep.1.1
    have hzy : A z = A y := sub_eq_zero.mp (by simpa only [map_sub] using hz)
    exact ⟨hzy.trans ih.1, hstep.2⟩

theorem finite_nonnegative_fiber_connectivity {M : Type*} [AddCommGroup M]
    (A : (ι → ℤ) →+ M) (c d : ι → ℤ) (hcd : A c = A d)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i) :
    ∃ G : Finset (ι → ℤ), (∀ g, g ∈ G ↔ Primitive A.ker g) ∧
      Relation.ReflTransGen (fun x y => y - x ∈ G ∧ A x = A c ∧ A y = A c ∧
        Between c d x ∧ Between c d y ∧
        (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i)) c d := by
  classical
  let G := (primitive_finite A.ker).toFinset
  have hG : ∀ g, g ∈ G ↔ Primitive A.ker g := by
    intro g
    exact Set.Finite.mem_toFinset _
  refine ⟨G, hG, ?_⟩
  have lift : ∀ {x : ι → ℤ}, Relation.ReflTransGen (BoundedMove A.ker c d) c x →
      Relation.ReflTransGen (fun x y => y - x ∈ G ∧ A x = A c ∧ A y = A c ∧
        Between c d x ∧ Between c d y ∧
        (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i)) c x := by
    intro x hpath
    induction hpath with
    | refl => exact Relation.ReflTransGen.refl
    | @tail y z hprev hstep ih =>
      apply ih.tail
      obtain ⟨hyA, hy⟩ := reachable_fiber_and_box A c d hprev
      obtain ⟨hzA, hz⟩ := reachable_fiber_and_box A c d (hprev.tail hstep)
      exact ⟨(hG _).mpr hstep.1, hyA, hzA, hy, hz,
        hy.nonnegative hc hd, hz.nonnegative hc hd⟩
  exact lift (kernel_primitive_connectivity A c d hcd)

end Unimodular.Graver

namespace Unimodular.PositiveCoordinates

open scoped BigOperators
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_eq_prod_diag_of_weight (T : Matrix ι ι ℤ) (w : ι → ℝ)
    (hw : ∀ i j, i ≠ j → T i j ≠ 0 → w j < w i) :
    T.det = ∏ i, T i i := by
  have hterm : ∀ σ : Equiv.Perm ι, σ ≠ 1 → ∏ i, T (σ i) i = 0 := by
    intro σ hσ
    by_contra hnz
    have hnzi : ∀ i, T (σ i) i ≠ 0 := by
      intro i hi
      apply hnz
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    have hle : ∀ i, w i ≤ w (σ i) := by
      intro i
      by_cases hi : σ i = i
      · rw [hi]
      · exact (hw (σ i) i hi (hnzi i)).le
    have hne : ∃ i, σ i ≠ i := by
      by_contra! h
      apply hσ
      ext i
      exact h i
    obtain ⟨i, hi⟩ := hne
    have hlt : (∑ j, w j) < ∑ j, w (σ j) :=
      Finset.sum_lt_sum (fun j _ => hle j)
        ⟨i, Finset.mem_univ i, hw (σ i) i hi (hnzi i)⟩
    have he : (∑ j, w (σ j)) = ∑ j, w j := Equiv.sum_comp σ w
    linarith
  rw [Matrix.det_apply, Finset.sum_eq_single (1 : Equiv.Perm ι)]
  · simp
  · intro σ _ hσ
    rw [hterm σ hσ]
    simp
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem weight_decreases (T : Matrix ι ι ℤ) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hdiag : ∀ i, T i i = 1)
    (hoff : ∀ i j, i ≠ j → T i j ≤ 0)
    (hpos : ∀ i, 0 < ∑ j, (T i j : ℝ) * w j)
    {i j : ι} (hij : i ≠ j) (ht : T i j ≠ 0) : w j < w i := by
  have htneg : (T i j : ℝ) ≤ -1 := by
    have h := hoff i j hij
    have : T i j ≤ -1 := by omega
    exact_mod_cast this
  have hbound : (∑ k, (T i k : ℝ) * w k) ≤ w i - w j := by
    calc
      (∑ k, (T i k : ℝ) * w k) ≤
          ∑ k, (if k = i then w i else if k = j then -w j else 0) := by
        apply Finset.sum_le_sum
        intro k _
        by_cases hki : k = i
        · subst k
          simp [hdiag]
        · by_cases hkj : k = j
          · subst k
            simp only [hij.symm, ↓reduceIte]
            nlinarith [hw j]
          · simp only [hki, hkj, ↓reduceIte]
            have hk : (T i k : ℝ) ≤ 0 := by exact_mod_cast hoff i k (Ne.symm hki)
            exact mul_nonpos_of_nonpos_of_nonneg hk (hw k).le
      _ = w i - w j := by
        have hiSum : (∑ k : ι, if k = i then w i else 0) = w i := by
          simpa using Finset.sum_ite_eq' (Finset.univ : Finset ι) i (fun _ => w i)
        have hjSum : (∑ k : ι, if k = j then -w j else 0) = -w j := by
          simpa using Finset.sum_ite_eq' (Finset.univ : Finset ι) j (fun _ => -w j)
        calc
          (∑ k, if k = i then w i else if k = j then -w j else 0) =
              (∑ k, if k = i then w i else 0) +
                (∑ k, if k = j then -w j else 0) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k _
            by_cases hki : k = i
            · subst k
              simp [hij]
            · simp [hki]
          _ = w i - w j := by rw [hiSum, hjSum, sub_eq_add_neg]
  have hp := hpos i
  linarith

theorem det_eq_one_of_positive_vector (T : Matrix ι ι ℤ) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hdiag : ∀ i, T i i = 1)
    (hoff : ∀ i j, i ≠ j → T i j ≤ 0)
    (hpos : ∀ i, 0 < ∑ j, (T i j : ℝ) * w j) : T.det = 1 := by
  rw [det_eq_prod_diag_of_weight T w
    (fun i j hij ht => weight_decreases T w hw hdiag hoff hpos hij ht)]
  simp [hdiag]

def PositiveCoordinateBound (T : Matrix ι ι ℤ) : Prop :=
  ∀ j, ∑ i, max (T i j) 0 ≤ 1

theorem positive_entry_eq_one {T : Matrix ι ι ℤ} (hT : PositiveCoordinateBound T)
    {i j : ι} (hij : 0 < T i j) : T i j = 1 := by
  have hsingle : max (T i j) 0 ≤ ∑ k, max (T k j) 0 :=
    Finset.single_le_sum (fun k _ => le_max_right (T k j) 0) (Finset.mem_univ i)
  have hi := hT j
  rw [max_eq_left hij.le] at hsingle
  omega

theorem positive_entry_unique {T : Matrix ι ι ℤ} (hT : PositiveCoordinateBound T)
    {i k j : ι} (hij : 0 < T i j) (hkj : 0 < T k j) : i = k := by
  by_contra hik
  have hsum : max (T i j) 0 + max (T k j) 0 ≤ ∑ a, max (T a j) 0 := by
    calc
      max (T i j) 0 + max (T k j) 0 = ∑ a ∈ ({i, k} : Finset ι), max (T a j) 0 := by
        simp [hik]
      _ ≤ ∑ a, max (T a j) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun a _ _ => le_max_right _ _)
  have hi := hT j
  rw [max_eq_left hij.le, max_eq_left hkj.le] at hsum
  omega

theorem exists_positive_in_row (T : Matrix ι ι ℤ) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hpos : ∀ i, 0 < ∑ j, (T i j : ℝ) * w j) :
    ∀ i, ∃ j, 0 < T i j := by
  intro i
  by_contra! hn
  have hnonpos : ∑ j, (T i j : ℝ) * w j ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    have hj : (T i j : ℝ) ≤ 0 := by exact_mod_cast hn j
    exact mul_nonpos_of_nonpos_of_nonneg hj (hw j).le
  exact (not_lt_of_ge hnonpos) (hpos i)

theorem abs_det_eq_one (T : Matrix ι ι ℤ) (hT : PositiveCoordinateBound T)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hpos : ∀ i, 0 < ∑ j, (T i j : ℝ) * w j) : |T.det| = 1 := by
  classical
  choose f hf using exists_positive_in_row T w hw hpos
  have hfi : Function.Injective f := by
    intro i k hik
    exact positive_entry_unique hT (hf i) (by simpa [hik] using hf k)
  let e : Equiv.Perm ι := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfi)
  let S : Matrix ι ι ℤ := T.submatrix id e
  let v : ι → ℝ := fun i => w (e i)
  have hdiag : ∀ i, S i i = 1 := by
    intro i
    exact positive_entry_eq_one hT (hf i)
  have hoff : ∀ i j, i ≠ j → S i j ≤ 0 := by
    intro i j hij
    by_contra! hp
    have hji : j = i := positive_entry_unique hT (hf j) hp
    exact hij hji.symm
  have hSpos : ∀ i, 0 < ∑ j, (S i j : ℝ) * v j := by
    intro i
    have heq : (∑ j, (S i j : ℝ) * v j) = ∑ j, (T i j : ℝ) * w j := by
      exact Equiv.sum_comp e (fun j => (T i j : ℝ) * w j)
    rw [heq]
    exact hpos i
  have hdet : S.det = 1 :=
    det_eq_one_of_positive_vector S v (fun i => hw (e i)) hdiag hoff hSpos
  have habs : |S.det| = |T.det| :=
    Matrix.abs_det_submatrix_equiv_equiv (Equiv.refl ι) e T
  rw [hdet, abs_one] at habs
  exact habs.symm

end Unimodular.PositiveCoordinates

namespace Unimodular.IntegralRigidity

open scoped BigOperators

variable {ι E M M' : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [Module ℤ M] [AddCommGroup M'] [Module ℤ M']

theorem det_replace_basis (b : Module.Basis ι ℤ M) (x : M) (i : ι) :
    b.det (Function.update b i x) = b.repr x i := by
  conv_lhs => rw [← b.sum_repr x]
  rw [b.det.map_update_sum]
  simp only [b.det.map_update_smul, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp [b.det_self]
  · intro j _ hji
    rw [b.det.map_update_self b (Ne.symm hji), mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

theorem sign_eq_self_of_abs_le_one {z : ℤ} (hz : |z| ≤ 1) : z.sign = z := by
  have hbounds := abs_le.mp hz
  have hcases : z = -1 ∨ z = 0 ∨ z = 1 := by omega
  rcases hcases with rfl | rfl | rfl <;> rfl

def Uniform (b : Module.Basis ι ℤ M) (U : E → M) : Prop :=
  ∀ a : ι → E, |b.det (U ∘ a)| ≤ 1

theorem independent_iff_det_ne_zero (b : Module.Basis ι ℤ M) (u : ι → M) :
    LinearIndependent ℤ u ↔ b.det u ≠ 0 := by
  letI : Module.Free ℤ M := Module.Free.of_basis b
  letI : Module.Finite ℤ M := Module.Finite.of_basis b
  let f : M →ₗ[ℤ] M := b.constr ℕ u
  have hd : f.det = b.det u := by
    rw [Module.Basis.det_apply, b.toMatrix_eq_toMatrix_constr,
      LinearMap.det_toMatrix]
  constructor
  · intro hu hz
    have hk : f.ker ≠ ⊥ := LinearMap.det_eq_zero_iff_ker_ne_bot.mp (hd.trans hz)
    exact hk (LinearMap.ker_eq_bot.mpr (b.injective_constr_of_linearIndependent hu))
  · intro hdet
    have hk : f.ker = ⊥ := by
      by_contra h
      exact hdet (hd.symm.trans (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h))
    have h := b.linearIndependent.map' f hk
    have he : (fun i => f (b i)) = u := funext (b.constr_basis ℕ u)
    simpa only [Function.comp_def, he] using h

theorem uniform_iff_independent_spans (b : Module.Basis ι ℤ M) (U : E → M) :
    Uniform b U ↔ ∀ a : ι → E, LinearIndependent ℤ (U ∘ a) →
      Submodule.span ℤ (Set.range (U ∘ a)) = ⊤ := by
  constructor
  · intro h a ha
    apply (b.is_basis_iff_det.mpr ?_).2
    apply Int.isUnit_iff_abs_eq.mpr
    have hn := (independent_iff_det_ne_zero b (U ∘ a)).mp ha
    have hb := h a
    have hpos : 0 < |b.det (U ∘ a)| := abs_pos.mpr hn
    omega
  · intro h a
    by_cases hz : b.det (U ∘ a) = 0
    · simp [hz]
    · have hi := (independent_iff_det_ne_zero b (U ∘ a)).mpr hz
      have hu := b.is_basis_iff_det.mp ⟨hi, h a hi⟩
      exact (Int.isUnit_iff_abs_eq.mp hu).le

def SameChirotope (b : Module.Basis ι ℤ M) (b' : Module.Basis ι ℤ M')
    (U : E → M) (V : E → M') : Prop :=
  ∀ a : ι → E, (b.det (U ∘ a)).sign = (b'.det (V ∘ a)).sign

theorem repr_eq_chirotope (b : Module.Basis ι ℤ M) (U : E → M)
    (labels : ι → E) (hb : ∀ i, U (labels i) = b i) (hU : Uniform b U)
    (e : E) (j : ι) :
    b.repr (U e) j = (b.det (U ∘ Function.update labels j e)).sign := by
  have hfamily : U ∘ Function.update labels j e = Function.update b j (U e) := by
    funext i
    by_cases hij : i = j
    · subst i
      simp
    · simp [Function.comp_def, hij, hb]
  rw [sign_eq_self_of_abs_le_one (hU _), hfamily, det_replace_basis]

theorem exists_unique_lattice_equiv
    (b : Module.Basis ι ℤ M) (b' : Module.Basis ι ℤ M')
    (U : E → M) (V : E → M') (labels : ι → E)
    (hb : ∀ i, U (labels i) = b i) (hb' : ∀ i, V (labels i) = b' i)
    (hU : Uniform b U) (hV : Uniform b' V) (hchi : SameChirotope b b' U V) :
    ∃! φ : M ≃ₗ[ℤ] M', ∀ e, φ (U e) = V e := by
  let φ : M ≃ₗ[ℤ] M' := b.repr.trans b'.repr.symm
  have hφ : ∀ e, φ (U e) = V e := by
    intro e
    apply b'.repr.injective
    change b'.repr (b'.repr.symm (b.repr (U e))) = b'.repr (V e)
    rw [b'.repr.apply_symm_apply]
    ext j
    rw [repr_eq_chirotope b U labels hb hU,
      repr_eq_chirotope b' V labels hb' hV]
    exact hchi _
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  apply LinearEquiv.toLinearMap_injective
  apply b.ext
  intro i
  change ψ (b i) = φ (b i)
  rw [← hb i, hψ, hφ]

end Unimodular.IntegralRigidity

namespace Unimodular.GenericWeights

open scoped BigOperators
open Polynomial

variable {κ : Type*} [Fintype κ]

theorem exists_positive_avoiding (p : κ → ℤ[X]) (hp : ∀ k, p k ≠ 0) :
    ∃ t : ℤ, 0 < t ∧ ∀ k, (p k).eval t ≠ 0 := by
  classical
  let P : ℤ[X] := ∏ k, p k
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hp k)
  obtain ⟨b, hb⟩ := P.exists_max_root hP
  let t := max b 0 + 1
  have ht : 0 < t := by dsimp [t]; omega
  refine ⟨t, ht, ?_⟩
  intro k hk
  have hroot : P.IsRoot t := by
    change P.eval t = 0
    simp only [P, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) hk
  have hb' := hb t hroot
  dsimp [t] at hb'
  omega

noncomputable def encode {n : ℕ} (a : Fin n → ℤ) : ℤ[X] :=
  ∑ i, Polynomial.monomial i.val (a i)

@[simp] theorem coeff_encode {n : ℕ} (a : Fin n → ℤ) (i : Fin n) :
    (encode a).coeff i.val = a i := by
  classical
  simp only [encode, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hv : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp [Polynomial.coeff_monomial, hv, hv.symm]
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

theorem encode_ne_zero {n : ℕ} {a : Fin n → ℤ} (ha : ∃ i, a i ≠ 0) :
    encode a ≠ 0 := by
  obtain ⟨i, hi⟩ := ha
  intro hz
  have hcoeff := congrArg (fun p : ℤ[X] => p.coeff i.val) hz
  apply hi
  simpa using hcoeff

@[simp] theorem eval_encode {n : ℕ} (a : Fin n → ℤ) (t : ℤ) :
    (encode a).eval t = ∑ i, a i * t ^ i.val := by
  simp [encode, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem exists_geometric_progression {n : ℕ} (a : κ → Fin n → ℤ)
    (ha : ∀ k, ∃ i, a k i ≠ 0) :
    ∃ t : ℤ, 0 < t ∧ ∀ k, ∑ i, a k i * t ^ i.val ≠ 0 := by
  obtain ⟨t, ht, havoid⟩ := exists_positive_avoiding
    (fun k => encode (a k)) (fun k => encode_ne_zero (ha k))
  exact ⟨t, ht, by simpa only [eval_encode] using havoid⟩

end Unimodular.GenericWeights

namespace Unimodular.BasisCover

open scoped BigOperators
open Unimodular.PositiveCoordinates Unimodular.IntegralRigidity

variable {n : ℕ} {κ E M : Type*} [Fintype κ]
  [AddCommGroup M] [Module ℤ M]

theorem basis_determinant_nonzero (b c : Module.Basis (Fin n) ℤ M)
    (u : Fin n → M) (hu : b.det u ≠ 0) : c.det u ≠ 0 := by
  intro hc
  have he : b.det u = b.det c * c.det u := by
    have hm := b.det.eq_smul_basis_det c
    have hv := congrArg (fun f : M [⋀^Fin n]→ₗ[ℤ] ℤ => f u) hm
    simpa only [AlternatingMap.smul_apply, smul_eq_mul] using hv
  rw [hc, mul_zero] at he
  exact hu he

theorem basis_determinant_abs (b c : Module.Basis (Fin n) ℤ M)
    (u : Fin n → M) : |b.det u| = |c.det u| := by
  have he : b.det u = b.det c * c.det u := by
    have hm := b.det.eq_smul_basis_det c
    have hv := congrArg (fun f : M [⋀^Fin n]→ₗ[ℤ] ℤ => f u) hm
    simpa only [AlternatingMap.smul_apply, smul_eq_mul] using hv
  have hunit : |b.det c| = 1 := Int.isUnit_iff_abs_eq.mp (b.isUnit_det c)
  rw [he, abs_mul, hunit, one_mul]

theorem uniform_of_basis_cover
    (B : κ → Module.Basis (Fin n) ℤ M) (U : E → M)
    (b₀ : Module.Basis (Fin n) ℤ M)
    (hcover : ∀ x : M, ∃ k, ∀ i, 0 ≤ (B k).repr x i)
    (hbound : ∀ k e, ∑ i, max ((B k).repr (U e) i) 0 ≤ 1) :
    Uniform b₀ U := by
  classical
  intro a
  by_cases hzero : b₀.det (U ∘ a) = 0
  · rw [hzero, abs_zero]
    exact zero_le_one
  let A : κ × Fin n → Fin n → ℤ :=
    fun p i => (B p.1).repr (U (a i)) p.2
  have hA : ∀ p, ∃ i, A p i ≠ 0 := by
    rintro ⟨k, j⟩
    by_contra! hrow
    have hdet : (B k).det (U ∘ a) = 0 := by
      rw [Module.Basis.det_apply]
      apply Matrix.det_eq_zero_of_row_eq_zero j
      intro i
      exact hrow i
    exact basis_determinant_nonzero b₀ (B k) (U ∘ a) hzero hdet
  obtain ⟨t, ht, hav⟩ := GenericWeights.exists_geometric_progression A hA
  let x : M := ∑ i : Fin n, t ^ i.val • U (a i)
  obtain ⟨k, hk⟩ := hcover x
  have hcoord (j : Fin n) : (B k).repr x j = ∑ i, A (k, j) i * t ^ i.val := by
    simp [x, A, map_sum, map_smul, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have hstrict : ∀ j, 0 < (B k).repr x j := by
    intro j
    have hn : (B k).repr x j ≠ 0 := by rw [hcoord]; exact hav (k, j)
    exact lt_of_le_of_ne (hk j) (Ne.symm hn)
  let T : Matrix (Fin n) (Fin n) ℤ := (B k).toMatrix (U ∘ a)
  let w : Fin n → ℝ := fun i => (t ^ i.val : ℤ)
  have hT : PositiveCoordinateBound T := by
    intro j
    exact hbound k (a j)
  have hw : ∀ i, 0 < w i := by
    intro i
    change (0 : ℝ) < (t ^ i.val : ℤ)
    exact_mod_cast pow_pos ht i.val
  have hp : ∀ j, 0 < ∑ i, (T j i : ℝ) * w i := by
    intro j
    have hz : 0 < ∑ i, A (k, j) i * t ^ i.val := by
      rw [← hcoord]
      exact hstrict j
    change (0 : ℝ) < ∑ i, ((B k).repr (U (a i)) j : ℝ) * (t ^ i.val : ℤ)
    exact_mod_cast hz
  have hdet : |(B k).det (U ∘ a)| = 1 := abs_det_eq_one T hT w hw hp
  rw [basis_determinant_abs b₀ (B k) (U ∘ a), hdet]

end Unimodular.BasisCover

noncomputable section

namespace Unimodular

open scoped BigOperators

abbrev Lattice (n : ℕ) := Fin n → ℤ
abbrev Ambient (n : ℕ) := Fin n → ℝ

def embed {n : ℕ} (x : Lattice n) : Ambient n := fun i => (x i : ℝ)

def realCoordinates {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Ambient n →ₗ[ℝ] Ambient n where
  toFun x i := ∑ j, ((b.repr (Pi.single j 1) i : ℤ) : ℝ) * x j
  map_add' x y := by
    ext i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    ext i
    simp [Finset.mul_sum, mul_assoc, mul_left_comm]

theorem realCoordinates_embed {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (x : Lattice n) (i : Fin n) :
    realCoordinates b (embed x) i = (b.repr x i : ℤ) := by
  have hdecomp : ∑ j, x j • (Pi.single j (1 : ℤ)) = x := by
    ext k
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  have hcoord : b.repr x i = ∑ j, x j * b.repr (Pi.single j 1) i := by
    conv_lhs => arg 1; rw [← hdecomp]
    simp only [map_sum, map_smulₛₗ, RingHom.id_apply, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, smul_eq_mul]
  change (∑ j, ((b.repr (Pi.single j 1) i : ℤ) : ℝ) * (x j : ℝ)) = _
  rw [hcoord, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [mul_comm]

theorem realCoordinates_basis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (j : Fin n) :
    realCoordinates b (embed (b j)) = Pi.single j 1 := by
  ext i
  rw [realCoordinates_embed]
  by_cases hij : i = j
  · subst i
    simp
  · simp [Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply, hij, Ne.symm hij]

theorem realCoordinates_sum_basis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (c : Fin n → ℝ) :
    realCoordinates b (∑ i, c i • embed (b i)) = c := by
  rw [map_sum]
  simp only [map_smul, realCoordinates_basis]
  ext j
  simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]

theorem sum_basis_realCoordinates {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (x : Ambient n) :
    ∑ i, realCoordinates b x i • embed (b i) = x := by
  have hsurj : Function.Surjective (realCoordinates b) :=
    fun c => ⟨∑ i, c i • embed (b i), realCoordinates_sum_basis b c⟩
  have hinj : Function.Injective (realCoordinates b) :=
    LinearMap.injective_iff_surjective.mpr hsurj
  apply hinj
  exact realCoordinates_sum_basis b (realCoordinates b x)

def basisCone {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n)) : Set (Ambient n) :=
  {x | ∃ c : Fin n → ℝ, (∀ i, 0 ≤ c i) ∧ ∑ i, c i • embed (b i) = x}

theorem mem_basisCone_iff {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (x : Ambient n) :
    x ∈ basisCone b ↔ ∀ i, 0 ≤ realCoordinates b x i := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    simpa only [realCoordinates_sum_basis] using hc
  · intro hx
    exact ⟨realCoordinates b x, hx, sum_basis_realCoordinates b x⟩

def basisFace {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) : Set (Ambient n) :=
  {x | ∃ c : Fin n → ℝ, (∀ i, 0 ≤ c i) ∧
    (∀ i ∉ I, c i = 0) ∧ ∑ i, c i • embed (b i) = x}

structure SmoothCompleteFan (n : ℕ) where
  maximal : Finset (Module.Basis (Fin n) ℤ (Lattice n))
  complete : ∀ x : Ambient n, ∃ b ∈ maximal, x ∈ basisCone b
  intersection : ∀ b ∈ maximal, ∀ c ∈ maximal,
    ∃ I J : Finset (Fin n), basisCone b ∩ basisCone c = basisFace b I ∧
      basisCone b ∩ basisCone c = basisFace c J

namespace SmoothCompleteFan

variable {n : ℕ} (fan : SmoothCompleteFan n)

def rays : Set (Lattice n) := {u | ∃ b ∈ fan.maximal, ∃ i, b i = u}

def PositiveCoordinateCriterion : Prop :=
  ∀ b ∈ fan.maximal, ∀ u ∈ fan.rays, ∑ i, max (b.repr u i) 0 ≤ 1

def UniformlyUnimodular : Prop :=
  IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
    (fun u : fan.rays => (u : Lattice n))

theorem uniformlyUnimodular_of_positiveCoordinateCriterion
    (hfan : fan.PositiveCoordinateCriterion) : fan.UniformlyUnimodular := by
  classical
  let B : fan.maximal → Module.Basis (Fin n) ℤ (Lattice n) := Subtype.val
  apply BasisCover.uniform_of_basis_cover B
  · intro x
    obtain ⟨b, hb, hx⟩ := fan.complete (embed x)
    refine ⟨⟨b, hb⟩, ?_⟩
    intro i
    have hi := (mem_basisCone_iff b (embed x)).mp hx i
    rw [realCoordinates_embed] at hi
    exact_mod_cast hi
  · intro b u
    exact hfan b.val b.property u.val u.property

end SmoothCompleteFan
end Unimodular

end

noncomputable section

namespace Unimodular

open scoped BigOperators

def pairing {n : ℕ} (m : Ambient n) (u : Lattice n) : ℝ :=
  ∑ j, m j * (u j : ℝ)

def dualCorner {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (t : Fin n → ℝ) : Ambient n :=
  fun j => ∑ i, t i * ((b.repr (Pi.single j 1) i : ℤ) : ℝ)

theorem pairing_dualCorner {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (t : Fin n → ℝ) (u : Lattice n) :
    pairing (dualCorner b t) u = ∑ i, t i * ((b.repr u i : ℤ) : ℝ) := by
  simp only [pairing, dualCorner, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  exact realCoordinates_embed b u i

def cornerParallelepiped {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) : Set (Ambient n) :=
  {m | ∃ t : Fin n → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧ dualCorner b t = m}

theorem cube_bound_iff_positive_mass {n : ℕ} (a : Fin n → ℤ) :
    (∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) →
      ∑ i, t i * (a i : ℝ) ≤ 1) ↔ ∑ i, max (a i) 0 ≤ 1 := by
  constructor
  · intro h
    let t : Fin n → ℝ := fun i => if 0 < a i then 1 else 0
    have ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1 := by
      intro i
      dsimp [t]
      split_ifs <;> norm_num
    have hs := h t ht
    have he : (∑ i, t i * (a i : ℝ)) = ((∑ i, max (a i) 0 : ℤ) : ℝ) := by
      rw [Int.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : 0 < a i
      · simp [t, hi, max_eq_left hi.le]
      · simp [t, hi, max_eq_right (le_of_not_gt hi)]
    rw [he] at hs
    exact_mod_cast hs
  · intro h t ht
    have hreal : ((∑ i, max (a i) 0 : ℤ) : ℝ) ≤ 1 := by exact_mod_cast h
    apply le_trans _ hreal
    rw [Int.cast_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : 0 ≤ a i
    · rw [max_eq_left hi]
      have ha : (0 : ℝ) ≤ (a i : ℝ) := by exact_mod_cast hi
      nlinarith [(ht i).2]
    · rw [max_eq_right (le_of_lt (lt_of_not_ge hi))]
      have ha : (a i : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hi))
      simpa using mul_nonpos_of_nonneg_of_nonpos (ht i).1 ha

namespace SmoothCompleteFan

variable {n : ℕ} (fan : SmoothCompleteFan n)

def rayPolytope : Set (Ambient n) := {m | ∀ u ∈ fan.rays, pairing m u ≤ 1}

def CornersContained : Prop :=
  ∀ b ∈ fan.maximal, cornerParallelepiped b ⊆ fan.rayPolytope

theorem cornersContained_iff_positiveCoordinateCriterion :
    fan.CornersContained ↔ fan.PositiveCoordinateCriterion := by
  constructor
  · intro h b hb u hu
    apply (cube_bound_iff_positive_mass (fun i => b.repr u i)).mp
    intro t ht
    have hm : dualCorner b t ∈ fan.rayPolytope := h b hb ⟨t, ht, rfl⟩
    have hmu := hm u hu
    rwa [pairing_dualCorner] at hmu
  · intro h b hb m hm u hu
    obtain ⟨t, ht, rfl⟩ := hm
    rw [pairing_dualCorner]
    exact (cube_bound_iff_positive_mass (fun i => b.repr u i)).mpr (h b hb u hu) t ht

theorem uniformlyUnimodular_of_cornersContained (h : fan.CornersContained) :
    fan.UniformlyUnimodular :=
  fan.uniformlyUnimodular_of_positiveCoordinateCriterion
    (fan.cornersContained_iff_positiveCoordinateCriterion.mp h)

end SmoothCompleteFan
end Unimodular

end
