module
public import e7_orbits
public import coordinate_orbits
public import Mathlib.GroupTheory.Perm.Sign

@[expose] public section
noncomputable section
namespace PaperVerification.ColdSpots
open scoped BigOperators

def coordinateSetFlip {R : Type*} [Neg R] (S : Finset (Fin 8)) (x : Fin 8 → R) : Fin 8 → R :=
  fun i => if i∈S then -x i else x i

lemma coordinateSetFlip_sum {R : Type*} [CommRing R] (S : Finset (Fin 8))
    (x : Fin 8 → R) : (∑ i,coordinateSetFlip S x i) = (∑ i,x i)-2*∑ i∈S,x i := by
  have h : coordinateSetFlip S x = fun i => x i-2*(if i∈S then x i else 0) := by
    funext i; simp only [coordinateSetFlip]; split_ifs <;> ring
  rw [h]
  simp [Finset.sum_sub_distrib,Finset.mul_sum,Finset.sum_ite]

lemma coordinateSetFlip_involutive {R : Type*} [InvolutiveNeg R] (S : Finset (Fin 8)) :
    Function.Involutive (coordinateSetFlip (R:=R) S) := by
  intro x; funext i; simp only [coordinateSetFlip]; split_ifs <;> simp

def coordinateSetFlipEquiv (S : Finset (Fin 8)) : (Fin 8 → ℝ) ≃ₗ[ℝ] (Fin 8 → ℝ) where
  toFun := coordinateSetFlip S
  invFun := coordinateSetFlip S
  left_inv := coordinateSetFlip_involutive S
  right_inv := coordinateSetFlip_involutive S
  map_add' x y := by ext i; simp only [coordinateSetFlip,Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [coordinateSetFlip,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    split_ifs <;> ring

lemma coordinateSetFlip_mem (S : Finset (Fin 8)) (hS : Even S.card) {x : Fin 8 → ℝ}
    (hx : x ∈ dPlusSet 8) : coordinateSetFlip S x ∈ dPlusSet 8 := by
  obtain ⟨z,hz,hx⟩ := hx
  rcases hx with rfl | rfl
  · refine ⟨coordinateSetFlip S z,?_,Or.inl ?_⟩
    · rw [coordinateSetFlip_sum]
      exact hz.sub (even_two.mul_right _)
    · funext i; simp only [coordinateSetFlip,intVec]; split_ifs <;> simp
  · let w : Fin 8 → ℤ := fun i => coordinateSetFlip S z i-(if i∈S then 1 else 0)
    refine ⟨w,?_,Or.inr ?_⟩
    · have hw : (∑ i,w i)=(∑ i,z i)-2*(∑ i∈S,z i)-S.card := by
        simp [w,Finset.sum_sub_distrib,coordinateSetFlip_sum,Finset.sum_ite]
      rw [hw]
      exact (hz.sub (even_two.mul_right _)).sub (by exact_mod_cast hS)
    · funext i
      simp only [coordinateSetFlip,w]
      split_ifs <;> push_cast <;> ring

lemma e8Symmetry_setFlip (S : Finset (Fin 8)) (hS : Even S.card) :
    CoordinateLatticeSymmetry (dPlusSet 8) (coordinateSetFlipEquiv S).toAffineEquiv := by
  constructor
  · intro x y
    unfold sqDist
    apply Finset.sum_congr rfl
    intro i hi
    change (coordinateSetFlip S x i-coordinateSetFlip S y i)^2=_
    simp only [coordinateSetFlip]; split_ifs <;> ring
  · intro x
    constructor
    · intro h
      change coordinateSetFlip S x ∈ dPlusSet 8 at h
      simpa only [coordinateSetFlip_involutive S x] using coordinateSetFlip_mem S hS h
    · exact coordinateSetFlip_mem S hS

lemma e8_integral_inner {x a : Fin 8 → ℝ} (hx : x ∈ dPlusSet 8) (ha : a ∈ dPlusSet 8) :
    ∃ k : ℤ, coordinateInner x a=(k:ℝ) := by
  obtain ⟨t,rfl⟩ := (e8_mem_iff_integer_root_coordinates x).mp hx
  obtain ⟨u,rfl⟩ := (e8_mem_iff_integer_root_coordinates a).mp ha
  refine ⟨e8IntegralQ (t+u)-e8IntegralQ t-e8IntegralQ u,?_⟩
  simp [coordinateInner,e8RootSum,e8SimpleRoot,e8IntegralQ,Fin.sum_univ_succ]
  ring

def e8RootReflection (a x : Fin 8 → ℝ) : Fin 8 → ℝ := x-coordinateInner x a • a

lemma e8RootReflection_involutive (a : Fin 8 → ℝ) (ha : coordinateInner a a=2) :
    Function.Involutive (e8RootReflection a) := by
  intro x
  have h : coordinateInner (e8RootReflection a x) a = -coordinateInner x a := by
    rw [e8RootReflection,coordinateInner_sub_left,coordinateInner_smul_left,ha]
    ring
  unfold e8RootReflection at *
  rw [h]
  module

def e8RootReflectionEquiv (a : Fin 8 → ℝ) (ha : coordinateInner a a=2) :
    (Fin 8 → ℝ) ≃ₗ[ℝ] (Fin 8 → ℝ) where
  toFun := e8RootReflection a
  invFun := e8RootReflection a
  left_inv := e8RootReflection_involutive a ha
  right_inv := e8RootReflection_involutive a ha
  map_add' x y := by
    have h : coordinateInner (x+y) a=coordinateInner x a+coordinateInner y a := by
      simp [coordinateInner,add_mul,Finset.sum_add_distrib]
    simp only [e8RootReflection,h,add_smul]; abel
  map_smul' c x := by
    simp only [e8RootReflection,coordinateInner_smul_left,RingHom.id_apply]; module

lemma e8RootReflection_sqDist (a : Fin 8 → ℝ) (ha : coordinateInner a a=2) (x y : Fin 8 → ℝ) :
    sqDist (e8RootReflection a x) (e8RootReflection a y)=sqDist x y := by
  let c := coordinateInner x a-coordinateInner y a
  have hc : coordinateInner (x-y) a=c := coordinateInner_sub_left _ _ _
  have hexpand (i : Fin 8) : (e8RootReflection a x i-e8RootReflection a y i)^2 =
      (x i-y i)^2 - 2*c*((x i-y i)*a i)+c^2*(a i*a i) := by
    simp only [e8RootReflection,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    dsimp [c]; ring
  unfold sqDist
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum]
  change _-2*c*coordinateInner (x-y) a+c^2*coordinateInner a a=_
  rw [hc,ha]; ring

lemma e8RootReflection_mem (a : Fin 8 → ℝ) (ha : a ∈ dPlusSet 8)
    {x : Fin 8 → ℝ} (hx : x ∈ dPlusSet 8) : e8RootReflection a x ∈ dPlusSet 8 := by
  obtain ⟨k,hk⟩ := e8_integral_inner hx ha
  rw [e8RootReflection,hk,Int.cast_smul_eq_zsmul ℝ]
  exact (dPlusAddSubgroup 8 (by decide)).sub_mem hx
    ((dPlusAddSubgroup 8 (by decide)).zsmul_mem ha k)

lemma e8Symmetry_reflection (a : Fin 8 → ℝ) (ha : a ∈ dPlusSet 8)
    (hn : coordinateInner a a=2) :
    CoordinateLatticeSymmetry (dPlusSet 8) (e8RootReflectionEquiv a hn).toAffineEquiv := by
  refine ⟨e8RootReflection_sqDist a hn,?_⟩
  intro x; constructor
  · intro h
    change e8RootReflection a x ∈ dPlusSet 8 at h
    simpa only [e8RootReflection_involutive a hn x] using e8RootReflection_mem a ha h
  · exact e8RootReflection_mem a ha

end PaperVerification.ColdSpots

namespace PaperVerification.ColdSpots
open scoped BigOperators

/-- The affine Weyl group in the explicit simply-laced E8 realization:
root-lattice translations and reflections in roots of squared norm two,
closed under composition and inverse. -/
inductive E8AffineWeyl : ((Fin 8 → ℝ) ≃ᵃ[ℝ] (Fin 8 → ℝ)) → Prop
  | identity : E8AffineWeyl (AffineEquiv.refl ℝ (Fin 8 → ℝ))
  | translation (t : Fin 8 → ℝ) (ht : t ∈ dPlusSet 8) :
      E8AffineWeyl (AffineEquiv.constVAdd ℝ (Fin 8 → ℝ) t)
  | reflection (a : Fin 8 → ℝ) (ha : a ∈ dPlusSet 8) (hn : coordinateInner a a=2) :
      E8AffineWeyl (e8RootReflectionEquiv a hn).toAffineEquiv
  | composition {f g} : E8AffineWeyl f → E8AffineWeyl g → E8AffineWeyl (f.trans g)
  | inverse {f} : E8AffineWeyl f → E8AffineWeyl f.symm

lemma E8AffineWeyl.is_symmetry {f} (hf : E8AffineWeyl f) :
    CoordinateLatticeSymmetry (dPlusSet 8) f := by
  induction hf with
  | identity => exact ⟨fun _ _ => rfl,fun _ => Iff.rfl⟩
  | translation t ht => exact dnSymmetry_translation (by decide) ht
  | reflection a ha hn => exact e8Symmetry_reflection a ha hn
  | composition hf hg ihf ihg => exact coordinateSymmetry_trans ihf ihg
  | inverse hf ih => exact coordinateSymmetry_symm ih

def e8PairRoot (a b : Fin 8) (s : ℝ) : Fin 8 → ℝ :=
  fun i => (if i=a then 1 else 0)+s*(if i=b then 1 else 0)

lemma e8PairRoot_inner (a b : Fin 8) (s : ℝ) (x : Fin 8 → ℝ) :
    coordinateInner x (e8PairRoot a b s)=x a+s*x b := by
  simp [coordinateInner,e8PairRoot,mul_add,Finset.sum_add_distrib,mul_comm,mul_left_comm]

lemma e8PairRoot_norm (a b : Fin 8) (hab : a≠b) (s : ℝ) (hs : s^2=1) :
    coordinateInner (e8PairRoot a b s) (e8PairRoot a b s)=2 := by
  rw [e8PairRoot_inner]
  simp [e8PairRoot,hab,Ne.symm hab]
  nlinarith

lemma e8PairRoot_mem (a b : Fin 8) (s : ℤ) (hs : Even (1+s)) :
    e8PairRoot a b (s:ℝ) ∈ dPlusSet 8 := by
  let z : Fin 8 → ℤ := fun i => (if i=a then 1 else 0)+s*(if i=b then 1 else 0)
  refine ⟨z,?_,Or.inl ?_⟩
  · simpa [z,Finset.sum_add_distrib,← Finset.mul_sum] using hs
  · funext i; simp [e8PairRoot,intVec,z]

lemma e8Weyl_swap (a b : Fin 8) (hab : a≠b) :
    E8AffineWeyl (coordinatePerm (Equiv.swap a b)).toAffineEquiv := by
  have hn := e8PairRoot_norm a b hab (-1) (by norm_num)
  have hm : e8PairRoot a b (-1) ∈ dPlusSet 8 := by
    exact_mod_cast e8PairRoot_mem a b (-1) (by decide)
  have he : (e8RootReflectionEquiv (e8PairRoot a b (-1)) hn).toAffineEquiv =
      (coordinatePerm (Equiv.swap a b)).toAffineEquiv := by
    ext x i
    change e8RootReflection (e8PairRoot a b (-1)) x i=x (Equiv.swap a b i)
    simp only [e8RootReflection,e8PairRoot_inner,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    by_cases ha : i=a <;> by_cases hb : i=b <;>
      simp_all [e8PairRoot,Equiv.swap_apply_def] <;> ring
  rw [← he]
  exact E8AffineWeyl.reflection _ hm hn

lemma e8Weyl_permutation (p : Equiv.Perm (Fin 8)) :
    E8AffineWeyl (coordinatePerm p).toAffineEquiv := by
  induction p using Equiv.Perm.swap_induction_on with
  | one => exact E8AffineWeyl.identity
  | swap_mul p a b hab ih =>
    have he : (coordinatePerm (Equiv.swap a b*p)).toAffineEquiv =
        ((coordinatePerm (Equiv.swap a b)).toAffineEquiv).trans (coordinatePerm p).toAffineEquiv := by
      ext x i; rfl
    rw [he]
    exact E8AffineWeyl.composition (e8Weyl_swap a b hab) ih

lemma e8Weyl_pairFlip (a b : Fin 8) (hab : a≠b) :
    E8AffineWeyl (coordinatePairFlipEquiv a b).toAffineEquiv := by
  have hn := e8PairRoot_norm a b hab 1 (by norm_num)
  have hm : e8PairRoot a b 1 ∈ dPlusSet 8 := by
    exact_mod_cast e8PairRoot_mem a b 1 (by decide)
  have he : (coordinatePairFlipEquiv a b).toAffineEquiv =
      ((e8RootReflectionEquiv (e8PairRoot a b 1) hn).toAffineEquiv).trans
        (coordinatePerm (Equiv.swap a b)).toAffineEquiv := by
    ext x i
    change coordinatePairFlip a b x i =
      e8RootReflection (e8PairRoot a b 1) x (Equiv.swap a b i)
    simp only [e8RootReflection,e8PairRoot_inner,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    by_cases ha : i=a <;> by_cases hb : i=b <;>
      simp_all [e8PairRoot,Equiv.swap_apply_def,coordinatePairFlip,Ne.symm hab] <;> ring
  rw [he]
  exact E8AffineWeyl.composition (E8AffineWeyl.reflection _ hm hn) (e8Weyl_swap a b hab)

end PaperVerification.ColdSpots

namespace PaperVerification.ColdSpots
open scoped BigOperators
lemma e8_half_set_integer_weyl (S : Finset (Fin 8))
    (hs : S.Nonempty) (hc : Sᶜ.Nonempty) (m : Fin 8 → ℤ) :
    ∃ f : (Fin 8 → ℝ) ≃ᵃ[ℝ] (Fin 8 → ℝ),
      E8AffineWeyl f ∧
      f (dnHalfSet S)=dnHalfSet S+intVec m := by
  classical
  by_cases hm : Even (∑ i,m i)
  · refine ⟨AffineEquiv.constVAdd ℝ _ (intVec m),
      E8AffineWeyl.translation _ ⟨m,hm,Or.inl rfl⟩,?_⟩
    exact add_comm _ _
  · obtain ⟨a,ha⟩ := hs
    obtain ⟨b,hb⟩ := hc
    have hb' : b∉S := Finset.mem_compl.mp hb
    have hab : a≠b := by intro h; exact hb' (h ▸ ha)
    let u : Fin 8 → ℤ := fun i => if i=a then 1 else 0
    have hu : (∑ i,u i)=1 := by simp [u]
    have hm' : Even (∑ i,(m+u) i) := by
      simpa only [Pi.add_apply,Finset.sum_add_distrib,hu] using
        (Int.not_even_iff_odd.mp hm).add_odd (by decide : Odd (1:ℤ))
    let f := (coordinatePairFlipEquiv a b).toAffineEquiv
    let t := intVec (m+u)
    refine ⟨f.trans (AffineEquiv.constVAdd ℝ _ t),
      E8AffineWeyl.composition (e8Weyl_pairFlip a b hab)
        (E8AffineWeyl.translation _ ⟨m+u,hm',Or.inl rfl⟩),?_⟩
    change t+coordinatePairFlip a b (dnHalfSet S)=dnHalfSet S+intVec m
    funext i
    by_cases hia : i=a <;> by_cases hib : i=b <;>
      simp_all [t,u,intVec,coordinatePairFlip,dnHalfSet] <;> ring

/-- All balanced half-grid points lie in one orbit under coordinate
permutations, even sign changes, and lattice translations. -/
theorem e8_half_grid_single_weyl_orbit
    (x y : Fin 8 → ℝ) (hx : PaperHalfGrid x) (hy : PaperHalfGrid y) :
    ∃ f : (Fin 8 → ℝ) ≃ᵃ[ℝ] (Fin 8 → ℝ),
      E8AffineWeyl f ∧ f x=y := by
  obtain ⟨m,S,rfl⟩ := dnHalfGrid_normalForm hx.1
  obtain ⟨k,T,rfl⟩ := dnHalfGrid_normalForm hy.1
  have hs : S.card=4 := by simpa only [nonintegerCount_halfSet_int] using hx.2
  have ht : T.card=4 := by simpa only [nonintegerCount_halfSet_int] using hy.2
  have hSn : S.Nonempty := Finset.card_pos.mp (by omega)
  have hTn : T.Nonempty := Finset.card_pos.mp (by omega)
  have hSc : Sᶜ.Nonempty := Finset.card_pos.mp (by simp only [Finset.card_compl,Fintype.card_fin,hs]; omega)
  have hTc : Tᶜ.Nonempty := Finset.card_pos.mp (by simp only [Finset.card_compl,Fintype.card_fin,ht]; omega)
  obtain ⟨f,hf,hfx⟩ := e8_half_set_integer_weyl S hSn hSc m
  obtain ⟨g,hg,hgy⟩ := e8_half_set_integer_weyl T hTn hTc k
  obtain ⟨p,hp⟩ := dn_half_set_permutation S T (hs.trans ht.symm)
  refine ⟨(f.symm.trans (coordinatePerm p).toAffineEquiv).trans g,
    E8AffineWeyl.composition (E8AffineWeyl.composition (E8AffineWeyl.inverse hf)
      (e8Weyl_permutation p)) hg,?_⟩
  change g (coordinatePerm p (f.symm (dnHalfSet S+intVec m)))=dnHalfSet T+intVec k
  rw [← hfx,f.symm_apply_apply,hp,hgy]


end PaperVerification.ColdSpots

namespace PaperVerification.ColdSpots

lemma e8Weyl_setFlip (S : Finset (Fin 8)) (hS : Even S.card) :
    E8AffineWeyl (coordinateSetFlipEquiv S).toAffineEquiv := by
  classical
  induction S using Finset.strongInductionOn
  rename_i S ih
  by_cases he : S=∅
  · subst S
    have hf : (coordinateSetFlipEquiv ∅).toAffineEquiv = AffineEquiv.refl ℝ _ := by
      ext x i
      change coordinateSetFlip ∅ x i=x i
      simp [coordinateSetFlip]
    rw [hf]; exact E8AffineWeyl.identity
  · obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hSa : (S.erase a).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem ha]
      obtain ⟨k,hk⟩ := hS
      have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      omega
    obtain ⟨b,hb⟩ := hSa
    have hab : a≠b := Ne.symm (Finset.mem_erase.mp hb).1
    let T := (S.erase a).erase b
    have ht : T ⊂ S := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨(Finset.erase_subset _ _).trans (Finset.erase_subset _ _),?_⟩
      intro h
      have : a∈T := h.symm ▸ ha
      simp [T] at this
    have hcard : T.card+2=S.card := by
      simp only [T,Finset.card_erase_of_mem hb,Finset.card_erase_of_mem ha]
      have := Finset.card_pos.mpr (show (S.erase a).Nonempty from ⟨b,hb⟩)
      rw [Finset.card_erase_of_mem ha] at this
      omega
    have htEven : Even T.card := by
      have h := hcard ▸ hS
      exact (Nat.even_add.mp h).mpr (by decide)
    have hf := ih T ht htEven
    have heq : (coordinateSetFlipEquiv S).toAffineEquiv =
        ((coordinatePairFlipEquiv a b).toAffineEquiv).trans (coordinateSetFlipEquiv T).toAffineEquiv := by
      ext x i
      change coordinateSetFlip S x i = coordinateSetFlip T (coordinatePairFlip a b x) i
      by_cases hi : i=a <;> by_cases hj : i=b <;>
        simp_all [coordinateSetFlip,coordinatePairFlip,T,Finset.mem_erase]
    rw [heq]
    exact E8AffineWeyl.composition (e8Weyl_pairFlip a b hab) hf

end PaperVerification.ColdSpots

namespace PaperVerification.ColdSpots
open scoped BigOperators

def e8QuarterBase : Fin 8 → ℝ := fun i => -(if i=0 then 1 else 0)+1/4

def e8OrbitHalfRoot : Fin 8 → ℝ := fun _ => 1/2

def e8OrbitBalancedRoot : Fin 8 → ℝ := ![1/2,1/2,1/2,1/2,-1/2,-1/2,-1/2,-1/2]

lemma e8OrbitHalfRoot_mem : e8OrbitHalfRoot ∈ dPlusSet 8 := by
  refine ⟨0,by simp,Or.inr ?_⟩
  ext i; simp [e8OrbitHalfRoot]
lemma e8OrbitHalfRoot_norm : coordinateInner e8OrbitHalfRoot e8OrbitHalfRoot=2 := by
  norm_num [coordinateInner,e8OrbitHalfRoot]
lemma e8OrbitBalancedRoot_mem : e8OrbitBalancedRoot ∈ dPlusSet 8 := by
  refine ⟨![0,0,0,0,-1,-1,-1,-1],by norm_num [Fin.sum_univ_succ]; decide,Or.inr ?_⟩
  ext i; fin_cases i <;> norm_num [e8OrbitBalancedRoot]
lemma e8OrbitBalancedRoot_norm : coordinateInner e8OrbitBalancedRoot e8OrbitBalancedRoot=2 := by
  norm_num [coordinateInner,e8OrbitBalancedRoot,Fin.sum_univ_succ]

lemma e8_quarter_base_weyl : ∃ f : (Fin 8 → ℝ) ≃ᵃ[ℝ] (Fin 8 → ℝ),
    E8AffineWeyl f ∧ f e8FirstVector=e8QuarterBase := by
  let r := (e8RootReflectionEquiv e8OrbitHalfRoot e8OrbitHalfRoot_norm).toAffineEquiv
  let g := (coordinateSetFlipEquiv Finset.univ).toAffineEquiv
  refine ⟨r.trans g,E8AffineWeyl.composition
    (E8AffineWeyl.reflection _ e8OrbitHalfRoot_mem e8OrbitHalfRoot_norm)
    (e8Weyl_setFlip Finset.univ (by decide)),?_⟩
  ext i
  change coordinateSetFlip Finset.univ (e8RootReflection e8OrbitHalfRoot e8FirstVector) i=e8QuarterBase i
  simp [coordinateSetFlip,e8RootReflection,coordinateInner,e8OrbitHalfRoot,e8FirstVector,e8QuarterBase]
  split_ifs <;> norm_num

lemma e8_quarter_family_weyl (x : Fin 8 → ℝ) (hx : E8QuarterFamily x) :
    ∃ f : (Fin 8 → ℝ) ≃ᵃ[ℝ] (Fin 8 → ℝ), E8AffineWeyl f ∧ f e8QuarterBase=x := by
  obtain ⟨m,ε,hm,hε,he,hx⟩ := hx
  let S := Finset.univ.filter (fun i => ε i = -1)
  have hS : Even S.card := he
  let v : Fin 8 → ℤ := fun i => if i=0 then -1 else 0
  let w := coordinateSetFlip S v
  have hw : Odd (∑ i,w i) := by
    rw [show w=coordinateSetFlip S v from rfl,coordinateSetFlip_sum]
    have hv : (∑ i,v i)=-1 := by simp [v]
    rw [hv]
    exact (by decide : Odd (-1:ℤ)).sub_even (even_two.mul_right _)
  have ht : intVec (m-w) ∈ dPlusSet 8 := by
    refine ⟨m-w,?_,Or.inl rfl⟩
    simpa only [Pi.sub_apply,Finset.sum_sub_distrib] using hm.sub_odd hw
  refine ⟨((coordinateSetFlipEquiv S).toAffineEquiv).trans
      (AffineEquiv.constVAdd ℝ _ (intVec (m-w))),
    E8AffineWeyl.composition (e8Weyl_setFlip S hS) (E8AffineWeyl.translation _ ht),?_⟩
  ext i
  change intVec (m-w) i + coordinateSetFlip S e8QuarterBase i = x i
  rw [hx i]
  rcases hε i with hi | hi
  all_goals
    by_cases h0 : i=0 <;>
      simp_all [intVec,w,v,coordinateSetFlip,S,e8QuarterBase] <;> ring

lemma e8_half_grid_bridge :
    PaperHalfGrid (e8RootReflection e8OrbitBalancedRoot (e8RootReflection e8OrbitHalfRoot e8FirstVector)) := by
  let S : Finset (Fin 8) := {0,1,2,3}
  let m : Fin 8 → ℤ := ![0,-1,-1,-1,0,0,0,0]
  have h : e8RootReflection e8OrbitBalancedRoot (e8RootReflection e8OrbitHalfRoot e8FirstVector) =
      dnHalfSet S+intVec m := by
    ext i; fin_cases i <;>
      norm_num [e8RootReflection,e8OrbitBalancedRoot,e8OrbitHalfRoot,e8FirstVector,
        coordinateInner,Fin.sum_univ_succ,dnHalfSet,intVec,S,m]
  rw [h]
  constructor
  · intro i
    refine ⟨2*m i+(if i∈S then 1 else 0),?_⟩
    simp only [Pi.add_apply,dnHalfSet,intVec]
    split_ifs <;> push_cast <;> ring
  · rw [nonintegerCount_halfSet_int]
    decide

lemma e8_half_family_weyl (x : Fin 8 → ℝ) (hx : PaperHalfGrid x) :
    ∃ f : (Fin 8 → ℝ) ≃ᵃ[ℝ] (Fin 8 → ℝ), E8AffineWeyl f ∧ f e8FirstVector=x := by
  let r := (e8RootReflectionEquiv e8OrbitHalfRoot e8OrbitHalfRoot_norm).toAffineEquiv
  let s := (e8RootReflectionEquiv e8OrbitBalancedRoot e8OrbitBalancedRoot_norm).toAffineEquiv
  obtain ⟨f,hf,hfx⟩ := e8_half_grid_single_weyl_orbit _ x e8_half_grid_bridge hx
  refine ⟨(r.trans s).trans f,E8AffineWeyl.composition
    (E8AffineWeyl.composition
      (E8AffineWeyl.reflection _ e8OrbitHalfRoot_mem e8OrbitHalfRoot_norm)
      (E8AffineWeyl.reflection _ e8OrbitBalancedRoot_mem e8OrbitBalancedRoot_norm)) hf,?_⟩
  exact hfx

/-- All three complete E8 hole families lie in the affine Weyl orbit of e1. -/
theorem e8_deep_hole_weyl_orbit (x : Fin 8 → ℝ) (hx : IsDeepHole (dPlusSet 8) x) :
    ∃ f : (Fin 8 → ℝ) ≃ᵃ[ℝ] (Fin 8 → ℝ), E8AffineWeyl f ∧ f e8FirstVector=x := by
  rcases (isDeepHole_E8_iff_paper x).mp hx with hfirst | hhalf | hquarter
  · obtain ⟨t,ht,rfl⟩ := hfirst
    exact ⟨AffineEquiv.constVAdd ℝ _ t,E8AffineWeyl.translation t ht,add_comm _ _⟩
  · exact e8_half_family_weyl x hhalf
  · obtain ⟨f,hf,hfx⟩ := e8_quarter_base_weyl
    obtain ⟨g,hg,hgx⟩ := e8_quarter_family_weyl x hquarter
    refine ⟨f.trans g,E8AffineWeyl.composition hf hg,?_⟩
    change g (f e8FirstVector)=x
    rw [hfx,hgx]

/-- The full set of actual E8 deep holes is one affine Weyl orbit.
The witness is additionally proved to preserve the lattice and Euclidean metric. -/
theorem e8_deep_holes_single_affine_weyl_orbit (x y : Fin 8 → ℝ)
    (hx : IsDeepHole (dPlusSet 8) x) (hy : IsDeepHole (dPlusSet 8) y) :
    ∃ f : (Fin 8 → ℝ) ≃ᵃ[ℝ] (Fin 8 → ℝ),
      E8AffineWeyl f ∧ CoordinateLatticeSymmetry (dPlusSet 8) f ∧ f x=y := by
  obtain ⟨f,hf,hfx⟩ := e8_deep_hole_weyl_orbit x hx
  obtain ⟨g,hg,hgy⟩ := e8_deep_hole_weyl_orbit y hy
  have hw := E8AffineWeyl.composition (E8AffineWeyl.inverse hf) hg
  refine ⟨f.symm.trans g,hw,hw.is_symmetry,?_⟩
  change g (f.symm x)=y
  rw [← hfx,f.symm_apply_apply,hgy]

#print axioms e8_deep_holes_single_affine_weyl_orbit
end PaperVerification.ColdSpots

namespace PaperVerification.ColdSpots

/-- Every generated affine Weyl element preserves literal Euclidean distance. -/
theorem E8AffineWeyl.euclidean_distance {f : (Fin 8 → ℝ) ≃ᵃ[ℝ] (Fin 8 → ℝ)}
    (hf : E8AffineWeyl f) (x y : Fin 8 → ℝ) :
    dist (WithLp.toLp 2 (f x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (f y)) =
      dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 y) :=
  hf.is_symmetry.euclidean_distance x y

end PaperVerification.ColdSpots
