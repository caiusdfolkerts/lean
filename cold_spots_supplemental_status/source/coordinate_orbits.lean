module
public import paper_verification.lattice007
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

@[expose] public section
noncomputable section
namespace PaperVerification.ColdSpots
open scoped BigOperators
variable {n : ℕ}

def CoordinateLatticeSymmetry (L : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ)) : Prop :=
  (∀ x y, sqDist (f x) (f y) = sqDist x y) ∧ (∀ x, f x ∈ L ↔ x ∈ L)

lemma coordinateSymmetry_trans {L : Set (Fin n → ℝ)}
    {f g : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ)}
    (hf : CoordinateLatticeSymmetry L f) (hg : CoordinateLatticeSymmetry L g) :
    CoordinateLatticeSymmetry L (f.trans g) :=
  ⟨fun x y => (hg.1 _ _).trans (hf.1 x y),fun x => (hg.2 _).trans (hf.2 x)⟩

lemma coordinateSymmetry_symm {L : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ)} (hf : CoordinateLatticeSymmetry L f) :
    CoordinateLatticeSymmetry L f.symm := by
  constructor
  · intro x y; simpa using (hf.1 (f.symm x) (f.symm y)).symm
  · intro x; simpa using (hf.2 (f.symm x)).symm

lemma dnSymmetry_translation (he : Even n) {t : Fin n → ℝ} (ht : t ∈ dPlusSet n) :
    CoordinateLatticeSymmetry (dPlusSet n) (AffineEquiv.constVAdd ℝ (Fin n → ℝ) t) := by
  constructor
  · intro x y
    change sqDist (t+x) (t+y) = _
    simpa only [add_comm t] using sqDist_add_add x y t
  · intro x
    change t+x ∈ dPlusAddSubgroup n he ↔ x ∈ dPlusAddSubgroup n he
    exact (dPlusAddSubgroup n he).add_mem_cancel_left ht

def coordinatePerm (p : Equiv.Perm (Fin n)) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun x := x ∘ p
  invFun x := x ∘ p.symm
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' x y := rfl
  map_smul' c x := rfl

lemma coordinatePerm_mem (p : Equiv.Perm (Fin n)) {x : Fin n → ℝ}
    (hx : x ∈ dPlusSet n) : coordinatePerm p x ∈ dPlusSet n := by
  obtain ⟨z,hz,hx⟩ := hx
  refine ⟨z ∘ p,?_,?_⟩
  · simpa only [Function.comp_apply, Equiv.sum_comp p] using hz
  · rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

lemma dnSymmetry_permutation (p : Equiv.Perm (Fin n)) :
    CoordinateLatticeSymmetry (dPlusSet n) (coordinatePerm p).toAffineEquiv := by
  constructor
  · intro x y
    change (∑ i,(x (p i)-y (p i))^2)=_
    exact Equiv.sum_comp p (fun i => (x i-y i)^2)
  · intro x
    constructor
    · intro h
      have h' := coordinatePerm_mem p.symm h
      simpa [coordinatePerm,Function.comp_def] using h'
    · exact coordinatePerm_mem p

def coordinatePairFlip {R : Type*} [Neg R] (a b : Fin n) (x : Fin n → R) : Fin n → R :=
  fun i => if i=a ∨ i=b then -x i else x i

lemma coordinatePairFlip_sum {R : Type*} [CommRing R] (a b : Fin n) (hab : a≠b)
    (x : Fin n → R) : (∑ i,coordinatePairFlip a b x i) = (∑ i,x i)-2*x a-2*x b := by
  classical
  have h : coordinatePairFlip a b x =
      fun i => x i-(if i=a then 2*x a else 0)-(if i=b then 2*x b else 0) := by
    funext i
    by_cases ha : i=a <;> by_cases hb : i=b <;> simp_all [coordinatePairFlip] <;> ring
  rw [h]
  simp [Finset.sum_sub_distrib]

lemma coordinatePairFlip_involutive {R : Type*} [InvolutiveNeg R] (a b : Fin n) :
    Function.Involutive (coordinatePairFlip (R:=R) a b) := by
  intro x; funext i
  simp only [coordinatePairFlip]
  split_ifs <;> simp

def coordinatePairFlipEquiv (a b : Fin n) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun := coordinatePairFlip a b
  invFun := coordinatePairFlip a b
  left_inv := coordinatePairFlip_involutive a b
  right_inv := coordinatePairFlip_involutive a b
  map_add' x y := by ext i; simp only [coordinatePairFlip,Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [coordinatePairFlip,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    split_ifs <;> ring

lemma coordinatePairFlip_mem (a b : Fin n) (hab : a≠b) {x : Fin n → ℝ}
    (hx : x ∈ dPlusSet n) : coordinatePairFlip a b x ∈ dPlusSet n := by
  classical
  obtain ⟨z,hz,hx⟩ := hx
  rcases hx with rfl | rfl
  · refine ⟨coordinatePairFlip a b z,?_,Or.inl ?_⟩
    · rw [coordinatePairFlip_sum a b hab]
      exact (hz.sub (even_two.mul_right _)).sub (even_two.mul_right _)
    · funext i; simp only [coordinatePairFlip,intVec]; split_ifs <;> simp
  · let w : Fin n → ℤ := fun i => coordinatePairFlip a b z i-
        (if i=a then 1 else 0)-(if i=b then 1 else 0)
    refine ⟨w,?_,Or.inr ?_⟩
    · have hw : (∑ i,w i)=(∑ i,z i)-2*z a-2*z b-2 := by
        simp [w,Finset.sum_sub_distrib,coordinatePairFlip_sum a b hab]
        ring
      rw [hw]
      exact ((hz.sub (even_two.mul_right _)).sub (even_two.mul_right _)).sub even_two
    · funext i
      by_cases ha : i=a <;> by_cases hb : i=b <;>
        simp_all [coordinatePairFlip,w] <;> ring

lemma dnSymmetry_pairFlip (a b : Fin n) (hab : a≠b) :
    CoordinateLatticeSymmetry (dPlusSet n) (coordinatePairFlipEquiv a b).toAffineEquiv := by
  constructor
  · intro x y
    unfold sqDist
    apply Finset.sum_congr rfl
    intro i hi
    change (coordinatePairFlip a b x i-coordinatePairFlip a b y i)^2=_
    simp only [coordinatePairFlip]
    split_ifs <;> ring
  · intro x
    constructor
    · intro h
      change coordinatePairFlip a b x ∈ dPlusSet n at h
      simpa only [coordinatePairFlip_involutive a b x] using coordinatePairFlip_mem a b hab h
    · exact coordinatePairFlip_mem a b hab

end PaperVerification.ColdSpots

namespace PaperVerification.ColdSpots
open scoped BigOperators
variable {n : ℕ}

lemma dn_half_set_permutation (S T : Finset (Fin n)) (hcard : S.card=T.card) :
    ∃ p : Equiv.Perm (Fin n), coordinatePerm p (dnHalfSet S)=dnHalfSet T := by
  classical
  let e := T.equivOfCardEq hcard.symm
  let p := e.extendSubtype
  have hp (i : Fin n) : p i ∈ S ↔ i ∈ T := by
    constructor
    · intro hi
      by_contra hn
      exact e.extendSubtype_not_mem i hn hi
    · exact e.extendSubtype_mem i
  refine ⟨p,?_⟩
  funext i
  change (if p i∈S then (1/2 : ℝ) else 0)=(if i∈T then 1/2 else 0)
  simp only [hp]

lemma dn_half_set_integer_orbit (he : Even n) (S : Finset (Fin n))
    (hs : S.Nonempty) (hc : Sᶜ.Nonempty) (m : Fin n → ℤ) :
    ∃ f : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ),
      CoordinateLatticeSymmetry (dPlusSet n) f ∧
      f (dnHalfSet S)=dnHalfSet S+intVec m := by
  classical
  by_cases hm : Even (∑ i,m i)
  · refine ⟨AffineEquiv.constVAdd ℝ _ (intVec m),
      dnSymmetry_translation he ⟨m,hm,Or.inl rfl⟩,?_⟩
    exact add_comm _ _
  · obtain ⟨a,ha⟩ := hs
    obtain ⟨b,hb⟩ := hc
    have hb' : b∉S := Finset.mem_compl.mp hb
    have hab : a≠b := by intro h; exact hb' (h ▸ ha)
    let u : Fin n → ℤ := fun i => if i=a then 1 else 0
    have hu : (∑ i,u i)=1 := by simp [u]
    have hm' : Even (∑ i,(m+u) i) := by
      simpa only [Pi.add_apply,Finset.sum_add_distrib,hu] using
        (Int.not_even_iff_odd.mp hm).add_odd (by decide : Odd (1:ℤ))
    let f := (coordinatePairFlipEquiv a b).toAffineEquiv
    let t := intVec (m+u)
    refine ⟨f.trans (AffineEquiv.constVAdd ℝ _ t),
      coordinateSymmetry_trans (dnSymmetry_pairFlip a b hab)
        (dnSymmetry_translation he ⟨m+u,hm',Or.inl rfl⟩),?_⟩
    change t+coordinatePairFlip a b (dnHalfSet S)=dnHalfSet S+intVec m
    funext i
    by_cases hia : i=a <;> by_cases hib : i=b <;>
      simp_all [t,u,intVec,coordinatePairFlip,dnHalfSet] <;> ring

/-- All balanced half-grid points lie in one orbit under coordinate
permutations, even sign changes, and lattice translations. -/
theorem dn_paper_half_grid_single_affine_orbit (hn : 0<n) (he : Even n)
    (x y : Fin n → ℝ) (hx : PaperHalfGrid x) (hy : PaperHalfGrid y) :
    ∃ f : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ),
      CoordinateLatticeSymmetry (dPlusSet n) f ∧ f x=y := by
  obtain ⟨m,S,rfl⟩ := dnHalfGrid_normalForm hx.1
  obtain ⟨k,T,rfl⟩ := dnHalfGrid_normalForm hy.1
  have hs : S.card=n/2 := by simpa only [nonintegerCount_halfSet_int] using hx.2
  have ht : T.card=n/2 := by simpa only [nonintegerCount_halfSet_int] using hy.2
  have hdim := even_half_identity he
  have hpos : 0<n/2 := by omega
  have hlt : n/2<n := by omega
  have hSn : S.Nonempty := Finset.card_pos.mp (by omega)
  have hTn : T.Nonempty := Finset.card_pos.mp (by omega)
  have hSc : Sᶜ.Nonempty := Finset.card_pos.mp (by simp only [Finset.card_compl,Fintype.card_fin,hs]; omega)
  have hTc : Tᶜ.Nonempty := Finset.card_pos.mp (by simp only [Finset.card_compl,Fintype.card_fin,ht]; omega)
  obtain ⟨f,hf,hfx⟩ := dn_half_set_integer_orbit he S hSn hSc m
  obtain ⟨g,hg,hgy⟩ := dn_half_set_integer_orbit he T hTn hTc k
  obtain ⟨p,hp⟩ := dn_half_set_permutation S T (hs.trans ht.symm)
  refine ⟨(f.symm.trans (coordinatePerm p).toAffineEquiv).trans g,
    coordinateSymmetry_trans (coordinateSymmetry_trans (coordinateSymmetry_symm hf)
      (dnSymmetry_permutation p)) hg,?_⟩
  change g (coordinatePerm p (f.symm (dnHalfSet S+intVec m)))=dnHalfSet T+intVec k
  rw [← hfx,f.symm_apply_apply,hp,hgy]

/-- Every two actual deep holes of Dn+ in every even dimension n>8 are
related by a lattice-preserving Euclidean affine isometry. -/
theorem dn_deep_holes_single_affine_orbit (hn : 8<n) (he : Even n)
    (x y : Fin n → ℝ) (hx : IsDeepHole (dPlusSet n) x) (hy : IsDeepHole (dPlusSet n) y) :
    ∃ f : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ),
      CoordinateLatticeSymmetry (dPlusSet n) f ∧ f x=y :=
  dn_paper_half_grid_single_affine_orbit (by omega) he x y
    ((isDeepHole_dPlus_iff_paperHalfGrid hn he x).mp hx)
    ((isDeepHole_dPlus_iff_paperHalfGrid hn he y).mp hy)

#print axioms dn_deep_holes_single_affine_orbit
end PaperVerification.ColdSpots

namespace PaperVerification.ColdSpots

/-- The sum-of-squares preservation condition is literal Euclidean distance
preservation after the standard Euclidean coordinate identification. -/
theorem CoordinateLatticeSymmetry.euclidean_distance {n : ℕ} {L : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ)} (hf : CoordinateLatticeSymmetry L f)
    (x y : Fin n → ℝ) :
    dist (WithLp.toLp 2 (f x) : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 (f y)) =
      dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 y) := by
  have h := hf.1 x y
  rw [sqDist_eq_euclidean_dist_sq,sqDist_eq_euclidean_dist_sq] at h
  have h₁ : 0 ≤ dist (WithLp.toLp 2 (f x) : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 (f y)) := dist_nonneg
  have h₂ : 0 ≤ dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 y) := dist_nonneg
  nlinarith

end PaperVerification.ColdSpots
