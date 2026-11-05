module

public import PaperVerification.AlternatingFormsCanonicalUnipotent

/-!
# The diagonal torus of the regular Borel action

In chain coordinates the integer weights are `2k-2i`. This gives precisely
`H aᵢ=(2i-2k-2)aᵢ` and `H bⱼ=(2k-2j)bⱼ`. The pullback weights of the two
forms are `-2` and `0`, and the torus rescales the nilpotent generator by the
square character. All identities are for actual linear maps and forms.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms.CanonicalUnipotent

open RegularNilpotentFlag

variable {K : Type*} [Field K] [CharZero K]

/-- Integer torus weights along the chain. -/
def chainWeight (k : ℕ) (i : Fin (2*k+1)) : ℤ := 2*(k : ℤ)-2*(i.val : ℤ)

/-- The diagonal torus acts through actual integer powers of a nonzero scalar. -/
def torusMap (k : ℕ) (t : Kˣ) : Module.End K (ChainSpace K k) where
  toFun v i := ((t^chainWeight k i : Kˣ) : K)*v i
  map_add' _ _ := by ext i; simp [mul_add]
  map_smul' _ _ := by ext i; simp [mul_left_comm]

@[simp] theorem torusMap_apply (k : ℕ) (t : Kˣ) (v : ChainSpace K k) (i) :
    torusMap k t v i=((t^chainWeight k i : Kˣ) : K)*v i := rfl

@[simp] theorem torusMap_one (k : ℕ) : torusMap (K := K) k 1=1 := by
  ext v i
  simp [torusMap]

theorem torusMap_mul (k : ℕ) (t u : Kˣ) :
    torusMap k (t*u)=torusMap k t*torusMap k u := by
  ext v i
  simp [torusMap,mul_zpow,mul_assoc]

@[simp] theorem torusMap_single (k : ℕ) (t : Kˣ) (i : Fin (2*k+1)) :
    torusMap k t (Pi.single i 1)=((t^chainWeight k i : Kˣ) : K) • Pi.single i 1 := by
  ext j
  by_cases h : i=j
  · subst j
    simp [torusMap,Pi.single_apply]
  · simp [torusMap,Pi.single_apply,h]

/-- A common anti-diagonal gives a single torus weight. -/
theorem torus_antiDiagonal_coeff (k r : ℕ) (t : Kˣ) (i j : Fin (2*k+1)) :
    ((t^chainWeight k i : Kˣ) : K)*((t^chainWeight k j : Kˣ) : K)*
        skewAntiDiagonal k r i j =
      ((t^(4*(k : ℤ)-2*(r : ℤ)) : Kˣ) : K)*skewAntiDiagonal k r i j := by
  by_cases h : i.val+j.val=r
  · have hcast : (i.val : ℤ)+(j.val : ℤ)=(r : ℤ) := by exact_mod_cast h
    have hw : chainWeight k i+chainWeight k j=4*(k : ℤ)-2*(r : ℤ) := by
      unfold chainWeight
      linear_combination -2*hcast
    rw [← Units.val_mul,← zpow_add,hw]
  · simp [skewAntiDiagonal,h]

/-- Exact pullback as an equality of actual bilinear forms. -/
theorem torus_antiDiagonal_pullback (k r : ℕ) (t : Kˣ) :
    ((skewAntiDiagonal (K := K) k r).toBilin').comp (torusMap k t) (torusMap k t) =
      ((t^(4*(k : ℤ)-2*(r : ℤ)) : Kˣ) : K) • (skewAntiDiagonal k r).toBilin' := by
  apply (Pi.basisFun K (Fin (2*k+1))).ext
  intro i
  apply (Pi.basisFun K (Fin (2*k+1))).ext
  intro j
  simp only [Pi.basisFun_apply,LinearMap.BilinForm.comp_apply,torusMap_single,
    map_smul,LinearMap.smul_apply,smul_eq_mul,Matrix.toBilin'_single]
  rw [← mul_assoc]
  simpa only [mul_comm] using torus_antiDiagonal_coeff k r t i j

/-- The first form has weight `-2`. -/
theorem firstForm_torus_pullback (k : ℕ) (t : Kˣ) :
    (firstForm k).comp (torusMap k t) (torusMap k t)=
      ((t^(-2 : ℤ) : Kˣ) : K) • firstForm k := by
  have h : 4*(k : ℤ)-2*((2*k+1 : ℕ) : ℤ)=(-2 : ℤ) := by push_cast; ring
  simpa only [firstForm,h] using torus_antiDiagonal_pullback k (2*k+1) t

/-- The second form has weight zero. -/
theorem secondForm_torus_pullback (k : ℕ) (t : Kˣ) :
    (secondForm k).comp (torusMap k t) (torusMap k t)=secondForm k := by
  have h : 4*(k : ℤ)-2*((2*k : ℕ) : ℤ)=0 := by push_cast; ring
  simpa only [secondForm,h,zpow_zero,Units.val_one,one_smul] using
    torus_antiDiagonal_pullback k (2*k) t

/-- The square character intertwines the generator and the torus. -/
theorem torusMap_generator (k : ℕ) (t : Kˣ) :
    torusMap k t*generator k=(t.val^2) • (generator k*torusMap k t) := by
  apply LinearMap.ext
  intro v
  funext i
  simp only [Module.End.mul_apply,torusMap_apply,generator,weightedShift_apply,
    LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul]
  split_ifs with h
  · have hw : chainWeight k i=2+chainWeight k ⟨i.val+1,h⟩ := by
      simp only [chainWeight,Nat.cast_add,Nat.cast_one]
      ring
    rw [hw,zpow_add]
    simp only [Units.val_mul,zpow_ofNat,Units.val_pow_eq_pow_val]
    ring
  · simp

/-- The actual unipotent and torus maps satisfy the Borel semidirect-product
relation, so the action has the required square character. -/
theorem torusMap_gaMap (k : ℕ) (t : Kˣ) (u : K) :
    torusMap k t*gaMap k u=gaMap k (t.val^2*u)*torusMap k t := by
  unfold gaMap
  have hcompat : ((t.val^2*u) • generator (K := K) k) ∘ₗ torusMap k t =
      torusMap k t ∘ₗ (u • generator k) := by
    apply LinearMap.ext
    intro v
    have h := congrArg (fun T : Module.End K (ChainSpace K k) => T v)
      (torusMap_generator k t)
    simp only [Module.End.mul_apply,LinearMap.smul_apply] at h
    simp only [LinearMap.comp_apply,LinearMap.smul_apply,map_smul,h,smul_smul]
    rw [mul_comm u]
  exact (Module.End.commute_exp_left_of_commute
    ((generator_nilpotent k).smul u)
    ((generator_nilpotent k).smul (t.val^2*u)) hcompat).symm

end PaperVerification.AlternatingForms.CanonicalUnipotent
