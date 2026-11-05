module

public import PaperVerification.PowerPermutationAction
public import PaperVerification.EquivariantCokernelSpecialization

/-!
# Actual group actions in the finite power-tail degree complex

The actions are obtained by decoding monomial coordinates, renaming the
polynomial variables, and reading the same coordinates. All generator indices
of the Koszul complex remain fixed. Decode identities prove the group laws,
the two equivariance identities, and specialization of the action matrices.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation Matrix
open scoped BigOperators

namespace PaperVerification.PowerOperators

section Ring

variable {R : Type*} [CommRing R] {n : ℕ}

def shiftedEncode (s d : ℕ) :
    MvPolynomial (Fin n) R →ₗ[R] (ShiftedExponent n s d → R) where
  toFun p a := p.coeff a.val
  map_add' p q := by ext a; exact MvPolynomial.coeff_add a.val p q
  map_smul' c p := by ext a; exact MvPolynomial.coeff_smul a.val c p

@[simp] theorem shiftedEncode_decode (s d : ℕ) (v : ShiftedExponent n s d → R) :
    shiftedEncode s d (shiftedDecode s d v) = v := by
  ext a
  exact shiftedDecode_coeff s d v a

theorem shiftedDecode_injective (s d : ℕ) : Function.Injective (shiftedDecode (R := R) (n := n) s d) := by
  intro v w h
  have hc := congrArg (shiftedEncode s d) h
  simpa only [shiftedEncode_decode] using hc

theorem rename_mem_shiftedPiece (e : Equiv.Perm (Fin n)) (s d : ℕ)
    {p : MvPolynomial (Fin n) R} (hp : p ∈ shiftedPiece R n s d) :
    MvPolynomial.rename e p ∈ shiftedPiece R n s d := by
  by_cases hs : s ≤ d
  · rw [shiftedPiece_eq_homogeneous hs] at hp ⊢
    exact rename_mem_homogeneousSubmodule e _ hp
  · rw [shiftedPiece_eq_bot (Nat.lt_of_not_ge hs), Submodule.mem_bot] at hp ⊢
    rw [hp, map_zero]

def shiftedRename (e : Equiv.Perm (Fin n)) (s d : ℕ) :
    Module.End R (ShiftedExponent n s d → R) :=
  (shiftedEncode s d).comp ((MvPolynomial.rename e).toLinearMap.comp (shiftedDecode s d))

theorem shiftedDecode_shiftedRename (e : Equiv.Perm (Fin n)) (s d : ℕ)
    (v : ShiftedExponent n s d → R) :
    shiftedDecode s d (shiftedRename e s d v) = MvPolynomial.rename e (shiftedDecode s d v) :=
  shiftedDecode_coeffs s d _ (rename_mem_shiftedPiece e s d (shiftedDecode_mem s d v))

@[simp] theorem shiftedRename_one (s d : ℕ) :
    shiftedRename (R := R) (n := n) 1 s d = 1 := by
  ext v a
  change (MvPolynomial.rename (id : Fin n → Fin n) (shiftedDecode s d v)).coeff a.val = v a
  rw [MvPolynomial.rename_id_apply, shiftedDecode_coeff]

theorem shiftedRename_mul (e f : Equiv.Perm (Fin n)) (s d : ℕ) :
    shiftedRename (R := R) (e*f) s d = shiftedRename e s d * shiftedRename f s d := by
  ext v a
  change (MvPolynomial.rename (e*f) (shiftedDecode s d v)).coeff a.val =
    (MvPolynomial.rename e (shiftedDecode s d (shiftedRename f s d v))).coeff a.val
  rw [shiftedDecode_shiftedRename, MvPolynomial.rename_rename]
  rfl

def shiftedDegreeAction (G : Subgroup (Equiv.Perm (Fin n))) (s d : ℕ) :
    Representation R G (ShiftedExponent n s d → R) where
  toFun g := shiftedRename (g : Equiv.Perm (Fin n)) s d
  map_one' := shiftedRename_one s d
  map_mul' g h := shiftedRename_mul _ _ s d

/-- A fixed family of representations on the blocks of a dependent finite
coordinate set. Group elements do not act on the block labels. -/
def sigmaCoordinateAction {H ι : Type*} [Group H] {κ : ι → Type*}
    (ρ : ∀ i, Representation R H (κ i → R)) :
    Representation R H ((i : ι) × κ i → R) where
  toFun g :=
    { toFun v a := ρ a.1 g (fun b => v ⟨a.1,b⟩) a.2
      map_add' v w := by
        ext a
        exact congrFun ((ρ a.1 g).map_add _ _) a.2
      map_smul' c v := by
        ext a
        exact congrFun ((ρ a.1 g).map_smul c _) a.2 }
  map_one' := by
    ext v a
    exact congrFun (congrArg (fun f => f (fun b => v ⟨a.1,b⟩)) (map_one (ρ a.1))) a.2
  map_mul' g h := by
    ext v a
    exact congrFun (congrArg (fun f => f (fun b => v ⟨a.1,b⟩)) (map_mul (ρ a.1) g h)) a.2

def tailDegreeAction (G : Subgroup (Equiv.Perm (Fin n))) (m d : ℕ) :
    Representation R G (TailDegreeIndex n m d → R) :=
  sigmaCoordinateAction fun i : Fin n => shiftedDegreeAction G (m+i.val) d

def syzygyDegreeAction (G : Subgroup (Equiv.Perm (Fin n))) (m d : ℕ) :
    Representation R G (SyzygyDegreeIndex n m d → R) :=
  sigmaCoordinateAction fun i : Fin n => sigmaCoordinateAction fun j : Fin n =>
    shiftedDegreeAction G ((m+i.val)+(m+j.val)) d

theorem tailDegreeDecode_action (G : Subgroup (Equiv.Perm (Fin n))) (m d : ℕ)
    (g : G) (v : TailDegreeIndex n m d → R) (i : Fin n) :
    tailDegreeDecode m d (tailDegreeAction G m d g v) i =
      MvPolynomial.rename (g : Equiv.Perm (Fin n)) (tailDegreeDecode m d v i) := by
  change shiftedDecode (m+i.val) d
    (shiftedRename (g : Equiv.Perm (Fin n)) (m+i.val) d (fun a => v ⟨i,a⟩)) =
      MvPolynomial.rename (g : Equiv.Perm (Fin n))
        (shiftedDecode (m+i.val) d (fun a => v ⟨i,a⟩))
  exact shiftedDecode_shiftedRename (R := R) (n := n)
    (g : Equiv.Perm (Fin n)) (m+i.val) d (fun a => v ⟨i,a⟩)

theorem syzygyDegreeDecode_action (G : Subgroup (Equiv.Perm (Fin n))) (m d : ℕ)
    (g : G) (v : SyzygyDegreeIndex n m d → R) (i j : Fin n) :
    syzygyDegreeDecode m d (syzygyDegreeAction G m d g v) i j =
      MvPolynomial.rename (g : Equiv.Perm (Fin n)) (syzygyDegreeDecode m d v i j) := by
  change shiftedDecode ((m+i.val)+(m+j.val)) d
    (shiftedRename (g : Equiv.Perm (Fin n)) ((m+i.val)+(m+j.val)) d (fun a => v ⟨i,j,a⟩)) =
      MvPolynomial.rename (g : Equiv.Perm (Fin n))
        (shiftedDecode ((m+i.val)+(m+j.val)) d (fun a => v ⟨i,j,a⟩))
  exact shiftedDecode_shiftedRename (R := R) (n := n)
    (g : Equiv.Perm (Fin n)) ((m+i.val)+(m+j.val)) d (fun a => v ⟨i,j,a⟩)

theorem tailDegreeMatrix_intertwines (G : Subgroup (Equiv.Perm (Fin n)))
    (c : Fin n → R) (lam : R) (m d : ℕ)
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) (g : G) :
    (tailDegreeMatrix c lam m d).mulVecLin.comp (tailDegreeAction G m d g) =
      (shiftedDegreeAction G 0 d g).comp (tailDegreeMatrix c lam m d).mulVecLin := by
  apply LinearMap.ext
  intro v
  apply shiftedDecode_injective 0 d
  change shiftedDecode 0 d
      (tailDegreeMatrix c lam m d *ᵥ (tailDegreeAction G m d g v)) =
    shiftedDecode 0 d (shiftedRename (g : Equiv.Perm (Fin n)) 0 d
      (tailDegreeMatrix c lam m d *ᵥ v))
  rw [shiftedDecode_tailDegreeMatrix,shiftedDecode_shiftedRename,shiftedDecode_tailDegreeMatrix]
  rw [rename_tailMap (g : Equiv.Perm (Fin n)) c lam (hfix g)]
  congr 1
  funext i
  exact tailDegreeDecode_action G m d g v i

theorem syzygyDegreeMatrix_intertwines (G : Subgroup (Equiv.Perm (Fin n)))
    (c : Fin n → R) (lam : R) (m d : ℕ)
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) (g : G) :
    (syzygyDegreeMatrix c lam m d).mulVecLin.comp (syzygyDegreeAction G m d g) =
      (tailDegreeAction G m d g).comp (syzygyDegreeMatrix c lam m d).mulVecLin := by
  ext v a
  have h : tailDegreeDecode m d
      ((syzygyDegreeMatrix c lam m d) *ᵥ (syzygyDegreeAction G m d g v)) a.1 =
      tailDegreeDecode m d
        (tailDegreeAction G m d g ((syzygyDegreeMatrix c lam m d) *ᵥ v)) a.1 := by
    rw [tailDegreeDecode_syzygyDegreeMatrix, tailDegreeDecode_action,
      tailDegreeDecode_syzygyDegreeMatrix, rename_syzygyMap _ c lam (hfix g)]
    apply congrArg (fun A => syzygyMap c lam m A a.1)
    funext i j
    exact syzygyDegreeDecode_action G m d g v i j
  simpa only [tailDegreeDecode, shiftedDecode_coeff, LinearMap.comp_apply,
    Matrix.mulVecLin_apply] using congrArg (fun p => p.coeff a.2.val) h

end Ring

section ChangeOfCoefficients

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

theorem map_shiftedDecode (φ : R →+* S) (s d : ℕ) (v : ShiftedExponent n s d → R) :
    MvPolynomial.map φ (shiftedDecode s d v) = shiftedDecode s d (fun a => φ (v a)) := by
  simp only [shiftedDecode_eq_sum, map_sum, map_coefficient_smul,
    MvPolynomial.map_monomial, map_one]

theorem map_shiftedRename (φ : R →+* S) (e : Equiv.Perm (Fin n)) (s d : ℕ)
    (v : ShiftedExponent n s d → R) (a : ShiftedExponent n s d) :
    φ (shiftedRename e s d v a) = shiftedRename e s d (fun b => φ (v b)) a := by
  change φ ((MvPolynomial.rename e (shiftedDecode s d v)).coeff a.val) = _
  rw [← MvPolynomial.coeff_map, MvPolynomial.map_rename, map_shiftedDecode]
  rfl

theorem map_shiftedDegreeAction (φ : R →+* S)
    (G : Subgroup (Equiv.Perm (Fin n))) (s d : ℕ) :
    EquivariantHomMatrices.mapRepresentation φ (shiftedDegreeAction (R := R) G s d) =
      shiftedDegreeAction (R := S) G s d := by
  classical
  apply MonoidHom.ext
  intro g
  apply LinearMap.toMatrix'.injective
  rw [EquivariantHomMatrices.mapRepresentation_toMatrix]
  ext a b
  simp only [Matrix.map_apply, LinearMap.toMatrix'_apply]
  change φ (shiftedRename (R := R) (g : Equiv.Perm (Fin n)) s d (Pi.single b 1) a) =
    shiftedRename (R := S) (g : Equiv.Perm (Fin n)) s d (Pi.single b 1) a
  rw [map_shiftedRename]
  apply congrArg (fun v : ShiftedExponent n s d → S =>
    shiftedRename (R := S) (g : Equiv.Perm (Fin n)) s d v a)
  funext t
  simp only [Pi.single_apply, apply_ite φ, map_one, map_zero]

theorem map_tailDegreeAction (φ : R →+* S)
    (G : Subgroup (Equiv.Perm (Fin n))) (m d : ℕ) :
    EquivariantHomMatrices.mapRepresentation φ (tailDegreeAction (R := R) G m d) =
      tailDegreeAction (R := S) G m d := by
  classical
  apply MonoidHom.ext
  intro g
  apply LinearMap.toMatrix'.injective
  have hmat (M : Matrix (TailDegreeIndex n m d) (TailDegreeIndex n m d) S) :
      LinearMap.toMatrix' M.mulVecLin = M := LinearMap.toMatrix'_toLin' M
  change LinearMap.toMatrix' (Matrix.mulVecLin _) = _
  rw [hmat]
  ext a b
  simp only [Matrix.map_apply, LinearMap.toMatrix'_apply]
  change φ (shiftedRename (g : Equiv.Perm (Fin n)) (m+a.1.val) d _ a.2) =
      shiftedRename (R := S) (g : Equiv.Perm (Fin n)) (m+a.1.val) d _ a.2
  rw [map_shiftedRename]
  apply congrArg (fun v : ShiftedExponent n (m+a.1.val) d → S =>
    shiftedRename (R := S) (g : Equiv.Perm (Fin n)) (m+a.1.val) d v a.2)
  funext t
  simp only [Pi.single_apply, apply_ite φ, map_one, map_zero]

theorem map_syzygyDegreeAction (φ : R →+* S)
    (G : Subgroup (Equiv.Perm (Fin n))) (m d : ℕ) :
    EquivariantHomMatrices.mapRepresentation φ (syzygyDegreeAction (R := R) G m d) =
      syzygyDegreeAction (R := S) G m d := by
  classical
  apply MonoidHom.ext
  intro g
  apply LinearMap.toMatrix'.injective
  have hmat (M : Matrix (SyzygyDegreeIndex n m d) (SyzygyDegreeIndex n m d) S) :
      LinearMap.toMatrix' M.mulVecLin = M := LinearMap.toMatrix'_toLin' M
  change LinearMap.toMatrix' (Matrix.mulVecLin _) = _
  rw [hmat]
  ext a b
  simp only [Matrix.map_apply, LinearMap.toMatrix'_apply]
  change φ (shiftedRename (g : Equiv.Perm (Fin n)) ((m+a.1.val)+(m+a.2.1.val)) d _ a.2.2) =
      shiftedRename (R := S) (g : Equiv.Perm (Fin n)) ((m+a.1.val)+(m+a.2.1.val)) d _ a.2.2
  rw [map_shiftedRename]
  apply congrArg (fun v : ShiftedExponent n ((m+a.1.val)+(m+a.2.1.val)) d → S =>
    shiftedRename (R := S) (g : Equiv.Perm (Fin n)) ((m+a.1.val)+(m+a.2.1.val)) d v a.2.2)
  funext t
  simp only [Pi.single_apply, apply_ite φ, map_one, map_zero]

end ChangeOfCoefficients

end PaperVerification.PowerOperators
