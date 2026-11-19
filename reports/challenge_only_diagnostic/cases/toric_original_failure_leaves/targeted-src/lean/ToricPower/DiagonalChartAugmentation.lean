module

public import ToricPower.DiagonalZerothExactness
public import ToricPower.CellularVertexAugmentation
public import ToricPower.DiagonalAugmentation

/-!
# The genuine augmented resolution over the product-chart ring

The target has one monomial basis vector for each integral weight whose
literal diagonal strip is nonempty.  Chart monomials shift that weight by
the sum of their two characters.  This defines an actual module over the
same product-chart coordinate ring as the cellular complex.

The ordinary cellular augmentation is compatible with that action by
naturality of the cellular-to-singular comparison and singular augmentation.
The resulting actual module-chain map is proved a quasi-isomorphism from
positive exactness and the genuine degree-zero cokernel calculation.

Identification of this explicitly described module with the structure
module of the scheme-theoretic diagonal is a separate comparison, using
the toric dual-semigroup decomposition.  It is not part of the definition.

Candidate until the full source closure passes the pinned Lean checker.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex
open scoped Classical

namespace ToricPower

theorem zeroHomologyQuotient_naturality {k : Type} [Ring k]
    {K L : ChainComplex (ModuleCat k) ℕ} (φ : K ⟶ L)
    {M : ModuleCat k} (eK : K.homology 0 ≅ M) (eL : L.homology 0 ≅ M)
    (he : HomologicalComplex.homologyMap φ 0 ≫ eL.hom = eK.hom) :
    φ.f 0 ≫ ModuleCat.ofHom (zeroHomologyQuotient L eL) =
      ModuleCat.ofHom (zeroHomologyQuotient K eK) := by
  change φ.f 0 ≫ L.pOpcycles 0 ≫ L.isoHomologyι₀.inv ≫ eL.hom =
    K.pOpcycles 0 ≫ K.isoHomologyι₀.inv ≫ eK.hom
  rw [← HomologicalComplex.p_opcyclesMap_assoc,
    ← ChainComplex.isoHomologyι₀_inv_naturality_assoc, he]

namespace IntegralArrangement

variable {n s : ℕ} (k : Type) [CommRing k] (A : Fin s → Fin n → ℤ)

local instance diagonalChartAugmentationPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

private local instance diagonalChartAugmentationStripCW (S T : Set (Fin s)) (u : Fin n → ℤ) :
    CWComplex (diagonalStripCarrier A S T u) :=
  inferInstanceAs (CWComplex (diagonalStripSubcomplex A S T u : Set (Fin n → ℝ)))

/-- The exact set of weights present in the augmentation target. -/
abbrev DiagonalSupportedWeight (S T : Set (Fin s)) :=
  {u : Fin n → ℤ // (diagonalStrip A S T u).Nonempty}

def diagonalSupportIndexEquiv (S T : Set (Fin s)) :
    (Σ u : Fin n → ℤ, DiagonalWeightAugmentationIndex A S T u) ≃
      DiagonalSupportedWeight A S T where
  toFun p := ⟨p.1,p.2.down⟩
  invFun u := ⟨u.val,⟨u.property⟩⟩
  left_inv p := by rcases p with ⟨u,⟨hu⟩⟩; rfl
  right_inv u := rfl

/-- The actual target coefficient module on all existing weights. -/
abbrev DiagonalChartHZero (S T : Set (Fin s)) := DiagonalSupportedWeight A S T →₀ k

/-- A chart monomial acts by the literal total-character shift. -/
def diagonalSupportedWeightTranslate (S T : Set (Fin s))
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T)
    (u : DiagonalSupportedWeight A S T) : DiagonalSupportedWeight A S T :=
  ⟨u.val+p.1.val+p.2.val, by
    obtain ⟨x,hx⟩ := u.property
    exact ⟨x+latticeLift p.1.val,diagonalStrip_monomial_translate A S T p u.val hx⟩⟩

@[simp]
theorem diagonalSupportedWeightTranslate_zero (S T : Set (Fin s))
    (u : DiagonalSupportedWeight A S T) : diagonalSupportedWeightTranslate A S T 0 u = u := by
  apply Subtype.ext
  simp [diagonalSupportedWeightTranslate]

theorem diagonalSupportedWeightTranslate_add (S T : Set (Fin s))
    (p q : rayCharacterMonoid A S × rayCharacterMonoid A T)
    (u : DiagonalSupportedWeight A S T) :
    diagonalSupportedWeightTranslate A S T (p+q) u =
      diagonalSupportedWeightTranslate A S T p
        (diagonalSupportedWeightTranslate A S T q u) := by
  apply Subtype.ext
  change u.val+(p.1.val+q.1.val)+(p.2.val+q.2.val) =
    u.val+q.1.val+q.2.val+p.1.val+p.2.val
  abel

def diagonalHZeroRepresentation (S T : Set (Fin s)) :
    Multiplicative (rayCharacterMonoid A S × rayCharacterMonoid A T) →*
      Module.End k (DiagonalChartHZero k A S T) where
  toFun p := Finsupp.lmapDomain k k (diagonalSupportedWeightTranslate A S T p.toAdd)
  map_one' := by
    change Finsupp.lmapDomain k k (diagonalSupportedWeightTranslate A S T 0) = LinearMap.id
    have h : diagonalSupportedWeightTranslate A S T 0 =
        (id : DiagonalSupportedWeight A S T → DiagonalSupportedWeight A S T) := by
      funext u
      exact diagonalSupportedWeightTranslate_zero A S T u
    rw [h,Finsupp.lmapDomain_id]
  map_mul' p q := by
    change Finsupp.lmapDomain k k (diagonalSupportedWeightTranslate A S T (p.toAdd+q.toAdd)) =
      (Finsupp.lmapDomain k k (diagonalSupportedWeightTranslate A S T p.toAdd)).comp
        (Finsupp.lmapDomain k k (diagonalSupportedWeightTranslate A S T q.toAdd))
    rw [← Finsupp.lmapDomain_comp]
    congr 1
    funext u
    exact diagonalSupportedWeightTranslate_add A S T p.toAdd q.toAdd u

def diagonalHZeroAction (S T : Set (Fin s)) :
    DiagonalChartRing k A S T →ₐ[k] Module.End k (DiagonalChartHZero k A S T) :=
  AddMonoidAlgebra.lift k _ _ (diagonalHZeroRepresentation k A S T)

instance diagonalChartHZero_module (S T : Set (Fin s)) :
    Module (DiagonalChartRing k A S T) (DiagonalChartHZero k A S T) :=
  Module.compHom _ (diagonalHZeroAction k A S T).toRingHom

theorem diagonalChartHZero_single_smul (S T : Set (Fin s))
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T)
    (r : k) (v : DiagonalChartHZero k A S T) :
    AddMonoidAlgebra.single p r • v =
      r • Finsupp.mapDomain (diagonalSupportedWeightTranslate A S T p) v := by
  change diagonalHZeroAction k A S T (AddMonoidAlgebra.single p r) v = _
  rw [diagonalHZeroAction,AddMonoidAlgebra.lift_single]
  rfl

/-- The actual augmentation on coefficients, after the explicit
bijection between a supported weight and its one-point weight target. -/
def diagonalChartAugmentationMap (S T : Set (Fin s)) :
    DiagonalChartChains k A S T 0 →ₗ[k] DiagonalChartHZero k A S T :=
  (Finsupp.domLCongr (diagonalSupportIndexEquiv A S T)).toLinearMap.comp
    (diagonalChartAugmentationCoordinates k A S T)

theorem diagonalChartAugmentationMap_exact (S T : Set (Fin s)) :
    Function.Exact (diagonalChartBoundary k A S T 0)
      (diagonalChartAugmentationMap k A S T) :=
  (diagonalChartAugmentationCoordinates_exact k A S T).comp_injective
    (Finsupp.domLCongr (R := k) (M := k) (diagonalSupportIndexEquiv A S T))
    (Finsupp.domLCongr (R := k) (M := k) (diagonalSupportIndexEquiv A S T)).injective
    (map_zero _)

theorem diagonalChartAugmentationMap_surjective (S T : Set (Fin s)) :
    Function.Surjective (diagonalChartAugmentationMap k A S T) :=
  (Finsupp.domLCongr (R := k) (M := k) (diagonalSupportIndexEquiv A S T)).surjective.comp
    (diagonalChartAugmentationCoordinates_surjective k A S T)

theorem diagonalChartAugmentationMap_single (S T : Set (Fin s))
    (u : Fin n → ℤ) (c : Topology.RelCWComplex.cell (diagonalStripCarrier A S T u) 0)
    (hne : (diagonalStrip A S T u).Nonempty) (r : k) :
    diagonalChartAugmentationMap k A S T (Finsupp.single ⟨u,c⟩ r) =
      Finsupp.single ⟨u,hne⟩
        (diagonalWeightAugmentationCoordinates k A S T u hne (Finsupp.single c r)) := by
  simp only [diagonalChartAugmentationMap,LinearMap.comp_apply, LinearEquiv.coe_coe,
    diagonalChartAugmentationCoordinates,sigmaWeightMap_single,
    diagonalWeightSupportedAugmentation,dif_pos hne,Finsupp.lsingle_apply,
    Finsupp.mapDomain_single,Finsupp.domLCongr_single,diagonalSupportIndexEquiv]
  rfl

/-- Each genuine vertex contributes its original scalar to its full
character weight, with the canonical degree-zero normalization. -/
theorem diagonalChartAugmentationMap_single_value (S T : Set (Fin s))
    (u : Fin n → ℤ) (c : Topology.RelCWComplex.cell (diagonalStripCarrier A S T u) 0)
    (hne : (diagonalStrip A S T u).Nonempty) (r : k) :
    diagonalChartAugmentationMap k A S T (Finsupp.single ⟨u,c⟩ r) =
      Finsupp.single ⟨u,hne⟩ r := by
  rw [diagonalChartAugmentationMap_single k A S T u c hne,
    diagonalWeightAugmentationCoordinates_vertex]

/-- Canonical zeroth cellular augmentation values are unchanged under
the genuine monomial-induced cellular map. -/
theorem diagonalWeightAugmentationCoordinates_translate_single (S T : Set (Fin s))
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (u : Fin n → ℤ)
    (hs : (diagonalStrip A S T u).Nonempty)
    (ht : (diagonalStrip A S T (u+p.1.val+p.2.val)).Nonempty)
    (c : Topology.RelCWComplex.cell (diagonalStripCarrier A S T u) 0) (r : k) :
    diagonalWeightAugmentationCoordinates k A S T (u+p.1.val+p.2.val) ht
        (Finsupp.single (diagonalStripCellTranslate A S T p u c) r) =
      diagonalWeightAugmentationCoordinates k A S T u hs (Finsupp.single c r) := by
  rw [diagonalWeightAugmentationCoordinates_vertex,
    diagonalWeightAugmentationCoordinates_vertex]

theorem diagonalChartAugmentationMap_monomial (S T : Set (Fin s))
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T)
    (v : DiagonalChartChains k A S T 0) :
    diagonalChartAugmentationMap k A S T
        (Finsupp.mapDomain (diagonalChartTranslate A S T p) v) =
      Finsupp.mapDomain (diagonalSupportedWeightTranslate A S T p)
        (diagonalChartAugmentationMap k A S T v) := by
  have h : (diagonalChartAugmentationMap k A S T).comp
      (Finsupp.lmapDomain k k (diagonalChartTranslate A S T p)) =
    (Finsupp.lmapDomain k k (diagonalSupportedWeightTranslate A S T p)).comp
      (diagonalChartAugmentationMap k A S T) := by
    apply Finsupp.lhom_ext
    rintro ⟨u,c⟩ r
    obtain ⟨x,hx⟩ := c.val.property.1
    have hs : (diagonalStrip A S T u).Nonempty :=
      ⟨x,(stripCellAllowed_iff_point A S T u c.val hx).mp c.property⟩
    have ht : (diagonalStrip A S T (u+p.1.val+p.2.val)).Nonempty :=
      ⟨x+latticeLift p.1.val,
        diagonalStrip_monomial_translate A S T p u
          ((stripCellAllowed_iff_point A S T u c.val hx).mp c.property)⟩
    simp only [LinearMap.comp_apply,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
    change diagonalChartAugmentationMap k A S T
        (Finsupp.single ⟨u+p.1.val+p.2.val, diagonalStripCellTranslate A S T p u c⟩ r) =
      Finsupp.mapDomain (diagonalSupportedWeightTranslate A S T p)
        (diagonalChartAugmentationMap k A S T (Finsupp.single ⟨u,c⟩ r))
    rw [diagonalChartAugmentationMap_single_value k A S T u c hs,
      diagonalChartAugmentationMap_single_value k A S T (u+p.1.val+p.2.val)
        (diagonalStripCellTranslate A S T p u c) ht, Finsupp.mapDomain_single]
    rfl
  exact DFunLike.congr_fun h v

theorem diagonalChartAugmentationMap_smul (S T : Set (Fin s))
    (r : DiagonalChartRing k A S T) (v : DiagonalChartChains k A S T 0) :
    diagonalChartAugmentationMap k A S T (r • v) =
      r • diagonalChartAugmentationMap k A S T v := by
  induction r using AddMonoidAlgebra.induction with
  | zero => simp
  | single_add p a r _ _ ih =>
      rw [add_smul,map_add,ih,add_smul]
      congr 1
      rw [diagonalChartChains_single_smul,diagonalChartHZero_single_smul,
        map_smul,diagonalChartAugmentationMap_monomial]

/-- The augmentation as an actual morphism over the product-chart ring. -/
def diagonalChartAugmentationLinear (S T : Set (Fin s)) :
    DiagonalChartChains k A S T 0 →ₗ[DiagonalChartRing k A S T]
      DiagonalChartHZero k A S T where
  toFun := diagonalChartAugmentationMap k A S T
  map_add' := (diagonalChartAugmentationMap k A S T).map_add
  map_smul' := diagonalChartAugmentationMap_smul k A S T

theorem diagonalChartBoundary_augmentation (S T : Set (Fin s)) :
    (diagonalChartComplex k A S T).d 1 0 ≫
      ModuleCat.ofHom (diagonalChartAugmentationLinear k A S T) = 0 := by
  rw [diagonalChartComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  exact (diagonalChartAugmentationMap_exact k A S T).apply_apply_eq_zero v

/-- The genuine homology object over the actual chart ring is the
explicit supported-weight module, by its proved cokernel universal property. -/
def diagonalChartHomologyZeroIso (S T : Set (Fin s)) :
    (diagonalChartComplex k A S T).homology 0 ≅
      ModuleCat.of (DiagonalChartRing k A S T) (DiagonalChartHZero k A S T) := by
  let K := diagonalChartComplex k A S T
  let ε := ModuleCat.ofHom (diagonalChartAugmentationLinear k A S T)
  let hε := diagonalChartBoundary_augmentation k A S T
  have hepi : Epi ε := (ModuleCat.epi_iff_surjective ε).mpr
    (diagonalChartAugmentationMap_surjective k A S T)
  have hexact : (ShortComplex.mk (K.d 1 0) ε hε).Exact := by
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    change Function.Exact ((diagonalChartComplex k A S T).d 1 0) ε
    rw [diagonalChartComplex_d]
    exact diagonalChartAugmentationMap_exact k A S T
  letI : IsIso (K.descOpcycles ε 1 (by simp) hε) :=
    (K.isIso_descOpcycles_iff ε hε).mpr ⟨hexact,hepi⟩
  exact K.isoHomologyι₀ ≪≫ asIso (K.descOpcycles ε 1 (by simp) hε)

/-- The actual augmented local cellular complex. -/
def diagonalChartAugmentation (S T : Set (Fin s)) :
    diagonalChartComplex k A S T ⟶
      (ChainComplex.single₀ (ModuleCat (DiagonalChartRing k A S T))).obj
        (ModuleCat.of (DiagonalChartRing k A S T) (DiagonalChartHZero k A S T)) :=
  augmentationOfHomologyZero (diagonalChartComplex k A S T)
    (diagonalChartHomologyZeroIso k A S T).hom

/-- Full local exactness, including the canonical zeroth augmentation,
over the entire product-chart coordinate ring. -/
theorem diagonalChartAugmentation_quasiIso (S T : Set (Fin s)) :
    QuasiIso (diagonalChartAugmentation k A S T) := by
  apply augmentationOfHomologyZero_quasiIso _ (diagonalChartHomologyZeroIso k A S T)
  intro q hq
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  exact diagonalChartComplex_exactAt k A S T d

end IntegralArrangement

end ToricPower
