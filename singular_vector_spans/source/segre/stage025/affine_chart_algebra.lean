module
import all Mathlib.AlgebraicGeometry.Modules.Sheaf
import all Mathlib.RingTheory.OreLocalization.Basic
import all Mathlib.Algebra.MonoidAlgebra.Defs
public import SegreVerified.Stage001
public import SegreVerified.Stage002
public import SegreVerified.Stage003
public import SegreVerified.Stage004
public import SegreVerified.Stage005
public import SegreVerified.Stage006
public import SegreVerified.Stage007
public import SegreVerified.Stage008
public import SegreVerified.Stage009
public import SegreVerified.Stage010
public import SegreVerified.Stage011
public import SegreVerified.Stage012
public import SegreVerified.Stage013
public import SegreVerified.Stage014
public import SegreVerified.Stage015
public import SegreVerified.Stage016
public import SegreVerified.Stage017
public import SegreVerified.Stage018
public import SegreVerified.Stage019
public import SegreVerified.Stage020
public import SegreVerified.Stage021
public import SegreVerified.Stage022
public import SegreVerified.Stage023
public import SegreVerified.Stage024

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Tactic.Push
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Polynomial.ContentIdeal
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Sym.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.FinRange
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorPower.Symmetric
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.FilteredAlgebra.Basic
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.Data.Sym.NatCard
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Fin.Basic
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Tactic.Linarith
public import Mathlib.Order.Sym2
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Data.Nat.Find
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.SuccPred.Fin
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.Basic.Finite.Sum
public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.TwoSquare
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.FiveLemma
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Order.Fin.Tuple
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.KrullDimension
public import Mathlib.Order.KrullDimension
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Algebra.Ring.Subgroup
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.LinearAlgebra.Finsupp.Span
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Regular.LinearMap
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Artinian.Algebra
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.Algebra.Ring.Int.Field
public import Mathlib.RingTheory.Ideal.NatInt
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.RingTheory.RootsOfUnity.Minpoly
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Logic.Function.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.Logic.Equiv.Option
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Tactic.Abel
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Data.Finset.Interval
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.Projectivization.Subspace
public import Lean.Util.CollectAxioms
import all Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public import Lean.Util.Sorry
public import Lean.Elab.Command
public import Lean.PrettyPrinter


set_option Elab.async false
set_option linter.all false

#eval do
  let toolchain ← IO.FS.readFile "lean-toolchain"
  let manifest ← IO.FS.readFile "lake-manifest.json"
  IO.println ("SEGRE_PUBLIC_ENVIRONMENT_BEGIN\n" ++ Lean.versionString ++ "\n" ++
    Lean.githash ++ "\n" ++ toolchain.trimAscii.toString ++ "\n" ++ manifest ++
    "\nSEGRE_PUBLIC_ENVIRONMENT_END")

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The retained source check requires kernel trust level zero"
  let imported := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let rows := CollectAxioms.runM (env.setExporting false) do
    #[``Nat.add_comm, ``Nat.zero_add].mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet imported.find? name)
  for (name, axioms) in rows do
    unless (env.checked.get.find? name).isSome do throwError "Unchecked smoke target: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved shared-collector smoke axiom: {ax}"
  logInfo "SEGRE_SHARED_COLLECTOR_READY"


set_option Elab.async false
set_option maxErrors 0
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section ProbeLayer391



/-!
# Singular-vector geometry and all-format spanning theorems

The named sections preserve the original proof stages and local scopes.
-/

@[expose] public section

-- Emit compilation progress immediately while checking this large unit.
set_option stderrAsMessages false
-- Style linting is separate from elaboration, kernel checking, and the axiom audit.
set_option linter.all false
noncomputable section
set_option autoImplicit false


section SegreChartCoordinateRings

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE SegreChartCoordinateRings"
  out.flush

/-!
# Actual projective and product chart coordinate rings

The named sections preserve the original proof stages and local scopes.
-/


section HomogeneousChartDehomogenization

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE HomogeneousChartDehomogenization"
  out.flush

/-!
# Degree-one dehomogenization of the actual Proj affine ring

For an arbitrary naturally graded commutative ring and a degree-one element f,
the actual degree-zero localization A_(f) is the literal quotient A/(f-1).
The construction sends a homogeneous fraction a/f^n to the class of a; its
inverse first normalizes every homogeneous component by its corresponding
power of f. Both inverses are proved. No domain, reducedness, or generation
in degree one is assumed.

This is the actual algebraic comparison needed to connect normalized
homogeneous charts to the affine basic opens of Proj.
-/

set_option autoImplicit false

namespace PaperVerification.HomogeneousChartDehomogenization

open DirectSum

universe u v
variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {f : A} (hf : f ∈ 𝒜 1)

/-- The full normalization ideal, without taking its radical. -/
def normalizationIdeal (f : A) : Ideal A := Ideal.span ({f - 1} : Set A)

/-- The literal normalized quotient ring. -/
abbrev NormalizedRing (f : A) := A ⧸ normalizationIdeal f

/-- The canonical quotient map. -/
def quotientMap (f : A) : A →+* NormalizedRing f :=
  Ideal.Quotient.mk (normalizationIdeal f)

@[simp] theorem quotientMap_pivot (f : A) : quotientMap f f = 1 := by
  apply sub_eq_zero.mp
  rw [← map_one (quotientMap f), ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

theorem quotientMap_pivot_isUnit (f : A) : IsUnit (quotientMap f f) := by
  rw [quotientMap_pivot]
  exact isUnit_one

/-- A degree-n element normalized by the literal power f^n. -/
def fraction (n : ℕ) (a : 𝒜 n) : HomogeneousLocalization.Away 𝒜 f :=
  HomogeneousLocalization.Away.mk 𝒜 hf n a (by simpa using a.property)

@[simp] theorem fraction_val (n : ℕ) (a : 𝒜 n) :
    (fraction 𝒜 hf n a).val =
      Localization.mk (a : A) (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f) := rfl

/-- For each fixed degree, normalization is genuinely additive. -/
def fractionAdd (n : ℕ) : 𝒜 n →+ HomogeneousLocalization.Away 𝒜 f where
  toFun := fraction 𝒜 hf n
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    simp only [fraction_val, ZeroMemClass.coe_zero,
      HomogeneousLocalization.val_zero, Localization.mk_zero]
  map_add' a b := by
    apply HomogeneousLocalization.val_injective
    simp only [fraction_val, HomogeneousLocalization.val_add, AddMemClass.coe_add]
    exact (Localization.add_mk_self _ _ _).symm

@[simp] theorem fractionAdd_apply (n : ℕ) (a : 𝒜 n) :
    fractionAdd 𝒜 hf n a = fraction 𝒜 hf n a := rfl

/-- The normalization maps preserve the actual graded unit. -/
theorem fractionAdd_one :
    fractionAdd 𝒜 hf 0
      (@GradedMonoid.GOne.one ℕ (fun n => ↥(𝒜 n)) _ _) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [fractionAdd_apply, fraction_val, SetLike.coe_gOne,
    HomogeneousLocalization.val_one, pow_zero]
  change Localization.mk (1 : A) (1 : Submonoid.powers f) = 1
  rw [Localization.mk_one_eq_algebraMap, map_one]

/-- The normalization maps preserve every actual graded product. -/
theorem fractionAdd_mul {i j : ℕ} (a : 𝒜 i) (b : 𝒜 j) :
    fractionAdd 𝒜 hf (i + j)
      (@GradedMonoid.GMul.mul ℕ (fun n => ↥(𝒜 n)) _ _ i j a b) =
      fractionAdd 𝒜 hf i a * fractionAdd 𝒜 hf j b := by
  apply HomogeneousLocalization.val_injective
  simp only [fractionAdd_apply, HomogeneousLocalization.val_mul, fraction_val,
    SetLike.coe_gMul, Localization.mk_eq_mk']
  rw [← IsLocalization.mk'_mul]
  exact congrArg
    (IsLocalization.mk' (Localization.Away f) ((a : A) * (b : A)))
    (Subtype.ext (pow_add f i j))

/-- First extend the homogeneous normalization maps to the actual direct sum. -/
def componentNormalization :
    (⨁ n : ℕ, 𝒜 n) →+* HomogeneousLocalization.Away 𝒜 f :=
  DirectSum.toSemiring (fractionAdd 𝒜 hf)
    (fractionAdd_one 𝒜 hf) (fractionAdd_mul 𝒜 hf)

/-- Normalize all homogeneous components using the actual graded decomposition. -/
def normalize : A →+* HomogeneousLocalization.Away 𝒜 f :=
  (componentNormalization 𝒜 hf).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom

/-- On a homogeneous element, the full map is its literal homogeneous fraction. -/
theorem normalize_of_mem {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    normalize 𝒜 hf a = fraction 𝒜 hf n ⟨a, ha⟩ := by
  change DirectSum.toAddMonoid (fractionAdd 𝒜 hf) (DirectSum.decompose 𝒜 a) = _
  rw [DirectSum.decompose_of_mem 𝒜 ha, DirectSum.toAddMonoid_of]
  rfl

@[simp] theorem normalize_pivot : normalize 𝒜 hf f = 1 := by
  rw [normalize_of_mem 𝒜 hf hf]
  apply HomogeneousLocalization.val_injective
  rw [fraction_val, HomogeneousLocalization.val_one]
  simp only [pow_one, Localization.mk_eq_mk']
  exact IsLocalization.mk'_self (Localization.Away f) (Submonoid.mem_powers f)

/-- The full normalization ideal is annihilated; no kernel equality is assumed. -/
theorem normalizationIdeal_le_ker :
    normalizationIdeal f ≤ RingHom.ker (normalize 𝒜 hf) := by
  apply Ideal.span_le.mpr
  intro a ha
  obtain rfl := Set.mem_singleton_iff.mp ha
  change normalize 𝒜 hf (f - 1) = 0
  rw [map_sub, normalize_pivot, map_one, sub_self]

/-- The map from the literal quotient to the actual homogeneous localization. -/
def fromQuotient : NormalizedRing f →+* HomogeneousLocalization.Away 𝒜 f :=
  Ideal.Quotient.lift (normalizationIdeal f) (normalize 𝒜 hf)
    (fun a ha => normalizationIdeal_le_ker 𝒜 hf ha)

@[simp] theorem fromQuotient_quotientMap (a : A) :
    fromQuotient 𝒜 hf (quotientMap f a) = normalize 𝒜 hf a := rfl

/-- Restrict the genuine localization lift of the quotient map to degree zero. -/
def toQuotient (_ : f ∈ 𝒜 1) : HomogeneousLocalization.Away 𝒜 f →+* NormalizedRing f :=
  HomogeneousLocalization.Away.lift 𝒜 (quotientMap f) (quotientMap_pivot_isUnit f)

/-- On every homogeneous fraction, setting f=1 retains its full numerator. -/
@[simp] theorem toQuotient_fraction (n : ℕ) (a : 𝒜 n) :
    toQuotient 𝒜 hf (fraction 𝒜 hf n a) = quotientMap f a := by
  have hu : (quotientMap_pivot_isUnit f).unit = 1 := by
    apply Units.ext
    exact (quotientMap_pivot_isUnit f).unit_spec.trans (quotientMap_pivot f)
  simp only [toQuotient, fraction, HomogeneousLocalization.Away.lift_mk,
    hu, one_pow, inv_one, Units.val_one, mul_one]

/-- Decomposition and subsequent normalization recover the original quotient map. -/
theorem toQuotient_normalize (a : A) :
    toQuotient 𝒜 hf (normalize 𝒜 hf a) = quotientMap f a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | homogeneous a =>
      rw [normalize_of_mem 𝒜 hf a.property, toQuotient_fraction]

/-- The quotient-to-localization-to-quotient composite is the identity. -/
theorem toQuotient_fromQuotient (x : NormalizedRing f) :
    toQuotient 𝒜 hf (fromQuotient 𝒜 hf x) = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [show Ideal.Quotient.mk (normalizationIdeal f) a = quotientMap f a from rfl,
    fromQuotient_quotientMap, toQuotient_normalize]

/-- The reverse composite is the identity on every homogeneous fraction. -/
theorem fromQuotient_toQuotient (z : HomogeneousLocalization.Away 𝒜 f) :
    fromQuotient 𝒜 hf (toQuotient 𝒜 hf z) = z := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf z
  have ha' : a ∈ 𝒜 n := by simpa using ha
  change fromQuotient 𝒜 hf
      (toQuotient 𝒜 hf (fraction 𝒜 hf n ⟨a, ha'⟩)) =
    fraction 𝒜 hf n ⟨a, ha'⟩
  rw [toQuotient_fraction, fromQuotient_quotientMap, normalize_of_mem 𝒜 hf ha']

/-- The actual degree-one affine Proj chart ring is the actual normalized quotient. -/
def awayEquivNormalized :
    HomogeneousLocalization.Away 𝒜 f ≃+* NormalizedRing f where
  toFun := toQuotient 𝒜 hf
  invFun := fromQuotient 𝒜 hf
  left_inv := fromQuotient_toQuotient 𝒜 hf
  right_inv := toQuotient_fromQuotient 𝒜 hf
  map_add' := map_add _
  map_mul' := map_mul _

/-- The equivalence has the defining formula on every degree-n fraction. -/
@[simp] theorem awayEquivNormalized_fraction (n : ℕ) (a : 𝒜 n) :
    awayEquivNormalized 𝒜 hf (fraction 𝒜 hf n a) = quotientMap f a :=
  toQuotient_fraction 𝒜 hf n a

/-- Its inverse on every homogeneous quotient element is the actual normalized fraction. -/
@[simp] theorem awayEquivNormalized_symm_quotientMap {n : ℕ} {a : A}
    (ha : a ∈ 𝒜 n) :
    (awayEquivNormalized 𝒜 hf).symm (quotientMap f a) =
      fraction 𝒜 hf n ⟨a, ha⟩ :=
  normalize_of_mem 𝒜 hf ha

end PaperVerification.HomogeneousChartDehomogenization

end HomogeneousChartDehomogenization

section SegrePolynomialChartRing

/-!
# The full coordinate algebra of a standard projective chart

The actual degree-zero homogeneous localization at a coordinate is identified
with the polynomial algebra on all the other coordinates. Both inverses are
constructed through the literal normalization quotient. The result preserves
the coefficient algebra and the formulas for the ratios Xᵢ/Xₚ; it is a ring
equivalence and retains the complete scheme structure.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.PolynomialChartRing

open MvPolynomial
open PaperVerification.HomogeneousChartDehomogenization

variable {K I : Type*} [CommRing K] [DecidableEq I]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The free coordinate set in the chart with pivot `p`. -/
abbrev FreeCoordinate (p : I) := {i : I // i≠p}

/-- The literal substitution setting the pivot coordinate equal to one. -/
def normalizedVariable (p i : I) : MvPolynomial (FreeCoordinate p) K :=
  if h : i=p then 1 else X ⟨i,h⟩

@[simp] theorem normalizedVariable_pivot (p : I) :
    normalizedVariable (K := K) p p=1 := by simp [normalizedVariable]

@[simp] theorem normalizedVariable_free (p : I) (i : FreeCoordinate p) :
    normalizedVariable (K := K) p i.val=X i := by simp [normalizedVariable,i.property]

def normalizeCoordinates (p : I) :
    MvPolynomial I K →ₐ[K] MvPolynomial (FreeCoordinate p) K :=
  aeval (normalizedVariable p)

@[simp] theorem normalizeCoordinates_X (p i : I) :
    normalizeCoordinates (K := K) p (X i)=normalizedVariable p i :=
  aeval_X _ _

/-- Normalization kills exactly the supplied equation at the level needed for
the quotient universal property; no kernel equality is assumed. -/
theorem normalizationIdeal_le_ker (p : I) :
    normalizationIdeal (X p : MvPolynomial I K) ≤
      RingHom.ker (normalizeCoordinates (K := K) p).toRingHom := by
  apply Ideal.span_le.mpr
  rintro f hf
  obtain rfl := Set.mem_singleton_iff.mp hf
  change normalizeCoordinates p (X p-1)=0
  rw [map_sub,normalizeCoordinates_X,normalizedVariable_pivot,map_one,sub_self]

/-- The actual normalized quotient maps to the free polynomial algebra. -/
def quotientToPolynomial (p : I) :
    NormalizedRing (X p : MvPolynomial I K) →ₐ[K] MvPolynomial (FreeCoordinate p) K :=
  Ideal.Quotient.liftₐ (normalizationIdeal (X p)) (normalizeCoordinates p)
    (fun f hf => normalizationIdeal_le_ker p hf)

@[simp] theorem quotientToPolynomial_mk (p : I) (f : MvPolynomial I K) :
    quotientToPolynomial p (quotientMap (X p) f)=normalizeCoordinates p f := rfl

/-- The inverse sends a free variable to the class of the corresponding
original homogeneous coordinate. -/
def polynomialToQuotient (p : I) :
    MvPolynomial (FreeCoordinate p) K →ₐ[K] NormalizedRing (X p : MvPolynomial I K) :=
  aeval (fun i => quotientMap (X p) (X i.val))

@[simp] theorem polynomialToQuotient_X (p : I) (i : FreeCoordinate p) :
    polynomialToQuotient (K := K) p (X i)=quotientMap (X p) (X i.val) :=
  aeval_X _ _

theorem polynomialToQuotient_normalizedVariable (p i : I) :
    polynomialToQuotient (K := K) p (normalizedVariable p i)=
      quotientMap (X p) (X i) := by
  by_cases hi : i=p
  · subst i
    simp
  · simp [normalizedVariable,hi]

theorem polynomialToQuotient_comp_normalizeCoordinates (p : I) :
    (polynomialToQuotient (K := K) p).comp (normalizeCoordinates p)=
      Ideal.Quotient.mkₐ K (normalizationIdeal (X p)) := by
  ext i
  simpa only [AlgHom.comp_apply, normalizeCoordinates_X,
    Ideal.Quotient.mkₐ_eq_mk, quotientMap] using
    (polynomialToQuotient_normalizedVariable (K := K) p i)

theorem polynomialToQuotient_quotientToPolynomial (p : I)
    (x : NormalizedRing (X p : MvPolynomial I K)) :
    polynomialToQuotient p (quotientToPolynomial p x)=x := by
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact AlgHom.congr_fun (polynomialToQuotient_comp_normalizeCoordinates p) f

theorem quotientToPolynomial_comp_polynomialToQuotient (p : I) :
    (quotientToPolynomial (K := K) p).comp (polynomialToQuotient p)=
      AlgHom.id K (MvPolynomial (FreeCoordinate p) K) := by
  ext i
  simp

/-- A genuine algebra equivalence with the normalization quotient. -/
def normalizedQuotientEquiv (p : I) :
    NormalizedRing (X p : MvPolynomial I K) ≃ₐ[K] MvPolynomial (FreeCoordinate p) K where
  __ := quotientToPolynomial p
  invFun := polynomialToQuotient p
  left_inv := polynomialToQuotient_quotientToPolynomial p
  right_inv x := AlgHom.congr_fun (quotientToPolynomial_comp_polynomialToQuotient p) x

@[simp] theorem normalizedQuotientEquiv_mk (p : I) (f : MvPolynomial I K) :
    normalizedQuotientEquiv p (quotientMap (X p) f)=normalizeCoordinates p f := rfl

/-- The degree-one normalization equivalence respects the original
coefficient algebra, not merely the underlying rings. -/
def awayEquivNormalizedAlgebra (p : I) :
    HomogeneousLocalization.Away (homogeneousSubmodule I K) (X p) ≃ₐ[K]
      NormalizedRing (X p : MvPolynomial I K) where
  __ := awayEquivNormalized (homogeneousSubmodule I K) (isHomogeneous_X K p)
  commutes' c := by
    change HomogeneousLocalization.Away.lift (homogeneousSubmodule I K)
      (quotientMap (X p)) (quotientMap_pivot_isUnit (X p))
      (algebraMap K _ c)=algebraMap K _ c
    rw [HomogeneousLocalization.algebraMap_eq_comp,RingHom.comp_apply]
    change HomogeneousLocalization.Away.lift (homogeneousSubmodule I K)
      (quotientMap (X p)) (quotientMap_pivot_isUnit (X p))
      (algebraMap ((homogeneousSubmodule I K) 0) _
        (algebraMap K ((homogeneousSubmodule I K) 0) c))=_
    rw [HomogeneousLocalization.Away.lift_algebraMap]
    rfl

/-- The full actual affine Proj chart algebra is a polynomial algebra in
every nonpivot coordinate. -/
def awayEquivPolynomial (p : I) :
    HomogeneousLocalization.Away (homogeneousSubmodule I K) (X p) ≃ₐ[K]
      MvPolynomial (FreeCoordinate p) K :=
  (awayEquivNormalizedAlgebra p).trans (normalizedQuotientEquiv p)

/-- On a homogeneous fraction, the map is ordinary dehomogenization. -/
@[simp] theorem awayEquivPolynomial_fraction (p : I) (d : ℕ)
    (f : (homogeneousSubmodule I K) d) :
    awayEquivPolynomial p
      (fraction (homogeneousSubmodule I K) (isHomogeneous_X K p) d f)=
        normalizeCoordinates p f.val := by
  exact congrArg (normalizedQuotientEquiv p)
    (awayEquivNormalized_fraction (homogeneousSubmodule I K) (isHomogeneous_X K p) d f)

/-- In particular, Xᵢ/Xₚ is the normalized coordinate, including the pivot. -/
@[simp] theorem awayEquivPolynomial_coordinate (p i : I) :
    awayEquivPolynomial (K := K) p
      (fraction (homogeneousSubmodule I K) (isHomogeneous_X K p) 1
        ⟨X i,isHomogeneous_X K i⟩)=normalizedVariable p i := by
  rw [awayEquivPolynomial_fraction,normalizeCoordinates_X]

end PaperVerification.Segre.PolynomialChartRing

end SegrePolynomialChartRing

end SegreChartCoordinateRings

end
end
end ProbeLayer391


/-! Future-only kernel audit for one exported mathematical stage.

Append to the stage being checked, with Lean.Util.CollectAxioms available through
both `public import Lean.Util.CollectAxioms` and `import all Lean.Util.CollectAxioms`
in that stage's header, as required by the reviewed FullFlattenedAudit.

Every new declaration in the checked kernel environment is included: public,
private, generated and vendored declarations receive the same direct-sorry and
transitive-axiom checks. This is evidence for this stage only. Later principal
theorems need not exist yet, and the final full principal audit remains required.

This preparation does not execute the audit, export a module or alter a proof.
-/

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The stage kernel audit requires kernel trust level zero"
  let names := (env.checked.get.constants.foldStage2
    (fun (names : Array Name) name _ => names.push name) #[]).qsort Name.quickLt
  unless names.size > 0 do throwError "The stage mathematical module is empty"
  -- Reject direct proof holes before computing transitive axiom closures.
  -- The complete successful audit below remains unchanged.
  for name in names do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
  let privateEnv := env.setExporting false
  let importedAxioms := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  -- Match Lean's ordinary export audit, sharing its traversal cache across names.
  let axiomRows := CollectAxioms.runM privateEnv do
    names.mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet importedAxioms.find? name)
  let mut theoremCount : Nat := 0
  for (name, axioms) in axiomRows do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom in {name}: {ax}"
    if let .thmInfo _ := info then
      theoremCount := theoremCount + 1
  let report := Json.mkObj [
    ("main_module", toJson env.header.mainModule.toString),
    ("declaration_count", toJson names.size),
    ("theorem_count", toJson theoremCount),
    ("trust_level", toJson env.header.trustLevel.toNat),
    ("allowed_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("audit_scope", toJson "current_stage_new_declarations")]
  logInfo m!"SEGRE_STAGE_KERNEL_AUDIT_PASS {report.compress}"
