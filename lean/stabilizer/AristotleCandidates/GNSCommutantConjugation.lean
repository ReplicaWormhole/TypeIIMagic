import AristotleCandidates.GNSUnitaryIntertwiner

/-!
# Conjugation by the GNS unitary and transport of commutants

For supplied data `D : StabilizerHyperfinite.BoundedStateGNS.Data` the module
`AristotleCandidates.GNSUnitaryIntertwiner` produced the GNS unitary

    gnsUnitary D : sourceGNS D ≃ₗᵢ[ℂ] targetGNS D

together with the intertwining identity relating the two GNS representations
along the supplied star-algebra equivalence `D.equivalence`.

Here we conjugate bounded operators by that unitary, in the direction

    T on sourceGNS  ↦  U ∘ T ∘ U⁻¹ on targetGNS,

package the conjugation as a `ℂ`-algebra equivalence

    gnsConjAlgEquiv D :
      (sourceGNS D →L[ℂ] sourceGNS D) ≃ₐ[ℂ] (targetGNS D →L[ℂ] targetGNS D),

which is moreover compatible with the adjoint operation (`gnsConj_star`) and so
is also packaged as a star-algebra equivalence `gnsConjStarAlgEquiv D`.

We record:

* `gnsConj_sourceGNSRepresentation`: conjugation carries the source GNS
  representative of `a` to the target GNS representative of `D.equivalence a`;
* `gnsConj_range`: it carries the range of the source representation onto the
  range of the target representation;
* `gnsConj_commute_iff`: `T` commutes with every source GNS representative iff
  its conjugate commutes with every target GNS representative;
* `gnsConj_image_centralizer` and `gnsConj_image_centralizer_centralizer`: the
  corresponding one- and two-fold centralizer (commutant / bicommutant in the
  purely algebraic, `Set.centralizer` sense) transport statements.

The two operator spaces are kept strictly distinct: everything is expressed
through the conjugation map, never through an ill-typed equality of sets of
operators living on different Hilbert spaces.

Nothing beyond this is claimed.  In particular there is **no** identification
with a tensor-product von Neumann algebra, **no** normal trace or weight, and
**no** normality, faithfulness, semifiniteness, hyperfiniteness or factor
classification.  The centralizers here are the algebraic ones supplied by
`Set.centralizer`; no topological closure or von Neumann bicommutant theorem is
invoked.
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace StabilizerHyperfinite

namespace BoundedStateGNS

open scoped ComplexOrder InnerProductSpace

/-! ### A general centralizer transport lemma for multiplicative equivalences -/

/-- A multiplicative equivalence carries the centralizer of a set onto the
centralizer of its image. -/
theorem image_centralizer_of_mulEquiv {A B : Type*} [Monoid A] [Monoid B] (e : A ≃* B)
    (S : Set A) : e '' S.centralizer = (e '' S).centralizer := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, hx s hs]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro s hs
    have := hy (e s) ⟨s, hs, rfl⟩
    have h := congrArg e.symm this
    simpa using h

variable (D : Data)

/-! ### Conjugation by the GNS unitary -/

/-- The GNS unitary as a continuous linear equivalence. -/
noncomputable def gnsUnitaryCLE : sourceGNS D ≃L[ℂ] targetGNS D :=
  (gnsUnitary D).toContinuousLinearEquiv

@[simp]
theorem gnsUnitaryCLE_apply (x : sourceGNS D) : gnsUnitaryCLE D x = gnsUnitary D x := rfl

@[simp]
theorem gnsUnitaryCLE_symm_apply (y : targetGNS D) :
    (gnsUnitaryCLE D).symm y = (gnsUnitary D).symm y := rfl

/-- Conjugation of a bounded operator on the source GNS space by the GNS
unitary, producing a bounded operator on the target GNS space:
`T ↦ U ∘ T ∘ U⁻¹`. -/
noncomputable def gnsConj (T : sourceGNS D →L[ℂ] sourceGNS D) :
    targetGNS D →L[ℂ] targetGNS D :=
  (gnsUnitaryCLE D : sourceGNS D →L[ℂ] targetGNS D).comp
    (T.comp ((gnsUnitaryCLE D).symm : targetGNS D →L[ℂ] sourceGNS D))

/-- Conjugation in the inverse direction: `T' ↦ U⁻¹ ∘ T' ∘ U`. -/
noncomputable def gnsConjSymm (T : targetGNS D →L[ℂ] targetGNS D) :
    sourceGNS D →L[ℂ] sourceGNS D :=
  ((gnsUnitaryCLE D).symm : targetGNS D →L[ℂ] sourceGNS D).comp
    (T.comp (gnsUnitaryCLE D : sourceGNS D →L[ℂ] targetGNS D))

@[simp]
theorem gnsConj_apply (T : sourceGNS D →L[ℂ] sourceGNS D) (y : targetGNS D) :
    gnsConj D T y = gnsUnitary D (T ((gnsUnitary D).symm y)) := rfl

@[simp]
theorem gnsConjSymm_apply (T : targetGNS D →L[ℂ] targetGNS D) (x : sourceGNS D) :
    gnsConjSymm D T x = (gnsUnitary D).symm (T (gnsUnitary D x)) := rfl

@[simp]
theorem gnsConjSymm_gnsConj (T : sourceGNS D →L[ℂ] sourceGNS D) :
    gnsConjSymm D (gnsConj D T) = T := by
  ext x
  simp

@[simp]
theorem gnsConj_gnsConjSymm (T : targetGNS D →L[ℂ] targetGNS D) :
    gnsConj D (gnsConjSymm D T) = T := by
  ext y
  simp

theorem gnsConj_add (S T : sourceGNS D →L[ℂ] sourceGNS D) :
    gnsConj D (S + T) = gnsConj D S + gnsConj D T := by
  ext x
  simp

theorem gnsConj_mul (S T : sourceGNS D →L[ℂ] sourceGNS D) :
    gnsConj D (S * T) = gnsConj D S * gnsConj D T := by
  ext x
  simp

theorem gnsConj_one : gnsConj D 1 = 1 := by
  ext x
  simp

theorem gnsConj_smul (r : ℂ) (T : sourceGNS D →L[ℂ] sourceGNS D) :
    gnsConj D (r • T) = r • gnsConj D T := by
  ext x
  simp

/-- Conjugation by the GNS unitary commutes with the adjoint operation: since
`U` is unitary, `(U T U⁻¹)^* = U T^* U⁻¹`. -/
theorem gnsConj_star (T : sourceGNS D →L[ℂ] sourceGNS D) :
    gnsConj D (star T) = star (gnsConj D T) := by
  rw [ContinuousLinearMap.star_eq_adjoint (gnsConj D T),
    ContinuousLinearMap.eq_adjoint_iff]
  intro y z
  rw [gnsConj_apply, gnsConj_apply, (gnsUnitary D).inner_map_eq_flip]
  conv_rhs => rw [← LinearIsometryEquiv.apply_symm_apply (gnsUnitary D) y]
  rw [(gnsUnitary D).inner_map_map, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

/-- Conjugation by the GNS unitary, packaged as a `ℂ`-algebra equivalence
between the bounded operators on the two GNS Hilbert spaces. -/
noncomputable def gnsConjAlgEquiv :
    (sourceGNS D →L[ℂ] sourceGNS D) ≃ₐ[ℂ] (targetGNS D →L[ℂ] targetGNS D) where
  toFun := gnsConj D
  invFun := gnsConjSymm D
  left_inv := gnsConjSymm_gnsConj D
  right_inv := gnsConj_gnsConjSymm D
  map_mul' := gnsConj_mul D
  map_add' := gnsConj_add D
  commutes' := by
    intro r
    ext x
    simp [Algebra.algebraMap_eq_smul_one]

@[simp]
theorem gnsConjAlgEquiv_apply (T : sourceGNS D →L[ℂ] sourceGNS D) :
    gnsConjAlgEquiv D T = gnsConj D T := rfl

@[simp]
theorem gnsConjAlgEquiv_symm_apply (T : targetGNS D →L[ℂ] targetGNS D) :
    (gnsConjAlgEquiv D).symm T = gnsConjSymm D T := rfl

/-- Conjugation by the GNS unitary, packaged as a `ℂ`-star-algebra equivalence
between the bounded operators on the two GNS Hilbert spaces. -/
noncomputable def gnsConjStarAlgEquiv :
    (sourceGNS D →L[ℂ] sourceGNS D) ≃⋆ₐ[ℂ] (targetGNS D →L[ℂ] targetGNS D) where
  toFun := gnsConj D
  invFun := gnsConjSymm D
  left_inv := gnsConjSymm_gnsConj D
  right_inv := gnsConj_gnsConjSymm D
  map_mul' := gnsConj_mul D
  map_add' := gnsConj_add D
  map_smul' := gnsConj_smul D
  map_star' := gnsConj_star D

@[simp]
theorem gnsConjStarAlgEquiv_apply (T : sourceGNS D →L[ℂ] sourceGNS D) :
    gnsConjStarAlgEquiv D T = gnsConj D T := rfl

@[simp]
theorem gnsConjStarAlgEquiv_symm_apply (T : targetGNS D →L[ℂ] targetGNS D) :
    (gnsConjStarAlgEquiv D).symm T = gnsConjSymm D T := rfl

/-! ### Conjugation of the GNS representations -/

/-- **Conjugation of the representations.**  Conjugation by the GNS unitary
carries the source GNS representative of `a` to the target GNS representative of
`D.equivalence a`. -/
theorem gnsConj_sourceGNSRepresentation (a : D.source) :
    gnsConj D (sourceGNSRepresentation D a) = targetGNSRepresentation D (D.equivalence a) := by
  ext y
  rw [gnsConj_apply, gnsUnitary_intertwines D a ((gnsUnitary D).symm y),
    LinearIsometryEquiv.apply_symm_apply]

/-- The inverse-direction form: conjugating back the target GNS representative
of `b` gives the source GNS representative of `D.equivalence.symm b`. -/
theorem gnsConjSymm_targetGNSRepresentation (b : D.target) :
    gnsConjSymm D (targetGNSRepresentation D b) =
      sourceGNSRepresentation D (D.equivalence.symm b) := by
  have h := gnsConj_sourceGNSRepresentation D (D.equivalence.symm b)
  rw [StarAlgEquiv.apply_symm_apply] at h
  rw [← h, gnsConjSymm_gnsConj]

/-- Conjugation carries the range of the source GNS representation onto the
range of the target GNS representation. -/
theorem gnsConj_range :
    gnsConj D '' Set.range (sourceGNSRepresentation D) =
      Set.range (targetGNSRepresentation D) := by
  ext T
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨D.equivalence a, (gnsConj_sourceGNSRepresentation D a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨sourceGNSRepresentation D (D.equivalence.symm b), ⟨_, rfl⟩, ?_⟩
    rw [gnsConj_sourceGNSRepresentation, StarAlgEquiv.apply_symm_apply]

/-! ### Transport of commutation -/

/-- **The commutation transport statement.**  A bounded operator `T` on the
source GNS space commutes with every source GNS representative if and only if
its conjugate commutes with every target GNS representative. -/
theorem gnsConj_commute_iff (T : sourceGNS D →L[ℂ] sourceGNS D) :
    (∀ a : D.source, Commute T (sourceGNSRepresentation D a)) ↔
      ∀ b : D.target, Commute (gnsConj D T) (targetGNSRepresentation D b) := by
  constructor
  · intro h b
    have hb : b = D.equivalence (D.equivalence.symm b) := (D.equivalence.apply_symm_apply b).symm
    rw [hb, ← gnsConj_sourceGNSRepresentation D (D.equivalence.symm b), Commute,
      SemiconjBy, ← gnsConj_mul, ← gnsConj_mul]
    exact congrArg (gnsConj D) (h (D.equivalence.symm b))
  · intro h a
    have h' := h (D.equivalence a)
    rw [← gnsConj_sourceGNSRepresentation D a, Commute, SemiconjBy,
      ← gnsConj_mul, ← gnsConj_mul] at h'
    exact (gnsConjAlgEquiv D).injective h'

/-- Equivalent formulation of the commutation transport in terms of membership
in the centralizer of the range of each representation. -/
theorem gnsConj_mem_centralizer_iff (T : sourceGNS D →L[ℂ] sourceGNS D) :
    T ∈ (Set.range (sourceGNSRepresentation D)).centralizer ↔
      gnsConj D T ∈ (Set.range (targetGNSRepresentation D)).centralizer := by
  constructor
  · intro h
    rw [← gnsConj_range]
    rintro _ ⟨S, hS, rfl⟩
    rw [← gnsConj_mul, ← gnsConj_mul, h S hS]
  · intro h
    rw [← gnsConj_range] at h
    rintro S hS
    have := h (gnsConj D S) ⟨S, hS, rfl⟩
    rw [← gnsConj_mul, ← gnsConj_mul] at this
    exact (gnsConjAlgEquiv D).injective this

/-- **Commutant transport.**  Conjugation by the GNS unitary carries the
commutant (algebraic centralizer) of the source GNS representation onto the
commutant of the target GNS representation. -/
theorem gnsConj_image_centralizer :
    gnsConj D '' (Set.range (sourceGNSRepresentation D)).centralizer =
      (Set.range (targetGNSRepresentation D)).centralizer := by
  rw [show (gnsConj D) = ((gnsConjAlgEquiv D : _ ≃* _) : _ → _) from rfl,
    image_centralizer_of_mulEquiv, ← show (gnsConj D) = ((gnsConjAlgEquiv D : _ ≃* _) : _ → _)
      from rfl, gnsConj_range]

/-- **Bicommutant transport.**  Conjugation by the GNS unitary carries the
two-fold commutant (algebraic double centralizer) of the source GNS
representation onto the two-fold commutant of the target GNS representation. -/
theorem gnsConj_image_centralizer_centralizer :
    gnsConj D '' (Set.range (sourceGNSRepresentation D)).centralizer.centralizer =
      (Set.range (targetGNSRepresentation D)).centralizer.centralizer := by
  rw [show (gnsConj D) = ((gnsConjAlgEquiv D : _ ≃* _) : _ → _) from rfl,
    image_centralizer_of_mulEquiv, ← show (gnsConj D) = ((gnsConjAlgEquiv D : _ ≃* _) : _ → _)
      from rfl, gnsConj_image_centralizer]

/-- Summary of this step: conjugation by the GNS unitary is an algebra
equivalence of the two bounded-operator algebras, it carries the source GNS
representation to the target GNS representation along the supplied equivalence,
and it transports commutation, commutants and bicommutants (in the algebraic
`Set.centralizer` sense). -/
theorem gnsConj_package :
    (∀ T : sourceGNS D →L[ℂ] sourceGNS D, gnsConjSymm D (gnsConj D T) = T) ∧
      (∀ T : targetGNS D →L[ℂ] targetGNS D, gnsConj D (gnsConjSymm D T) = T) ∧
      (∀ T : sourceGNS D →L[ℂ] sourceGNS D, gnsConj D (star T) = star (gnsConj D T)) ∧
      (∀ a : D.source,
        gnsConj D (sourceGNSRepresentation D a) =
          targetGNSRepresentation D (D.equivalence a)) ∧
      gnsConj D '' Set.range (sourceGNSRepresentation D) =
        Set.range (targetGNSRepresentation D) ∧
      (∀ T : sourceGNS D →L[ℂ] sourceGNS D,
        (∀ a : D.source, Commute T (sourceGNSRepresentation D a)) ↔
          ∀ b : D.target, Commute (gnsConj D T) (targetGNSRepresentation D b)) ∧
      gnsConj D '' (Set.range (sourceGNSRepresentation D)).centralizer =
        (Set.range (targetGNSRepresentation D)).centralizer ∧
      gnsConj D '' (Set.range (sourceGNSRepresentation D)).centralizer.centralizer =
        (Set.range (targetGNSRepresentation D)).centralizer.centralizer :=
  ⟨gnsConjSymm_gnsConj D, gnsConj_gnsConjSymm D, gnsConj_star D, gnsConj_sourceGNSRepresentation D,
    gnsConj_range D, gnsConj_commute_iff D, gnsConj_image_centralizer D,
    gnsConj_image_centralizer_centralizer D⟩

end BoundedStateGNS

end StabilizerHyperfinite
