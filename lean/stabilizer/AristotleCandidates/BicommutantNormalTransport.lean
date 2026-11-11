import AristotleCandidates.BicommutantVonNeumannCore
import AristotleCandidates.StatePreservingGNSModel

/-!
# Bicommutant transport along the GNS unitary, and the normality boundary

**Context declaration.** Source basis: `main.tex:1970-2004` (the passage which
passes from the C⋆/GNS identification to the generated von Neumann algebras,
invokes Blackadar III.5.1.6 and Takesaki 2.12 to convert an algebraic
⋆-isomorphism of generated von Neumann algebras into quasi-equivalence, and
uses the Blackadar III.2.1.4 series representation of *normal* functionals to
compare the folia of the two representations).

This module is deliberately split into three clearly separated layers.

## Layer 1 — checked *algebraic* bicommutant facts

Purely algebraic statements about `Set.centralizer` and the bicommutant
construction `StarSubalgebra.vonNeumannGenerated` of
`AristotleCandidates.BicommutantVonNeumannCore`.  No operator topology, no
double commutant theorem.

* `image_centralizer_centralizer_of_mulEquiv` — a multiplicative equivalence
  carries a double centralizer onto the double centralizer of the image;
* `image_vonNeumannGenerated` — hence a ⋆-algebra equivalence of the bounded
  operators carrying a ⋆-subalgebra `S` onto `T` carries `S''` onto `T''`;
* `starEquivOfImageEq`, `vonNeumannGeneratedStarEquiv` — the induced ⋆-algebra
  equivalence of the two generated bicommutants.

Specialised to the P39 datum `StatePreservingGNSModel.StatePreservingData` (its
GNS unitary and the conjugation `gnsConj` it induces) this gives the
**conjugation formulas for generated bicommutants**:

* `gnsConj_image_sourceVN` : `U · U⁻¹` maps `π_ω(A)''` onto `π_ω̃(B)''`;
* `gnsConj_image_commutant` : and `π_ω(A)'` onto `π_ω̃(B)'`;
* `bicommutantStarEquiv` : the resulting ⋆-algebra equivalence
  `π_ω(A)'' ≃⋆ₐ[ℂ] π_ω̃(B)''`, with `bicommutantStarEquiv_sourceRepVN`
  showing it implements the manuscript's `π_ω(a) ↦ π_ω̃(α(a))`.

## Layer 2 — checked *analytic* transport of vector-series functionals

`IsVectorSeriesFunctional N phi` is the Blackadar III.2.1.4 shape used by the
manuscript: `phi T = ∑ₙ ⟪ξₙ, T ηₙ⟫` with `∑ₙ ‖ξₙ‖ < ∞` and `∑ₙ ‖ηₙ‖ < ∞`.
Because conjugation by a *unitary* transforms `⟪ξ, U T U⁻¹ η⟫` into
`⟪U⁻¹ξ, T U⁻¹η⟫`, this class is transported **exactly**, and this is proved
here, not assumed:

* `isVectorSeriesFunctional_comp_bicommutantStarEquiv`;
* `folium_source_eq_pullback_folium_target` — the manuscript's statement that
  the two folia (normal functionals of the generated von Neumann algebra,
  restricted to the C⋆-algebra) agree along `alphaCStar`.

## Layer 3 — the analytic statements pinned Mathlib does not provide

These are recorded as explicit `Prop`-valued **interfaces** (parameters of
conditional theorems), never as axioms:

* `DoubleCommutantStatement H` — `S'' = WOT-closure of S` in `B(H)`;
* `NormalFunctionalCharacterization N IsNormal` — Blackadar III.2.1.4, that the
  normal functionals of a von Neumann algebra are exactly the vector-series
  functionals.

The conditional results are

* `bicommutantStarEquiv_normal_of_characterization` — given only the
  characterization interface, the bicommutant ⋆-equivalence of Layer 1 is
  **normal** (both directions), i.e. a normal ⋆-isomorphism.  Normality is
  *derived* here; it is not assumed of the map;
* `bicommutant_eq_wotClosure_of_interface` — given only the double commutant
  interface, the generated bicommutants are the WOT closures of the two GNS
  images.

The manuscript's remaining citations are handled as follows.  Blackadar
III.5.1.6 and Takesaki 2.12 are used there to *obtain* quasi-equivalence from
an algebraic ⋆-isomorphism, respectively from agreement of folia.  On the route
taken here neither implication is needed: the P39 datum already supplies a
unitary intertwiner, so the algebraic form of quasi-equivalence
(`AlgebraicallyQuasiEquivalent`, a ⋆-isomorphism of the generated von Neumann
algebras intertwining the two representations along `α`) is *proved* in
`algebraicallyQuasiEquivalent`, and the agreement of the folia is *proved* in
`folium_source_eq_pullback_folium_target`.  What is genuinely missing from
pinned Mathlib, and therefore recorded as the two interfaces above, is only the
analytic identification of the algebraic bicommutant with an operator-topology
closure and of normal functionals with vector-series functionals.

Nothing beyond this is claimed: no tensor product decomposition, no
Araki–Woods classification, no trace, no factor type.
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace AristotleCandidates

namespace BicommutantNormalTransport

open StabilizerHyperfinite
open AristotleCandidates.StatePreservingGNSModel

open scoped ComplexOrder InnerProductSpace

/-! ## Layer 1a — algebraic transport of centralizers and bicommutants -/

section Algebraic

variable {A B : Type*} [Monoid A] [Monoid B]

/-- A multiplicative equivalence carries the **double** centralizer of a set onto
the double centralizer of its image.  (One application of
`BoundedStateGNS.image_centralizer_of_mulEquiv` for each centralizer.) -/
theorem image_centralizer_centralizer_of_mulEquiv (e : A ≃* B) (S : Set A) :
    e '' S.centralizer.centralizer = (e '' S).centralizer.centralizer := by
  rw [BoundedStateGNS.image_centralizer_of_mulEquiv,
    BoundedStateGNS.image_centralizer_of_mulEquiv]

end Algebraic

section Bicommutant

variable {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

/-- **The algebraic conjugation formula for generated bicommutants.**  If a
⋆-algebra equivalence `Φ` of the bounded operators carries the ⋆-subalgebra `S`
onto `T`, then it carries the generated bicommutant `S''` onto `T''`.

This is purely algebraic: `vonNeumannGenerated` is the `Set.centralizer` double
commutant, and no operator-topology closure is involved. -/
theorem image_vonNeumannGenerated
    (Φ : (H₁ →L[ℂ] H₁) ≃⋆ₐ[ℂ] (H₂ →L[ℂ] H₂))
    {S : StarSubalgebra ℂ (H₁ →L[ℂ] H₁)} {T : StarSubalgebra ℂ (H₂ →L[ℂ] H₂)}
    (h : Φ '' (S : Set (H₁ →L[ℂ] H₁)) = (T : Set (H₂ →L[ℂ] H₂))) :
    Φ '' (StarSubalgebra.vonNeumannGenerated S : Set (H₁ →L[ℂ] H₁)) =
      (StarSubalgebra.vonNeumannGenerated T : Set (H₂ →L[ℂ] H₂)) := by
  rw [StarSubalgebra.coe_vonNeumannGenerated, StarSubalgebra.coe_vonNeumannGenerated, ← h]
  exact image_centralizer_centralizer_of_mulEquiv (Φ : (H₁ →L[ℂ] H₁) ≃* (H₂ →L[ℂ] H₂)) _

/-- The commutants also correspond: `Φ '' S' = T'`. -/
theorem image_commutant
    (Φ : (H₁ →L[ℂ] H₁) ≃⋆ₐ[ℂ] (H₂ →L[ℂ] H₂))
    {S : StarSubalgebra ℂ (H₁ →L[ℂ] H₁)} {T : StarSubalgebra ℂ (H₂ →L[ℂ] H₂)}
    (h : Φ '' (S : Set (H₁ →L[ℂ] H₁)) = (T : Set (H₂ →L[ℂ] H₂))) :
    Φ '' ((StarSubalgebra.vonNeumannGenerated S).commutant : Set (H₁ →L[ℂ] H₁)) =
      ((StarSubalgebra.vonNeumannGenerated T).commutant : Set (H₂ →L[ℂ] H₂)) := by
  rw [StarSubalgebra.coe_commutant_vonNeumannGenerated,
    StarSubalgebra.coe_commutant_vonNeumannGenerated, ← h]
  exact BoundedStateGNS.image_centralizer_of_mulEquiv (Φ : (H₁ →L[ℂ] H₁) ≃* (H₂ →L[ℂ] H₂)) _

end Bicommutant

/-! ## Layer 1b — the induced equivalence of the two generated bicommutants -/

section SubalgebraEquiv

variable {A B : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]

/-- A ⋆-algebra equivalence carrying (the carrier set of) a ⋆-subalgebra `S` onto
a ⋆-subalgebra `T` restricts to a ⋆-algebra equivalence `S ≃⋆ₐ[ℂ] T`. -/
noncomputable def starEquivOfImageEq (Φ : A ≃⋆ₐ[ℂ] B)
    {S : StarSubalgebra ℂ A} {T : StarSubalgebra ℂ B}
    (h : Φ '' (S : Set A) = (T : Set B)) : S ≃⋆ₐ[ℂ] T where
  toFun x := ⟨Φ x, by rw [← SetLike.mem_coe, ← h]; exact ⟨x, x.2, rfl⟩⟩
  invFun y := ⟨Φ.symm y, by
    have hy : (y : B) ∈ Φ '' (S : Set A) := by rw [h]; exact y.2
    obtain ⟨x, hxS, hx⟩ := hy
    have : Φ.symm (y : B) = x := by rw [← hx, StarAlgEquiv.symm_apply_apply]
    rw [this]; exact hxS⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by simp)
  map_star' x := Subtype.ext (by simpa using map_star Φ (x : A))

@[simp] theorem coe_starEquivOfImageEq (Φ : A ≃⋆ₐ[ℂ] B)
    {S : StarSubalgebra ℂ A} {T : StarSubalgebra ℂ B}
    (h : Φ '' (S : Set A) = (T : Set B)) (x : S) :
    ((starEquivOfImageEq Φ h x : T) : B) = Φ (x : A) := rfl

@[simp] theorem coe_starEquivOfImageEq_symm (Φ : A ≃⋆ₐ[ℂ] B)
    {S : StarSubalgebra ℂ A} {T : StarSubalgebra ℂ B}
    (h : Φ '' (S : Set A) = (T : Set B)) (y : T) :
    (((starEquivOfImageEq Φ h).symm y : S) : A) = Φ.symm (y : B) := rfl

end SubalgebraEquiv

/-! ## Layer 2a — vector-series (Blackadar III.2.1.4 shape) functionals -/

section VectorSeries

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The shape of a normal functional used by the manuscript (Blackadar
III.2.1.4): `phi T = ∑ₙ ⟪ξₙ, T ηₙ⟫` with `∑ₙ ‖ξₙ‖ < ∞` and `∑ₙ ‖ηₙ‖ < ∞`.

This is a *definition*, not an assumption: no claim is made here that these are
exactly the normal functionals of the von Neumann algebra `N` — that
identification is the analytic interface `NormalFunctionalCharacterization` of
Layer 3. -/
def IsVectorSeriesFunctional (N : StarSubalgebra ℂ (H →L[ℂ] H)) (phi : N →ₗ[ℂ] ℂ) : Prop :=
  ∃ xi eta : ℕ → H, Summable (fun n => ‖xi n‖) ∧ Summable (fun n => ‖eta n‖) ∧
    ∀ T : N, phi T = ∑' n, ⟪xi n, (T : H →L[ℂ] H) (eta n)⟫_ℂ

/-- The vector functional `T ↦ ⟪ξ, T η⟫` of a von Neumann algebra `N`. -/
def vectorFunctional (N : StarSubalgebra ℂ (H →L[ℂ] H)) (xi eta : H) : N →ₗ[ℂ] ℂ where
  toFun T := ⟪xi, (T : H →L[ℂ] H) eta⟫_ℂ
  map_add' T S := by simp
  map_smul' c T := by simp

@[simp] theorem vectorFunctional_apply (N : StarSubalgebra ℂ (H →L[ℂ] H)) (xi eta : H) (T : N) :
    vectorFunctional N xi eta T = ⟪xi, (T : H →L[ℂ] H) eta⟫_ℂ := rfl

/-- The class is non-empty: every vector functional is a vector-series
functional (a one-term series). -/
theorem isVectorSeriesFunctional_vectorFunctional (N : StarSubalgebra ℂ (H →L[ℂ] H))
    (xi eta : H) : IsVectorSeriesFunctional N (vectorFunctional N xi eta) := by
  refine ⟨fun n => if n = 0 then xi else 0, fun n => if n = 0 then eta else 0,
    summable_of_ne_finset_zero (s := {0}) ?_, summable_of_ne_finset_zero (s := {0}) ?_, ?_⟩
  · intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [hn]
  · intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [hn]
  · intro T
    rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
    simp [vectorFunctional]

end VectorSeries

section VectorSeriesTransport

variable {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

/-- **Checked transport of vector-series functionals.**  If a ⋆-algebra
equivalence `E` of two operator ⋆-subalgebras is implemented by conjugation by a
unitary `U`, then the pullback along `E` of a vector-series functional is again
a vector-series functional, with vectors `U⁻¹ξₙ`, `U⁻¹ηₙ`.

No normality assumption is used: this is an exact computation with
`⟪ξ, U T U⁻¹ η⟫ = ⟪U⁻¹ξ, T U⁻¹η⟫`. -/
theorem isVectorSeriesFunctional_comp (U : H₁ ≃ₗᵢ[ℂ] H₂)
    {N₁ : StarSubalgebra ℂ (H₁ →L[ℂ] H₁)} {N₂ : StarSubalgebra ℂ (H₂ →L[ℂ] H₂)}
    (E : N₁ ≃⋆ₐ[ℂ] N₂)
    (hE : ∀ (T : N₁) (y : H₂), ((E T : N₂) : H₂ →L[ℂ] H₂) y = U ((T : H₁ →L[ℂ] H₁) (U.symm y)))
    (psi : N₂ →ₗ[ℂ] ℂ) (h : IsVectorSeriesFunctional N₂ psi) :
    IsVectorSeriesFunctional N₁ (psi ∘ₗ E.toAlgEquiv.toLinearMap) := by
  obtain ⟨xi, eta, hxi, heta, hpsi⟩ := h
  refine ⟨fun n => U.symm (xi n), fun n => U.symm (eta n), by simpa using hxi,
    by simpa using heta, ?_⟩
  intro T
  have hcomp : (psi ∘ₗ E.toAlgEquiv.toLinearMap) T = psi (E T) := rfl
  rw [hcomp, hpsi (E T)]
  refine tsum_congr fun n => ?_
  rw [hE T (eta n)]
  conv_lhs => rw [← U.apply_symm_apply (xi n)]
  rw [U.inner_map_map]

/-- If `E` is implemented by conjugation by `U`, then `E.symm` is implemented by
conjugation by `U.symm`. -/
theorem conj_symm_of_conj (U : H₁ ≃ₗᵢ[ℂ] H₂)
    {N₁ : StarSubalgebra ℂ (H₁ →L[ℂ] H₁)} {N₂ : StarSubalgebra ℂ (H₂ →L[ℂ] H₂)}
    (E : N₁ ≃⋆ₐ[ℂ] N₂)
    (hE : ∀ (T : N₁) (y : H₂), ((E T : N₂) : H₂ →L[ℂ] H₂) y = U ((T : H₁ →L[ℂ] H₁) (U.symm y)))
    (S : N₂) (x : H₁) :
    ((E.symm S : N₁) : H₁ →L[ℂ] H₁) x = U.symm ((S : H₂ →L[ℂ] H₂) (U.symm.symm x)) := by
  have h := hE (E.symm S) (U x)
  rw [StarAlgEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply] at h
  rw [LinearIsometryEquiv.symm_symm, h, LinearIsometryEquiv.symm_apply_apply]

end VectorSeriesTransport

/-! ## Layer 1c — the generated bicommutants of the two GNS representations -/

section GNS

variable (M : StatePreservingData)

/-- The ⋆-algebra `π_ω(A)` of operators in the image of the source GNS
representation. -/
noncomputable def sourceAlgebra : StarSubalgebra ℂ (M.sourceGNS →L[ℂ] M.sourceGNS) :=
  M.sourceGNSRepresentation.range

/-- The ⋆-algebra `π_ω̃(B)` of operators in the image of the regional GNS
representation. -/
noncomputable def targetAlgebra : StarSubalgebra ℂ (M.targetGNS →L[ℂ] M.targetGNS) :=
  M.targetGNSRepresentation.range

@[simp] theorem coe_sourceAlgebra :
    (sourceAlgebra M : Set (M.sourceGNS →L[ℂ] M.sourceGNS)) =
      Set.range M.sourceGNSRepresentation := rfl

@[simp] theorem coe_targetAlgebra :
    (targetAlgebra M : Set (M.targetGNS →L[ℂ] M.targetGNS)) =
      Set.range M.targetGNSRepresentation := rfl

/-- The **generated bicommutant** `π_ω(A)''` of the source GNS representation,
as a concrete von Neumann algebra (the algebraic double commutant). -/
noncomputable def sourceVN : VonNeumannAlgebra M.sourceGNS :=
  StarSubalgebra.vonNeumannGenerated (sourceAlgebra M)

/-- The **generated bicommutant** `π_ω̃(B)''` of the regional GNS
representation. -/
noncomputable def targetVN : VonNeumannAlgebra M.targetGNS :=
  StarSubalgebra.vonNeumannGenerated (targetAlgebra M)

theorem coe_gnsConjStarAlgEquiv : ⇑M.gnsConjStarAlgEquiv = M.gnsConj := rfl

/-- Conjugation by the GNS unitary carries `π_ω(A)` onto `π_ω̃(B)`. -/
theorem gnsConj_image_sourceAlgebra :
    ⇑M.gnsConjStarAlgEquiv '' (sourceAlgebra M : Set (M.sourceGNS →L[ℂ] M.sourceGNS)) =
      (targetAlgebra M : Set (M.targetGNS →L[ℂ] M.targetGNS)) := by
  rw [coe_gnsConjStarAlgEquiv, coe_sourceAlgebra, coe_targetAlgebra]
  exact M.gnsConj_range

/-- **The bicommutant conjugation formula.**  Conjugation by the GNS unitary
carries the generated bicommutant `π_ω(A)''` onto `π_ω̃(B)''`.  Purely
algebraic: no operator-topology closure is used. -/
theorem gnsConj_image_sourceVN :
    M.gnsConj '' (sourceVN M : Set (M.sourceGNS →L[ℂ] M.sourceGNS)) =
      (targetVN M : Set (M.targetGNS →L[ℂ] M.targetGNS)) :=
  image_vonNeumannGenerated M.gnsConjStarAlgEquiv (gnsConj_image_sourceAlgebra M)

/-- **The commutant conjugation formula.**  Conjugation by the GNS unitary
carries `π_ω(A)'` onto `π_ω̃(B)'`. -/
theorem gnsConj_image_commutant :
    M.gnsConj '' ((sourceVN M).commutant : Set (M.sourceGNS →L[ℂ] M.sourceGNS)) =
      ((targetVN M).commutant : Set (M.targetGNS →L[ℂ] M.targetGNS)) :=
  image_commutant M.gnsConjStarAlgEquiv (gnsConj_image_sourceAlgebra M)

/-- The source GNS representation, corestricted to the generated bicommutant. -/
noncomputable def sourceRepVN :
    M.toAlphaGNSData.SourceCStar →⋆ₐ[ℂ] (sourceVN M).toStarSubalgebra :=
  StarAlgHom.codRestrict M.sourceGNSRepresentation _ fun a =>
    StarSubalgebra.mem_vonNeumannGenerated_of_mem ⟨a, rfl⟩

/-- The regional GNS representation, corestricted to the generated
bicommutant. -/
noncomputable def targetRepVN :
    M.toAlphaGNSData.TargetCStar →⋆ₐ[ℂ] (targetVN M).toStarSubalgebra :=
  StarAlgHom.codRestrict M.targetGNSRepresentation _ fun b =>
    StarSubalgebra.mem_vonNeumannGenerated_of_mem ⟨b, rfl⟩

@[simp] theorem coe_sourceRepVN (a : M.toAlphaGNSData.SourceCStar) :
    ((sourceRepVN M a : (sourceVN M).toStarSubalgebra) : M.sourceGNS →L[ℂ] M.sourceGNS) =
      M.sourceGNSRepresentation a := rfl

@[simp] theorem coe_targetRepVN (b : M.toAlphaGNSData.TargetCStar) :
    ((targetRepVN M b : (targetVN M).toStarSubalgebra) : M.targetGNS →L[ℂ] M.targetGNS) =
      M.targetGNSRepresentation b := rfl

/-- **The ⋆-algebra equivalence of the generated bicommutants** induced by the
GNS unitary.  This is the algebraic content of the manuscript's step
"`π_ω(A)''` and `π_ω̃(B)''` are ⋆-isomorphic"; normality of this isomorphism is
*not* asserted here (see Layer 3). -/
noncomputable def bicommutantStarEquiv :
    (sourceVN M).toStarSubalgebra ≃⋆ₐ[ℂ] (targetVN M).toStarSubalgebra :=
  starEquivOfImageEq M.gnsConjStarAlgEquiv (gnsConj_image_sourceVN M)

@[simp] theorem coe_bicommutantStarEquiv (T : (sourceVN M).toStarSubalgebra) :
    ((bicommutantStarEquiv M T : (targetVN M).toStarSubalgebra) :
        M.targetGNS →L[ℂ] M.targetGNS) =
      M.gnsConj (T : M.sourceGNS →L[ℂ] M.sourceGNS) := rfl

@[simp] theorem coe_bicommutantStarEquiv_symm (T : (targetVN M).toStarSubalgebra) :
    (((bicommutantStarEquiv M).symm T : (sourceVN M).toStarSubalgebra) :
        M.sourceGNS →L[ℂ] M.sourceGNS) =
      M.gnsConjStarAlgEquiv.symm (T : M.targetGNS →L[ℂ] M.targetGNS) := rfl

/-- **The equivalence implements the manuscript's map** `π_ω(a) ↦ π_ω̃(α(a))`. -/
theorem bicommutantStarEquiv_sourceRepVN (a : M.toAlphaGNSData.SourceCStar) :
    bicommutantStarEquiv M (sourceRepVN M a) =
      targetRepVN M (M.toAlphaGNSData.alphaCStar a) := by
  refine Subtype.ext ?_
  rw [coe_bicommutantStarEquiv, coe_sourceRepVN, coe_targetRepVN,
    M.gnsConj_sourceGNSRepresentation]

/-! ### Quasi-equivalence in the algebraic (Blackadar III.5.1.6) sense -/

/-- The algebraic form of quasi-equivalence used by the manuscript when it cites
Blackadar III.5.1.6: a ⋆-isomorphism of the two generated von Neumann algebras
intertwining the two representations along the C⋆-level equivalence `α`.

This is the *algebraic* notion; it carries no normality/σ-weak continuity
claim, which is the separate analytic content of Layer 3. -/
def AlgebraicallyQuasiEquivalent : Prop :=
  ∃ E : (sourceVN M).toStarSubalgebra ≃⋆ₐ[ℂ] (targetVN M).toStarSubalgebra,
    ∀ a : M.toAlphaGNSData.SourceCStar,
      E (sourceRepVN M a) = targetRepVN M (M.toAlphaGNSData.alphaCStar a)

/-- **The two GNS representations are algebraically quasi-equivalent.**  Because
the P39 datum already produces a *unitary* intertwiner, this is proved outright:
no appeal to Takesaki 2.12 or Blackadar III.5.1.6 is needed on this route. -/
theorem algebraicallyQuasiEquivalent : AlgebraicallyQuasiEquivalent M :=
  ⟨bicommutantStarEquiv M, bicommutantStarEquiv_sourceRepVN M⟩

/-! ## Layer 2b — transport of vector-series functionals and of the folia -/

/-- The bicommutant equivalence is implemented by conjugation by the GNS
unitary. -/
theorem bicommutantStarEquiv_conj (T : (sourceVN M).toStarSubalgebra) (y : M.targetGNS) :
    ((bicommutantStarEquiv M T : (targetVN M).toStarSubalgebra) :
        M.targetGNS →L[ℂ] M.targetGNS) y =
      M.gnsUnitary ((T : M.sourceGNS →L[ℂ] M.sourceGNS) (M.gnsUnitary.symm y)) := rfl

/-- **Pullback of a vector-series functional** of `π_ω̃(B)''` along the
bicommutant equivalence is a vector-series functional of `π_ω(A)''`. -/
theorem isVectorSeriesFunctional_pullback
    (psi : (targetVN M).toStarSubalgebra →ₗ[ℂ] ℂ)
    (h : IsVectorSeriesFunctional (targetVN M).toStarSubalgebra psi) :
    IsVectorSeriesFunctional (sourceVN M).toStarSubalgebra
      (psi ∘ₗ (bicommutantStarEquiv M).toAlgEquiv.toLinearMap) :=
  isVectorSeriesFunctional_comp M.gnsUnitary (bicommutantStarEquiv M)
    (bicommutantStarEquiv_conj M) psi h

/-- **Pushforward of a vector-series functional** of `π_ω(A)''` along the inverse
of the bicommutant equivalence is a vector-series functional of `π_ω̃(B)''`. -/
theorem isVectorSeriesFunctional_pushforward
    (phi : (sourceVN M).toStarSubalgebra →ₗ[ℂ] ℂ)
    (h : IsVectorSeriesFunctional (sourceVN M).toStarSubalgebra phi) :
    IsVectorSeriesFunctional (targetVN M).toStarSubalgebra
      (phi ∘ₗ (bicommutantStarEquiv M).symm.toAlgEquiv.toLinearMap) :=
  isVectorSeriesFunctional_comp M.gnsUnitary.symm (bicommutantStarEquiv M).symm
    (conj_symm_of_conj M.gnsUnitary (bicommutantStarEquiv M) (bicommutantStarEquiv_conj M)) phi h

/-- The **folium** of the source GNS representation, in the manuscript's sense:
the functionals on the C⋆-algebra obtained by restricting, along `π_ω`, a
vector-series functional of the generated von Neumann algebra `π_ω(A)''`. -/
def sourceFolium : Set (M.toAlphaGNSData.SourceCStar →ₗ[ℂ] ℂ) :=
  {f | ∃ phi : (sourceVN M).toStarSubalgebra →ₗ[ℂ] ℂ,
    IsVectorSeriesFunctional (sourceVN M).toStarSubalgebra phi ∧
      ∀ a, f a = phi (sourceRepVN M a)}

/-- The **folium** of the regional GNS representation. -/
def targetFolium : Set (M.toAlphaGNSData.TargetCStar →ₗ[ℂ] ℂ) :=
  {g | ∃ psi : (targetVN M).toStarSubalgebra →ₗ[ℂ] ℂ,
    IsVectorSeriesFunctional (targetVN M).toStarSubalgebra psi ∧
      ∀ b, g b = psi (targetRepVN M b)}

/-- **The folia agree.**  A functional on the source C⋆-algebra lies in the
folium of `π_ω` if and only if it is the pullback along the C⋆-equivalence
`alphaCStar` of a functional in the folium of `π_ω̃`.

This is the manuscript's step "the two closed invariant subspaces of `P*` agree",
proved here for the explicit Blackadar III.2.1.4 vector-series class; the
identification of that class with the normal functionals is the Layer 3
interface. -/
theorem folium_source_eq_pullback_folium_target :
    sourceFolium M =
      {f : M.toAlphaGNSData.SourceCStar →ₗ[ℂ] ℂ |
        ∃ g ∈ targetFolium M, ∀ a, f a = g (M.toAlphaGNSData.alphaCStar a)} := by
  ext f
  constructor
  · rintro ⟨phi, hphi, hf⟩
    refine ⟨(phi ∘ₗ (bicommutantStarEquiv M).symm.toAlgEquiv.toLinearMap) ∘ₗ
        (targetRepVN M).toAlgHom.toLinearMap, ⟨_, isVectorSeriesFunctional_pushforward M phi hphi,
        fun b => rfl⟩, fun a => ?_⟩
    show f a = phi ((bicommutantStarEquiv M).symm (targetRepVN M (M.toAlphaGNSData.alphaCStar a)))
    rw [hf a, ← bicommutantStarEquiv_sourceRepVN M a, StarAlgEquiv.symm_apply_apply]
  · rintro ⟨g, ⟨psi, hpsi, hg⟩, hf⟩
    refine ⟨psi ∘ₗ (bicommutantStarEquiv M).toAlgEquiv.toLinearMap,
      isVectorSeriesFunctional_pullback M psi hpsi, fun a => ?_⟩
    show f a = psi (bicommutantStarEquiv M (sourceRepVN M a))
    rw [hf a, hg, bicommutantStarEquiv_sourceRepVN M a]

/-! ## Layer 3 — the analytic statements pinned Mathlib does not supply

The following are `Prop`-valued **interfaces**.  They are never assumed
globally and never axiomatized; they appear only as explicit hypotheses of the
conditional theorems below. -/

/-- **Interface: the von Neumann double commutant theorem.**  For a ⋆-subalgebra
`S` of `B(H)`, the algebraic bicommutant `S''` is the closure of `S` in the weak
operator topology.

This statement is *not* available in the pinned Mathlib (the module docstring of
`Mathlib/Analysis/VonNeumannAlgebra/Basic.lean` lists it as future work), so it
is recorded here as an interface. -/
def DoubleCommutantStatement (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Prop :=
  ∀ S : StarSubalgebra ℂ (H →L[ℂ] H),
    ⇑(ContinuousLinearMap.toWOT (RingHom.id ℂ) H H) ''
        (StarSubalgebra.vonNeumannGenerated S : Set (H →L[ℂ] H)) =
      closure (⇑(ContinuousLinearMap.toWOT (RingHom.id ℂ) H H) '' (S : Set (H →L[ℂ] H)))

/-- **Interface: Blackadar III.2.1.4.**  A supplied predicate `IsNormal` on the
functionals of a von Neumann algebra `N ⊆ B(H)` singles out exactly the
vector-series functionals. -/
def NormalFunctionalCharacterization {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (N : StarSubalgebra ℂ (H →L[ℂ] H))
    (IsNormal : (N →ₗ[ℂ] ℂ) → Prop) : Prop :=
  ∀ phi, IsNormal phi ↔ IsVectorSeriesFunctional N phi

/-- **Conditional theorem: the bicommutant ⋆-equivalence is normal.**  Assuming
only the Blackadar-style characterization of normal functionals on both sides
(the analytic input pinned Mathlib does not provide), the algebraic
⋆-equivalence `bicommutantStarEquiv` of Layer 1 is a *normal* ⋆-isomorphism:
pullback carries normal functionals to normal functionals in both directions.

Note that normality is here **derived**, not assumed of the map: the only
assumptions are about what "normal" means. -/
theorem bicommutantStarEquiv_normal_of_characterization
    (IsNormalSource : ((sourceVN M).toStarSubalgebra →ₗ[ℂ] ℂ) → Prop)
    (IsNormalTarget : ((targetVN M).toStarSubalgebra →ₗ[ℂ] ℂ) → Prop)
    (hS : NormalFunctionalCharacterization (sourceVN M).toStarSubalgebra IsNormalSource)
    (hT : NormalFunctionalCharacterization (targetVN M).toStarSubalgebra IsNormalTarget) :
    (∀ psi, IsNormalTarget psi →
        IsNormalSource (psi ∘ₗ (bicommutantStarEquiv M).toAlgEquiv.toLinearMap)) ∧
      (∀ phi, IsNormalSource phi →
        IsNormalTarget (phi ∘ₗ (bicommutantStarEquiv M).symm.toAlgEquiv.toLinearMap)) := by
  constructor
  · intro psi hpsi
    exact (hS _).2 (isVectorSeriesFunctional_pullback M psi ((hT psi).1 hpsi))
  · intro phi hphi
    exact (hT _).2 (isVectorSeriesFunctional_pushforward M phi ((hS phi).1 hphi))

/-- **Conditional theorem: identification of the bicommutants with the WOT
closures.**  Assuming the double commutant interface on both GNS Hilbert
spaces, the generated bicommutants of Layer 1 are exactly the weak-operator
closures of the two GNS images. -/
theorem bicommutant_eq_wotClosure_of_interface
    (h₁ : DoubleCommutantStatement M.sourceGNS) (h₂ : DoubleCommutantStatement M.targetGNS) :
    ⇑(ContinuousLinearMap.toWOT (RingHom.id ℂ) M.sourceGNS M.sourceGNS) ''
          (sourceVN M : Set (M.sourceGNS →L[ℂ] M.sourceGNS)) =
        closure (⇑(ContinuousLinearMap.toWOT (RingHom.id ℂ) M.sourceGNS M.sourceGNS) ''
          Set.range M.sourceGNSRepresentation) ∧
      ⇑(ContinuousLinearMap.toWOT (RingHom.id ℂ) M.targetGNS M.targetGNS) ''
          (targetVN M : Set (M.targetGNS →L[ℂ] M.targetGNS)) =
        closure (⇑(ContinuousLinearMap.toWOT (RingHom.id ℂ) M.targetGNS M.targetGNS) ''
          Set.range M.targetGNSRepresentation) :=
  ⟨h₁ (sourceAlgebra M), h₂ (targetAlgebra M)⟩

/-! ## The packaged P40 statement -/

/-- **The P40 package.**  For the P39 state-preserving datum `M`:

1. (algebraic, checked) conjugation by the GNS unitary carries the generated
   bicommutant `π_ω(A)''` onto `π_ω̃(B)''` and the commutant `π_ω(A)'` onto
   `π_ω̃(B)'`, and the induced ⋆-algebra equivalence implements
   `π_ω(a) ↦ π_ω̃(α(a))`, so the representations are algebraically
   quasi-equivalent;
2. (analytic, checked) vector-series functionals of Blackadar III.2.1.4 shape
   transport in both directions, and consequently the two folia agree along
   `alphaCStar`;
3. (analytic, conditional) with the Blackadar characterization of normal
   functionals supplied as an interface, the ⋆-equivalence is normal in both
   directions.

No double commutant theorem, quasi-equivalence theorem or tensor product
theorem is invoked. -/
theorem bicommutant_normal_transport_package :
    M.gnsConj '' (sourceVN M : Set (M.sourceGNS →L[ℂ] M.sourceGNS)) =
        (targetVN M : Set (M.targetGNS →L[ℂ] M.targetGNS)) ∧
      M.gnsConj '' ((sourceVN M).commutant : Set (M.sourceGNS →L[ℂ] M.sourceGNS)) =
        ((targetVN M).commutant : Set (M.targetGNS →L[ℂ] M.targetGNS)) ∧
      (∀ a : M.toAlphaGNSData.SourceCStar, bicommutantStarEquiv M (sourceRepVN M a) =
        targetRepVN M (M.toAlphaGNSData.alphaCStar a)) ∧
      AlgebraicallyQuasiEquivalent M ∧
      (∀ psi : (targetVN M).toStarSubalgebra →ₗ[ℂ] ℂ,
        IsVectorSeriesFunctional (targetVN M).toStarSubalgebra psi →
          IsVectorSeriesFunctional (sourceVN M).toStarSubalgebra
            (psi ∘ₗ (bicommutantStarEquiv M).toAlgEquiv.toLinearMap)) ∧
      (∀ phi : (sourceVN M).toStarSubalgebra →ₗ[ℂ] ℂ,
        IsVectorSeriesFunctional (sourceVN M).toStarSubalgebra phi →
          IsVectorSeriesFunctional (targetVN M).toStarSubalgebra
            (phi ∘ₗ (bicommutantStarEquiv M).symm.toAlgEquiv.toLinearMap)) ∧
      sourceFolium M =
        {f : M.toAlphaGNSData.SourceCStar →ₗ[ℂ] ℂ |
          ∃ g ∈ targetFolium M, ∀ a, f a = g (M.toAlphaGNSData.alphaCStar a)} :=
  ⟨gnsConj_image_sourceVN M, gnsConj_image_commutant M, bicommutantStarEquiv_sourceRepVN M,
    algebraicallyQuasiEquivalent M, isVectorSeriesFunctional_pullback M,
    isVectorSeriesFunctional_pushforward M, folium_source_eq_pullback_folium_target M⟩

end GNS

/-! ## Non-vacuity

The constructions above are parameterised by a P39 `StatePreservingData`, which
P39 shows to be inhabited by its one-stage model.  Instantiating there shows
that none of the statements above is vacuous. -/

/-- Sanity check: over P39's one-stage model the two GNS representations are
algebraically quasi-equivalent, by the theorem proved above. -/
theorem sanity_algebraicallyQuasiEquivalent :
    AlgebraicallyQuasiEquivalent opStatePreserving :=
  algebraicallyQuasiEquivalent _

end BicommutantNormalTransport

end AristotleCandidates
