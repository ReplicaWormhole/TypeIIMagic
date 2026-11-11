import FiniteFiber.FiniteRegionFullPauliMultiplication

/-!
# Full-Pauli support and finite-region locality

This file closes the gap left open by `FiniteFiber.FullPauliLattice` and
`FiniteFiber.FiniteRegionFullPauliMultiplication`: it identifies the *syntactic*
finite support of an algebraic full-Pauli word `a : FullPauliWord Site` with the
availability of a **finite-region matrix realization** of `a` inside the local
matrix algebra `finiteRegionQubitAlgebra F` of a finite region `F`.

The finite-region matrix of a word is the already checked
`fullPauliRegionMatrix F a`.  Two statements are proved.

* **Identity padding.**  If the label support of `a` lies in `F` and `F ⊆ F'`,
  then

  `finiteRegionEmbed F F' hFF' (fullPauliRegionMatrix F a) = fullPauliRegionMatrix F' a`,

  i.e. enlarging the region pads the local matrix by the identity on `F' \ F`
  (`finiteRegionEmbed_fullPauliRegionMatrix`).

* **The exact support equivalence.**  Conversely, for `F ⊆ F'` and a word whose
  support lies in `F'`, if the `F'`-matrix of `a` is in the image of
  `finiteRegionEmbed F F'` then the support of `a` already lies in `F`
  (`supportedIn_of_finiteRegionEmbed_eq`).  Combining the two directions gives
  the exact equivalence

  `a.SupportedIn F ↔ a.HasFiniteRegionRealization F`

  (`supportedIn_iff_hasFiniteRegionRealization`), where the right-hand side is
  the explicit predicate "there is a matrix `A` on the region `F` whose identity
  padding is the finite-region matrix of `a` in every larger finite region".
  The realizing matrix is unique and equals `fullPauliRegionMatrix F a`
  (`eq_fullPauliRegionMatrix_of_realization`).

Everything here is finite: the regions are `Finset`s, the algebras are finite
complex matrix algebras, and no membership in an unspecified global or
quasilocal algebra is used or claimed.  In particular there is no colimit, no
norm completion, no state, no GNS representation, no normality statement and no
von Neumann algebra.

## Supplied finite-region hypotheses

Every theorem below is stated with completely explicit finite hypotheses:

* `F F' : Finset Site` are finite regions of a site type with `DecidableEq`;
* `hFF' : F ⊆ F'` is the finite inclusion of regions used to form
  `finiteRegionEmbed F F' hFF'`;
* `a.SupportedIn F`, i.e. `a.label.support ⊆ F`, is the explicit finite support
  hypothesis of the padding theorem;
* `hsupp : a.label.support ⊆ F'` is the (necessary) hypothesis of the converse:
  without it a word supported entirely outside `F'` has `F'`-matrix a scalar
  multiple of the identity, which is trivially an identity padding.
-/

namespace FiniteFiber

open scoped BigOperators

open scoped FiniteFiber.FiniteRegionQubitMatrix

/-! ### One-site entries of the raw normal-form matrix -/

/-- The computational-basis index selected by the `X` exponent of a label. -/
def labelXBit (p : ProjectivePauliLabel) : Fin 2 := if p.1 = 0 then 0 else 1

/-- A label with trivial `X` exponent selects the basis index `0`. -/
@[simp] theorem labelXBit_of_fst_eq_zero {p : ProjectivePauliLabel} (hp : p.1 = 0) :
    labelXBit p = 0 := by
  rw [labelXBit, if_pos hp]

/-- A label with nontrivial `X` exponent selects the basis index `1`. -/
theorem labelXBit_of_fst_ne_zero {p : ProjectivePauliLabel} (hp : p.1 ≠ 0) :
    labelXBit p = 1 := by
  rw [labelXBit, if_neg hp]

/--
Every raw one-site normal-form matrix `X^x Z^z` has a nonzero entry in the
column `0`, namely in the row selected by its own `X` exponent.
-/
theorem normalFormOneSiteMatrix_labelXBit_ne_zero (p : ProjectivePauliLabel) :
    normalFormOneSiteMatrix p (labelXBit p) 0 ≠ 0 := by
  obtain ⟨x, z⟩ := p
  fin_cases x <;> fin_cases z <;>
    · norm_num [normalFormOneSiteMatrix, labelXBit, PauliLabel.matrix,
        Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_fin_two]

/-- With trivial `X` exponent the raw matrix is diagonal with `(0,0)` entry `1`. -/
theorem normalFormOneSiteMatrix_zero_zero_of_fst_eq_zero
    {p : ProjectivePauliLabel} (hp : p.1 = 0) :
    normalFormOneSiteMatrix p 0 0 = 1 := by
  obtain ⟨x, z⟩ := p
  simp only at hp
  subst hp
  fin_cases z <;>
    · norm_num [normalFormOneSiteMatrix, PauliLabel.matrix, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.one_fin_two]

/-- The raw matrix of a pure `Z` label has `(1,1)` entry `-1`. -/
theorem normalFormOneSiteMatrix_one_one_of_pure_z
    {p : ProjectivePauliLabel} (h1 : p.1 = 0) (h2 : p.2 ≠ 0) :
    normalFormOneSiteMatrix p 1 1 = -1 := by
  obtain ⟨x, z⟩ := p
  simp only at h1 h2
  subst h1
  fin_cases z
  · exact absurd rfl h2
  · norm_num [normalFormOneSiteMatrix, PauliLabel.matrix, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_fin_two]

/-! ### Explicit finite support and its finite-region matrix -/

variable {Site : Type*} [DecidableEq Site]

namespace FullPauliWord

/--
The explicit finite support predicate of a full Pauli word: every site outside
the finite region `F` carries the trivial projective label.
-/
def SupportedIn (a : FullPauliWord Site) (F : Finset Site) : Prop :=
  a.label.support ⊆ F

/-- Sitewise form of the explicit finite support predicate. -/
theorem supportedIn_iff_forall_label_eq_zero (a : FullPauliWord Site)
    (F : Finset Site) :
    a.SupportedIn F ↔ ∀ i, i ∉ F → a.label i = 0 := by
  constructor
  · intro h i hi
    exact Finsupp.notMem_support_iff.mp fun hmem => hi (h hmem)
  · intro h i hi
    by_contra hiF
    exact (Finsupp.mem_support_iff.mp hi) (h i hiF)

/-- Sitewise form of the support predicate through the canonical Pauli labels. -/
theorem supportedIn_iff_forall_localPauliLabel_eq_I (a : FullPauliWord Site)
    (F : Finset Site) :
    a.SupportedIn F ↔ ∀ i, i ∉ F → FullPauliWord.localPauliLabel a i = PauliLabel.I := by
  rw [supportedIn_iff_forall_label_eq_zero]
  refine forall_congr' fun i => forall_congr' fun _ => ?_
  rw [FullPauliWord.localPauliLabel, PauliLabel.ofProjectiveCoordinates_eq_I_iff]

/--
The explicit predicate "`a` has a finite-region matrix realization on `F`":
there is a matrix on the local algebra of `F` whose identity padding along
every finite enlargement `F ⊆ F'` is the finite-region matrix of `a` on `F'`.
-/
def HasFiniteRegionRealization (a : FullPauliWord Site) (F : Finset Site) : Prop :=
  ∃ A : finiteRegionQubitAlgebra F, ∀ (F' : Finset Site) (hFF' : F ⊆ F'),
    fullPauliRegionMatrix F' a = finiteRegionEmbed F F' hFF' A

end FullPauliWord

omit [DecidableEq Site] in
/-- The entrywise formula for the finite-region matrix of a full Pauli word. -/
theorem fullPauliRegionMatrix_apply (F : Finset Site) (a : FullPauliWord Site)
    (f g : finiteRegionBasis F) :
    fullPauliRegionMatrix F a f g =
      zmod4PhaseFactor a.phase *
        ∏ i : ↥F, normalFormOneSiteMatrix (a.label i.val) (f i) (g i) := rfl

/-- The phase factor of a full Pauli word is never zero. -/
theorem zmod4PhaseFactor_ne_zero (k : ZMod 4) : zmod4PhaseFactor k ≠ 0 :=
  pow_ne_zero _ Complex.I_ne_zero

/-! ### Identity padding of the finite-region matrix -/

/--
For a word supported in `F`, restricting its labels to a larger region `F'` is
the same as padding its `F`-labels by the trivial label on `F' \ F`.
-/
theorem restrictLabel_eq_pad_of_supportedIn
    (F F' : Finset Site) (a : FullPauliWord Site) (ha : a.SupportedIn F) :
    finiteRegionPadProjectiveLabels F F' (restrictLabel F a.label) =
      restrictLabel F' a.label := by
  classical
  funext x
  by_cases hx : x.val ∈ F
  · simp [finiteRegionPadProjectiveLabels, restrictLabel, hx]
  · have hzero : a.label x.val = 0 :=
      (FullPauliWord.supportedIn_iff_forall_label_eq_zero a F).mp ha x.val hx
    simp [finiteRegionPadProjectiveLabels, restrictLabel, hx, hzero]

/--
**Identity padding.**  For a full Pauli word whose label support lies in the
finite region `F`, the local inclusion of regions `F ⊆ F'` sends its
finite-region matrix on `F` to its finite-region matrix on `F'`: enlarging the
region pads the local matrix by the identity on `F' \ F`.
-/
theorem finiteRegionEmbed_fullPauliRegionMatrix
    (F F' : Finset Site) (hFF' : F ⊆ F') (a : FullPauliWord Site)
    (ha : a.SupportedIn F) :
    finiteRegionEmbed F F' hFF' (fullPauliRegionMatrix F a) =
      fullPauliRegionMatrix F' a := by
  rw [fullPauliRegionMatrix, map_smul, finiteRegionEmbed_normalFormMatrix,
    restrictLabel_eq_pad_of_supportedIn F F' a ha, fullPauliRegionMatrix]

/-- The inclusion of a region into itself is the identity map of its local algebra. -/
theorem finiteRegionEmbed_self (F : Finset Site)
    (A : finiteRegionQubitAlgebra F) :
    finiteRegionEmbed F F (subset_refl F) A = A := by
  classical
  ext f g
  rw [finiteRegionEmbed_apply_entry, if_pos]
  · rfl
  · intro x hx
    exact absurd x.property hx

/-! ### The converse: a local realization forces the support to be local -/

/--
**The converse locality statement.**  Let `F ⊆ F'` be finite regions and let `a`
be a full Pauli word whose label support lies in `F'`.  If the finite-region
matrix of `a` on `F'` is the identity padding of some matrix `A` on the smaller
region `F`, then the support of `a` already lies in `F`.

The hypothesis `a.label.support ⊆ F'` cannot be dropped: a word supported
entirely outside `F'` has `F'`-matrix a scalar multiple of the identity, which
is an identity padding of a matrix on `F` for trivial reasons.
-/
theorem supportedIn_of_finiteRegionEmbed_eq
    (F F' : Finset Site) (hFF' : F ⊆ F') (a : FullPauliWord Site)
    (hsupp : a.SupportedIn F') (A : finiteRegionQubitAlgebra F)
    (hA : fullPauliRegionMatrix F' a = finiteRegionEmbed F F' hFF' A) :
    a.SupportedIn F := by
  classical
  intro s hs
  by_contra hsF
  have hsF' : s ∈ F' := hsupp hs
  have hlabel_ne : a.label s ≠ 0 := Finsupp.mem_support_iff.mp hs
  set s0 : ↥F' := ⟨s, hsF'⟩ with hs0
  set f : finiteRegionBasis F' := fun i => labelXBit (a.label i.val) with hf
  set g : finiteRegionBasis F' := fun _ => 0 with hg
  -- the entrywise consequence of the assumed identity padding
  have hentry : ∀ u v : finiteRegionBasis F',
      fullPauliRegionMatrix F' a u v =
        if (∀ x : ↥F', x.val ∉ F → u x = v x) then
          A (finiteRegionRestrict F F' hFF' u) (finiteRegionRestrict F F' hFF' v)
        else 0 := by
    intro u v
    rw [hA]
    exact finiteRegionEmbed_apply_entry F F' hFF' A u v
  -- the chosen entry of the finite-region matrix is nonzero
  have hne : fullPauliRegionMatrix F' a f g ≠ 0 := by
    rw [fullPauliRegionMatrix_apply]
    refine mul_ne_zero (zmod4PhaseFactor_ne_zero _) ?_
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact normalFormOneSiteMatrix_labelXBit_ne_zero (a.label i.val)
  by_cases hagree : ∀ x : ↥F', x.val ∉ F → f x = g x
  · -- every site outside `F` has trivial `X` exponent; use the `Z` diagonal instead
    have hfs : f s0 = 0 := hagree s0 hsF
    have hx : (a.label s).1 = 0 := by
      by_contra hx
      rw [hf] at hfs
      simp only [hs0] at hfs
      rw [labelXBit_of_fst_ne_zero hx] at hfs
      exact absurd hfs (by decide)
    have hz : (a.label s).2 ≠ 0 := by
      intro hz
      exact hlabel_ne (Prod.ext hx hz)
    set f' : finiteRegionBasis F' := Function.update f s0 1 with hf'
    set g' : finiteRegionBasis F' := Function.update g s0 1 with hg'
    -- the updated configurations still agree outside `F`
    have hagree' : ∀ x : ↥F', x.val ∉ F → f' x = g' x := by
      intro x hx'
      by_cases hxs : x = s0
      · rw [hf', hg', hxs, Function.update_self, Function.update_self]
      · rw [hf', hg', Function.update_of_ne hxs, Function.update_of_ne hxs]
        exact hagree x hx'
    -- and they have the same restriction to `F`
    have hrestrict : ∀ u : finiteRegionBasis F',
        finiteRegionRestrict F F' hFF' (Function.update u s0 1) =
          finiteRegionRestrict F F' hFF' u := by
      intro u
      funext y
      have hy : (⟨y.val, hFF' y.property⟩ : ↥F') ≠ s0 := by
        intro hcon
        have hval : y.val = s := congrArg Subtype.val hcon
        exact hsF (hval ▸ y.property)
      simp only [finiteRegionRestrict]
      rw [Function.update_of_ne hy]
    -- so the two entries agree
    have heq : fullPauliRegionMatrix F' a f' g' = fullPauliRegionMatrix F' a f g := by
      rw [hentry f' g', hentry f g, if_pos hagree', if_pos hagree, hf', hg',
        hrestrict f, hrestrict g]
    -- but the pure-`Z` factor at `s` flips the sign
    have hsplit : ∀ u v : finiteRegionBasis F',
        (∏ i : ↥F', normalFormOneSiteMatrix (a.label i.val) (u i) (v i)) =
          normalFormOneSiteMatrix (a.label s) (u s0) (v s0) *
            ∏ i ∈ Finset.univ.erase s0,
              normalFormOneSiteMatrix (a.label i.val) (u i) (v i) := by
      intro u v
      exact (Finset.mul_prod_erase Finset.univ
        (fun i : ↥F' => normalFormOneSiteMatrix (a.label i.val) (u i) (v i))
        (Finset.mem_univ s0)).symm
    have hprodeq : (∏ i ∈ Finset.univ.erase s0,
          normalFormOneSiteMatrix (a.label i.val) (f' i) (g' i)) =
        ∏ i ∈ Finset.univ.erase s0,
          normalFormOneSiteMatrix (a.label i.val) (f i) (g i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hne' : i ≠ s0 := Finset.ne_of_mem_erase hi
      rw [hf', hg', Function.update_of_ne hne', Function.update_of_ne hne']
    have hgs : g s0 = 0 := rfl
    have hflip : fullPauliRegionMatrix F' a f' g' =
        - fullPauliRegionMatrix F' a f g := by
      rw [fullPauliRegionMatrix_apply, fullPauliRegionMatrix_apply,
        hsplit f' g', hsplit f g, hprodeq, hfs, hgs]
      have h1 : f' s0 = 1 := by rw [hf', Function.update_self]
      have h2 : g' s0 = 1 := by rw [hg', Function.update_self]
      rw [h1, h2, normalFormOneSiteMatrix_one_one_of_pure_z hx hz,
        normalFormOneSiteMatrix_zero_zero_of_fst_eq_zero hx]
      ring
    rw [heq] at hflip
    exact hne (by linear_combination hflip / 2)
  · -- some site outside `F` has nontrivial `X` exponent: the entry must vanish
    exact hne (by rw [hentry f g, if_neg hagree])

/-- A word supported in `F` has a finite-region matrix realization on `F`. -/
theorem hasFiniteRegionRealization_of_supportedIn
    (F : Finset Site) (a : FullPauliWord Site) (ha : a.SupportedIn F) :
    a.HasFiniteRegionRealization F :=
  ⟨fullPauliRegionMatrix F a, fun F' hFF' =>
    (finiteRegionEmbed_fullPauliRegionMatrix F F' hFF' a ha).symm⟩

/--
**The exact support equivalence.**  A full Pauli word has its explicit finite
label support inside the finite region `F` if and only if it admits a
finite-region matrix realization on `F`, i.e. a matrix on the local algebra of
`F` whose identity padding along every finite enlargement `F ⊆ F'` is the
finite-region matrix of the word on `F'`.
-/
theorem supportedIn_iff_hasFiniteRegionRealization
    (F : Finset Site) (a : FullPauliWord Site) :
    a.SupportedIn F ↔ a.HasFiniteRegionRealization F := by
  classical
  refine ⟨hasFiniteRegionRealization_of_supportedIn F a, ?_⟩
  rintro ⟨A, hA⟩
  have hFF' : F ⊆ F ∪ a.label.support := Finset.subset_union_left
  have hsupp : a.SupportedIn (F ∪ a.label.support) := Finset.subset_union_right
  exact supportedIn_of_finiteRegionEmbed_eq F (F ∪ a.label.support) hFF' a hsupp A
    (hA (F ∪ a.label.support) hFF')

/-- The realizing matrix is unique: it is the finite-region matrix of the word. -/
theorem eq_fullPauliRegionMatrix_of_realization
    (F : Finset Site) (a : FullPauliWord Site) (A : finiteRegionQubitAlgebra F)
    (hA : ∀ (F' : Finset Site) (hFF' : F ⊆ F'),
      fullPauliRegionMatrix F' a = finiteRegionEmbed F F' hFF' A) :
    A = fullPauliRegionMatrix F a := by
  have h := hA F (subset_refl F)
  rw [finiteRegionEmbed_self] at h
  exact h.symm

end FiniteFiber
