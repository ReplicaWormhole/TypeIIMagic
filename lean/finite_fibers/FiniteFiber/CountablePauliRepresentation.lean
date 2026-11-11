import FiniteFiber.FiniteStabilizerStateChain
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Group.Measure

/-!
# A concrete countable Pauli configuration representation

This module begins the countable-lattice realization missing from the finite
ordered-qubit chain.  The configuration space is the additive group of
finitely supported binary configurations on `ℕ`, equipped with counting
measure.  Its `L²` space carries:

* translations by finite configurations; and
* multiplication by the one-site binary phase character.

The declarations here construct genuine bounded operators and record their
almost-everywhere action.  They do not yet prove the finite/tail factorization
which identifies the finite-site Pauli image with a finite matrix algebra, nor
do they construct a quasilocal closure or a global stabilizer state.
-/

open scoped ENNReal NNReal
open MeasureTheory

namespace FiniteFiber

/-- Finitely supported binary configurations on the countable ordered lattice. -/
abbrev CountablePauliConfiguration := ℕ →₀ ZMod 2

/-- The canonical discrete sigma algebra on the countable configuration space. -/
noncomputable instance : MeasurableSpace CountablePauliConfiguration := ⊤

/-- The concrete countable configuration Hilbert space with counting measure. -/
noncomputable abbrev CountablePauliHilbert :=
  MeasureTheory.Lp ℂ 2 (Measure.count : Measure CountablePauliConfiguration)

/-- The binary configuration supported at a single lattice site. -/
noncomputable def configurationBit (i : ℕ) : CountablePauliConfiguration :=
  Finsupp.single i 1

/-- A one-site binary configuration is nonzero. -/
theorem configurationBit_ne_zero (i : ℕ) : configurationBit i ≠ 0 := by
  intro hzero
  have hvalue := congrArg (fun x : CountablePauliConfiguration => x i) hzero
  simp [configurationBit] at hvalue

/-- A one-site binary configuration has additive order two. -/
theorem configurationBit_add_self (i : ℕ) :
    configurationBit i + configurationBit i = 0 := by
  ext j
  by_cases h : j = i
  · subst h
    simp only [configurationBit, Finsupp.add_apply, Finsupp.single_eq_same]
    exact ZMod.natCast_self 2
  · simp [configurationBit, h]

/-- The initial restriction of a configuration to the coordinates `i < n`. -/
def configurationInitial (n : ℕ) :
    CountablePauliConfiguration →+ CountablePauliConfiguration :=
  Finsupp.filterAddHom fun i => i < n

/-- The tail restriction of a configuration to the coordinates `n ≤ i`. -/
def configurationTail (n : ℕ) :
    CountablePauliConfiguration →+ CountablePauliConfiguration :=
  Finsupp.filterAddHom fun i => n ≤ i

/-- The initial and tail restrictions recompose the original configuration. -/
theorem configurationInitial_add_configurationTail
    (n : ℕ) (x : CountablePauliConfiguration) :
    configurationInitial n x + configurationTail n x = x := by
  simpa only [configurationInitial, configurationTail, Finsupp.filterAddHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Nat.not_lt] using
    Finsupp.filter_pos_add_filter_neg x (fun i => i < n)

/-- The initial restriction vanishes at coordinates beyond the cut. -/
theorem configurationInitial_apply_of_le
    (n : ℕ) (x : CountablePauliConfiguration) (i : ℕ) (h : n ≤ i) :
    configurationInitial n x i = 0 := by
  show (x.filter fun i => i < n) i = 0
  exact Finsupp.filter_apply_neg _ _ (Nat.not_lt.mpr h)

/-- The tail restriction vanishes at coordinates before the cut. -/
theorem configurationTail_apply_of_lt
    (n : ℕ) (x : CountablePauliConfiguration) (i : ℕ) (h : i < n) :
    configurationTail n x i = 0 := by
  show (x.filter fun i => n ≤ i) i = 0
  exact Finsupp.filter_apply_neg _ _ (Nat.not_le.mpr h)

/-- The initial restriction fixes a one-site generator before the cut. -/
theorem configurationInitial_bit_of_lt (n i : ℕ) (h : i < n) :
    configurationInitial n (configurationBit i) = configurationBit i := by
  show ((configurationBit i).filter fun j => j < n) = configurationBit i
  exact Finsupp.filter_single_of_pos _ h

/-- The tail restriction fixes a one-site generator at or beyond the cut. -/
theorem configurationTail_bit_of_le (n i : ℕ) (h : n ≤ i) :
    configurationTail n (configurationBit i) = configurationBit i := by
  show ((configurationBit i).filter fun j => n ≤ j) = configurationBit i
  exact Finsupp.filter_single_of_pos _ h

/-- Every binary residue is either zero or one. -/
theorem zmod2_eq_zero_or_eq_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> simp

/-- Translation by a finite configuration as a bounded operator on `L²`. -/
noncomputable def configurationShift
    (g : CountablePauliConfiguration) :
    CountablePauliHilbert →L[ℂ] CountablePauliHilbert :=
  (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ (fun x => g + x)
    (MeasureTheory.measurePreserving_add_left
      (Measure.count : Measure CountablePauliConfiguration) g)).toContinuousLinearMap

/-- The local bit-flip generator in the concrete countable representation. -/
noncomputable def countablePauliX (i : ℕ) :
    CountablePauliHilbert →L[ℂ] CountablePauliHilbert :=
  configurationShift (configurationBit i)

/-- Translation preserves the `L²` norm exactly. -/
theorem configurationShift_norm
    (g : CountablePauliConfiguration) (f : CountablePauliHilbert) :
    ‖configurationShift g f‖ = ‖f‖ := by
  change ‖(MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ (fun x => g + x)
    (MeasureTheory.measurePreserving_add_left
      (Measure.count : Measure CountablePauliConfiguration) g)) f‖ = ‖f‖
  exact (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ (fun x => g + x)
    (MeasureTheory.measurePreserving_add_left
      (Measure.count : Measure CountablePauliConfiguration) g)).norm_map f

/-- The concrete translation formula for `configurationShift`. -/
theorem configurationShift_apply_ae
    (g : CountablePauliConfiguration) (f : CountablePauliHilbert) :
    configurationShift g f =ᵐ[Measure.count] fun x => f (g + x) := by
  exact MeasureTheory.Lp.coeFn_compMeasurePreserving f
    (MeasureTheory.measurePreserving_add_left
      (Measure.count : Measure CountablePauliConfiguration) g)

/-- Almost-everywhere identities may be pulled back along a translation. -/
private theorem ae_comp_add_left
    (h : CountablePauliConfiguration) {u v : CountablePauliConfiguration → ℂ}
    (huv : u =ᵐ[Measure.count] v) :
    (fun x => u (h + x)) =ᵐ[Measure.count] fun x => v (h + x) :=
  (MeasureTheory.measurePreserving_add_left
      (Measure.count : Measure CountablePauliConfiguration)
      h).quasiMeasurePreserving.ae_eq_comp huv

/-- Translation by the neutral configuration acts as the identity on `L²`. -/
theorem configurationShift_zero :
    configurationShift 0 =
      ContinuousLinearMap.id ℂ CountablePauliHilbert := by
  ext f
  refine (configurationShift_apply_ae 0 f).trans ?_
  simp

/-- Translations compose in the order determined by the pullback action. -/
theorem configurationShift_add
    (g h : CountablePauliConfiguration) :
    configurationShift (g + h) =
      (configurationShift h).comp (configurationShift g) := by
  ext f
  have hleft : configurationShift (g + h) f
      =ᵐ[Measure.count] fun x => (f : CountablePauliConfiguration → ℂ) (g + h + x) :=
    configurationShift_apply_ae (g + h) f
  have hright : (configurationShift h) (configurationShift g f)
      =ᵐ[Measure.count] fun x =>
        ((configurationShift g f : CountablePauliConfiguration → ℂ)) (h + x) :=
    configurationShift_apply_ae h (configurationShift g f)
  have hpull := ae_comp_add_left
    (u := (configurationShift g f : CountablePauliConfiguration → ℂ)) h
    (configurationShift_apply_ae g f)
  simp only [ContinuousLinearMap.comp_apply]
  refine hleft.trans (Filter.EventuallyEq.trans ?_ (hright.trans hpull).symm)
  filter_upwards with x
  rw [add_assoc]

/-- A composition of two bit-flip translations is a translation by their sum. -/
private theorem countablePauliX_comp_eq_shift (i j : ℕ) :
    (countablePauliX i).comp (countablePauliX j) =
      configurationShift (configurationBit j + configurationBit i) := by
  simpa [countablePauliX] using
    (configurationShift_add (configurationBit j) (configurationBit i)).symm

/-- The countable bit-flip translation generators commute. -/
theorem countablePauliX_comm (i j : ℕ) :
    (countablePauliX i).comp (countablePauliX j) =
      (countablePauliX j).comp (countablePauliX i) := by
  rw [countablePauliX_comp_eq_shift, countablePauliX_comp_eq_shift,
    add_comm]

/-- Composing the one-site bit flip with itself is the identity operator. -/
theorem countablePauliX_comp_self (i : ℕ) :
    (countablePauliX i).comp (countablePauliX i) =
      ContinuousLinearMap.id ℂ CountablePauliHilbert := by
  have hadd := configurationShift_add (configurationBit i) (configurationBit i)
  rw [configurationBit_add_self, configurationShift_zero] at hadd
  simpa [countablePauliX] using hadd.symm

/-- The pointwise binary phase character at one lattice site. -/
def phaseCharacter (i : ℕ) (x : CountablePauliConfiguration) : ℂ :=
  if x i = 0 then 1 else -1

/-- Every one-site phase has square one. -/
theorem phaseCharacter_mul_self
    (i : ℕ) (x : CountablePauliConfiguration) :
    phaseCharacter i x * phaseCharacter i x = 1 := by
  simp only [phaseCharacter]
  split_ifs <;> norm_num

/-- Flipping the same binary site reverses its phase character. -/
theorem phaseCharacter_bit_add
    (i : ℕ) (x : CountablePauliConfiguration) :
    phaseCharacter i (configurationBit i + x) = - phaseCharacter i x := by
  rcases zmod2_eq_zero_or_eq_one (x i) with hx | hx
  · simp [phaseCharacter, Finsupp.add_apply, configurationBit, hx]
  · have htwo : (1 : ZMod 2) + 1 = 0 := by
      change (2 : ZMod 2) = 0
      exact ZMod.natCast_self 2
    simp [phaseCharacter, Finsupp.add_apply, configurationBit, hx, htwo]

/-- Flipping a distinct site leaves a one-site phase character unchanged. -/
theorem phaseCharacter_other_bit_add
    (i j : ℕ) (hij : i ≠ j) (x : CountablePauliConfiguration) :
    phaseCharacter i (configurationBit j + x) = phaseCharacter i x := by
  simp [phaseCharacter, Finsupp.add_apply, configurationBit,
    Finsupp.single_eq_of_ne hij]

/-- The phase character is a bounded `L∞` function for counting measure. -/
lemma phaseCharacter_memLp_top (i : ℕ) :
    MemLp (phaseCharacter i) ∞
      (Measure.count : Measure CountablePauliConfiguration) := by
  refine memLp_top_of_bound StronglyMeasurable.of_discrete.aestronglyMeasurable 1 ?_
  filter_upwards [] with x
  simp only [phaseCharacter]
  split_ifs <;> norm_num

/-- The local phase generator as multiplication on the countable `L²` space. -/
noncomputable def configurationPhase
    (i : ℕ) : CountablePauliHilbert →L[ℂ] CountablePauliHilbert :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL
    (Measure.count : Measure CountablePauliConfiguration) ∞ 2 2
    ((phaseCharacter_memLp_top i).toLp (phaseCharacter i))

/-- The local phase generator in the concrete countable representation. -/
noncomputable def countablePauliZ (i : ℕ) :
    CountablePauliHilbert →L[ℂ] CountablePauliHilbert :=
  configurationPhase i

/-- The concrete multiplication formula for the phase generator. -/
theorem configurationPhase_apply_ae
    (i : ℕ) (f : CountablePauliHilbert) :
    configurationPhase i f =ᵐ[Measure.count]
      fun x => phaseCharacter i x * f x := by
  change (ContinuousLinearMap.mul ℂ ℂ).holder 2
    ((phaseCharacter_memLp_top i).toLp (phaseCharacter i)) f =ᵐ[Measure.count]
      fun x => phaseCharacter i x * f x
  filter_upwards [
    ContinuousLinearMap.coeFn_holder (r := 2) (ContinuousLinearMap.mul ℂ ℂ)
      ((phaseCharacter_memLp_top i).toLp (phaseCharacter i)) f,
    (phaseCharacter_memLp_top i).coeFn_toLp
  ] with x hmul hphase
  simpa [ContinuousLinearMap.mul_apply', hphase] using hmul

/-- The one-site phase generator squares to the identity operator. -/
theorem configurationPhase_comp_self (i : ℕ) :
    (configurationPhase i).comp (configurationPhase i) =
      ContinuousLinearMap.id ℂ CountablePauliHilbert := by
  ext f
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  refine (configurationPhase_apply_ae i (configurationPhase i f)).trans ?_
  filter_upwards [configurationPhase_apply_ae i f] with x hx
  rw [hx, ← mul_assoc, phaseCharacter_mul_self, one_mul]

/-- The almost-everywhere action of a composite of two phase multipliers. -/
private theorem configurationPhase_comp_apply_ae (i j : ℕ)
    (f : CountablePauliHilbert) :
    (configurationPhase i).comp (configurationPhase j) f =ᵐ[Measure.count]
      fun x => phaseCharacter i x * (phaseCharacter j x * f x) := by
  simp only [ContinuousLinearMap.comp_apply]
  refine (configurationPhase_apply_ae i (configurationPhase j f)).trans ?_
  filter_upwards [configurationPhase_apply_ae j f] with x hx
  rw [hx]

/-- The countable one-site phase generators commute. -/
theorem countablePauliZ_comm (i j : ℕ) :
    (countablePauliZ i).comp (countablePauliZ j) =
      (countablePauliZ j).comp (countablePauliZ i) := by
  ext f
  refine (configurationPhase_comp_apply_ae i j f).trans
    (Filter.EventuallyEq.symm ?_)
  refine (configurationPhase_comp_apply_ae j i f).trans ?_
  filter_upwards with x
  ring

/-- The phase generator applied after a bit flip acts by the unshifted phase. -/
private theorem countablePauliZ_comp_countablePauliX_apply_ae
    (i j : ℕ) (f : CountablePauliHilbert) :
    ((countablePauliZ i).comp (countablePauliX j)) f =ᵐ[Measure.count]
      fun x => phaseCharacter i x * (f : CountablePauliConfiguration → ℂ)
        (configurationBit j + x) := by
  simp only [ContinuousLinearMap.comp_apply, countablePauliZ, countablePauliX]
  filter_upwards [configurationPhase_apply_ae i (configurationShift (configurationBit j) f),
    configurationShift_apply_ae (configurationBit j) f] with x h1 h2
  rw [h1, h2]

/-- The bit flip applied after the phase generator acts by the shifted phase. -/
private theorem countablePauliX_comp_countablePauliZ_apply_ae
    (i j : ℕ) (f : CountablePauliHilbert) :
    ((countablePauliX j).comp (countablePauliZ i)) f =ᵐ[Measure.count]
      fun x => phaseCharacter i (configurationBit j + x) *
        (f : CountablePauliConfiguration → ℂ) (configurationBit j + x) := by
  simp only [ContinuousLinearMap.comp_apply, countablePauliZ, countablePauliX]
  filter_upwards [configurationShift_apply_ae (configurationBit j)
      (configurationPhase i f),
    ae_comp_add_left (configurationBit j) (configurationPhase_apply_ae i f)]
    with x h1 h2
  rw [h1, h2]

/-- Same-site mixed generators anticommute. -/
theorem countablePauliZ_comp_countablePauliX_same (i : ℕ) :
    (countablePauliZ i).comp (countablePauliX i) =
      -((countablePauliX i).comp (countablePauliZ i)) := by
  ext f
  simp only [ContinuousLinearMap.neg_apply]
  refine (countablePauliZ_comp_countablePauliX_apply_ae i i f).trans ?_
  filter_upwards [Lp.coeFn_neg (((countablePauliX i).comp (countablePauliZ i)) f),
    countablePauliX_comp_countablePauliZ_apply_ae i i f] with x hneg hx
  rw [hneg, Pi.neg_apply, hx, phaseCharacter_bit_add]
  ring

/-- Mixed generators at distinct sites commute. -/
theorem countablePauliZ_comp_countablePauliX_other
    (i j : ℕ) (hij : i ≠ j) :
    (countablePauliZ i).comp (countablePauliX j) =
      (countablePauliX j).comp (countablePauliZ i) := by
  ext f
  refine (countablePauliZ_comp_countablePauliX_apply_ae i j f).trans ?_
  filter_upwards [countablePauliX_comp_countablePauliZ_apply_ae i j f] with x hx
  rw [hx, phaseCharacter_other_bit_add i j hij]

end FiniteFiber
