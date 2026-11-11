import AristotleCandidates.LocalHyperbolicAlgebraicAlpha
import Formalization.DyadicTensorTower
import Mathlib.Data.Matrix.Composition

/-!
# P55A — the finite-stage local-hyperbolic Pauli-to-dyadic bridge

**Context declaration: infrastructure only.**  No manuscript claim is asserted
in this module.  It constructs the finite-dimensional bridge that was missing
between the coordinate Pauli stages of P53
(`AristotleCandidates.LocalHyperbolicAlgebraicAlpha`) and the standard dyadic
matrix stages of `Formalization.DyadicTensorTower`.

## Plan alignment

* Package `P55A`, lane `H`; predecessor `P53`.
* Gate: construct the finite-stage Pauli-to-dyadic star equivalences and prove
  their norm and generator formulas.
* No direct-limit equivalence, C⋆ completion, regional alpha, state identity,
  GNS tensor split, factor classification, or trace/weight conclusion is
  claimed here.
-/

namespace StabilizerHyperfinite

namespace UHFBridge

open LocalHyperbolicAlpha

/-! ## The standard Pauli words of a finite qubit register (matrix model) -/

section RegPairing

variable {ι : Type*} [Fintype ι]

/-- Configurations of a finite qubit register: `F₂`-valued exponent vectors. -/
abbrev Reg (ι : Type*) := ι → PauliBit

/-- The `F₂` pairing of two exponent vectors. -/
def regPairing (a b : Reg ι) : PauliBit := ∑ i, a i * b i

theorem regPairing_comm (a b : Reg ι) : regPairing a b = regPairing b a := by
  simp [regPairing, mul_comm]

theorem regPairing_add_left (a a' b : Reg ι) :
    regPairing (a + a') b = regPairing a b + regPairing a' b := by
  simp [regPairing, add_mul, Finset.sum_add_distrib]

theorem regPairing_add_right (a b b' : Reg ι) :
    regPairing a (b + b') = regPairing a b + regPairing a b' := by
  simp [regPairing, mul_add, Finset.sum_add_distrib]

@[simp] theorem regPairing_zero_left (b : Reg ι) : regPairing 0 b = 0 := by
  simp [regPairing]

@[simp] theorem regPairing_zero_right (a : Reg ι) : regPairing a 0 = 0 := by
  simp [regPairing]

theorem pauliSign_mul_self (a : PauliBit) : pauliSign a * pauliSign a = 1 := by
  fin_cases a <;> simp

end RegPairing

section StdWord

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The standard Pauli word `X^a Z^b`** of a finite qubit register, in the
regular matrix model on the configuration space `Reg ι`. -/
noncomputable def stdWord (a b : Reg ι) : Matrix (Reg ι) (Reg ι) ℂ :=
  Matrix.of fun r c => if r = a + c then pauliSign (regPairing b c) else 0

omit [DecidableEq ι] in
theorem stdWord_apply (a b : Reg ι) (r c : Reg ι) :
    stdWord a b r c = if r = a + c then pauliSign (regPairing b c) else 0 := rfl

omit [DecidableEq ι] in
@[simp] theorem stdWord_zero : stdWord (0 : Reg ι) 0 = 1 := by
  ext r c
  simp [stdWord_apply, Matrix.one_apply]

/-- The Pauli multiplier of the ordered `X^a Z^b` convention. -/
theorem stdWord_mul (a b a' b' : Reg ι) :
    stdWord a b * stdWord a' b' = pauliSign (regPairing b a') • stdWord (a + a') (b + b') := by
  ext r c
  rw [Matrix.mul_apply, Finset.sum_eq_single (a' + c)]
  · rw [stdWord_apply, stdWord_apply, Matrix.smul_apply, stdWord_apply, if_pos rfl,
      ← add_assoc, regPairing_add_right, regPairing_add_left, pauliSign_add, pauliSign_add,
      smul_eq_mul]
    by_cases h : r = a + a' + c
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  · intro d _ hd
    rw [stdWord_apply (a := a'), if_neg hd, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [DecidableEq ι] in
/-- The involution phase of the ordered `X^a Z^b` convention. -/
theorem stdWord_star (a b : Reg ι) :
    star (stdWord a b) = pauliSign (regPairing a b) • stdWord a b := by
  ext r c
  rw [Matrix.star_apply, stdWord_apply, Matrix.smul_apply, stdWord_apply]
  by_cases h : r = a + c
  · have hc : c = a + r := by
      rw [h, ← add_assoc]
      simp [pauliBit_add_self_eq_zero]
    rw [if_pos hc, if_pos h, star_pauliSign, hc, regPairing_add_right, pauliSign_add,
      smul_eq_mul, regPairing_comm a b, ← mul_assoc, pauliSign_mul_self, one_mul]
  · have hc : ¬ c = a + r := by
      intro hc
      exact h (by rw [hc, ← add_assoc]; simp [pauliBit_add_self_eq_zero])
    rw [if_neg hc, if_neg h, star_zero, smul_eq_mul, mul_zero]

/-! ### The standard Pauli words are a basis -/

theorem exists_regPairing_eq_one {b : Reg ι} (hb : b ≠ 0) : ∃ c, regPairing b c = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hb
  refine ⟨Pi.single i 1, ?_⟩
  rw [regPairing, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, mul_one]
    have hb0 : b i ≠ 0 := hi
    revert hb0
    generalize b i = t
    revert t
    decide
  · intro j _ hj; rw [Pi.single_eq_of_ne hj, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Character orthogonality for the `F₂` pairing. -/
theorem sum_pauliSign_regPairing (b : Reg ι) :
    ∑ c : Reg ι, pauliSign (regPairing b c) =
      if b = 0 then (Fintype.card (Reg ι) : ℂ) else 0 := by
  by_cases hb : b = 0
  · subst hb; simp
  · rw [if_neg hb]
    obtain ⟨c0, hc0⟩ := exists_regPairing_eq_one hb
    have hshift : ∑ c : Reg ι, pauliSign (regPairing b c)
        = ∑ c : Reg ι, pauliSign (regPairing b (c + c0)) :=
      (Fintype.sum_equiv (Equiv.addRight c0) _ _ (fun _ => rfl)).symm
    have hneg : ∑ c : Reg ι, pauliSign (regPairing b (c + c0))
        = - ∑ c : Reg ι, pauliSign (regPairing b c) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro c _
      rw [regPairing_add_right, pauliSign_add, hc0, pauliSign_one, mul_neg_one]
    exact self_eq_neg.mp (hshift.trans hneg)

/-- The (unnormalized) matrix trace of a standard Pauli word. -/
theorem trace_stdWord (a b : Reg ι) :
    Matrix.trace (stdWord a b) =
      if a = 0 ∧ b = 0 then (Fintype.card (Reg ι) : ℂ) else 0 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, stdWord_apply]
  by_cases ha : a = 0
  · subst ha
    simp only [zero_add, true_and]
    rw [← sum_pauliSign_regPairing b]
    simp
  · rw [if_neg (by tauto)]
    refine Finset.sum_eq_zero ?_
    intro r _
    rw [if_neg]
    intro hr
    exact ha (by
      have h2 : a + r = 0 + r := by rw [zero_add]; exact hr.symm
      exact add_right_cancel h2)

theorem trace_stdWord_mul (a₀ b₀ a b : Reg ι) (z : ℂ) :
    Matrix.trace (stdWord a₀ b₀ * (z • stdWord a b)) =
      if a₀ + a = 0 ∧ b₀ + b = 0 then
        z * pauliSign (regPairing b₀ a) * (Fintype.card (Reg ι) : ℂ) else 0 := by
  rw [Matrix.mul_smul, stdWord_mul, smul_smul, Matrix.trace_smul, trace_stdWord, smul_eq_mul]
  split_ifs with h
  · ring
  · rw [mul_zero]

theorem stdWord_linearIndependent :
    LinearIndependent ℂ (fun p : Reg ι × Reg ι => stdWord p.1 p.2) := by
  rw [Fintype.linearIndependent_iff]
  rintro g hg ⟨a₀, b₀⟩
  have h0 : Matrix.trace (stdWord a₀ b₀ * ∑ p : Reg ι × Reg ι, g p • stdWord p.1 p.2) = 0 := by
    rw [hg, mul_zero, Matrix.trace_zero]
  rw [Finset.mul_sum, Matrix.trace_sum, Finset.sum_eq_single (a₀, b₀)] at h0
  · rw [trace_stdWord_mul] at h0
    rw [if_pos ⟨by simp [pauliBit_add_self_eq_zero], by simp [pauliBit_add_self_eq_zero]⟩] at h0
    have hcard : (Fintype.card (Reg ι) : ℂ) ≠ 0 :=
      (Nat.cast_ne_zero (R := ℂ)).mpr Fintype.card_ne_zero
    have hsign := pauliSign_ne_zero (regPairing b₀ a₀)
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact h2
      · exact absurd h2 hsign
    · exact absurd h1 hcard
  · rintro ⟨a, b⟩ _ hne
    rw [trace_stdWord_mul, if_neg]
    rintro ⟨h1, h2⟩
    refine hne (Prod.ext ?_ ?_)
    · have h3 : a₀ + (a₀ + a) = a₀ + 0 := by rw [h1]
      simpa [← add_assoc, pauliBit_add_self_eq_zero] using h3
    · have h3 : b₀ + (b₀ + b) = b₀ + 0 := by rw [h2]
      simpa [← add_assoc, pauliBit_add_self_eq_zero] using h3
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The standard Pauli words form a complex basis** of the matrix model. -/
noncomputable def stdWordBasis :
    Module.Basis (Reg ι × Reg ι) ℂ (Matrix (Reg ι) (Reg ι) ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank stdWord_linearIndependent (by
    simp [Fintype.card_prod, Module.finrank_matrix])

@[simp] theorem stdWordBasis_apply (p : Reg ι × Reg ι) :
    stdWordBasis p = stdWord p.1 p.2 := by
  rw [stdWordBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

end StdWord

/-! ## Bilinear identities for Pauli label forms -/

section Form

variable {V : Type*} [AddCommGroup V]

theorem form_sum_left (B : PauliForm V) {κ : Type*} (s : Finset κ) (f : κ → V) (w : V) :
    B.form (∑ i ∈ s, f i) w = ∑ i ∈ s, B.form (f i) w := by
  classical
  induction s using Finset.induction with
  | empty => simp [B.zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, B.add_left, ih]

theorem form_sum_right (B : PauliForm V) {κ : Type*} (s : Finset κ) (v : V) (f : κ → V) :
    B.form v (∑ i ∈ s, f i) = ∑ i ∈ s, B.form v (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [B.zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, B.add_right, ih]

variable [Module PauliBit V]

theorem form_smul_left (B : PauliForm V) (c : PauliBit) (v w : V) :
    B.form (c • v) w = c * B.form v w := by
  fin_cases c
  · simp [B.zero_left]
  · simp

theorem form_smul_right (B : PauliForm V) (c : PauliBit) (v w : V) :
    B.form v (c • w) = c * B.form v w := by
  fin_cases c
  · simp [B.zero_right]
  · simp

end Form

/-! ## Matrix star equivalences used by the dyadic tower -/

section MatrixEquivs

variable {R S : Type*} [Semiring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
variable [Semiring S] [Algebra ℂ S] [StarRing S] [StarModule ℂ S]

/-- Entrywise application of a star equivalence to matrices. -/
def matrixMapStarEquiv (m : Type*) [Fintype m] [DecidableEq m] (φ : R ≃⋆ₐ[ℂ] S) :
    Matrix m m R ≃⋆ₐ[ℂ] Matrix m m S :=
  StarAlgEquiv.ofAlgEquiv (AlgEquiv.mapMatrix φ.toAlgEquiv) (by
    intro M
    ext i j
    simp [AlgEquiv.mapMatrix_apply, Matrix.star_apply, Matrix.map_apply, map_star])

omit [StarModule ℂ R] [StarModule ℂ S] in
@[simp] theorem matrixMapStarEquiv_apply (m : Type*) [Fintype m] [DecidableEq m]
    (φ : R ≃⋆ₐ[ℂ] S) (M : Matrix m m R) (i j : m) :
    matrixMapStarEquiv m φ M i j = φ (M i j) := rfl

/-- Reindexing matrices along an equivalence of index types. -/
def matrixReindexStarEquiv {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]
    (e : m ≃ p) : Matrix m m R ≃⋆ₐ[ℂ] Matrix p p R :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ R e) (by
    intro M
    ext i j
    simp [Matrix.reindexAlgEquiv, Matrix.reindex_apply, Matrix.star_apply,
      Matrix.submatrix_apply])

omit [StarModule ℂ R] in
@[simp] theorem matrixReindexStarEquiv_apply {m p : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] (e : m ≃ p) (M : Matrix m m R) (i j : p) :
    matrixReindexStarEquiv (R := R) e M i j = M (e.symm i) (e.symm j) := rfl

/-- Matrices over matrices, as matrices over the product index type. -/
def matrixCompStarEquiv (m p : Type*) [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p] :
    Matrix m m (Matrix p p R) ≃⋆ₐ[ℂ] Matrix (m × p) (m × p) R :=
  StarAlgEquiv.ofAlgEquiv (Matrix.compAlgEquiv m p R ℂ) (by
    intro M
    ext i j
    simp [Matrix.compAlgEquiv, Matrix.comp, Matrix.star_apply])

omit [StarModule ℂ R] in
@[simp] theorem matrixCompStarEquiv_apply (m p : Type*) [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] (M : Matrix m m (Matrix p p R)) (i j : m × p) :
    matrixCompStarEquiv (R := R) m p M i j = M i.1 j.1 i.2 j.2 := rfl

/-- A one-by-one matrix algebra is its coefficient algebra. -/
def scalarMatrixStarEquiv (m : Type*) [Unique m] [Fintype m] [DecidableEq m] :
    R ≃⋆ₐ[ℂ] Matrix m m R where
  toFun z := Matrix.of fun _ _ => z
  invFun M := M default default
  left_inv _ := rfl
  right_inv M := by
    ext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default]
    rfl
  map_add' _ _ := rfl
  map_mul' _ _ := by
    ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single default]
    · rfl
    · intro b _ hb; exact absurd (Subsingleton.elim b default) hb
    · intro h; exact absurd (Finset.mem_univ _) h
  map_smul' _ _ := rfl
  map_star' _ := by ext i j; rw [Matrix.star_apply]; rfl

omit [StarModule ℂ R] in
@[simp] theorem scalarMatrixStarEquiv_apply (m : Type*) [Unique m] [Fintype m] [DecidableEq m]
    (z : R) (i j : m) : scalarMatrixStarEquiv m z i j = z := rfl

end MatrixEquivs

/-! ## The dyadic tower in the standard register model -/

/-- The two-element matrix index of a qubit, read as a Pauli bit. -/
def bitEquiv : Fin 2 ≃ PauliBit where
  toFun i := (i.val : ZMod 2)
  invFun b := ⟨b.val, b.val_lt⟩
  left_inv := by decide
  right_inv := by decide

/-- Splitting off the first qubit of a register. -/
def regSuccEquiv (k : ℕ) : Fin 2 × Reg (Fin k) ≃ Reg (Fin (k + 1)) :=
  (bitEquiv.prodCongr (Equiv.refl (Reg (Fin k)))).trans (Fin.consEquiv fun _ => PauliBit)

theorem regSuccEquiv_symm_apply (k : ℕ) (x : Reg (Fin (k + 1))) :
    (regSuccEquiv k).symm x = (bitEquiv.symm (x 0), Fin.tail x) := rfl

/-- **The dyadic stage in the register matrix model**: the recursive
`QubitTensorPower` model of `k` qubits is the matrix algebra on the
configuration space of a `k`-qubit register. -/
noncomputable def qubitMatrixEquiv : (k : ℕ) →
    QubitTensorPower k ≃⋆ₐ[ℂ] Matrix (Reg (Fin k)) (Reg (Fin k)) ℂ
  | 0 => scalarMatrixStarEquiv (Reg (Fin 0))
  | k + 1 =>
      ((matrixMapStarEquiv (Fin 2) (qubitMatrixEquiv k)).trans
        (matrixCompStarEquiv (Fin 2) (Reg (Fin k)))).trans
        (matrixReindexStarEquiv (regSuccEquiv k))

theorem qubitMatrixEquiv_succ_apply (k : ℕ) (M : QubitTensorPower (k + 1))
    (x y : Reg (Fin (k + 1))) :
    qubitMatrixEquiv (k + 1) M x y =
      qubitMatrixEquiv k
        ((M : Matrix (Fin 2) (Fin 2) (QubitTensorPower k))
          (bitEquiv.symm (x 0)) (bitEquiv.symm (y 0))) (Fin.tail x) (Fin.tail y) := rfl

/-! ## The standard `X` and `Z` words in the recursive dyadic model -/

theorem reg_succ_add_eq_iff {k : ℕ} (a x y : Reg (Fin (k + 1))) :
    x = a + y ↔ (x 0 = a 0 + y 0 ∧ Fin.tail x = Fin.tail a + Fin.tail y) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, ht⟩
    funext i
    induction i using Fin.cases with
    | zero => exact h0
    | succ i => exact congrFun ht i

theorem reg_succ_eq_iff {k : ℕ} (x y : Reg (Fin (k + 1))) :
    x = y ↔ (x 0 = y 0 ∧ Fin.tail x = Fin.tail y) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, ht⟩
    funext i
    induction i using Fin.cases with
    | zero => exact h0
    | succ i => exact congrFun ht i

theorem regPairing_succ {k : ℕ} (b y : Reg (Fin (k + 1))) :
    regPairing b y = b 0 * y 0 + regPairing (Fin.tail b) (Fin.tail y) := by
  rw [regPairing, regPairing, Fin.sum_univ_succ]
  rfl

/-- **The standard `X`-word** `X^a` of a finite qubit register, defined by
recursion in the `QubitTensorPower` model: the first qubit is the outer matrix
factor. -/
noncomputable def qubitX : (k : ℕ) → Reg (Fin k) → QubitTensorPower k
  | 0, _ => (1 : ℂ)
  | k + 1, a =>
      (Matrix.of fun r c : Fin 2 =>
        if bitEquiv r = a 0 + bitEquiv c then qubitX k (Fin.tail a) else 0 :
          Matrix (Fin 2) (Fin 2) (QubitTensorPower k))

/-- **The standard `Z`-word** `Z^b` of a finite qubit register, defined by
recursion in the `QubitTensorPower` model. -/
noncomputable def qubitZ : (k : ℕ) → Reg (Fin k) → QubitTensorPower k
  | 0, _ => (1 : ℂ)
  | k + 1, b =>
      (Matrix.of fun r c : Fin 2 =>
        if r = c then pauliSign (b 0 * bitEquiv c) • qubitZ k (Fin.tail b) else 0 :
          Matrix (Fin 2) (Fin 2) (QubitTensorPower k))

/-- The register model identifies the recursive `X`-word with `X^a Z^0`. -/
theorem qubitMatrixEquiv_qubitX : ∀ (k : ℕ) (a : Reg (Fin k)),
    qubitMatrixEquiv k (qubitX k a) = stdWord a 0
  | 0, a => by
    ext x y
    show (scalarMatrixStarEquiv (Reg (Fin 0)) (1 : ℂ)) x y = _
    rw [scalarMatrixStarEquiv_apply, stdWord_apply, if_pos (Subsingleton.elim _ _),
      regPairing_zero_left, pauliSign_zero]
  | k + 1, a => by
    ext x y
    rw [qubitMatrixEquiv_succ_apply, stdWord_apply]
    show qubitMatrixEquiv k (if bitEquiv (bitEquiv.symm (x 0)) = a 0 + bitEquiv (bitEquiv.symm (y 0))
        then qubitX k (Fin.tail a) else 0) (Fin.tail x) (Fin.tail y) = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    by_cases h0 : x 0 = a 0 + y 0
    · rw [if_pos h0, qubitMatrixEquiv_qubitX k (Fin.tail a), stdWord_apply]
      by_cases ht : Fin.tail x = Fin.tail a + Fin.tail y
      · rw [if_pos ht, if_pos ((reg_succ_add_eq_iff a x y).2 ⟨h0, ht⟩),
          regPairing_zero_left, regPairing_zero_left]
      · rw [if_neg ht, if_neg (fun h => ht ((reg_succ_add_eq_iff a x y).1 h).2)]
    · rw [if_neg h0, map_zero, if_neg (fun h => h0 ((reg_succ_add_eq_iff a x y).1 h).1)]
      rfl

/-- The register model identifies the recursive `Z`-word with `X^0 Z^b`. -/
theorem qubitMatrixEquiv_qubitZ : ∀ (k : ℕ) (b : Reg (Fin k)),
    qubitMatrixEquiv k (qubitZ k b) = stdWord 0 b
  | 0, b => by
    ext x y
    show (scalarMatrixStarEquiv (Reg (Fin 0)) (1 : ℂ)) x y = _
    rw [scalarMatrixStarEquiv_apply, stdWord_apply, if_pos (Subsingleton.elim _ _)]
    simp [regPairing]
  | k + 1, b => by
    ext x y
    rw [qubitMatrixEquiv_succ_apply, stdWord_apply]
    show qubitMatrixEquiv k (if bitEquiv.symm (x 0) = bitEquiv.symm (y 0)
        then pauliSign (b 0 * bitEquiv (bitEquiv.symm (y 0))) • qubitZ k (Fin.tail b) else 0)
        (Fin.tail x) (Fin.tail y) = _
    rw [Equiv.apply_symm_apply, show (0 : Reg (Fin (k + 1))) + y = y from zero_add y]
    by_cases h0 : x 0 = y 0
    · rw [if_pos (by rw [h0]), map_smul, qubitMatrixEquiv_qubitZ k (Fin.tail b),
        Matrix.smul_apply, stdWord_apply, smul_eq_mul]
      by_cases ht : Fin.tail x = Fin.tail y
      · rw [if_pos (show Fin.tail x = 0 + Fin.tail y by rw [zero_add]; exact ht),
          if_pos ((reg_succ_eq_iff x y).2 ⟨h0, ht⟩), regPairing_succ, pauliSign_add]
      · rw [if_neg (show ¬ Fin.tail x = 0 + Fin.tail y by rw [zero_add]; exact ht),
          if_neg (fun h => ht ((reg_succ_eq_iff x y).1 h).2), mul_zero]
    · rw [if_neg (fun h => h0 (bitEquiv.symm.injective h)), map_zero,
        if_neg (fun h => h0 ((reg_succ_eq_iff x y).1 h).1)]
      rfl

/-- **The standard Pauli word** `X^a Z^b` of a finite qubit register. -/
noncomputable def qubitWord (k : ℕ) (a b : Reg (Fin k)) : QubitTensorPower k :=
  qubitX k a * qubitZ k b

theorem qubitMatrixEquiv_qubitWord (k : ℕ) (a b : Reg (Fin k)) :
    qubitMatrixEquiv k (qubitWord k a b) = stdWord a b := by
  rw [qubitWord, map_mul, qubitMatrixEquiv_qubitX, qubitMatrixEquiv_qubitZ, stdWord_mul,
    regPairing_zero_left, pauliSign_zero, one_smul, add_zero, zero_add]

theorem qubitMatrixEquiv_injective (k : ℕ) :
    Function.Injective (fun x : QubitTensorPower k => qubitMatrixEquiv k x) := by
  intro x y h
  have h2 := congrArg (qubitMatrixEquiv k).symm h
  simpa using h2

@[simp] theorem qubitX_zero (k : ℕ) : qubitX k 0 = 1 := by
  refine qubitMatrixEquiv_injective k ?_
  dsimp only
  rw [qubitMatrixEquiv_qubitX, map_one, stdWord_zero]

@[simp] theorem qubitZ_zero (k : ℕ) : qubitZ k 0 = 1 := by
  refine qubitMatrixEquiv_injective k ?_
  dsimp only
  rw [qubitMatrixEquiv_qubitZ, map_one, stdWord_zero]

theorem qubitX_mul (k : ℕ) (a a' : Reg (Fin k)) :
    qubitX k a * qubitX k a' = qubitX k (a + a') := by
  refine qubitMatrixEquiv_injective k ?_
  dsimp only
  rw [map_mul, qubitMatrixEquiv_qubitX, qubitMatrixEquiv_qubitX, qubitMatrixEquiv_qubitX,
    stdWord_mul, regPairing_zero_left, pauliSign_zero, one_smul, add_zero]

theorem qubitZ_mul (k : ℕ) (b b' : Reg (Fin k)) :
    qubitZ k b * qubitZ k b' = qubitZ k (b + b') := by
  refine qubitMatrixEquiv_injective k ?_
  dsimp only
  rw [map_mul, qubitMatrixEquiv_qubitZ, qubitMatrixEquiv_qubitZ, qubitMatrixEquiv_qubitZ,
    stdWord_mul, regPairing_zero_right, pauliSign_zero, one_smul, add_zero]

/-- **The Pauli commutation relation** in the recursive dyadic model. -/
theorem qubitZ_mul_qubitX (k : ℕ) (a b : Reg (Fin k)) :
    qubitZ k b * qubitX k a = pauliSign (regPairing b a) • qubitWord k a b := by
  refine qubitMatrixEquiv_injective k ?_
  dsimp only
  rw [map_mul, map_smul, qubitMatrixEquiv_qubitZ, qubitMatrixEquiv_qubitX,
    qubitMatrixEquiv_qubitWord, stdWord_mul, add_zero, zero_add]

@[simp] theorem star_qubitX (k : ℕ) (a : Reg (Fin k)) : star (qubitX k a) = qubitX k a := by
  refine qubitMatrixEquiv_injective k ?_
  dsimp only
  rw [map_star, qubitMatrixEquiv_qubitX, stdWord_star, regPairing_zero_right, pauliSign_zero,
    one_smul]

@[simp] theorem star_qubitZ (k : ℕ) (b : Reg (Fin k)) : star (qubitZ k b) = qubitZ k b := by
  refine qubitMatrixEquiv_injective k ?_
  dsimp only
  rw [map_star, qubitMatrixEquiv_qubitZ, stdWord_star, regPairing_zero_left, pauliSign_zero,
    one_smul]

/-- **The involution phase of the ordered word** `X^a Z^b`. -/
theorem star_qubitWord (k : ℕ) (a b : Reg (Fin k)) :
    star (qubitWord k a b) = pauliSign (regPairing a b) • qubitWord k a b := by
  refine qubitMatrixEquiv_injective k ?_
  dsimp only
  rw [map_star, map_smul, qubitMatrixEquiv_qubitWord, stdWord_star]

/-- **The convention-dependent fourth-root phase.**  The ordered word
`X^a Z^b` is self-adjoint exactly up to the sign `(-1)^{a·b}`; multiplying it by
the fourth root of unity `i^{a·b}` produces the self-adjoint normalization. -/
theorem star_fourthRoot_smul_qubitWord (k : ℕ) (a b : Reg (Fin k)) :
    star (zmodFourPhase (liftPauliBit (regPairing a b)) • qubitWord k a b) =
      zmodFourPhase (liftPauliBit (regPairing a b)) • qubitWord k a b := by
  rw [star_smul, star_qubitWord, smul_smul]
  congr 1
  have h : ∀ m : PauliBit,
      star (zmodFourPhase (liftPauliBit m)) * pauliSign m = zmodFourPhase (liftPauliBit m) := by
    intro m
    have hm : m = 0 ∨ m = 1 := by revert m; decide
    rcases hm with rfl | rfl
    · simp [zmodFourPhase, liftPauliBit]
    · rw [show liftPauliBit (1 : PauliBit) = 1 from by simp [liftPauliBit]]

      rw [show zmodFourPhase (1 : ZMod 4) = Complex.I from by
        simp [zmodFourPhase, show ((1 : ZMod 4)).val = 1 from rfl]]
      rw [pauliSign_one, Complex.star_def, Complex.conj_I]
      ring
  exact h (regPairing a b)

end UHFBridge

/-! ## The source stage of P53 in exponent-vector coordinates -/

namespace LocalHyperbolicAlpha

namespace AlphaData

open UHFBridge

variable {L I : Type*} [LinearOrder I] (A : AlphaData L I) (n : ℕ)

noncomputable instance coordFintype : Fintype (A.Coord n) := Fintype.ofFinite _

noncomputable instance coordDecEq : DecidableEq (A.Coord n) := Classical.decEq _

theorem sourceForm_z_x (i j : A.Coord n) :
    (A.sourceForm n).form (A.stageCoordBasis n (Sum.inl i)) (A.stageCoordBasis n (Sum.inr j))
      = if i = j then 1 else 0 := by
  show (coordPairing I).form ((A.stageCoordBasis n (Sum.inl i) : A.SourceLabel n) : PauliCoordinateLabels I)
      ((A.stageCoordBasis n (Sum.inr j) : A.SourceLabel n) : PauliCoordinateLabels I) = _
  rw [show ((A.stageCoordBasis n (Sum.inl i) : A.SourceLabel n) : PauliCoordinateLabels I)
        = Finsupp.single (Sum.inl (i : I)) 1 from A.stageCoordinates_z_coe n i,
    show ((A.stageCoordBasis n (Sum.inr j) : A.SourceLabel n) : PauliCoordinateLabels I)
        = Finsupp.single (Sum.inr (j : I)) 1 from A.stageCoordinates_x_coe n j]
  show (Finsupp.single (Sum.inl (i : I)) (1 : PauliBit)).sum
      (fun p c => c * Sum.elim (fun i => (Finsupp.single (Sum.inr (j : I)) (1 : PauliBit))
        (Sum.inr i)) (fun _ => (0 : PauliBit)) p) = _
  rw [Finsupp.sum_single_index (by simp)]
  simp only [Sum.elim_inl, Finsupp.single_apply, Sum.inr.injEq, one_mul]
  exact if_congr (by simp [Subtype.ext_iff, eq_comm]) rfl rfl

theorem sourceForm_z_z (i j : A.Coord n) :
    (A.sourceForm n).form (A.stageCoordBasis n (Sum.inl i))
      (A.stageCoordBasis n (Sum.inl j)) = 0 := by
  show (coordPairing I).form ((A.stageCoordBasis n (Sum.inl i) : A.SourceLabel n) : PauliCoordinateLabels I)
      ((A.stageCoordBasis n (Sum.inl j) : A.SourceLabel n) : PauliCoordinateLabels I) = _
  rw [show ((A.stageCoordBasis n (Sum.inl i) : A.SourceLabel n) : PauliCoordinateLabels I)
        = Finsupp.single (Sum.inl (i : I)) 1 from A.stageCoordinates_z_coe n i,
    show ((A.stageCoordBasis n (Sum.inl j) : A.SourceLabel n) : PauliCoordinateLabels I)
        = Finsupp.single (Sum.inl (j : I)) 1 from A.stageCoordinates_z_coe n j]
  show (Finsupp.single (Sum.inl (i : I)) (1 : PauliBit)).sum
      (fun p c => c * Sum.elim (fun i => (Finsupp.single (Sum.inl (j : I)) (1 : PauliBit))
        (Sum.inr i)) (fun _ => (0 : PauliBit)) p) = _
  rw [Finsupp.sum_single_index (by simp)]
  simp

theorem sourceForm_x_left (i : A.Coord n) (w : A.SourceLabel n) :
    (A.sourceForm n).form (A.stageCoordBasis n (Sum.inr i)) w = 0 := by
  show (coordPairing I).form ((A.stageCoordBasis n (Sum.inr i) : A.SourceLabel n) : PauliCoordinateLabels I)
      ((w : A.SourceLabel n) : PauliCoordinateLabels I) = _
  rw [show ((A.stageCoordBasis n (Sum.inr i) : A.SourceLabel n) : PauliCoordinateLabels I)
        = Finsupp.single (Sum.inr (i : I)) 1 from A.stageCoordinates_x_coe n i]
  show (Finsupp.single (Sum.inr (i : I)) (1 : PauliBit)).sum
      (fun p c => c * Sum.elim (fun i => ((w : A.SourceLabel n) : PauliCoordinateLabels I)
        (Sum.inr i)) (fun _ => (0 : PauliBit)) p) = _
  rw [Finsupp.sum_single_index (by simp)]
  simp

/-- The `Z`-exponent vector of a stage label. -/
noncomputable def zPart (v : A.SourceLabel n) : Reg (A.Coord n) :=
  fun i => (A.stageCoordBasis n).repr v (Sum.inl i)

/-- The `X`-exponent vector of a stage label. -/
noncomputable def xPart (v : A.SourceLabel n) : Reg (A.Coord n) :=
  fun i => (A.stageCoordBasis n).repr v (Sum.inr i)

/-- **The stage Pauli pairing in exponent coordinates**: the label form of the
P53 source stage is the `F₂` pairing of the `Z`-exponents of its first argument
with the `X`-exponents of its second. -/
theorem sourceForm_eq (v w : A.SourceLabel n) :
    (A.sourceForm n).form v w = regPairing (A.zPart n v) (A.xPart n w) := by
  conv_lhs => rw [← Module.Basis.sum_repr (A.stageCoordBasis n) v,
    ← Module.Basis.sum_repr (A.stageCoordBasis n) w]
  rw [form_sum_left]
  simp only [form_smul_left, form_sum_right, form_smul_right]
  rw [Fintype.sum_sum_type]
  have hx : ∀ i : A.Coord n, ∑ q : A.Coord n ⊕ A.Coord n,
      (A.stageCoordBasis n).repr w q *
        ((A.stageCoordBasis n).repr v (Sum.inr i) *
          (A.sourceForm n).form (A.stageCoordBasis n (Sum.inr i))
            (A.stageCoordBasis n q)) = 0 := by
    intro i
    refine Finset.sum_eq_zero ?_
    intro q _
    rw [A.sourceForm_x_left n i, mul_zero, mul_zero]
  simp only [hx, Finset.sum_const_zero, add_zero]
  rw [regPairing]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Fintype.sum_sum_type]
  have h1 : ∑ j : A.Coord n, (A.stageCoordBasis n).repr w (Sum.inl j) *
      ((A.stageCoordBasis n).repr v (Sum.inl i) *
        (A.sourceForm n).form (A.stageCoordBasis n (Sum.inl i))
          (A.stageCoordBasis n (Sum.inl j))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j _
    rw [A.sourceForm_z_z n i j, mul_zero, mul_zero]
  rw [h1, zero_add, Finset.sum_eq_single i]
  · rw [A.sourceForm_z_x n i i, if_pos rfl, mul_one]
    exact mul_comm _ _
  · intro j _ hj
    rw [A.sourceForm_z_x n i j, if_neg (fun h => hj h.symm), mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### The exponent-coordinate description of a stage -/

/-- Exponent coordinates of a stage label: its `X`- and `Z`-exponent vectors. -/
noncomputable def coordRepr : A.SourceLabel n ≃ₗ[PauliBit] (Reg (A.Coord n) × Reg (A.Coord n)) :=
  ((A.stageCoordBasis n).repr.trans
    ((Finsupp.linearEquivFunOnFinite PauliBit PauliBit (A.Coord n ⊕ A.Coord n)).trans
      (LinearEquiv.sumArrowLequivProdArrow (A.Coord n) (A.Coord n) PauliBit PauliBit))).trans
    (LinearEquiv.prodComm PauliBit _ _)

theorem coordRepr_apply (v : A.SourceLabel n) :
    A.coordRepr n v = (A.xPart n v, A.zPart n v) := rfl

variable {k : ℕ} (e : A.Coord n ≃ Fin k)

/-- Exponent coordinates of a stage label in the chosen enumeration of the
stage coordinate block. -/
noncomputable def enumRepr : A.SourceLabel n ≃ₗ[PauliBit] (Reg (Fin k) × Reg (Fin k)) :=
  (A.coordRepr n).trans
    ((LinearEquiv.funCongrLeft PauliBit PauliBit e.symm).prodCongr
      (LinearEquiv.funCongrLeft PauliBit PauliBit e.symm))

theorem enumRepr_apply (v : A.SourceLabel n) :
    A.enumRepr n e v = (fun j => A.xPart n v (e.symm j), fun j => A.zPart n v (e.symm j)) := rfl

theorem regPairing_congr (a b : Reg (A.Coord n)) :
    regPairing (fun j => a (e.symm j)) (fun j => b (e.symm j)) = regPairing a b := by
  rw [regPairing, regPairing]
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

/-- The stage label form in the enumerated exponent coordinates. -/
theorem sourceForm_enum (v w : A.SourceLabel n) :
    (A.sourceForm n).form v w = regPairing (A.enumRepr n e v).2 (A.enumRepr n e w).1 := by
  rw [enumRepr_apply, enumRepr_apply, A.sourceForm_eq n v w]
  exact (A.regPairing_congr n e _ _).symm

/-! ### The finite-stage Pauli-to-matrix star equivalence -/

/-- The underlying complex-linear word map of the finite-stage bridge: it sends
the P53 Pauli word of the label `v` to the standard word `X^a Z^b` whose
exponent vectors are the enumerated `X`- and `Z`-exponents of `v`. -/
noncomputable def sourceStageMatrixLinear :
    pauliAlgebra (A.sourceForm n) ≃ₗ[ℂ] Matrix (Reg (Fin k)) (Reg (Fin k)) ℂ :=
  (pauliWordBasis (A.sourceForm n)).equiv stdWordBasis (A.enumRepr n e).toEquiv

theorem sourceStageMatrixLinear_word (v : A.SourceLabel n) :
    A.sourceStageMatrixLinear n e (pauliWord (A.sourceForm n) v) =
      stdWord (A.enumRepr n e v).1 (A.enumRepr n e v).2 := by
  rw [← pauliWordBasis_apply, sourceStageMatrixLinear, Module.Basis.equiv_apply,
    stdWordBasis_apply]
  rfl

theorem sourceStageMatrixLinear_word_mul (v w : A.SourceLabel n) :
    A.sourceStageMatrixLinear n e (pauliWord (A.sourceForm n) v * pauliWord (A.sourceForm n) w) =
      A.sourceStageMatrixLinear n e (pauliWord (A.sourceForm n) v) *
        A.sourceStageMatrixLinear n e (pauliWord (A.sourceForm n) w) := by
  rw [pauliWord_mul, map_smul, sourceStageMatrixLinear_word, sourceStageMatrixLinear_word,
    sourceStageMatrixLinear_word, stdWord_mul, map_add, A.sourceForm_enum n e v w]
  rfl

theorem sourceStageMatrixLinear_mul (x y : pauliAlgebra (A.sourceForm n)) :
    A.sourceStageMatrixLinear n e (x * y) =
      A.sourceStageMatrixLinear n e x * A.sourceStageMatrixLinear n e y := by
  have hword : ∀ (v : A.SourceLabel n) (y : pauliAlgebra (A.sourceForm n)),
      A.sourceStageMatrixLinear n e (pauliWord (A.sourceForm n) v * y) =
        A.sourceStageMatrixLinear n e (pauliWord (A.sourceForm n) v) *
          A.sourceStageMatrixLinear n e y := by
    intro v y
    refine pauliAlgebra_linear_ext (A.sourceForm n)
      (((A.sourceStageMatrixLinear n e : _ →ₗ[ℂ] _)).comp
        (LinearMap.mulLeft ℂ (pauliWord (A.sourceForm n) v)))
      ((LinearMap.mulLeft ℂ (A.sourceStageMatrixLinear n e (pauliWord (A.sourceForm n) v))).comp
        (A.sourceStageMatrixLinear n e : _ →ₗ[ℂ] _)) ?_ y
    intro w
    exact A.sourceStageMatrixLinear_word_mul n e v w
  refine pauliAlgebra_linear_ext (A.sourceForm n)
    (((A.sourceStageMatrixLinear n e : _ →ₗ[ℂ] _)).comp (LinearMap.mulRight ℂ y))
    ((LinearMap.mulRight ℂ (A.sourceStageMatrixLinear n e y)).comp
      (A.sourceStageMatrixLinear n e : _ →ₗ[ℂ] _)) ?_ x
  intro v
  exact hword v y

theorem sourceStageMatrixLinear_star (x : pauliAlgebra (A.sourceForm n)) :
    A.sourceStageMatrixLinear n e (star x) = star (A.sourceStageMatrixLinear n e x) := by
  obtain ⟨c, rfl⟩ : ∃ c : A.SourceLabel n → ℂ,
      x = ∑ v, c v • pauliWord (A.sourceForm n) v :=
    ⟨fun v => (pauliWordBasis (A.sourceForm n)).repr x v, by
      conv_lhs => rw [← Module.Basis.sum_repr (pauliWordBasis (A.sourceForm n)) x]
      exact Finset.sum_congr rfl (fun v _ => by rw [pauliWordBasis_apply])⟩
  rw [star_sum, map_sum, map_sum, star_sum]
  refine Finset.sum_congr rfl ?_
  intro v _
  rw [star_smul, map_smul, map_smul, star_smul, pauliWord_star, pauli_neg_eq_self, map_smul,
    sourceStageMatrixLinear_word, stdWord_star, A.sourceForm_enum n e v v, regPairing_comm]

/-- **The finite-stage Pauli-to-matrix star equivalence.** -/
noncomputable def sourceStageMatrixEquiv :
    pauliAlgebra (A.sourceForm n) ≃⋆ₐ[ℂ] Matrix (Reg (Fin k)) (Reg (Fin k)) ℂ where
  toFun := A.sourceStageMatrixLinear n e
  invFun := (A.sourceStageMatrixLinear n e).symm
  left_inv := (A.sourceStageMatrixLinear n e).left_inv
  right_inv := (A.sourceStageMatrixLinear n e).right_inv
  map_add' := map_add _
  map_mul' := A.sourceStageMatrixLinear_mul n e
  map_smul' := map_smul _
  map_star' := A.sourceStageMatrixLinear_star n e

@[simp] theorem sourceStageMatrixEquiv_apply (x : pauliAlgebra (A.sourceForm n)) :
    A.sourceStageMatrixEquiv n e x = A.sourceStageMatrixLinear n e x := rfl

/-! ### The finite-stage Pauli-to-dyadic star equivalence -/

/-- **The finite-stage bridge.**  For an explicit enumeration `e` of the P53
coordinate block of stage `n` by `Fin k`, the twisted coordinate Pauli algebra
of the stage is the `k`-qubit dyadic matrix stage. -/
noncomputable def sourceStageUHFEquiv :
    pauliAlgebra (A.sourceForm n) ≃⋆ₐ[ℂ] QubitTensorPower k :=
  (A.sourceStageMatrixEquiv n e).trans (qubitMatrixEquiv k).symm

/-- **The word formula of the bridge**: the P53 Pauli word of a stage label is
sent to the ordered dyadic word `X^a Z^b` of its enumerated exponent vectors,
with no extra phase. -/
theorem sourceStageUHFEquiv_word (v : A.SourceLabel n) :
    A.sourceStageUHFEquiv n e (pauliWord (A.sourceForm n) v) =
      qubitWord k (A.enumRepr n e v).1 (A.enumRepr n e v).2 := by
  refine qubitMatrixEquiv_injective k ?_
  dsimp only
  rw [qubitMatrixEquiv_qubitWord, sourceStageUHFEquiv, StarAlgEquiv.trans_apply,
    StarAlgEquiv.apply_symm_apply, sourceStageMatrixEquiv_apply,
    sourceStageMatrixLinear_word]

theorem enumRepr_z (i : A.Coord n) :
    A.enumRepr n e (A.stageCoordBasis n (Sum.inl i)) = (0, Pi.single (e i) 1) := by
  rw [enumRepr_apply]
  refine Prod.ext ?_ ?_
  · funext j
    show (A.stageCoordBasis n).repr (A.stageCoordBasis n (Sum.inl i)) (Sum.inr (e.symm j)) = 0
    rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg (by simp)]
  · funext j
    show (A.stageCoordBasis n).repr (A.stageCoordBasis n (Sum.inl i)) (Sum.inl (e.symm j)) = _
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    show _ = Pi.single (M := fun _ : Fin k => PauliBit) (e i) 1 j
    rw [Pi.single_apply]
    exact if_congr (by
      constructor
      · rintro h
        have : i = e.symm j := by simpa using h
        rw [this, Equiv.apply_symm_apply]
      · rintro rfl
        simp) rfl rfl

theorem enumRepr_x (i : A.Coord n) :
    A.enumRepr n e (A.stageCoordBasis n (Sum.inr i)) = (Pi.single (e i) 1, 0) := by
  rw [enumRepr_apply]
  refine Prod.ext ?_ ?_
  · funext j
    show (A.stageCoordBasis n).repr (A.stageCoordBasis n (Sum.inr i)) (Sum.inr (e.symm j)) = _
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    show _ = Pi.single (M := fun _ : Fin k => PauliBit) (e i) 1 j
    rw [Pi.single_apply]
    exact if_congr (by
      constructor
      · rintro h
        have : i = e.symm j := by simpa using h
        rw [this, Equiv.apply_symm_apply]
      · rintro rfl
        simp) rfl rfl
  · funext j
    show (A.stageCoordBasis n).repr (A.stageCoordBasis n (Sum.inr i)) (Sum.inl (e.symm j)) = 0
    rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg (by simp)]

/-- **The image of the P53 coordinate `Z` generator.**  The convention-dependent
fourth-root phase is trivial: both sides use the ordered `X^a Z^b` convention. -/
theorem sourceStageUHFEquiv_zGenerator (i : A.Coord n) :
    A.sourceStageUHFEquiv n e (pauliWord (A.sourceForm n) ((A.stageCoordinates n).z i)) =
      qubitZ k (Pi.single (e i) 1) := by
  rw [show (A.stageCoordinates n).z i = A.stageCoordBasis n (Sum.inl i) from rfl,
    A.sourceStageUHFEquiv_word n e, A.enumRepr_z n e i, qubitWord, qubitX_zero, one_mul]

/-- **The image of the P53 coordinate `X` generator**, again with trivial
fourth-root phase. -/
theorem sourceStageUHFEquiv_xGenerator (i : A.Coord n) :
    A.sourceStageUHFEquiv n e (pauliWord (A.sourceForm n) ((A.stageCoordinates n).x i)) =
      qubitX k (Pi.single (e i) 1) := by
  rw [show (A.stageCoordinates n).x i = A.stageCoordBasis n (Sum.inr i) from rfl,
    A.sourceStageUHFEquiv_word n e, A.enumRepr_x n e i, qubitWord, qubitZ_zero, mul_one]

theorem sourceStageUHFEquiv_map_mul (x y : pauliAlgebra (A.sourceForm n)) :
    A.sourceStageUHFEquiv n e (x * y) =
      A.sourceStageUHFEquiv n e x * A.sourceStageUHFEquiv n e y :=
  map_mul _ x y

theorem sourceStageUHFEquiv_map_star (x : pauliAlgebra (A.sourceForm n)) :
    A.sourceStageUHFEquiv n e (star x) = star (A.sourceStageUHFEquiv n e x) :=
  map_star _ x

theorem sourceStageUHFEquiv_bijective :
    Function.Bijective (fun x : pauliAlgebra (A.sourceForm n) => A.sourceStageUHFEquiv n e x) :=
  ⟨fun x y h => by
    have h2 := congrArg (A.sourceStageUHFEquiv n e).symm h
    simpa using h2,
   fun y => ⟨(A.sourceStageUHFEquiv n e).symm y, by simp⟩⟩

/-! ### The default enumeration -/

/-- The constructed enumeration of the stage coordinate block. -/
noncomputable def coordEnumeration : A.Coord n ≃ Fin (Nat.card (A.Coord n)) :=
  Finite.equivFin _

/-- **The default finite-stage bridge**, at `k = Nat.card (A.Coord n)`. -/
noncomputable def sourceStageUHFEquivDefault :
    pauliAlgebra (A.sourceForm n) ≃⋆ₐ[ℂ] QubitTensorPower (Nat.card (A.Coord n)) :=
  A.sourceStageUHFEquiv n (A.coordEnumeration n)

theorem sourceStageUHFEquivDefault_zGenerator (i : A.Coord n) :
    A.sourceStageUHFEquivDefault n (pauliWord (A.sourceForm n) ((A.stageCoordinates n).z i)) =
      qubitZ (Nat.card (A.Coord n)) (Pi.single (A.coordEnumeration n i) 1) :=
  A.sourceStageUHFEquiv_zGenerator n (A.coordEnumeration n) i

theorem sourceStageUHFEquivDefault_xGenerator (i : A.Coord n) :
    A.sourceStageUHFEquivDefault n (pauliWord (A.sourceForm n) ((A.stageCoordinates n).x i)) =
      qubitX (Nat.card (A.Coord n)) (Pi.single (A.coordEnumeration n i) 1) :=
  A.sourceStageUHFEquiv_xGenerator n (A.coordEnumeration n) i

end AlphaData

end LocalHyperbolicAlpha

/-! ## Norm control of the finite-stage bridge

The finite-dimensional algebras involved carry their C⋆ norms: the coordinate
Pauli algebra is a star subalgebra of a matrix algebra, and the dyadic stage is
normed through its register matrix model.  Both are C⋆-algebras, so the bridge
is isometric. -/

section Norms

open scoped Matrix.Norms.L2Operator

open UHFBridge LocalHyperbolicAlpha

noncomputable local instance matrixCStarAlgebra (m : Type*) [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}

noncomputable local instance pauliAlgebraCStarAlgebra {V : Type*} [AddCommGroup V]
    [Module PauliBit V] [DecidableEq V] [Fintype V] (B : PauliForm V) :
    CStarAlgebra (pauliAlgebra B) := by
  haveI : FiniteDimensional ℂ (pauliAlgebra B) := Module.Finite.of_basis (pauliWordBasis B)
  haveI : CompleteSpace (pauliAlgebra B) := FiniteDimensional.complete ℂ _
  exact {}

namespace UHFBridge

/-- A star equivalence of C⋆-algebras is isometric. -/
theorem norm_starAlgEquiv {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y]
    (φ : X ≃⋆ₐ[ℂ] Y) (x : X) : ‖φ x‖ = ‖x‖ := by
  refine le_antisymm (NonUnitalStarAlgHom.norm_apply_le (φ : X →⋆ₐ[ℂ] Y) x) ?_
  have h := NonUnitalStarAlgHom.norm_apply_le ((φ.symm : Y →⋆ₐ[ℂ] X)) (φ x)
  simpa using h

/-- **The C⋆ norm of the finite dyadic stage**, defined through its register
matrix model. -/
noncomputable def qubitOpNorm (k : ℕ) (x : QubitTensorPower k) : ℝ :=
  ‖qubitMatrixEquiv k x‖

theorem qubitOpNorm_nonneg (k : ℕ) (x : QubitTensorPower k) : 0 ≤ qubitOpNorm k x :=
  norm_nonneg _

theorem qubitOpNorm_eq_zero (k : ℕ) (x : QubitTensorPower k) :
    qubitOpNorm k x = 0 ↔ x = 0 := by
  rw [qubitOpNorm, norm_eq_zero]
  constructor
  · intro h
    refine qubitMatrixEquiv_injective k ?_
    dsimp only
    rw [h]
    exact (map_zero (qubitMatrixEquiv k)).symm
  · rintro rfl
    exact map_zero _

theorem qubitOpNorm_one (k : ℕ) : qubitOpNorm k 1 = 1 := by
  rw [qubitOpNorm, map_one, norm_one]

theorem qubitOpNorm_mul_le (k : ℕ) (x y : QubitTensorPower k) :
    qubitOpNorm k (x * y) ≤ qubitOpNorm k x * qubitOpNorm k y := by
  rw [qubitOpNorm, qubitOpNorm, qubitOpNorm, map_mul]
  exact norm_mul_le _ _

theorem qubitOpNorm_add_le (k : ℕ) (x y : QubitTensorPower k) :
    qubitOpNorm k (x + y) ≤ qubitOpNorm k x + qubitOpNorm k y := by
  rw [qubitOpNorm, qubitOpNorm, qubitOpNorm, map_add]
  exact norm_add_le _ _

/-- The dyadic stage norm satisfies the C⋆ identity. -/
theorem qubitOpNorm_star_mul_self (k : ℕ) (x : QubitTensorPower k) :
    qubitOpNorm k (star x * x) = qubitOpNorm k x * qubitOpNorm k x := by
  rw [qubitOpNorm, qubitOpNorm, map_mul, map_star, CStarRing.norm_star_mul_self]

theorem qubitOpNorm_star (k : ℕ) (x : QubitTensorPower k) :
    qubitOpNorm k (star x) = qubitOpNorm k x := by
  rw [qubitOpNorm, qubitOpNorm, map_star, norm_star]

end UHFBridge

namespace LocalHyperbolicAlpha.AlphaData

variable {L I : Type*} [LinearOrder I] (A : AlphaData L I) (n : ℕ) {k : ℕ}
  (e : A.Coord n ≃ Fin k)

/-- **The finite-stage bridge is isometric** for the C⋆ norms of the two
finite-dimensional algebras. -/
theorem norm_sourceStageUHFEquiv (x : pauliAlgebra (A.sourceForm n)) :
    UHFBridge.qubitOpNorm k (A.sourceStageUHFEquiv n e x) = ‖x‖ := by
  rw [UHFBridge.qubitOpNorm, sourceStageUHFEquiv, StarAlgEquiv.trans_apply,
    StarAlgEquiv.apply_symm_apply]
  exact UHFBridge.norm_starAlgEquiv (A.sourceStageMatrixEquiv n e) x

/-- The bridge to the register matrix model is an isometry. -/
theorem norm_sourceStageMatrixEquiv (x : pauliAlgebra (A.sourceForm n)) :
    ‖A.sourceStageMatrixEquiv n e x‖ = ‖x‖ :=
  UHFBridge.norm_starAlgEquiv (A.sourceStageMatrixEquiv n e) x

theorem isometry_sourceStageMatrixEquiv :
    Isometry (fun x : pauliAlgebra (A.sourceForm n) => A.sourceStageMatrixEquiv n e x) := by
  refine AddMonoidHomClass.isometry_of_norm
    (f := (A.sourceStageMatrixEquiv n e : pauliAlgebra (A.sourceForm n) →⋆ₐ[ℂ]
      Matrix (UHFBridge.Reg (Fin k)) (UHFBridge.Reg (Fin k)) ℂ)) ?_
  intro x
  exact A.norm_sourceStageMatrixEquiv n e x

/-- The distance form of the isometry statement.  It is phrased in the register
matrix model because the recursive dyadic model `QubitTensorPower k` carries only
a semiring structure, hence no subtraction. -/
theorem norm_sourceStageMatrixEquiv_sub (x y : pauliAlgebra (A.sourceForm n)) :
    ‖A.sourceStageMatrixEquiv n e x - A.sourceStageMatrixEquiv n e y‖ = ‖x - y‖ := by
  rw [← map_sub]
  exact A.norm_sourceStageMatrixEquiv n e (x - y)

end LocalHyperbolicAlpha.AlphaData

end Norms

end StabilizerHyperfinite
