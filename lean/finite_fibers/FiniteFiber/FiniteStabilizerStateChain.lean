import FiniteFiber.FiniteNestedTensorState

/-!
# A coherent sequential finite stabilizer-state system

This file turns the checked one-step initial-segment inclusion into a genuine
sequential system.  Longer embeddings are *defined* as compositions of the
one-site maps, rather than being identified with a separately chosen bulk
coordinate equivalence.  Thus the compatibility theorem below is coherent
along this sequence by construction.

The scope is intentionally narrow.  It does not yet prove that this sequence
agrees with every finite lattice-region inclusion, construct the norm-closed
quasilocal algebra, or extend the compatible state to that closure.
-/

namespace FiniteFiber

open scoped FiniteFiber.FiniteQubitMatrix

/--
The `m`-step initial-segment embedding, defined recursively from one-site
physical-coordinate embeddings.  The recursion—not an unproved bulk
factorization—fixes the transition maps of this sequential system.
-/
noncomputable def iterInitialSegmentEmbed (n : ℕ) : (m : ℕ) →
    Matrix (QubitIndex n) (QubitIndex n) ℂ →⋆ₐ[ℂ]
      Matrix (QubitIndex (n + m)) (QubitIndex (n + m)) ℂ
  | 0 => StarAlgHom.id ℂ (Matrix (QubitIndex n) (QubitIndex n) ℂ)
  | m + 1 => (embedInitialSegment (n + m) 1).comp (iterInitialSegmentEmbed n m)

/-- The zero-step transition is the identity. -/
theorem iterInitialSegmentEmbed_zero (n : ℕ) :
    iterInitialSegmentEmbed n 0 =
      StarAlgHom.id ℂ (Matrix (QubitIndex n) (QubitIndex n) ℂ) :=
  rfl

/-- A successor transition is one more physical one-site inclusion. -/
theorem iterInitialSegmentEmbed_succ (n m : ℕ)
    (A : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    iterInitialSegmentEmbed n (m + 1) A =
      embedInitialSegment (n + m) 1 (iterInitialSegmentEmbed n m A) :=
  rfl

/-- Transporting a one-site physical embedding across an equality of volumes. -/
private lemma embedInitialSegment_one_cast
    {a b : ℕ} (h : a = b)
    (A : Matrix (QubitIndex a) (QubitIndex a) ℂ) :
    (LinearEquiv.cast (R := ℂ)
      (M := fun r => Matrix (QubitIndex r) (QubitIndex r) ℂ)
      (congrArg Nat.succ h))
      (embedInitialSegment a 1 A) =
      embedInitialSegment b 1
        ((LinearEquiv.cast (R := ℂ)
          (M := fun r => Matrix (QubitIndex r) (QubitIndex r) ℂ) h) A) := by
  subst b
  rfl

/--
Successive physical embeddings compose, with the sole transport forced by
associativity of the volume indices.  This is the finite-coordinate
composition law underlying the sequential system.
-/
theorem iterInitialSegmentEmbed_comp (n m : ℕ) : ∀ (k : ℕ)
    (A : Matrix (QubitIndex n) (QubitIndex n) ℂ),
    (LinearEquiv.cast (R := ℂ)
      (M := fun r => Matrix (QubitIndex r) (QubitIndex r) ℂ)
      (Nat.add_assoc n m k).symm)
      (iterInitialSegmentEmbed n (m + k) A) =
      iterInitialSegmentEmbed (n + m) k
        (iterInitialSegmentEmbed n m A) := by
  intro k
  induction k with
  | zero =>
      intro A
      rfl
  | succ k ih =>
      intro A
      change
        (LinearEquiv.cast (R := ℂ)
          (M := fun r => Matrix (QubitIndex r) (QubitIndex r) ℂ)
          (congrArg Nat.succ (Nat.add_assoc n m k).symm))
          (embedInitialSegment (n + (m + k)) 1
            (iterInitialSegmentEmbed n (m + k) A)) =
          embedInitialSegment ((n + m) + k) 1
            (iterInitialSegmentEmbed (n + m) k
              (iterInitialSegmentEmbed n m A))
      rw [embedInitialSegment_one_cast (Nat.add_assoc n m k).symm]
      rw [ih]

/-- Every recursively composed transition is injective. -/
theorem iterInitialSegmentEmbed_injective (n m : ℕ) :
    Function.Injective (iterInitialSegmentEmbed n m) := by
  induction m with
  | zero =>
      intro a b hab
      exact hab
  | succ m ih =>
      intro a b hab
      apply ih
      apply embedInitialSegment_injective (n + m) 1
      exact hab

/-- Every recursively composed transition is norm preserving. -/
theorem iterInitialSegmentEmbed_norm (n m : ℕ)
    (A : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    ‖iterInitialSegmentEmbed n m A‖ = ‖A‖ := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change ‖embedInitialSegment (n + m) 1 (iterInitialSegmentEmbed n m A)‖ = ‖A‖
      rw [embedInitialSegment_norm, ih]

/--
The physical star-algebra embedding from volume n to a later volume m.
It is defined directly by Nat.leRecOn from the one-site initial-segment
embeddings, so the identity and composition laws are available at the typed
endpoints themselves.
-/
noncomputable def sequentialEmbed (n m : ℕ) (h : n ≤ m) :
    Matrix (QubitIndex n) (QubitIndex n) ℂ →⋆ₐ[ℂ]
      Matrix (QubitIndex m) (QubitIndex m) ℂ :=
  Nat.leRecOn h
    (@fun k f => (embedInitialSegment k 1).comp f)
    (StarAlgHom.id ℂ (Matrix (QubitIndex n) (QubitIndex n) ℂ))

/-- The zero-length physical transition is the identity star-algebra map. -/
theorem sequentialEmbed_self (n : ℕ) :
    sequentialEmbed n n le_rfl =
      StarAlgHom.id ℂ (Matrix (QubitIndex n) (QubitIndex n) ℂ) := by
  unfold sequentialEmbed
  rw [Nat.leRecOn_self]

/-- A later physical transition is one more one-site inclusion. -/
theorem sequentialEmbed_succ (n m : ℕ) (h : n ≤ m) :
    sequentialEmbed n (m + 1) (Nat.le.step h) =
      (embedInitialSegment m 1).comp (sequentialEmbed n m h) := by
  unfold sequentialEmbed
  rw [Nat.leRecOn_succ h]

/--
At a volume presented as an explicit added block, the typed endpoint map agrees
with the original length-indexed recursive physical embedding.
-/
theorem sequentialEmbed_add_eq_iter (n : ℕ) : ∀ m : ℕ,
    sequentialEmbed n (n + m) (Nat.le_add_right n m) =
      iterInitialSegmentEmbed n m := by
  intro m
  induction m with
  | zero =>
      exact sequentialEmbed_self n
  | succ m ih =>
      change
        sequentialEmbed n ((n + m) + 1)
          (Nat.le.step (Nat.le_add_right n m)) =
          iterInitialSegmentEmbed n (m + 1)
      rw [sequentialEmbed_succ n (n + m) (Nat.le_add_right n m)]
      rw [ih]
      rfl

/--
The typed physical embeddings form a sequential composition system.  This is
the endpoint-indexed form of the associativity-transport theorem for the
iterated physical embeddings.
-/
theorem sequentialEmbed_comp
    (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) :
    sequentialEmbed n l (hnm.trans hml) =
      (sequentialEmbed m l hml).comp (sequentialEmbed n m hnm) := by
  induction l, hml using Nat.le_induction with
  | base =>
      rw [sequentialEmbed_self]
      rfl
  | succ l hml ih =>
      rw [sequentialEmbed_succ n l (hnm.trans hml)]
      rw [sequentialEmbed_succ m l hml]
      rw [ih]
      rfl

/-- Every typed physical star-algebra transition is injective. -/
theorem sequentialEmbed_injective
    (n m : ℕ) (h : n ≤ m) :
    Function.Injective (sequentialEmbed n m h) := by
  induction m, h using Nat.le_induction with
  | base =>
      intro A B hAB
      rw [sequentialEmbed_self] at hAB
      exact hAB
  | succ m h ih =>
      intro A B hAB
      apply ih
      apply embedInitialSegment_injective m 1
      rw [sequentialEmbed_succ] at hAB
      exact hAB

/-- Every typed physical star-algebra transition preserves the operator norm. -/
theorem sequentialEmbed_norm
    (n m : ℕ) (h : n ≤ m)
    (A : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    ‖sequentialEmbed n m h A‖ = ‖A‖ := by
  induction m, h using Nat.le_induction with
  | base =>
      rw [sequentialEmbed_self]
      rfl
  | succ m h ih =>
      rw [sequentialEmbed_succ n m h]
      change ‖embedInitialSegment m 1 (sequentialEmbed n m h A)‖ = ‖A‖
      rw [embedInitialSegment_norm, ih]

/--
The linear map underlying sequentialEmbed.  The star-algebra map is retained
above so that multiplication, star, unit, identity, and composition are not
lost when forming the typed sequential system.
-/
noncomputable def sequentialTransition (n m : ℕ) (h : n ≤ m) :
    Matrix (QubitIndex n) (QubitIndex n) ℂ →ₗ[ℂ]
      Matrix (QubitIndex m) (QubitIndex m) ℂ :=
  (sequentialEmbed n m h).toLinearMap

/-- The typed linear transition is the identity at a fixed volume. -/
theorem sequentialTransition_self (n : ℕ) :
    sequentialTransition n n le_rfl = LinearMap.id := by
  unfold sequentialTransition
  rw [sequentialEmbed_self]
  rfl

/-- A successor typed linear transition is one more physical inclusion. -/
theorem sequentialTransition_succ (n m : ℕ) (h : n ≤ m) :
    sequentialTransition n (m + 1) (Nat.le.step h) =
      (embedInitialSegment m 1).toLinearMap.comp (sequentialTransition n m h) := by
  unfold sequentialTransition
  rw [sequentialEmbed_succ]
  rfl

/-- The typed linear transitions obey the directed-system composition law. -/
theorem sequentialTransition_comp
    (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) :
    (sequentialTransition m l hml).comp (sequentialTransition n m hnm) =
      sequentialTransition n l (hnm.trans hml) := by
  apply LinearMap.ext
  intro A
  change sequentialEmbed m l hml
      (sequentialEmbed n m hnm A) =
      sequentialEmbed n l (hnm.trans hml) A
  exact congrArg (fun f => f A)
    (sequentialEmbed_comp n m l hnm hml).symm

/-- The typed linear transition preserves the finite operator norm. -/
theorem sequentialTransition_norm
    (n m : ℕ) (h : n ≤ m)
    (A : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    ‖sequentialTransition n m h A‖ = ‖A‖ :=
  sequentialEmbed_norm n m h A

/-- The finite matrix spaces and typed physical transitions form a directed system. -/
noncomputable instance sequentialTransition_directedSystem :
    DirectedSystem
      (fun n => Matrix (QubitIndex n) (QubitIndex n) ℂ)
      (fun n m h => sequentialTransition n m h) where
  map_self := by
    intro n A
    rw [sequentialTransition_self]
    rfl
  map_map := by
    intro k j i hij hjk A
    exact congrArg (fun f => f A)
      (sequentialTransition_comp i j k hij hjk)

/--
The recursively composed physical transition sends every ordered Pauli string
to the same string padded by identity labels on all subsequently added sites.
This is a matrix-level statement about the sequential system; it does not
identify the transition with a separately chosen arbitrary-block embedding on
all matrices.
-/
theorem iterInitialSegmentEmbed_pauliString (n : ℕ) : ∀ (m : ℕ)
    (a : Fin n → PauliLabel),
    iterInitialSegmentEmbed n m (pauliStringMatrix a) =
      pauliStringMatrix (appendIdentityPauliLabels m a) := by
  intro m
  induction m with
  | zero =>
      intro a
      rw [iterInitialSegmentEmbed_zero, appendIdentityPauliLabels_zero]
      rfl
  | succ m ih =>
      intro a
      rw [iterInitialSegmentEmbed_succ, ih]
      rw [embedInitialSegment_pauliString]
      congr 1
      funext i
      apply Fin.addCases (m := n + m) (n := 1)
        (motive := fun i =>
          Fin.addCases (motive := fun _ => PauliLabel)
            (appendIdentityPauliLabels m a) (fun _ : Fin 1 => PauliLabel.I) i =
            appendIdentityPauliLabels (m + 1) a i)
      · intro j
        rw [Fin.addCases_left]
        exact appendIdentityPauliLabels_castAdd n m a j
      · intro j
        rw [Fin.addCases_right]
        have hj : j = 0 := Fin.eq_zero j
        subst j
        change PauliLabel.I = appendIdentityPauliLabels (m + 1) a
          (Fin.natAdd (n + m) (0 : Fin 1))
        rw [show Fin.natAdd (n + m) (0 : Fin 1) =
          Fin.natAdd n (Fin.natAdd m (0 : Fin 1)) by
          simpa using (Fin.natAdd_natAdd n m (0 : Fin 1)).symm]
        simp only [appendIdentityPauliLabels, Fin.addCases_right]

/-- The sequential physical transition also preserves the explicit Pauli sign. -/
theorem iterInitialSegmentEmbed_signedPauliString (n m : ℕ)
    (negative : Bool) (a : Fin n → PauliLabel) :
    iterInitialSegmentEmbed n m (signedPauliStringMatrix negative a) =
      signedPauliStringMatrix negative (appendIdentityPauliLabels m a) := by
  cases negative <;>
    simp [signedPauliStringMatrix, iterInitialSegmentEmbed_pauliString]

/--
The endpoint-indexed physical embedding pads every ordered Pauli string by
identity labels on an explicitly added final block.
-/
theorem sequentialEmbed_add_pauliString (n m : ℕ)
    (a : Fin n → PauliLabel) :
    sequentialEmbed n (n + m) (Nat.le_add_right n m)
      (pauliStringMatrix a) =
      pauliStringMatrix (appendIdentityPauliLabels m a) := by
  rw [sequentialEmbed_add_eq_iter]
  exact iterInitialSegmentEmbed_pauliString n m a

/-- The endpoint-indexed physical embedding also preserves the Pauli sign. -/
theorem sequentialEmbed_add_signedPauliString (n m : ℕ)
    (negative : Bool) (a : Fin n → PauliLabel) :
    sequentialEmbed n (n + m) (Nat.le_add_right n m)
      (signedPauliStringMatrix negative a) =
      signedPauliStringMatrix negative (appendIdentityPauliLabels m a) := by
  rw [sequentialEmbed_add_eq_iter]
  exact iterInitialSegmentEmbed_signedPauliString n m negative a

/--
Data for a sequence of actual finite stabilizer densities whose adjacent
restrictions are certified by `NestedFinitePauliStabilizerData` in the literal
initial/final `Fin` coordinates.
-/
structure StepwiseCompatibleFiniteStabilizerChain where
  /-- The finite stabilizer group at each volume. -/
  G : ℕ → Type
  /-- Group structure of each finite stabilizer group. -/
  group : ∀ n, Group (G n)
  /-- Finiteness needed for the stabilizer density at each volume. -/
  fintype : ∀ n, Fintype (G n)
  /-- Decidable equality used by the finite survivor calculation. -/
  decidableEq : ∀ n, DecidableEq (G n)
  /-- The actual finite stabilizer density data at each volume. -/
  density : ∀ n, @FinitePauliStabilizerData (G n) (group n) n
  /-- The checked nested data for the one-site inclusion from `n` to `n + 1`. -/
  step : ∀ n, @NestedFinitePauliStabilizerData
    (G (n + 1)) (G n) (group (n + 1)) (group n) n 1
  /-- The larger density in each step is the density at the next volume. -/
  step_large : ∀ n, (step n).large = density (n + 1)
  /-- The smaller density in each step is the density at the current volume. -/
  step_small : ∀ n, (step n).small = density n
  /-- Each step uses the physical initial/final `Fin` coordinate split. -/
  step_coordinate : ∀ n, (step n).coordinateEquiv = qubitIndexInitialSegmentEquiv n 1

namespace StepwiseCompatibleFiniteStabilizerChain

/-- The finite stabilizer state functional at a specified volume. -/
noncomputable def state (C : StepwiseCompatibleFiniteStabilizerChain) (n : ℕ) :
    Matrix (QubitIndex n) (QubitIndex n) ℂ →ₗ[ℂ] ℂ := by
  letI : Group (C.G n) := C.group n
  letI : Fintype (C.G n) := C.fintype n
  exact (C.density n).stabilizerStateFunctional

/-- Adjacent finite stabilizer states agree under the physical one-site inclusion. -/
theorem state_step (C : StepwiseCompatibleFiniteStabilizerChain) (n : ℕ)
    (A : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    C.state (n + 1) (embedInitialSegment n 1 A) = C.state n A := by
  letI : Group (C.G n) := C.group n
  letI : Group (C.G (n + 1)) := C.group (n + 1)
  letI : Fintype (C.G n) := C.fintype n
  letI : Fintype (C.G (n + 1)) := C.fintype (n + 1)
  letI : DecidableEq (C.G (n + 1)) := C.decidableEq (n + 1)
  have h := (C.step n).stabilizerStateFunctional_embedInitialSegment
    (C.step_coordinate n) A
  change (C.density (n + 1)).stabilizerStateFunctional
    (embedInitialSegment n 1 A) = (C.density n).stabilizerStateFunctional A
  simpa only [C.step_large, C.step_small] using h

/--
The finite stabilizer state at every later sequential stage restricts to the
state at the initial stage.  This is the coherent finite-volume state
compatibility needed before a separate quasilocal-completion construction.
-/
theorem state_iter (C : StepwiseCompatibleFiniteStabilizerChain) (n m : ℕ)
    (A : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    C.state (n + m) (iterInitialSegmentEmbed n m A) = C.state n A := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change C.state ((n + m) + 1)
        (embedInitialSegment (n + m) 1 (iterInitialSegmentEmbed n m A)) = C.state n A
      rw [C.state_step (n + m)]
      exact ih

/-- The finite state is invariant under transport along an equality of volumes. -/
lemma state_cast (C : StepwiseCompatibleFiniteStabilizerChain)
    {i j : ℕ} (h : i = j)
    (A : Matrix (QubitIndex i) (QubitIndex i) ℂ) :
    C.state j ((LinearEquiv.cast (R := ℂ)
      (M := fun r => Matrix (QubitIndex r) (QubitIndex r) ℂ) h) A) = C.state i A := by
  subst j
  rfl

/--
The finite states are compatible along every typed later-volume transition,
not only along a transition presented as an explicit added block.
-/
theorem state_sequentialTransition (C : StepwiseCompatibleFiniteStabilizerChain)
    (n m : ℕ) (h : n ≤ m)
    (A : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    C.state m (sequentialTransition n m h A) = C.state n A := by
  induction m, h using Nat.le_induction with
  | base =>
      rw [sequentialTransition_self]
      rfl
  | succ m h ih =>
      rw [sequentialTransition_succ n m h]
      change C.state (m + 1)
        (embedInitialSegment m 1 (sequentialTransition n m h A)) = C.state n A
      rw [C.state_step m]
      exact ih

end StepwiseCompatibleFiniteStabilizerChain

/--
A stepwise compatible finite stabilizer chain whose local Pauli labels are
already written in literal initial/final `Fin` coordinates.  In contrast to
`StepwiseCompatibleFiniteStabilizerChain`, no separate tensor-coordinate
decomposition is supplied: it is derived from the physical Pauli-string
factorization.
-/
structure InitialSegmentStepwiseCompatibleFiniteStabilizerChain where
  /-- The finite stabilizer group at each volume. -/
  G : ℕ → Type
  /-- Group structure of each finite stabilizer group. -/
  group : ∀ n, Group (G n)
  /-- Finiteness needed for each finite stabilizer density. -/
  fintype : ∀ n, Fintype (G n)
  /-- Decidable equality used by the finite survivor calculation. -/
  decidableEq : ∀ n, DecidableEq (G n)
  /-- The actual finite stabilizer density data at each volume. -/
  density : ∀ n, @FinitePauliStabilizerData (G n) (group n) n
  /-- Literal-coordinate nested data for the one-site transition. -/
  step : ∀ n, @InitialSegmentNestedFinitePauliStabilizerData
    (G (n + 1)) (G n) (group (n + 1)) (group n) n 1
  /-- The larger density of a step is the next density in the chain. -/
  step_large : ∀ n, (step n).large = density (n + 1)
  /-- The smaller density of a step is the current density in the chain. -/
  step_small : ∀ n, (step n).small = density n

namespace InitialSegmentStepwiseCompatibleFiniteStabilizerChain

/--
Forgetting the derived literal-coordinate structure produces the generic
stepwise compatible chain used by the sequential state theorem.
-/
noncomputable def toStepwiseCompatibleFiniteStabilizerChain
    (C : InitialSegmentStepwiseCompatibleFiniteStabilizerChain) :
    StepwiseCompatibleFiniteStabilizerChain where
  G := C.G
  group := C.group
  fintype := C.fintype
  decidableEq := C.decidableEq
  density := C.density
  step := by
    intro n
    letI : Group (C.G n) := C.group n
    letI : Group (C.G (n + 1)) := C.group (n + 1)
    exact (C.step n).toNestedFinitePauliStabilizerData
  step_large := C.step_large
  step_small := C.step_small
  step_coordinate := fun _ => rfl

/-- The finite stabilizer state at one volume in the literal-coordinate chain. -/
noncomputable def state (C : InitialSegmentStepwiseCompatibleFiniteStabilizerChain)
    (n : ℕ) : Matrix (QubitIndex n) (QubitIndex n) ℂ →ₗ[ℂ] ℂ :=
  C.toStepwiseCompatibleFiniteStabilizerChain.state n

/--
Literal-coordinate step data yield compatible finite states along every
recursively composed physical transition.
-/
theorem state_iter (C : InitialSegmentStepwiseCompatibleFiniteStabilizerChain)
    (n m : ℕ) (A : Matrix (QubitIndex n) (QubitIndex n) ℂ) :
    C.state (n + m) (iterInitialSegmentEmbed n m A) = C.state n A := by
  exact C.toStepwiseCompatibleFiniteStabilizerChain.state_iter n m A

end InitialSegmentStepwiseCompatibleFiniteStabilizerChain

end FiniteFiber
