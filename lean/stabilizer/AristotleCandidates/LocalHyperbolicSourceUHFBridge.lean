import AristotleCandidates.LocalHyperbolicFiniteStageUHFBridge
import Formalization.DyadicTensorTower

/-!
# P55B — the coherent source-limit to UHF bridge

**Context declaration: infrastructure only.**  No manuscript claim is asserted
in this module.  It identifies the algebraic source direct limit assembled in
P53 (`AristotleCandidates.LocalHyperbolicAlgebraicAlpha`) with the dyadic
finite-coordinate system assembled from the finite-stage bridges of P55A
(`AristotleCandidates.LocalHyperbolicFiniteStageUHFBridge`).

## Plan alignment

* Package `P55B`, lane `H`; predecessors `P53` and `P55A`.
* Gate: prove finite-stage coherence of the P55A stage maps with the P53 source
  connecting maps, construct the coordinate-dyadic direct limit and its
  star-equivalence with the P53 source limit, and prove the two endpoint
  statements (terminal finite block, cofinal infinite exhaustion) separately.
* No operator-range completion, regional C⋆ alpha, state identity, GNS tensor
  split, factor classification, or trace/weight conclusion is claimed here.

## What is constructed

1. A **coherent enumeration** of the nested finite coordinate blocks: each
   block `A.Coord n` is enumerated by `Fin (A.stageCard n)` so that passing
   from stage `n` to stage `m ≥ n` shifts every old coordinate by exactly
   `A.stageCard m - A.stageCard n` positions.  This is *constructed* from the
   P52 exhaustion (through the birth stage of a coordinate and the given linear
   order on `I`), not assumed.
2. The **commuting squares**: the P55A stage equivalences intertwine the P53
   source connecting maps with the dyadic tower maps
   (`stageUHFEquiv_sourceConnecting`).  This is proved, not assumed.
3. The **coordinate-dyadic direct limit** `A.CoordinateDyadicLimit` and the
   star equivalence `A.sourceToCoordinateDyadic`, with its stage formula and
   uniqueness.
4. The **finite branch**: if `I` is finite the exhaustion has a terminal
   coordinate block and `A.sourceFiniteEquiv` identifies the source limit with
   `QubitTensorPower (Nat.card I)`.
5. The **infinite branch**: if `I` is infinite the stage cardinalities are
   cofinal in `ℕ`, the coordinate-dyadic limit is the qubit UHF algebra, and
   `A.sourceUHFEquiv : A.SourceLimit ≃⋆ₐ[ℂ] QubitUHFAlgebra`.
-/

namespace StabilizerHyperfinite

namespace UHFBridge

open LocalHyperbolicAlpha

/-! ## Padding of finite registers along the dyadic tower

The dyadic connecting map `qubitTensorPowerMap k k'` adjoins new qubits on the
*left* of a register, so on exponent vectors it is the padding that places the
old `k`-qubit register in the last `k` positions of a `k'`-qubit register. -/

/-- Pad an exponent vector of a `k`-qubit register into a `k'`-qubit register,
placing the old register in the last `k` positions. -/
def padReg (k k' : ℕ) (a : Reg (Fin k)) : Reg (Fin k') :=
  fun j => if h : k' ≤ (j : ℕ) + k then a ⟨(j : ℕ) + k - k', by have := j.isLt; omega⟩ else 0

theorem padReg_self (k : ℕ) (a : Reg (Fin k)) : padReg k k a = a := by
  funext j
  rw [padReg, dif_pos (by omega)]
  congr 1
  exact Fin.ext (by simp)

theorem padReg_succ {k k' : ℕ} (h : k ≤ k') (a : Reg (Fin k)) :
    padReg k (k' + 1) a = Fin.cons 0 (padReg k k' a) := by
  funext j
  induction j using Fin.cases with
  | zero => rw [padReg, dif_neg (by simp; omega)]; rfl
  | succ i =>
      rw [Fin.cons_succ, padReg, padReg]
      by_cases hc : k' ≤ (i : ℕ) + k
      · rw [dif_pos (by rw [Fin.val_succ]; omega), dif_pos hc]
        congr 1
        refine Fin.ext ?_
        simp only [Fin.val_succ]
        omega
      · rw [dif_neg (by rw [Fin.val_succ]; omega), dif_neg hc]

/-- The value of a padded exponent vector at a position coming from the old
register. -/
theorem padReg_apply_of_le {k k' : ℕ} (a : Reg (Fin k)) (j : Fin k') (i : Fin k)
    (hij : (j : ℕ) + k = k' + (i : ℕ)) : padReg k k' a j = a i := by
  rw [padReg, dif_pos (by omega)]
  congr 1
  exact Fin.ext (by simp; omega)

/-- The value of a padded exponent vector at a genuinely new position. -/
theorem padReg_apply_of_lt {k k' : ℕ} (a : Reg (Fin k)) (j : Fin k')
    (hj : (j : ℕ) + k < k') : padReg k k' a j = 0 := by
  rw [padReg, dif_neg (by omega)]

theorem succEmbedding_qubitX (k : ℕ) (a : Reg (Fin k)) :
    qubitTensorPowerSuccEmbedding k (qubitX k a) = qubitX (k + 1) (Fin.cons 0 a) := by
  have h1 : qubitX (k + 1) (Fin.cons 0 a) =
      (Matrix.of fun r c : Fin 2 =>
        if bitEquiv r = (Fin.cons (0 : PauliBit) a : Reg (Fin (k + 1))) 0 + bitEquiv c
        then qubitX k (Fin.tail (Fin.cons (0 : PauliBit) a : Reg (Fin (k + 1)))) else 0 :
          Matrix (Fin 2) (Fin 2) (QubitTensorPower k)) := rfl
  rw [h1]
  show Matrix.scalar (Fin 2) (qubitX k a) = _
  ext r c
  rw [Fin.cons_zero, Fin.tail_cons]
  show (Matrix.diagonal (fun _ => qubitX k a)) r c =
    if bitEquiv r = 0 + bitEquiv c then qubitX k a else 0
  rw [Matrix.diagonal_apply, zero_add]
  by_cases h : r = c
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun hh => h (bitEquiv.injective hh))]

theorem succEmbedding_qubitZ (k : ℕ) (b : Reg (Fin k)) :
    qubitTensorPowerSuccEmbedding k (qubitZ k b) = qubitZ (k + 1) (Fin.cons 0 b) := by
  have h1 : qubitZ (k + 1) (Fin.cons 0 b) =
      (Matrix.of fun r c : Fin 2 =>
        if r = c then pauliSign ((Fin.cons (0 : PauliBit) b : Reg (Fin (k + 1))) 0 * bitEquiv c) •
          qubitZ k (Fin.tail (Fin.cons (0 : PauliBit) b : Reg (Fin (k + 1)))) else 0 :
          Matrix (Fin 2) (Fin 2) (QubitTensorPower k)) := rfl
  rw [h1]
  show Matrix.scalar (Fin 2) (qubitZ k b) = _
  ext r c
  rw [Fin.cons_zero, Fin.tail_cons]
  show (Matrix.diagonal (fun _ => qubitZ k b)) r c =
    if r = c then pauliSign (0 * bitEquiv c) • qubitZ k b else 0
  rw [Matrix.diagonal_apply, zero_mul, pauliSign_zero, one_smul]

theorem succEmbedding_qubitWord (k : ℕ) (a b : Reg (Fin k)) :
    qubitTensorPowerSuccEmbedding k (qubitWord k a b) =
      qubitWord (k + 1) (Fin.cons 0 a) (Fin.cons 0 b) := by
  rw [qubitWord, qubitWord, map_mul, succEmbedding_qubitX, succEmbedding_qubitZ]

/-- **The dyadic tower map on standard words**: the canonical inclusion of the
`k`-qubit stage into the `k'`-qubit stage is the zero-padding of exponent
vectors. -/
theorem qubitTensorPowerMap_qubitWord (k k' : ℕ) (h : k ≤ k') (a b : Reg (Fin k)) :
    qubitTensorPowerMap k k' h (qubitWord k a b) =
      qubitWord k' (padReg k k' a) (padReg k k' b) := by
  induction k', h using Nat.le_induction with
  | base => rw [qubitTensorPowerMap_self, padReg_self, padReg_self]; rfl
  | succ m hm ih =>
      rw [qubitTensorPowerMap_succ k m hm, StarAlgHom.comp_apply, ih,
        succEmbedding_qubitWord, padReg_succ hm, padReg_succ hm]

/-- The canonical map of a dyadic stage into the qubit UHF algebra. -/
noncomputable abbrev qubitUHFOf (k : ℕ) (x : QubitTensorPower k) : QubitUHFAlgebra :=
  DirectLimit.Module.of ℂ ℕ QubitTensorPower qubitTensorPowerMap k x

theorem qubitUHFOf_map {k k' : ℕ} (h : k ≤ k') (x : QubitTensorPower k) :
    qubitUHFOf k' (qubitTensorPowerMap k k' h x) = qubitUHFOf k x :=
  DirectLimit.Module.of_f (hij := h)

/-- Dyadic stages with the same number of qubits are canonically identified. -/
noncomputable def qubitTensorPowerCongr {k k' : ℕ} (h : k = k') :
    QubitTensorPower k ≃⋆ₐ[ℂ] QubitTensorPower k' := by
  subst h; exact StarAlgEquiv.refl

@[simp] theorem qubitTensorPowerCongr_refl (k : ℕ) (x : QubitTensorPower k) :
    qubitTensorPowerCongr (rfl : k = k) x = x := rfl

theorem qubitTensorPowerCongr_trans {k k' k'' : ℕ} (h : k = k') (h' : k' = k'')
    (x : QubitTensorPower k) :
    qubitTensorPowerCongr h' (qubitTensorPowerCongr h x) =
      qubitTensorPowerCongr (h.trans h') x := by
  subst h; subst h'; rfl

/-- If no qubit is added, the dyadic tower map is the canonical identification. -/
theorem qubitTensorPowerMap_of_eq {k k' : ℕ} (h : k ≤ k') (he : k = k')
    (x : QubitTensorPower k) :
    qubitTensorPowerMap k k' h x = qubitTensorPowerCongr he x := by
  subst he
  rw [qubitTensorPowerMap_self]
  rfl

theorem qubitTensorPowerMap_bijective_of_eq {k k' : ℕ} (h : k ≤ k') (he : k = k') :
    Function.Bijective (qubitTensorPowerMap k k' h) := by
  have : ∀ x, qubitTensorPowerMap k k' h x = qubitTensorPowerCongr he x :=
    qubitTensorPowerMap_of_eq h he
  rw [show (qubitTensorPowerMap k k' h : QubitTensorPower k → QubitTensorPower k') =
    (qubitTensorPowerCongr he : QubitTensorPower k → QubitTensorPower k') from funext this]
  exact (qubitTensorPowerCongr he).bijective

end UHFBridge

/-! ## The coherent enumeration of the nested coordinate blocks -/

namespace LocalHyperbolicAlpha

namespace AlphaData

open CoherentLocalHyperbolic UHFBridge
open scoped Classical

variable {L I : Type*} [LinearOrder I] (A : AlphaData L I)

/-- The first stage of the P52 exhaustion whose coordinate block contains `i`. -/
noncomputable def birth (i : I) : ℕ :=
  Nat.find (A.family.exists_mem_coordinateBlock A.exhaustion i)

theorem mem_coordinateBlock_birth (i : I) :
    i ∈ A.family.coordinateBlock A.exhaustion (A.birth i) :=
  Nat.find_spec (A.family.exists_mem_coordinateBlock A.exhaustion i)

theorem birth_le_of_mem {i : I} {n : ℕ} (h : i ∈ A.family.coordinateBlock A.exhaustion n) :
    A.birth i ≤ n :=
  Nat.find_min' _ h

theorem mem_coordinateBlock_of_birth_le {i : I} {n : ℕ} (h : A.birth i ≤ n) :
    i ∈ A.family.coordinateBlock A.exhaustion n :=
  A.family.coordinateBlock_mono A.exhaustion h (A.mem_coordinateBlock_birth i)

/-- The stage-`n` coordinate block as a finite set of labels. -/
noncomputable def blockFinset (n : ℕ) : Finset I := A.family.blockFinset A.exhaustion n

@[simp] theorem mem_blockFinset (n : ℕ) (i : I) :
    i ∈ A.blockFinset n ↔ i ∈ A.family.coordinateBlock A.exhaustion n :=
  A.family.mem_blockFinset A.exhaustion n i

theorem blockFinset_subset {n m : ℕ} (h : n ≤ m) : A.blockFinset n ⊆ A.blockFinset m := by
  intro i hi
  rw [mem_blockFinset] at hi ⊢
  exact A.family.coordinateBlock_mono A.exhaustion h hi

/-- The number of coordinates of the stage-`n` block: the number of qubits of
the dyadic stage attached to it. -/
noncomputable def stageCard (n : ℕ) : ℕ := (A.blockFinset n).card

theorem stageCard_mono {n m : ℕ} (h : n ≤ m) : A.stageCard n ≤ A.stageCard m :=
  Finset.card_le_card (A.blockFinset_subset h)

theorem card_coord (n : ℕ) : Fintype.card (A.Coord n) = A.stageCard n := by
  rw [stageCard, blockFinset, CoherentLocalHyperbolic.LocalHyperbolicFamily.blockFinset,
    Set.Finite.card_toFinset]

/-- The ordering key of a coordinate: its birth stage first, then the linear
order of the coordinate index type.  Coordinate blocks are exactly the initial
segments of this order that the exhaustion produces. -/
noncomputable def key (i : I) : ℕ ×ₗ I := toLex (A.birth i, i)

theorem key_lt_of_birth_lt {i j : I} (h : A.birth i < A.birth j) : A.key i < A.key j :=
  Prod.Lex.lt_iff.2 (Or.inl h)

theorem birth_le_of_key_lt {i j : I} (h : A.key i < A.key j) : A.birth i ≤ A.birth j := by
  rcases Prod.Lex.lt_iff.1 h with h | ⟨h, -⟩
  · exact le_of_lt h
  · exact le_of_eq h

theorem key_injective : Function.Injective A.key := by
  intro i j h
  have := congrArg (fun z => (ofLex z).2) h
  simpa using this

/-- **The position of a coordinate inside its stage block**: the number of block
coordinates that are strictly later in the birth-stage ordering.  Coordinates
born at a later stage therefore receive the smaller positions, which is the
convention forced by the dyadic tower. -/
noncomputable def rankIdx (n : ℕ) (i : I) : ℕ :=
  ((A.blockFinset n).filter (fun j => A.key i < A.key j)).card

theorem rankIdx_lt {n : ℕ} {i : I} (hi : i ∈ A.blockFinset n) :
    A.rankIdx n i < A.stageCard n := by
  refine Finset.card_lt_card ?_
  refine (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2 ⟨i, hi, ?_⟩
  simp

theorem rankIdx_lt_rankIdx {n : ℕ} {i j : I} (hj : j ∈ A.blockFinset n)
    (hij : A.key i < A.key j) : A.rankIdx n j < A.rankIdx n i := by
  refine Finset.card_lt_card ?_
  refine (Finset.ssubset_iff_of_subset ?_).2 ⟨j, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hij.trans hp.2⟩
  · rw [Finset.mem_filter]; exact ⟨hj, hij⟩
  · simp

theorem rankIdx_injOn {n : ℕ} {i j : I} (hi : i ∈ A.blockFinset n) (hj : j ∈ A.blockFinset n)
    (h : A.rankIdx n i = A.rankIdx n j) : i = j := by
  rcases lt_trichotomy (A.key i) (A.key j) with hlt | heq | hgt
  · have := A.rankIdx_lt_rankIdx hj hlt; omega
  · exact A.key_injective heq
  · have := A.rankIdx_lt_rankIdx (i := j) (j := i) hi hgt; omega

/-- **Coherence of the block enumeration.**  Passing from stage `n` to a later
stage shifts the position of every old coordinate by exactly the number of new
coordinates. -/
theorem stageCard_add_rankIdx {n m : ℕ} (hnm : n ≤ m) {i : I} (hi : i ∈ A.blockFinset n) :
    A.stageCard n + A.rankIdx m i = A.stageCard m + A.rankIdx n i := by
  classical
  set S := A.blockFinset n with hS
  set T := A.blockFinset m with hT
  have hST : S ⊆ T := A.blockFinset_subset hnm
  have hbi : A.birth i ≤ n := A.birth_le_of_mem ((A.mem_blockFinset n i).1 hi)
  have hsplit : T.filter (fun j => A.key i < A.key j) =
      S.filter (fun j => A.key i < A.key j) ∪ (T \ S).filter (fun j => A.key i < A.key j) := by
    rw [← Finset.filter_union, Finset.union_sdiff_of_subset hST]
  have hdisj : Disjoint (S.filter (fun j => A.key i < A.key j))
      ((T \ S).filter (fun j => A.key i < A.key j)) :=
    Finset.disjoint_filter_filter Finset.disjoint_sdiff
  have hall : (T \ S).filter (fun j => A.key i < A.key j) = T \ S := by
    refine Finset.filter_true_of_mem ?_
    intro j hj
    rw [Finset.mem_sdiff] at hj
    refine A.key_lt_of_birth_lt ?_
    have hjn : ¬ A.birth j ≤ n := by
      intro hle
      exact hj.2 ((A.mem_blockFinset n j).2 (A.mem_coordinateBlock_of_birth_le hle))
    omega
  have hcard : A.rankIdx m i = A.rankIdx n i + (T \ S).card := by
    rw [rankIdx, rankIdx, ← hS, ← hT, hsplit, Finset.card_union_of_disjoint hdisj, hall]
  have hcards : (T \ S).card + S.card = T.card := Finset.card_sdiff_add_card_eq_card hST
  rw [stageCard, stageCard, ← hS, ← hT, hcard]
  omega

/-- **The new coordinates occupy the leading positions.**  A coordinate of a
later block that is not yet present at stage `n` has position strictly below
the number of new coordinates. -/
theorem stageCard_add_rankIdx_lt {n m : ℕ} (hnm : n ≤ m) {i : I} (him : i ∈ A.blockFinset m)
    (hin : i ∉ A.blockFinset n) : A.stageCard n + A.rankIdx m i < A.stageCard m := by
  classical
  set S := A.blockFinset n with hS
  set T := A.blockFinset m with hT
  have hST : S ⊆ T := A.blockFinset_subset hnm
  have hbi : ¬ A.birth i ≤ n := by
    intro hle
    exact hin ((A.mem_blockFinset n i).2 (A.mem_coordinateBlock_of_birth_le hle))
  have hsub : T.filter (fun j => A.key i < A.key j) ⊆ (T \ S).erase i := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_erase, Finset.mem_sdiff]
    refine ⟨?_, hj.1, ?_⟩
    · intro hji
      exact absurd (hji ▸ hj.2) (lt_irrefl _)
    · intro hjS
      have h1 : A.birth j ≤ n := A.birth_le_of_mem ((A.mem_blockFinset n j).1 hjS)
      have h2 := A.birth_le_of_key_lt hj.2
      omega
  have h1 : A.rankIdx m i ≤ ((T \ S).erase i).card := Finset.card_le_card hsub
  have h2 : ((T \ S).erase i).card = (T \ S).card - 1 := Finset.card_erase_of_mem
    (by rw [Finset.mem_sdiff]; exact ⟨him, hin⟩)
  have h3 : 0 < (T \ S).card := Finset.card_pos.2 ⟨i, by rw [Finset.mem_sdiff]; exact ⟨him, hin⟩⟩
  have hcards : (T \ S).card + S.card = T.card := Finset.card_sdiff_add_card_eq_card hST
  rw [stageCard, stageCard, ← hS, ← hT]
  omega

/-! ### The coherent enumeration of a stage -/

theorem rankIdx_bijective (n : ℕ) :
    Function.Bijective
      (fun i : A.Coord n => (⟨A.rankIdx n (i : I),
        A.rankIdx_lt ((A.mem_blockFinset n (i : I)).2 i.2)⟩ : Fin (A.stageCard n))) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro i j hij
    exact Subtype.ext (A.rankIdx_injOn ((A.mem_blockFinset n (i : I)).2 i.2)
      ((A.mem_blockFinset n (j : I)).2 j.2) (congrArg Fin.val hij))
  · rw [A.card_coord n, Fintype.card_fin]

/-- **The constructed coherent enumeration of a stage coordinate block.** -/
noncomputable def stageEnum (n : ℕ) : A.Coord n ≃ Fin (A.stageCard n) :=
  Equiv.ofBijective _ (A.rankIdx_bijective n)

@[simp] theorem stageEnum_val (n : ℕ) (i : A.Coord n) :
    ((A.stageEnum n i : Fin (A.stageCard n)) : ℕ) = A.rankIdx n (i : I) := rfl

/-- The inclusion of a stage coordinate block into a later one. -/
def coordIncl {n m : ℕ} (h : n ≤ m) (i : A.Coord n) : A.Coord m :=
  ⟨(i : I), A.family.coordinateBlock_mono A.exhaustion h i.2⟩

@[simp] theorem coordIncl_coe {n m : ℕ} (h : n ≤ m) (i : A.Coord n) :
    ((A.coordIncl h i : A.Coord m) : I) = (i : I) := rfl

/-- **The coherence equation of the constructed enumerations.** -/
theorem stageEnum_coherent {n m : ℕ} (h : n ≤ m) (i : A.Coord n) :
    A.stageCard n + ((A.stageEnum m (A.coordIncl h i) : Fin (A.stageCard m)) : ℕ) =
      A.stageCard m + ((A.stageEnum n i : Fin (A.stageCard n)) : ℕ) := by
  rw [stageEnum_val, stageEnum_val, coordIncl_coe]
  exact A.stageCard_add_rankIdx h ((A.mem_blockFinset n (i : I)).2 i.2)

/-- **The leading positions of a later stage are the new coordinates.** -/
theorem stageEnum_lt_of_not_mem {n m : ℕ} (h : n ≤ m) (i : A.Coord m)
    (hi : (i : I) ∉ A.family.coordinateBlock A.exhaustion n) :
    A.stageCard n + ((A.stageEnum m i : Fin (A.stageCard m)) : ℕ) < A.stageCard m := by
  rw [stageEnum_val]
  exact A.stageCard_add_rankIdx_lt h ((A.mem_blockFinset m (i : I)).2 i.2)
    (fun hc => hi ((A.mem_blockFinset n (i : I)).1 hc))

/-! ## Exponent coordinates along the source inclusions -/

/-- The basis coefficients of a stage label are the coefficients of the
underlying finitely supported coordinate word. -/
theorem stageCoordBasis_repr_apply (n : ℕ) (v : A.SourceLabel n)
    (p : A.Coord n ⊕ A.Coord n) :
    (A.stageCoordBasis n).repr v p =
      (v : PauliCoordinateLabels I) ((A.blockIndexEquiv n p : ↥(A.coordSupport n)) : I ⊕ I) := by
  have key : ∀ q : A.Coord n ⊕ A.Coord n,
      ((Finsupp.lapply p).comp (A.stageCoordBasis n).repr.toLinearMap) (A.stageCoordBasis n q) =
      ((Finsupp.lapply ((A.blockIndexEquiv n p : ↥(A.coordSupport n)) : I ⊕ I)).comp
        ((A.SourceLabel n).subtype)) (A.stageCoordBasis n q) := by
    intro q
    show (A.stageCoordBasis n).repr (A.stageCoordBasis n q) p =
      ((A.stageCoordBasis n q : A.SourceLabel n) : PauliCoordinateLabels I) _
    rw [Module.Basis.repr_self, A.stageCoordBasis_coe n q, Finsupp.single_apply,
      Finsupp.single_apply]
    refine if_congr ?_ rfl rfl
    constructor
    · rintro rfl; rfl
    · intro h
      exact (A.blockIndexEquiv n).injective (Subtype.ext h)
  have hext := Module.Basis.ext (A.stageCoordBasis n) key
  exact congrFun (congrArg (fun f : A.SourceLabel n →ₗ[PauliBit] PauliBit => (f : _ → _)) hext) v

theorem zPart_apply (n : ℕ) (v : A.SourceLabel n) (i : A.Coord n) :
    A.zPart n v i = (v : PauliCoordinateLabels I) (Sum.inl (i : I)) :=
  A.stageCoordBasis_repr_apply n v (Sum.inl i)

theorem xPart_apply (n : ℕ) (v : A.SourceLabel n) (i : A.Coord n) :
    A.xPart n v i = (v : PauliCoordinateLabels I) (Sum.inr (i : I)) :=
  A.stageCoordBasis_repr_apply n v (Sum.inr i)

/-- A stage label has no coefficient outside its coordinate block. -/
theorem coeff_eq_zero_of_not_mem (n : ℕ) (v : A.SourceLabel n) (p : I ⊕ I)
    (hp : CoherentLocalHyperbolic.site p ∉ A.family.coordinateBlock A.exhaustion n) :
    (v : PauliCoordinateLabels I) p = 0 := by
  by_contra hne
  exact hp (((A.family.mem_sourceLabels_iff A.exhaustion n _).1 v.2) p
    (Finsupp.mem_support_iff.2 hne))

/-- **Exponent transport.**  Along a source inclusion the enumerated exponent
vectors are exactly the zero-paddings of the earlier ones.  This is the
combinatorial heart of the coherence square. -/
theorem enumRepr_sourceIncl {n m : ℕ} (h : n ≤ m) (v : A.SourceLabel n) :
    A.enumRepr m (A.stageEnum m) (A.sourceIncl h v) =
      (padReg (A.stageCard n) (A.stageCard m) (A.enumRepr n (A.stageEnum n) v).1,
        padReg (A.stageCard n) (A.stageCard m) (A.enumRepr n (A.stageEnum n) v).2) := by
  have main : ∀ (part : ∀ (n : ℕ), A.SourceLabel n → A.Coord n → PauliBit),
      (∀ (n : ℕ) (w : A.SourceLabel n) (i : A.Coord n),
        part n w i = (w : PauliCoordinateLabels I) (Sum.inl (i : I))) ∨
      (∀ (n : ℕ) (w : A.SourceLabel n) (i : A.Coord n),
        part n w i = (w : PauliCoordinateLabels I) (Sum.inr (i : I))) →
      (fun j => part m (A.sourceIncl h v) ((A.stageEnum m).symm j)) =
        padReg (A.stageCard n) (A.stageCard m)
          (fun j => part n v ((A.stageEnum n).symm j)) := by
    intro part hpart
    funext j
    set i : A.Coord m := (A.stageEnum m).symm j with hi
    have hj : A.stageEnum m i = j := (A.stageEnum m).apply_symm_apply j
    by_cases hmem : (i : I) ∈ A.family.coordinateBlock A.exhaustion n
    · set i' : A.Coord n := ⟨(i : I), hmem⟩ with hi'
      have hincl : A.coordIncl h i' = i := Subtype.ext rfl
      have hcoh := A.stageEnum_coherent h i'
      rw [hincl, hj] at hcoh
      have hpad : padReg (A.stageCard n) (A.stageCard m)
          (fun j => part n v ((A.stageEnum n).symm j)) j =
          part n v ((A.stageEnum n).symm (A.stageEnum n i')) :=
        padReg_apply_of_le _ j (A.stageEnum n i') (by omega)
      rw [hpad, Equiv.symm_apply_apply]
      rcases hpart with hp | hp
      · rw [hp m (A.sourceIncl h v) i, hp n v i', A.sourceIncl_coe h v]
      · rw [hp m (A.sourceIncl h v) i, hp n v i', A.sourceIncl_coe h v]
    · have hlt := A.stageEnum_lt_of_not_mem h i hmem
      rw [hj] at hlt
      rw [padReg_apply_of_lt _ j (by omega)]
      rcases hpart with hp | hp
      · rw [hp m (A.sourceIncl h v) i, A.sourceIncl_coe h v]
        exact A.coeff_eq_zero_of_not_mem n v (Sum.inl (i : I)) hmem
      · rw [hp m (A.sourceIncl h v) i, A.sourceIncl_coe h v]
        exact A.coeff_eq_zero_of_not_mem n v (Sum.inr (i : I)) hmem
  refine Prod.ext ?_ ?_
  · exact main A.xPart (Or.inr (fun n w i => A.xPart_apply n w i))
  · exact main A.zPart (Or.inl (fun n w i => A.zPart_apply n w i))

/-! ## The coherent finite-stage bridge and its commuting squares -/

/-- **The coherent finite-stage bridge** of P55A, taken in the constructed
coherent enumeration of the stage coordinate block. -/
noncomputable def stageUHFEquiv (n : ℕ) :
    pauliAlgebra (A.sourceForm n) ≃⋆ₐ[ℂ] QubitTensorPower (A.stageCard n) :=
  A.sourceStageUHFEquiv n (A.stageEnum n)

theorem stageUHFEquiv_word (n : ℕ) (v : A.SourceLabel n) :
    A.stageUHFEquiv n (pauliWord (A.sourceForm n) v) =
      qubitWord (A.stageCard n) (A.enumRepr n (A.stageEnum n) v).1
        (A.enumRepr n (A.stageEnum n) v).2 :=
  A.sourceStageUHFEquiv_word n (A.stageEnum n) v

/-- **The coherence square.**  The constructed finite-stage bridges intertwine
the P53 source connecting maps with the canonical dyadic tower maps.  Nothing
here is assumed: both the enumeration and the square are constructed. -/
theorem stageUHFEquiv_sourceConnecting {n m : ℕ} (h : n ≤ m)
    (x : pauliAlgebra (A.sourceForm n)) :
    A.stageUHFEquiv m (A.sourceConnecting n m h x) =
      qubitTensorPowerMap (A.stageCard n) (A.stageCard m) (A.stageCard_mono h)
        (A.stageUHFEquiv n x) := by
  refine pauliAlgebra_linear_ext (A.sourceForm n)
    (((A.stageUHFEquiv m).toAlgEquiv.toLinearMap).comp
      ((A.sourceConnecting n m h).toAlgHom.toLinearMap))
    (((qubitTensorPowerMap (A.stageCard n) (A.stageCard m)
        (A.stageCard_mono h)).toAlgHom.toLinearMap).comp
      ((A.stageUHFEquiv n).toAlgEquiv.toLinearMap)) ?_ x
  intro v
  show A.stageUHFEquiv m (A.sourceConnecting n m h (pauliWord (A.sourceForm n) v)) =
    qubitTensorPowerMap (A.stageCard n) (A.stageCard m) (A.stageCard_mono h)
      (A.stageUHFEquiv n (pauliWord (A.sourceForm n) v))
  rw [A.sourceConnecting_word n m h v, A.stageUHFEquiv_word m, A.stageUHFEquiv_word n,
    qubitTensorPowerMap_qubitWord, A.enumRepr_sourceIncl h v]

/-! ## The coordinate-dyadic direct limit -/

/-- The dyadic connecting maps attached to the coordinate stages. -/
noncomputable def coordDyadicMap (n m : ℕ) (h : n ≤ m) :
    QubitTensorPower (A.stageCard n) →⋆ₐ[ℂ] QubitTensorPower (A.stageCard m) :=
  qubitTensorPowerMap (A.stageCard n) (A.stageCard m) (A.stageCard_mono h)

noncomputable instance coordDyadicDirected :
    DirectedSystem (fun n => QubitTensorPower (A.stageCard n))
      (fun n m h => A.coordDyadicMap n m h) where
  map_self := by
    intro n x
    change qubitTensorPowerMap (A.stageCard n) (A.stageCard n) _ x = x
    rw [qubitTensorPowerMap_self]
    rfl
  map_map := by
    intro k j i hij hjk x
    change qubitTensorPowerMap (A.stageCard j) (A.stageCard k) _
        (qubitTensorPowerMap (A.stageCard i) (A.stageCard j) _ x) =
      qubitTensorPowerMap (A.stageCard i) (A.stageCard k) _ x
    rw [qubitTensorPowerMap_comp (A.stageCard i) (A.stageCard j) (A.stageCard k)
      (A.stageCard_mono hij) (A.stageCard_mono hjk)]
    rfl

/-- **The coordinate-dyadic direct limit**: the algebraic direct limit of the
dyadic matrix stages attached to the coordinate blocks. -/
noncomputable abbrev CoordinateDyadicLimit : Type :=
  DirectLimit (fun n => QubitTensorPower (A.stageCard n)) (fun n m h => A.coordDyadicMap n m h)

/-- The canonical map of a coordinate-dyadic stage into the limit. -/
noncomputable abbrev coordDyadicOf (n : ℕ) (x : QubitTensorPower (A.stageCard n)) :
    A.CoordinateDyadicLimit :=
  DirectLimit.Module.of ℂ ℕ (fun n => QubitTensorPower (A.stageCard n))
    (fun n m h => A.coordDyadicMap n m h) n x

theorem coordDyadicOf_map {n m : ℕ} (h : n ≤ m) (x : QubitTensorPower (A.stageCard n)) :
    A.coordDyadicOf m (A.coordDyadicMap n m h x) = A.coordDyadicOf n x :=
  DirectLimit.Module.of_f (hij := h)

/-- **The source-to-coordinate-dyadic star equivalence.**  It is constructed
from the P55A finite-stage bridges and the proved coherence square, not
supplied. -/
noncomputable def sourceToCoordinateDyadic :
    A.SourceLimit ≃⋆ₐ[ℂ] A.CoordinateDyadicLimit :=
  algebraicLimitStarAlgEquiv
    (A := fun n => pauliAlgebra (A.sourceForm n))
    (f := fun n m h => A.sourceConnecting n m h)
    (D := fun n => QubitTensorPower (A.stageCard n))
    (h := fun n m h => A.coordDyadicMap n m h)
    A.stageUHFEquiv (fun _ _ h x => A.stageUHFEquiv_sourceConnecting h x)

/-- **The stage formula.** -/
@[simp] theorem sourceToCoordinateDyadic_of (n : ℕ) (x : pauliAlgebra (A.sourceForm n)) :
    A.sourceToCoordinateDyadic (A.sourceOf n x) = A.coordDyadicOf n (A.stageUHFEquiv n x) :=
  rfl

/-- **Uniqueness from the stage formulas.**  Any star-algebra homomorphism with
the stage formulas of `sourceToCoordinateDyadic` is that map. -/
theorem sourceToCoordinateDyadic_unique
    (psi : A.SourceLimit →⋆ₐ[ℂ] A.CoordinateDyadicLimit)
    (hpsi : ∀ (n : ℕ) (x : pauliAlgebra (A.sourceForm n)),
      psi (A.sourceOf n x) = A.coordDyadicOf n (A.stageUHFEquiv n x)) :
    ∀ z, psi z = A.sourceToCoordinateDyadic z := by
  intro z
  induction z using DirectLimit.induction with
  | _ n x => exact hpsi n x

/-! ## The infinite branch: cofinal stage cardinalities and the UHF algebra -/

/-- **Cofinality of the stage cardinalities.**  If the coordinate index type is
infinite, every number of qubits is reached by some coordinate block. -/
theorem stageCard_cofinal [Infinite I] (k : ℕ) : ∃ n, k ≤ A.stageCard n := by
  classical
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq I k
  refine ⟨S.sup A.birth, ?_⟩
  have hsub : S ⊆ A.blockFinset (S.sup A.birth) := by
    intro i hi
    rw [mem_blockFinset]
    exact A.mem_coordinateBlock_of_birth_le (Finset.le_sup hi)
  calc k = S.card := hS.symm
    _ ≤ (A.blockFinset (S.sup A.birth)).card := Finset.card_le_card hsub
    _ = A.stageCard (S.sup A.birth) := rfl

/-- A coordinate stage with at least `k` qubits. -/
noncomputable def cofinalStage [Infinite I] (k : ℕ) : ℕ :=
  Nat.find (A.stageCard_cofinal k)

theorem le_stageCard_cofinalStage [Infinite I] (k : ℕ) :
    k ≤ A.stageCard (A.cofinalStage k) :=
  Nat.find_spec (A.stageCard_cofinal k)

/-- The dyadic stage `k`, mapped into the coordinate-dyadic limit through a
coordinate block large enough to contain it. -/
noncomputable def uhfStageToCoord [Infinite I] (k : ℕ) :
    QubitTensorPower k →⋆ₐ[ℂ] A.CoordinateDyadicLimit :=
  (algebraicLimitStageStarAlgHom
      (A := fun n => QubitTensorPower (A.stageCard n))
      (f := fun n m h => A.coordDyadicMap n m h) (A.cofinalStage k)).comp
    (qubitTensorPowerMap k (A.stageCard (A.cofinalStage k)) (A.le_stageCard_cofinalStage k))

/-- The value of `uhfStageToCoord` may be computed at any sufficiently large
coordinate stage. -/
theorem uhfStageToCoord_eq [Infinite I] {k n : ℕ} (hk : k ≤ A.stageCard n)
    (hn : A.cofinalStage k ≤ n) (x : QubitTensorPower k) :
    A.uhfStageToCoord k x = A.coordDyadicOf n (qubitTensorPowerMap k (A.stageCard n) hk x) := by
  have hcomp : qubitTensorPowerMap k (A.stageCard n) hk x =
      A.coordDyadicMap (A.cofinalStage k) n hn
        (qubitTensorPowerMap k (A.stageCard (A.cofinalStage k))
          (A.le_stageCard_cofinalStage k) x) := by
    show _ = qubitTensorPowerMap (A.stageCard (A.cofinalStage k)) (A.stageCard n) _
      (qubitTensorPowerMap k (A.stageCard (A.cofinalStage k)) _ x)
    rw [qubitTensorPowerMap_comp k (A.stageCard (A.cofinalStage k)) (A.stageCard n)
      (A.le_stageCard_cofinalStage k) (A.stageCard_mono hn)]
    rfl
  rw [hcomp, A.coordDyadicOf_map hn]
  rfl

theorem uhfStageToCoord_compatible [Infinite I] {k k' : ℕ} (h : k ≤ k')
    (x : QubitTensorPower k) :
    A.uhfStageToCoord k' (qubitTensorPowerMap k k' h x) = A.uhfStageToCoord k x := by
  set n : ℕ := max (A.cofinalStage k) (A.cofinalStage k') with hn
  have hk' : k' ≤ A.stageCard n :=
    le_trans (A.le_stageCard_cofinalStage k') (A.stageCard_mono (le_max_right _ _))
  have hk : k ≤ A.stageCard n := le_trans h hk'
  rw [A.uhfStageToCoord_eq hk' (le_max_right _ _), A.uhfStageToCoord_eq hk (le_max_left _ _),
    qubitTensorPowerMap_comp k k' (A.stageCard n) h hk']
  rfl

/-- The star-algebra map from the qubit UHF algebra into the coordinate-dyadic
limit. -/
noncomputable def uhfToCoordDyadic [Infinite I] :
    QubitUHFAlgebra →⋆ₐ[ℂ] A.CoordinateDyadicLimit :=
  algebraicLimitStarAlgHom A.uhfStageToCoord
    (fun _ _ h x => A.uhfStageToCoord_compatible h x)

/-- The star-algebra map from the coordinate-dyadic limit into the qubit UHF
algebra. -/
noncomputable def coordDyadicToUHF : A.CoordinateDyadicLimit →⋆ₐ[ℂ] QubitUHFAlgebra :=
  algebraicLimitStarAlgHom
    (A := fun n => QubitTensorPower (A.stageCard n))
    (f := fun n m h => A.coordDyadicMap n m h)
    (fun n => algebraicLimitStageStarAlgHom
      (A := QubitTensorPower) (f := qubitTensorPowerMap) (A.stageCard n))
    (fun _ _ h _ => DirectLimit.Module.of_f (hij := A.stageCard_mono h))

@[simp] theorem coordDyadicToUHF_of (n : ℕ) (x : QubitTensorPower (A.stageCard n)) :
    A.coordDyadicToUHF (A.coordDyadicOf n x) = qubitUHFOf (A.stageCard n) x := rfl

@[simp] theorem uhfToCoordDyadic_of [Infinite I] (k : ℕ) (x : QubitTensorPower k) :
    A.uhfToCoordDyadic (qubitUHFOf k x) = A.uhfStageToCoord k x := rfl

/-- **The coordinate-dyadic limit is the qubit UHF algebra.**  This uses only
cofinality of the stage cardinalities. -/
noncomputable def coordinateDyadicUHFEquiv [Infinite I] :
    A.CoordinateDyadicLimit ≃⋆ₐ[ℂ] QubitUHFAlgebra :=
  StarAlgEquiv.ofStarAlgHom A.coordDyadicToUHF A.uhfToCoordDyadic
    (by
      intro z
      induction z using DirectLimit.induction with
      | _ n y =>
        show A.uhfToCoordDyadic (A.coordDyadicToUHF (A.coordDyadicOf n y)) = A.coordDyadicOf n y
        rw [A.coordDyadicToUHF_of n y, A.uhfToCoordDyadic_of]
        set m : ℕ := max n (A.cofinalStage (A.stageCard n)) with hm
        have hk : A.stageCard n ≤ A.stageCard m := A.stageCard_mono (le_max_left _ _)
        rw [A.uhfStageToCoord_eq hk (le_max_right _ _)]
        exact A.coordDyadicOf_map (le_max_left n (A.cofinalStage (A.stageCard n))) y)
    (by
      intro z
      induction z using DirectLimit.induction with
      | _ k x =>
        show A.coordDyadicToUHF (A.uhfToCoordDyadic (qubitUHFOf k x)) = qubitUHFOf k x
        rw [A.uhfToCoordDyadic_of, uhfStageToCoord]
        show A.coordDyadicToUHF (A.coordDyadicOf (A.cofinalStage k)
          (qubitTensorPowerMap k (A.stageCard (A.cofinalStage k))
            (A.le_stageCard_cofinalStage k) x)) = qubitUHFOf k x
        rw [A.coordDyadicToUHF_of]
        exact qubitUHFOf_map (A.le_stageCard_cofinalStage k) x)

@[simp] theorem coordinateDyadicUHFEquiv_of [Infinite I] (n : ℕ)
    (x : QubitTensorPower (A.stageCard n)) :
    A.coordinateDyadicUHFEquiv (A.coordDyadicOf n x) = qubitUHFOf (A.stageCard n) x :=
  A.coordDyadicToUHF_of n x

/-- **The infinite branch.**  If the coordinate index type is infinite, the P53
algebraic source limit is star-equivalent to the qubit UHF algebra. -/
noncomputable def sourceUHFEquiv [Infinite I] : A.SourceLimit ≃⋆ₐ[ℂ] QubitUHFAlgebra :=
  A.sourceToCoordinateDyadic.trans A.coordinateDyadicUHFEquiv

/-- **The stage formula of the infinite branch.** -/
@[simp] theorem sourceUHFEquiv_of [Infinite I] (n : ℕ) (x : pauliAlgebra (A.sourceForm n)) :
    A.sourceUHFEquiv (A.sourceOf n x) = qubitUHFOf (A.stageCard n) (A.stageUHFEquiv n x) := by
  show A.coordinateDyadicUHFEquiv (A.sourceToCoordinateDyadic (A.sourceOf n x)) = _
  rw [A.sourceToCoordinateDyadic_of n x, A.coordinateDyadicUHFEquiv_of]

/-- **Uniqueness from the stage formulas, infinite branch.** -/
theorem sourceUHFEquiv_unique [Infinite I] (psi : A.SourceLimit →⋆ₐ[ℂ] QubitUHFAlgebra)
    (hpsi : ∀ (n : ℕ) (x : pauliAlgebra (A.sourceForm n)),
      psi (A.sourceOf n x) = qubitUHFOf (A.stageCard n) (A.stageUHFEquiv n x)) :
    ∀ z, psi z = A.sourceUHFEquiv z := by
  intro z
  induction z using DirectLimit.induction with
  | _ n x =>
    show psi (A.sourceOf n x) = A.sourceUHFEquiv (A.sourceOf n x)
    rw [hpsi n x, A.sourceUHFEquiv_of n x]

/-! ## The finite branch: a terminal coordinate block -/

/-- **The exhaustion reaches a terminal coordinate block.**  If the coordinate
index type is finite, some stage of the exhaustion already contains every
coordinate. -/
theorem exists_terminal_stage [Finite I] : ∃ N : ℕ, ∀ i : I, A.birth i ≤ N := by
  classical
  haveI : Fintype I := Fintype.ofFinite I
  exact ⟨Finset.univ.sup A.birth, fun i => Finset.le_sup (Finset.mem_univ i)⟩

/-- The first terminal stage of the exhaustion. -/
noncomputable def terminalStage [Finite I] : ℕ := Nat.find A.exists_terminal_stage

theorem birth_le_terminalStage [Finite I] (i : I) : A.birth i ≤ A.terminalStage :=
  Nat.find_spec A.exists_terminal_stage i

/-- **The terminal coordinate block is everything.** -/
theorem mem_coordinateBlock_terminal [Finite I] {n : ℕ} (h : A.terminalStage ≤ n) (i : I) :
    i ∈ A.family.coordinateBlock A.exhaustion n :=
  A.mem_coordinateBlock_of_birth_le (le_trans (A.birth_le_terminalStage i) h)

/-- From the terminal stage on, every stage carries exactly `Nat.card I`
qubits. -/
theorem stageCard_eq_card [Finite I] {n : ℕ} (h : A.terminalStage ≤ n) :
    A.stageCard n = Nat.card I := by
  classical
  haveI : Fintype I := Fintype.ofFinite I
  have huniv : A.blockFinset n = Finset.univ :=
    Finset.eq_univ_iff_forall.2 (fun i => (A.mem_blockFinset n i).2
      (A.mem_coordinateBlock_terminal h i))
  rw [stageCard, huniv, Finset.card_univ, Nat.card_eq_fintype_card]

theorem coordDyadicMap_bijective_of_terminal [Finite I] {n m : ℕ}
    (hn : A.terminalStage ≤ n) (h : n ≤ m) : Function.Bijective (A.coordDyadicMap n m h) :=
  qubitTensorPowerMap_bijective_of_eq (A.stageCard_mono h)
    ((A.stageCard_eq_card hn).trans (A.stageCard_eq_card (le_trans hn h)).symm)

/-- **The coordinate-dyadic limit is reached at the terminal stage.** -/
theorem coordDyadicOf_terminal_bijective [Finite I] :
    Function.Bijective (fun x : QubitTensorPower (A.stageCard A.terminalStage) =>
      A.coordDyadicOf A.terminalStage x) := by
  constructor
  · intro x y hxy
    obtain ⟨i, hx, hy, heq⟩ := Quotient.eq.mp hxy
    exact (A.coordDyadicMap_bijective_of_terminal le_rfl hx).1 heq
  · intro z
    induction z using DirectLimit.induction with
    | _ n y =>
      obtain ⟨w, hw⟩ := (A.coordDyadicMap_bijective_of_terminal le_rfl
        (le_max_left A.terminalStage n)).2
          (A.coordDyadicMap n (max A.terminalStage n) (le_max_right _ _) y)
      refine ⟨w, ?_⟩
      have hstep : A.coordDyadicOf (max A.terminalStage n)
          (A.coordDyadicMap n (max A.terminalStage n) (le_max_right _ _) y) =
          A.coordDyadicOf n y := A.coordDyadicOf_map (le_max_right _ _) y
      show A.coordDyadicOf A.terminalStage w = A.coordDyadicOf n y
      rw [← hstep, ← hw]
      exact (A.coordDyadicOf_map (le_max_left A.terminalStage n) w).symm

/-- **The terminal stage identification** of the coordinate-dyadic limit. -/
noncomputable def terminalDyadicEquiv [Finite I] :
    QubitTensorPower (A.stageCard A.terminalStage) ≃⋆ₐ[ℂ] A.CoordinateDyadicLimit :=
  StarAlgEquiv.ofBijective
    (algebraicLimitStageStarAlgHom
      (A := fun n => QubitTensorPower (A.stageCard n))
      (f := fun n m h => A.coordDyadicMap n m h) A.terminalStage)
    A.coordDyadicOf_terminal_bijective

@[simp] theorem terminalDyadicEquiv_apply [Finite I]
    (x : QubitTensorPower (A.stageCard A.terminalStage)) :
    A.terminalDyadicEquiv x = A.coordDyadicOf A.terminalStage x := rfl

theorem terminalDyadicEquiv_symm_coordDyadicOf [Finite I] {n : ℕ} (hn : A.terminalStage ≤ n)
    (y : QubitTensorPower (A.stageCard n)) :
    A.terminalDyadicEquiv.symm (A.coordDyadicOf n y) =
      qubitTensorPowerCongr ((A.stageCard_eq_card hn).trans
        (A.stageCard_eq_card (le_refl A.terminalStage)).symm) y := by
  have hmap : A.coordDyadicMap A.terminalStage n hn
      (qubitTensorPowerCongr ((A.stageCard_eq_card hn).trans
        (A.stageCard_eq_card (le_refl A.terminalStage)).symm) y) = y := by
    rw [coordDyadicMap, qubitTensorPowerMap_of_eq (A.stageCard_mono hn)
      ((A.stageCard_eq_card (le_refl A.terminalStage)).trans (A.stageCard_eq_card hn).symm),
      qubitTensorPowerCongr_trans]
    rfl
  have hy : A.coordDyadicOf n y =
      A.terminalDyadicEquiv (qubitTensorPowerCongr ((A.stageCard_eq_card hn).trans
        (A.stageCard_eq_card (le_refl A.terminalStage)).symm) y) := by
    rw [terminalDyadicEquiv_apply, ← A.coordDyadicOf_map hn, hmap]
  rw [hy, StarAlgEquiv.symm_apply_apply]

/-- **The finite branch.**  If the coordinate index type is finite, the P53
algebraic source limit is star-equivalent to the finite dyadic algebra of
`Nat.card I` qubits. -/
noncomputable def sourceFiniteEquiv [Finite I] :
    A.SourceLimit ≃⋆ₐ[ℂ] QubitTensorPower (Nat.card I) :=
  (A.sourceToCoordinateDyadic.trans A.terminalDyadicEquiv.symm).trans
    (qubitTensorPowerCongr (A.stageCard_eq_card (le_refl A.terminalStage)))

/-- **The stage formula of the finite branch**, at every stage from the terminal
one on. -/
theorem sourceFiniteEquiv_of [Finite I] {n : ℕ} (hn : A.terminalStage ≤ n)
    (x : pauliAlgebra (A.sourceForm n)) :
    A.sourceFiniteEquiv (A.sourceOf n x) =
      qubitTensorPowerCongr (A.stageCard_eq_card hn) (A.stageUHFEquiv n x) := by
  show qubitTensorPowerCongr (A.stageCard_eq_card (le_refl A.terminalStage))
    (A.terminalDyadicEquiv.symm (A.sourceToCoordinateDyadic (A.sourceOf n x))) = _
  rw [A.sourceToCoordinateDyadic_of n x, A.terminalDyadicEquiv_symm_coordDyadicOf hn,
    qubitTensorPowerCongr_trans]

/-- The canonical stage maps into the source limit are compatible with the P53
source connecting maps. -/
theorem sourceOf_sourceConnecting {n m : ℕ} (h : n ≤ m) (x : pauliAlgebra (A.sourceForm n)) :
    A.sourceOf m (A.sourceConnecting n m h x) = A.sourceOf n x := by
  have himg : A.sourceToCoordinateDyadic (A.sourceOf m (A.sourceConnecting n m h x)) =
      A.sourceToCoordinateDyadic (A.sourceOf n x) := by
    rw [A.sourceToCoordinateDyadic_of, A.sourceToCoordinateDyadic_of,
      A.stageUHFEquiv_sourceConnecting h x]
    exact A.coordDyadicOf_map h (A.stageUHFEquiv n x)
  exact A.sourceToCoordinateDyadic.injective himg

/-- **Uniqueness from the stage formulas, finite branch.** -/
theorem sourceFiniteEquiv_unique [Finite I]
    (psi : A.SourceLimit →⋆ₐ[ℂ] QubitTensorPower (Nat.card I))
    (hpsi : ∀ (n : ℕ) (hn : A.terminalStage ≤ n) (x : pauliAlgebra (A.sourceForm n)),
      psi (A.sourceOf n x) =
        qubitTensorPowerCongr (A.stageCard_eq_card hn) (A.stageUHFEquiv n x)) :
    ∀ z, psi z = A.sourceFiniteEquiv z := by
  have key : ∀ (n : ℕ) (x : pauliAlgebra (A.sourceForm n)),
      psi (A.sourceOf n x) = A.sourceFiniteEquiv (A.sourceOf n x) := by
    intro n x
    have hnm : n ≤ max n A.terminalStage := le_max_left _ _
    have htm : A.terminalStage ≤ max n A.terminalStage := le_max_right _ _
    rw [← A.sourceOf_sourceConnecting hnm x, hpsi _ htm, A.sourceFiniteEquiv_of htm]
  intro z
  induction z using DirectLimit.induction with
  | _ n x => exact key n x

end AlphaData

end LocalHyperbolicAlpha

end StabilizerHyperfinite
