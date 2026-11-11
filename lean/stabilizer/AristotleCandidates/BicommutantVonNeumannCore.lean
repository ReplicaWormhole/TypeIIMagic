import Mathlib.Analysis.VonNeumannAlgebra.Basic

/-!
# The algebraic bicommutant of a star subalgebra of `B(H)`

Given a Hilbert space `H` and a star subalgebra `S : StarSubalgebra ℂ (H →L[ℂ] H)` of the
bounded operators on `H`, its *commutant* (centralizer) `S'` is again a star subalgebra, and
the double commutant `S''` satisfies `S'''' = S''`.  Hence `S''` is a *concrete* von Neumann
algebra in the sense of `VonNeumannAlgebra H` (Mathlib's `structure` bundling a star
subalgebra which equals its own double commutant).

This file packages that construction as

    StarSubalgebra.vonNeumannGenerated : StarSubalgebra ℂ (H →L[ℂ] H) → VonNeumannAlgebra H

and proves the elementary order-theoretic facts which are available *purely* from the
centralizer API:

* `StarSubalgebra.le_vonNeumannGenerated` — `S ≤ S''`;
* `StarSubalgebra.vonNeumannGenerated_mono` — `S ≤ T → S'' ≤ T''`;
* `VonNeumannAlgebra.vonNeumannGenerated_toStarSubalgebra` — `M'' = M` for a concrete
  von Neumann algebra `M`;
* `StarSubalgebra.vonNeumannGenerated_idem` — idempotence of the construction;
* `StarSubalgebra.mem_vonNeumannGenerated_iff` — membership in `S''` is exactly
  "commutes with everything in the commutant of `S`", and the variant
  `StarSubalgebra.mem_vonNeumannGenerated_iff_commutant` phrased via
  `VonNeumannAlgebra.commutant`.

## Scope: algebra versus analysis

Everything below is **purely algebraic**: `Set.centralizer` is used throughout and no
topology on `H →L[ℂ] H` enters.  In particular this file does **not** assert (and does not
use) the von Neumann *double commutant theorem*, i.e. the analytic statement that for a
unital star subalgebra `S ⊆ B(H)` one has

    S'' = closure of S in the strong operator topology
        = closure of S in the weak operator topology.

At the pinned Mathlib commit that theorem is not available: there is no declaration in
`Mathlib.Analysis.VonNeumannAlgebra.*` relating `Set.centralizer (Set.centralizer S)` to any
operator-topology closure (the module docstring of `Mathlib/Analysis/VonNeumannAlgebra/Basic.lean`
explicitly lists it as future work: *"We'll also need to prove the von Neumann double commutant
theorem, that the concrete definition is equivalent to a *-closed subalgebra which is weakly
closed."*).  Accordingly no such statement is axiomatized here; only the algebraic facts that
do compile are stated.  Consequently `vonNeumannGenerated S` should be read as *the smallest
concrete von Neumann algebra containing `S` that the algebraic API can produce*, and its
minimality among von Neumann algebras containing `S` is recorded below in
`StarSubalgebra.vonNeumannGenerated_le` (which *is* purely algebraic).
-/

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace StarSubalgebra

/-- The underlying set of the centralizer of a *star* subalgebra `S` of `H →L[ℂ] H` is just the
set-theoretic centralizer of `S`: no star-closure is needed since `S` is already star closed. -/
theorem coe_centralizer_of_starSubalgebra (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) =
      Set.centralizer (S : Set (H →L[ℂ] H)) := by
  rw [StarSubalgebra.coe_centralizer, StarMemClass.star_coe_eq, Set.union_self]

/-- The underlying set of the double centralizer of a star subalgebra `S` of `H →L[ℂ] H` is the
set-theoretic double centralizer of `S`. -/
theorem coe_centralizer_centralizer_of_starSubalgebra (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    ((StarSubalgebra.centralizer ℂ
        (StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) :
          StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) =
      Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
  rw [StarSubalgebra.coe_centralizer_centralizer, StarMemClass.star_coe_eq, Set.union_self]

/-- The bicommutant of a star subalgebra `S` of the bounded operators on a Hilbert space `H`,
packaged as a concrete von Neumann algebra.

This is the **algebraic** double commutant construction; see the module docstring for the
relation (not proved here) with the strong/weak operator closure. -/
noncomputable def vonNeumannGenerated (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    VonNeumannAlgebra H where
  toStarSubalgebra :=
    StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))
  centralizer_centralizer' := by
    show Set.centralizer (Set.centralizer
        ((StarSubalgebra.centralizer ℂ
          (StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) :
            StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H))) =
      ((StarSubalgebra.centralizer ℂ
          (StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) :
            StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H))
    rw [coe_centralizer_centralizer_of_starSubalgebra,
      Set.centralizer_centralizer_centralizer]

@[simp]
theorem coe_vonNeumannGenerated (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (vonNeumannGenerated S : Set (H →L[ℂ] H)) =
      Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
  exact coe_centralizer_centralizer_of_starSubalgebra S

/-- **Membership in the bicommutant**: `x ∈ S''` iff `x` commutes with every element of the
commutant of `S`. -/
theorem mem_vonNeumannGenerated_iff {S : StarSubalgebra ℂ (H →L[ℂ] H)} {x : H →L[ℂ] H} :
    x ∈ vonNeumannGenerated S ↔
      ∀ y ∈ Set.centralizer (S : Set (H →L[ℂ] H)), y * x = x * y := by
  rw [← SetLike.mem_coe, coe_vonNeumannGenerated]
  rfl

/-- The commutant of `S''`, as a von Neumann algebra, has underlying set the commutant of `S`. -/
@[simp]
theorem coe_commutant_vonNeumannGenerated (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    ((vonNeumannGenerated S).commutant : Set (H →L[ℂ] H)) =
      Set.centralizer (S : Set (H →L[ℂ] H)) := by
  rw [VonNeumannAlgebra.coe_commutant, coe_vonNeumannGenerated,
    Set.centralizer_centralizer_centralizer]

/-- Membership in the generated von Neumann algebra is characterized by commuting with the
commutant, phrased via `VonNeumannAlgebra.commutant`. -/
theorem mem_vonNeumannGenerated_iff_commutant {S : StarSubalgebra ℂ (H →L[ℂ] H)}
    {x : H →L[ℂ] H} :
    x ∈ vonNeumannGenerated S ↔ ∀ y ∈ (vonNeumannGenerated S).commutant, y * x = x * y := by
  rw [mem_vonNeumannGenerated_iff]
  refine forall_congr' fun y => ?_
  rw [← SetLike.mem_coe, coe_commutant_vonNeumannGenerated]

/-- **(1)** A star subalgebra is contained in its bicommutant. -/
theorem le_vonNeumannGenerated (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (S : Set (H →L[ℂ] H)) ⊆ (vonNeumannGenerated S : Set (H →L[ℂ] H)) := by
  rw [coe_vonNeumannGenerated]
  exact Set.subset_centralizer_centralizer

theorem mem_vonNeumannGenerated_of_mem {S : StarSubalgebra ℂ (H →L[ℂ] H)} {x : H →L[ℂ] H}
    (hx : x ∈ S) : x ∈ vonNeumannGenerated S :=
  le_vonNeumannGenerated S hx

/-- **(2)** The bicommutant construction is monotone. -/
theorem vonNeumannGenerated_mono {S T : StarSubalgebra ℂ (H →L[ℂ] H)} (h : S ≤ T) :
    vonNeumannGenerated S ≤ vonNeumannGenerated T := by
  intro x hx
  rw [← SetLike.mem_coe, coe_vonNeumannGenerated] at hx ⊢
  exact Set.centralizer_subset (Set.centralizer_subset h) hx

end StarSubalgebra

namespace VonNeumannAlgebra

open StarSubalgebra

/-- **(3)** The bicommutant of (the star subalgebra underlying) a concrete von Neumann algebra
is that von Neumann algebra itself. -/
@[simp]
theorem vonNeumannGenerated_toStarSubalgebra (M : VonNeumannAlgebra H) :
    vonNeumannGenerated M.toStarSubalgebra = M := by
  refine SetLike.coe_injective ?_
  rw [coe_vonNeumannGenerated]
  exact M.centralizer_centralizer

end VonNeumannAlgebra

namespace StarSubalgebra

/-- **(4)** The construction is idempotent at the `VonNeumannAlgebra` level. -/
@[simp]
theorem vonNeumannGenerated_idem (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    vonNeumannGenerated (vonNeumannGenerated S).toStarSubalgebra = vonNeumannGenerated S :=
  VonNeumannAlgebra.vonNeumannGenerated_toStarSubalgebra _

/-- Minimality: `S''` is contained in any concrete von Neumann algebra containing `S`.
This is purely algebraic (no operator-topology closure is involved). -/
theorem vonNeumannGenerated_le {S : StarSubalgebra ℂ (H →L[ℂ] H)} {M : VonNeumannAlgebra H}
    (h : (S : Set (H →L[ℂ] H)) ⊆ (M : Set (H →L[ℂ] H))) :
    (vonNeumannGenerated S : Set (H →L[ℂ] H)) ⊆ (M : Set (H →L[ℂ] H)) := by
  rw [coe_vonNeumannGenerated, ← M.centralizer_centralizer]
  exact Set.centralizer_subset (Set.centralizer_subset h)

/-- The commutant of `S` and the commutant of `S''` agree (as sets of operators):
taking commutants three times is the same as taking it once. -/
theorem centralizer_vonNeumannGenerated (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Set.centralizer (vonNeumannGenerated S : Set (H →L[ℂ] H)) =
      Set.centralizer (S : Set (H →L[ℂ] H)) := by
  rw [coe_vonNeumannGenerated, Set.centralizer_centralizer_centralizer]

end StarSubalgebra
