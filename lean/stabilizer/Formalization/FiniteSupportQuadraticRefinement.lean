import Formalization.QuadraticPhaseRefinement

/-!
# The finite-support quadratic-refinement formula

This is the literal coordinate formula used for a Pauli cocycle correction.
Every sum is indexed by the finite support of the coordinate word, so the
definition applies to an infinite ordered coordinate set.
-/

namespace StabilizerHyperfinite

/-- Regard a Pauli bit as its representative in the fourth-root exponent
group. -/
def liftPauliBit (a : ZMod 2) : ZMod 4 :=
  if a = 0 then 0 else 1

@[simp]
theorem liftPauliBit_zero : liftPauliBit 0 = 0 := by
  simp [liftPauliBit]

@[simp]
theorem liftPauliBit_one : liftPauliBit 1 = 1 := by
  simp [liftPauliBit]

/-- Addition of Pauli bits, read in ZMod 4, carries the usual quadratic
correction term. -/
theorem liftPauliBit_add (a b : ZMod 2) :
    liftPauliBit (a + b) =
      liftPauliBit a + liftPauliBit b - 2 * liftPauliBit a * liftPauliBit b := by
  have h_two : (2 : ZMod 2) = 0 := by
    change ((2 : ℕ) : ZMod 2) = 0
    exact ZMod.natCast_self 2
  fin_cases a
  all_goals fin_cases b
  all_goals norm_num [liftPauliBit, ZMod.val]
  all_goals simp [h_two]

/-- After multiplication by two, the bit lift is additive in ZMod 4. -/
theorem two_liftPauliBit_add (a b : ZMod 2) :
    2 * liftPauliBit (a + b) =
      2 * liftPauliBit a + 2 * liftPauliBit b := by
  have h_two : (2 : ZMod 2) = 0 := by
    change ((2 : ℕ) : ZMod 2) = 0
    exact ZMod.natCast_self 2
  have h_four : (4 : ZMod 4) = 0 := by
    change ((4 : ℕ) : ZMod 4) = 0
    exact ZMod.natCast_self 4
  fin_cases a
  all_goals fin_cases b
  all_goals norm_num [liftPauliBit, ZMod.val]
  all_goals simp [h_two, h_four]

/-- The ordered-basis candidate for the ZMod 4-valued quadratic refinement of
a Pauli cocycle discrepancy.  Symmetry is required later to prove its
polarization identity. -/
def coordinateQuadraticRefinement
    {ι : Type*} [LinearOrder ι] (discrepancy : ι → ι → ZMod 2)
    (x : ι →₀ ZMod 2) : ZMod 4 :=
  (∑ i ∈ x.support, liftPauliBit (x i) * liftPauliBit (discrepancy i i)) +
    ∑ i ∈ x.support, ∑ j ∈ x.support.filter (fun j => i < j),
      2 * liftPauliBit (x i) * liftPauliBit (x j) *
        liftPauliBit (discrepancy i j)

/-- The ZMod 4-valued finite-coordinate discrepancy pairing.  The factor of
two makes it additive in each Pauli-bit word argument. -/
def coordinateBilinear
    {ι : Type*} [LinearOrder ι] (discrepancy : ι → ι → ZMod 2)
    (x y : ι →₀ ZMod 2) : ZMod 4 :=
  x.sum fun i xi =>
    y.sum fun j yj =>
      2 * liftPauliBit xi * liftPauliBit yj * liftPauliBit (discrepancy i j)

/-- The explicit double-sum expansion of the finite-coordinate discrepancy
pairing. -/
theorem coordinateBilinear_apply
    {ι : Type*} [LinearOrder ι] (discrepancy : ι → ι → ZMod 2)
    (x y : ι →₀ ZMod 2) :
    coordinateBilinear discrepancy x y =
      ∑ i ∈ x.support, ∑ j ∈ y.support,
        2 * liftPauliBit (x i) * liftPauliBit (y j) *
          liftPauliBit (discrepancy i j) :=
  rfl

/-- The finite-coordinate discrepancy pairing is additive in its left word.
The proof uses the ZMod 4 form of bit-lift additivity. -/
theorem coordinateBilinear_add_left
    {ι : Type*} [LinearOrder ι] (discrepancy : ι → ι → ZMod 2)
    (x y z : ι →₀ ZMod 2) :
    coordinateBilinear discrepancy (x + y) z =
      coordinateBilinear discrepancy x z + coordinateBilinear discrepancy y z := by
  unfold coordinateBilinear
  apply Finsupp.sum_add_index'
  · intro i
    apply Finset.sum_eq_zero
    intro j hj
    simp
  · intro i a b
    rw [two_liftPauliBit_add]
    change (∑ j ∈ z.support,
      (2 * liftPauliBit a + 2 * liftPauliBit b) * liftPauliBit (z j) *
        liftPauliBit (discrepancy i j)) =
      (∑ j ∈ z.support,
        2 * liftPauliBit a * liftPauliBit (z j) *
          liftPauliBit (discrepancy i j)) +
      ∑ j ∈ z.support,
        2 * liftPauliBit b * liftPauliBit (z j) *
          liftPauliBit (discrepancy i j)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring

/-- The finite-coordinate discrepancy pairing is additive in its right word. -/
theorem coordinateBilinear_add_right
    {ι : Type*} [LinearOrder ι] (discrepancy : ι → ι → ZMod 2)
    (x y z : ι →₀ ZMod 2) :
    coordinateBilinear discrepancy x (y + z) =
      coordinateBilinear discrepancy x y + coordinateBilinear discrepancy x z := by
  unfold coordinateBilinear
  have h_inner : ∀ i xi,
      (y + z).sum (fun j yj =>
        2 * liftPauliBit xi * liftPauliBit yj * liftPauliBit (discrepancy i j)) =
      (y.sum (fun j yj =>
        2 * liftPauliBit xi * liftPauliBit yj * liftPauliBit (discrepancy i j))) +
      z.sum (fun j zj =>
        2 * liftPauliBit xi * liftPauliBit zj * liftPauliBit (discrepancy i j)) := by
    intro i xi
    apply Finsupp.sum_add_index'
    · intro j
      simp
    · intro j a b
      calc
        2 * liftPauliBit xi * liftPauliBit (a + b) *
            liftPauliBit (discrepancy i j) =
          liftPauliBit xi * (2 * liftPauliBit (a + b)) *
            liftPauliBit (discrepancy i j) := by ring
        _ = liftPauliBit xi *
            (2 * liftPauliBit a + 2 * liftPauliBit b) *
            liftPauliBit (discrepancy i j) := by rw [two_liftPauliBit_add]
        _ = 2 * liftPauliBit xi * liftPauliBit a *
            liftPauliBit (discrepancy i j) +
          2 * liftPauliBit xi * liftPauliBit b *
            liftPauliBit (discrepancy i j) := by ring
  change (∑ i ∈ x.support, (y + z).sum (fun j yj =>
      2 * liftPauliBit (x i) * liftPauliBit yj * liftPauliBit (discrepancy i j))) = _
  simp_rw [h_inner]
  rw [Finset.sum_add_distrib]
  rfl

/-- A symmetric discrepancy matrix gives a symmetric finite-coordinate
pairing.  The proof reduces additivity to one-coordinate words and then uses
the symmetry of the matrix entry. -/
theorem coordinateBilinear_symm
    {ι : Type*} [LinearOrder ι] (discrepancy : ι → ι → ZMod 2)
    (hsymm : ∀ i j, discrepancy i j = discrepancy j i)
    (x y : ι →₀ ZMod 2) :
    coordinateBilinear discrepancy x y = coordinateBilinear discrepancy y x := by
  induction x using Finsupp.induction with
  | zero =>
    simp [coordinateBilinear]
  | single_add i a x hix ha ihx =>
    rw [coordinateBilinear_add_left]
    rw [coordinateBilinear_add_right, ihx]
    have h_single : ∀ y : ι →₀ ZMod 2,
        coordinateBilinear discrepancy (Finsupp.single i a) y =
          coordinateBilinear discrepancy y (Finsupp.single i a) := by
      intro y
      induction y using Finsupp.induction with
      | zero => simp [coordinateBilinear]
      | single_add j b y hjb hb ihy =>
        rw [coordinateBilinear_add_right, coordinateBilinear_add_left, ihy]
        have h_pair :
            coordinateBilinear discrepancy (Finsupp.single i a) (Finsupp.single j b) =
              coordinateBilinear discrepancy (Finsupp.single j b) (Finsupp.single i a) := by
          simp [coordinateBilinear, hsymm]
          ring
        rw [h_pair]
    exact congrArg (fun z => z + coordinateBilinear discrepancy y x) (h_single y)

/-- The pairing against one coordinate is the expected finite sum of the
corresponding discrepancy-matrix column. -/
theorem coordinateBilinear_right_single
    {ι : Type*} [LinearOrder ι] (discrepancy : ι → ι → ZMod 2)
    (f : ι →₀ ZMod 2) (a : ι) (b : ZMod 2) :
    coordinateBilinear discrepancy f (Finsupp.single a b) =
      ∑ i ∈ f.support, 2 * liftPauliBit (f i) * liftPauliBit b *
        liftPauliBit (discrepancy i a) := by
  unfold coordinateBilinear
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- Every value of the ZMod 4 coordinate pairing has additive order at most
two, because each summand carries an explicit factor of two. -/
theorem coordinateBilinear_add_self
    {ι : Type*} [LinearOrder ι] (discrepancy : ι → ι → ZMod 2)
    (x y : ι →₀ ZMod 2) :
    coordinateBilinear discrepancy x y + coordinateBilinear discrepancy x y = 0 := by
  unfold coordinateBilinear
  change (∑ i ∈ x.support, ∑ j ∈ y.support,
    2 * liftPauliBit (x i) * liftPauliBit (y j) * liftPauliBit (discrepancy i j)) +
    (∑ i ∈ x.support, ∑ j ∈ y.support,
      2 * liftPauliBit (x i) * liftPauliBit (y j) * liftPauliBit (discrepancy i j)) = 0
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j hj
  have hfour : (4 : ZMod 4) = 0 := by
    change ((4 : ℕ) : ZMod 4) = 0
    exact ZMod.natCast_self 4
  rw [show (2 * liftPauliBit (x i) * liftPauliBit (y j) *
      liftPauliBit (discrepancy i j)) +
      2 * liftPauliBit (x i) * liftPauliBit (y j) *
        liftPauliBit (discrepancy i j) =
      4 * liftPauliBit (x i) * liftPauliBit (y j) *
        liftPauliBit (discrepancy i j) by ring]
  simp [hfour]

/-- The coordinate quadratic refinement vanishes at the zero word. -/
theorem coordinateQuadraticRefinement_zero
    {ι : Type*} [LinearOrder ι] (discrepancy : ι → ι → ZMod 2) :
    coordinateQuadraticRefinement discrepancy 0 = 0 := by
  simp [coordinateQuadraticRefinement]

/-- On a single basis coordinate, only the diagonal discrepancy contributes. -/
theorem coordinateQuadraticRefinement_single
    {ι : Type*} [LinearOrder ι] (discrepancy : ι → ι → ZMod 2) (i : ι) :
    coordinateQuadraticRefinement discrepancy (Finsupp.single i 1) =
      liftPauliBit (discrepancy i i) := by
  unfold coordinateQuadraticRefinement
  rw [Finsupp.support_single_ne_zero _ one_ne_zero]
  simp only [Finset.sum_singleton, Finsupp.single_eq_same, liftPauliBit_one,
    one_mul]
  have h_filter : ({i} : Finset ι).filter (fun x => i < x) = ∅ := by
    simp
  rw [h_filter]
  simp

/-- Adding a new largest coordinate to a finite word adds its diagonal phase
and precisely the ordered cross terms with the earlier support.  This is the
induction step for the finite-support polarization identity. -/
theorem coordinateQuadraticRefinement_single_add_of_support_lt
    {ι : Type*} [LinearOrder ι] (discrepancy : ι → ι → ZMod 2)
    (a : ι) (b : ZMod 2) (f : ι →₀ ZMod 2)
    (hmax : ∀ c ∈ f.support, c < a) (hb : b ≠ 0) :
    coordinateQuadraticRefinement discrepancy (Finsupp.single a b + f) =
      coordinateQuadraticRefinement discrepancy f +
        liftPauliBit b * liftPauliBit (discrepancy a a) +
          ∑ i ∈ f.support, 2 * liftPauliBit (f i) * liftPauliBit b *
            liftPauliBit (discrepancy i a) := by
  classical
  have ha : a ∉ f.support := by
    intro ha
    exact (lt_irrefl a) (hmax a ha)
  unfold coordinateQuadraticRefinement
  rw [show (Finsupp.single a b + f).support = Finset.cons a f.support ha from
    Finsupp.support_single_add ha hb]
  rw [Finset.cons_eq_insert, Finset.sum_insert ha, Finset.sum_insert ha]
  have h_value_a : (Finsupp.single a b + f) a = b := by
    rw [Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.notMem_support_iff.mp ha, add_zero]
  have h_value_of_mem : ∀ x ∈ f.support, (Finsupp.single a b + f) x = f x := by
    intro x hx
    have hxa : x ≠ a := (hmax x hx).ne
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hxa, zero_add]
  have h_filter_a : (insert a f.support).filter (a < ·) = ∅ := by
    apply Finset.filter_false_of_mem
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact lt_irrefl _
    · exact not_lt_of_ge (hmax c hc).le
  rw [h_filter_a]
  simp only [h_value_a, Finset.sum_empty]
  have h_filter_of_mem : ∀ x ∈ f.support,
      (insert a f.support).filter (x < ·) =
        insert a (f.support.filter (x < ·)) := by
    intro x hx
    rw [Finset.filter_insert]
    simp [hmax x hx]
  have h_inner_tail : ∀ x ∈ f.support,
      ∑ j ∈ f.support.filter (x < ·),
        2 * liftPauliBit ((Finsupp.single a b + f) x) *
          liftPauliBit ((Finsupp.single a b + f) j) *
            liftPauliBit (discrepancy x j) =
      ∑ j ∈ f.support.filter (x < ·),
        2 * liftPauliBit (f x) * liftPauliBit (f j) *
          liftPauliBit (discrepancy x j) := by
    intro x hx
    apply Finset.sum_congr rfl
    intro j hj
    rw [h_value_of_mem x hx,
      h_value_of_mem j (Finset.mem_filter.mp hj).1]
  have h_inner : ∀ x ∈ f.support,
      ∑ j ∈ (insert a f.support).filter (x < ·),
        2 * liftPauliBit ((Finsupp.single a b + f) x) *
          liftPauliBit ((Finsupp.single a b + f) j) *
            liftPauliBit (discrepancy x j) =
        (∑ j ∈ f.support.filter (x < ·),
          2 * liftPauliBit (f x) * liftPauliBit (f j) *
            liftPauliBit (discrepancy x j)) +
          2 * liftPauliBit (f x) * liftPauliBit b *
            liftPauliBit (discrepancy x a) := by
    intro x hx
    rw [h_filter_of_mem x hx]
    rw [Finset.sum_insert]
    · rw [h_inner_tail x hx]
      rw [h_value_of_mem x hx, h_value_a]
      ring
    · simp [ha]
  have h_diag :
      (∑ x ∈ f.support, liftPauliBit ((Finsupp.single a b + f) x) *
        liftPauliBit (discrepancy x x)) =
      ∑ x ∈ f.support, liftPauliBit (f x) * liftPauliBit (discrepancy x x) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [h_value_of_mem x hx]
  have h_inter :
      (∑ x ∈ f.support,
        ∑ j ∈ (insert a f.support).filter (x < ·),
          2 * liftPauliBit ((Finsupp.single a b + f) x) *
            liftPauliBit ((Finsupp.single a b + f) j) *
              liftPauliBit (discrepancy x j)) =
      ∑ x ∈ f.support,
        ((∑ j ∈ f.support.filter (x < ·),
          2 * liftPauliBit (f x) * liftPauliBit (f j) *
            liftPauliBit (discrepancy x j)) +
          2 * liftPauliBit (f x) * liftPauliBit b *
            liftPauliBit (discrepancy x a)) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact h_inner x hx
  rw [h_diag, h_inter, Finset.sum_add_distrib]
  ring

/-- Uniform maximal-coordinate splitting formula.  Unlike the raw recurrence,
this version also handles a zero coefficient at the new coordinate, which is
needed to split two arbitrary words along a common finite support. -/
theorem coordinateQuadraticRefinement_split_max
    {ι : Type*} [LinearOrder ι] (discrepancy : ι → ι → ZMod 2)
    (a : ι) (b : ZMod 2) (f : ι →₀ ZMod 2)
    (hmax : ∀ c ∈ f.support, c < a) :
    coordinateQuadraticRefinement discrepancy (Finsupp.single a b + f) =
      coordinateQuadraticRefinement discrepancy f +
        liftPauliBit b * liftPauliBit (discrepancy a a) +
          coordinateBilinear discrepancy f (Finsupp.single a b) := by
  by_cases hb : b = 0
  · subst b
    simp [coordinateBilinear]
  · rw [coordinateQuadraticRefinement_single_add_of_support_lt discrepancy a b f hmax hb]
    rw [coordinateBilinear_right_single]

/-- The explicit finite-support quadratic refinement polarizes to the
finite-coordinate discrepancy pairing whenever the discrepancy matrix is
symmetric.  The proof inducts on the common finite support of the two words,
splitting both words at its largest coordinate. -/
theorem coordinateQuadraticRefinement_polarization
    {ι : Type*} [LinearOrder ι] (discrepancy : ι → ι → ZMod 2)
    (hsymm : ∀ i j, discrepancy i j = discrepancy j i)
    (x y : ι →₀ ZMod 2) :
    coordinateQuadraticRefinement discrepancy (x + y) =
      coordinateQuadraticRefinement discrepancy x +
        coordinateQuadraticRefinement discrepancy y +
          coordinateBilinear discrepancy x y := by
  classical
  let P : Finset ι → Prop := fun s =>
    ∀ x y : ι →₀ ZMod 2, x.support ⊆ s → y.support ⊆ s →
      coordinateQuadraticRefinement discrepancy (x + y) =
        coordinateQuadraticRefinement discrepancy x +
          coordinateQuadraticRefinement discrepancy y +
            coordinateBilinear discrepancy x y
  have hP : ∀ s : Finset ι, P s := by
    intro s
    induction s using Finset.induction_on_max with
    | h0 =>
      intro x y hx hy
      have hxzero : x = 0 := Finsupp.support_eq_empty.mp (Finset.subset_empty.mp hx)
      have hyzero : y = 0 := Finsupp.support_eq_empty.mp (Finset.subset_empty.mp hy)
      subst x
      subst y
      simp [coordinateQuadraticRefinement, coordinateBilinear]
    | step a s hmax ih =>
      intro x y hx hy
      let x0 := Finsupp.erase a x
      let y0 := Finsupp.erase a y
      have hx0 : x0.support ⊆ s := by
        intro c hc
        rw [show x0 = Finsupp.erase a x from rfl, Finsupp.support_erase,
          Finset.mem_erase] at hc
        rcases Finset.mem_insert.mp (hx hc.2) with hca | hcs
        · exact (hc.1 hca).elim
        · exact hcs
      have hy0 : y0.support ⊆ s := by
        intro c hc
        rw [show y0 = Finsupp.erase a y from rfl, Finsupp.support_erase,
          Finset.mem_erase] at hc
        rcases Finset.mem_insert.mp (hy hc.2) with hca | hcs
        · exact (hc.1 hca).elim
        · exact hcs
      have hxmax : ∀ c ∈ x0.support, c < a := fun c hc => hmax c (hx0 hc)
      have hymax : ∀ c ∈ y0.support, c < a := fun c hc => hmax c (hy0 hc)
      have hsummax : ∀ c ∈ (x0 + y0).support, c < a := by
        intro c hc
        rcases Finset.mem_union.mp (Finsupp.support_add hc) with hcx | hcy
        · exact hxmax c hcx
        · exact hymax c hcy
      have hxsplit : Finsupp.single a (x a) + x0 = x := by
        exact Finsupp.single_add_erase a x
      have hysplit : Finsupp.single a (y a) + y0 = y := by
        exact Finsupp.single_add_erase a y
      have hsumsplit : Finsupp.single a (x a + y a) + (x0 + y0) = x + y := by
        dsimp [x0, y0]
        rw [Finsupp.single_add]
        calc
          (Finsupp.single a (x a) + Finsupp.single a (y a)) +
              (Finsupp.erase a x + Finsupp.erase a y) =
            (Finsupp.single a (x a) + Finsupp.erase a x) +
              (Finsupp.single a (y a) + Finsupp.erase a y) := by ac_rfl
          _ = x + y := by rw [Finsupp.single_add_erase, Finsupp.single_add_erase]
      have h0 := ih x0 y0 hx0 hy0
      have hqx := coordinateQuadraticRefinement_split_max discrepancy a (x a) x0 hxmax
      have hqy := coordinateQuadraticRefinement_split_max discrepancy a (y a) y0 hymax
      have hqsum := coordinateQuadraticRefinement_split_max discrepancy a (x a + y a)
        (x0 + y0) hsummax
      have hBxy : coordinateBilinear discrepancy x y =
          coordinateBilinear discrepancy (Finsupp.single a (x a)) (Finsupp.single a (y a)) +
            coordinateBilinear discrepancy (Finsupp.single a (x a)) y0 +
              coordinateBilinear discrepancy x0 (Finsupp.single a (y a)) +
                coordinateBilinear discrepancy x0 y0 := by
        calc
          coordinateBilinear discrepancy x y =
              coordinateBilinear discrepancy
                (Finsupp.single a (x a) + x0) (Finsupp.single a (y a) + y0) := by
              rw [hxsplit, hysplit]
          _ = coordinateBilinear discrepancy (Finsupp.single a (x a)) (Finsupp.single a (y a)) +
                coordinateBilinear discrepancy (Finsupp.single a (x a)) y0 +
                  coordinateBilinear discrepancy x0 (Finsupp.single a (y a)) +
                    coordinateBilinear discrepancy x0 y0 := by
              rw [coordinateBilinear_add_left, coordinateBilinear_add_right,
                coordinateBilinear_add_right]
              ring
      have hBsum : coordinateBilinear discrepancy (x0 + y0)
          (Finsupp.single a (x a + y a)) =
            coordinateBilinear discrepancy x0 (Finsupp.single a (x a)) +
              coordinateBilinear discrepancy x0 (Finsupp.single a (y a)) +
                coordinateBilinear discrepancy y0 (Finsupp.single a (x a)) +
                  coordinateBilinear discrepancy y0 (Finsupp.single a (y a)) := by
        rw [Finsupp.single_add, coordinateBilinear_add_left,
          coordinateBilinear_add_right, coordinateBilinear_add_right]
        ring
      have hdiag : liftPauliBit (x a + y a) * liftPauliBit (discrepancy a a) =
          liftPauliBit (x a) * liftPauliBit (discrepancy a a) +
            liftPauliBit (y a) * liftPauliBit (discrepancy a a) +
              coordinateBilinear discrepancy (Finsupp.single a (x a))
                (Finsupp.single a (y a)) := by
        rw [liftPauliBit_add]
        simp [coordinateBilinear]
        have hneg_two : (-2 : ZMod 4) = 2 := by
          have hfour : (4 : ZMod 4) = 0 := by
            change ((4 : ℕ) : ZMod 4) = 0
            exact ZMod.natCast_self 4
          calc
            (-2 : ZMod 4) = 2 - 4 := by ring
            _ = 2 := by rw [hfour, sub_zero]
        calc
          (liftPauliBit (x a) + liftPauliBit (y a) -
              2 * liftPauliBit (x a) * liftPauliBit (y a)) *
              liftPauliBit (discrepancy a a) =
            (liftPauliBit (x a) + liftPauliBit (y a) +
              (-2) * liftPauliBit (x a) * liftPauliBit (y a)) *
                liftPauliBit (discrepancy a a) := by ring
          _ = liftPauliBit (x a) * liftPauliBit (discrepancy a a) +
              liftPauliBit (y a) * liftPauliBit (discrepancy a a) +
                2 * liftPauliBit (x a) * liftPauliBit (y a) *
                  liftPauliBit (discrepancy a a) := by rw [hneg_two]; ring
      have hqx' : coordinateQuadraticRefinement discrepancy x =
          coordinateQuadraticRefinement discrepancy x0 +
            liftPauliBit (x a) * liftPauliBit (discrepancy a a) +
              coordinateBilinear discrepancy x0 (Finsupp.single a (x a)) := by
        calc
          coordinateQuadraticRefinement discrepancy x =
              coordinateQuadraticRefinement discrepancy (Finsupp.single a (x a) + x0) := by
                rw [hxsplit]
          _ = _ := hqx
      have hqy' : coordinateQuadraticRefinement discrepancy y =
          coordinateQuadraticRefinement discrepancy y0 +
            liftPauliBit (y a) * liftPauliBit (discrepancy a a) +
              coordinateBilinear discrepancy y0 (Finsupp.single a (y a)) := by
        calc
          coordinateQuadraticRefinement discrepancy y =
              coordinateQuadraticRefinement discrepancy (Finsupp.single a (y a) + y0) := by
                rw [hysplit]
          _ = _ := hqy
      have hmiddle :
          (coordinateQuadraticRefinement discrepancy x0 +
              coordinateQuadraticRefinement discrepancy y0 +
                coordinateBilinear discrepancy x0 y0) +
            liftPauliBit (x a + y a) * liftPauliBit (discrepancy a a) +
              coordinateBilinear discrepancy (x0 + y0)
                (Finsupp.single a (x a + y a)) =
          (coordinateQuadraticRefinement discrepancy x0 +
              liftPauliBit (x a) * liftPauliBit (discrepancy a a) +
                coordinateBilinear discrepancy x0 (Finsupp.single a (x a))) +
            (coordinateQuadraticRefinement discrepancy y0 +
              liftPauliBit (y a) * liftPauliBit (discrepancy a a) +
                coordinateBilinear discrepancy y0 (Finsupp.single a (y a))) +
              coordinateBilinear discrepancy x y := by
        rw [hdiag, hBsum, hBxy,
          coordinateBilinear_symm discrepancy hsymm y0 (Finsupp.single a (x a))]
        ring
      calc
        coordinateQuadraticRefinement discrepancy (x + y) =
            coordinateQuadraticRefinement discrepancy
              (Finsupp.single a (x a + y a) + (x0 + y0)) := by rw [hsumsplit]
        _ = coordinateQuadraticRefinement discrepancy (x0 + y0) +
            liftPauliBit (x a + y a) * liftPauliBit (discrepancy a a) +
              coordinateBilinear discrepancy (x0 + y0)
                (Finsupp.single a (x a + y a)) := hqsum
        _ = (coordinateQuadraticRefinement discrepancy x0 +
              coordinateQuadraticRefinement discrepancy y0 +
                coordinateBilinear discrepancy x0 y0) +
            liftPauliBit (x a + y a) * liftPauliBit (discrepancy a a) +
              coordinateBilinear discrepancy (x0 + y0)
                (Finsupp.single a (x a + y a)) := by rw [h0]
        _ = (coordinateQuadraticRefinement discrepancy x0 +
              liftPauliBit (x a) * liftPauliBit (discrepancy a a) +
                coordinateBilinear discrepancy x0 (Finsupp.single a (x a))) +
            (coordinateQuadraticRefinement discrepancy y0 +
              liftPauliBit (y a) * liftPauliBit (discrepancy a a) +
                coordinateBilinear discrepancy y0 (Finsupp.single a (y a))) +
              coordinateBilinear discrepancy x y := hmiddle
        _ = coordinateQuadraticRefinement discrepancy x +
            coordinateQuadraticRefinement discrepancy y +
              coordinateBilinear discrepancy x y := by rw [← hqx', ← hqy']
  exact hP (x.support ∪ y.support) x y Finset.subset_union_left Finset.subset_union_right

/-- The polarization identity evaluated on a word twice supplies the diagonal
identity required by the Pauli involution phase equation. -/
theorem two_coordinateQuadraticRefinement
    {ι : Type*} [LinearOrder ι] (discrepancy : ι → ι → ZMod 2)
    (hsymm : ∀ i j, discrepancy i j = discrepancy j i)
    (x : ι →₀ ZMod 2) :
    2 * coordinateQuadraticRefinement discrepancy x = coordinateBilinear discrepancy x x := by
  have hpol := coordinateQuadraticRefinement_polarization discrepancy hsymm x x
  rw [pauliBit_add_self_eq_zero, coordinateQuadraticRefinement_zero] at hpol
  have hpol' : 0 = 2 * coordinateQuadraticRefinement discrepancy x +
      coordinateBilinear discrepancy x x := by
    simpa [two_mul] using hpol
  calc
    2 * coordinateQuadraticRefinement discrepancy x = -coordinateBilinear discrepancy x x := by
      linear_combination -hpol'
    _ = coordinateBilinear discrepancy x x :=
      neg_eq_of_add_eq_zero_right (coordinateBilinear_add_self discrepancy x x)

/-- The explicit two-coordinate check fixes the sign and order convention of
the quadratic phase: the sole off-diagonal contribution is the discrepancy
with the smaller index written first. -/
theorem coordinateQuadraticRefinement_two_of_lt
    {ι : Type*} [LinearOrder ι] (discrepancy : ι → ι → ZMod 2)
    (i j : ι) (hij : i < j) :
    coordinateQuadraticRefinement discrepancy
      (Finsupp.single i 1 + Finsupp.single j 1) =
        liftPauliBit (discrepancy i i) + liftPauliBit (discrepancy j j) +
          2 * liftPauliBit (discrepancy i j) := by
  rw [add_comm]
  rw [coordinateQuadraticRefinement_single_add_of_support_lt discrepancy j 1
    (Finsupp.single i 1) (by
      intro c hc
      rw [Finsupp.support_single_ne_zero _ one_ne_zero] at hc
      simpa only [Finset.mem_singleton.mp hc] using hij) one_ne_zero]
  rw [coordinateQuadraticRefinement_single]
  rw [Finsupp.support_single_ne_zero _ one_ne_zero]
  simp

end StabilizerHyperfinite
