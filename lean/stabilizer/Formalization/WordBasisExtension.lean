import Mathlib

/-!
# Extending a Pauli-word map from a linear basis

The phase-corrected calculation on individual Pauli words is not by itself an
algebra-homomorphism theorem.  This module supplies the finite-word bridge:
if those words form a complex linear basis, checking multiplication on pairs
of words makes the induced linear map multiplicative on all finite sums.
-/

namespace StabilizerHyperfinite

section

variable {ι A B : Type*}
variable [Semiring A] [Semiring B] [Algebra ℂ A] [Algebra ℂ B]

/-- A complex-linear map that respects products of every pair of vectors in a
basis respects products of arbitrary finite linear combinations. -/
theorem LinearMap.map_mul_of_basis
    (map : A →ₗ[ℂ] B) (basis : Module.Basis ι ℂ A)
    (h_basis : ∀ i j, map (basis i * basis j) = map (basis i) * map (basis j))
    (x y : A) :
    map (x * y) = map x * map y := by
  let left : A →ₗ[ℂ] B :=
    { toFun := fun z => map (z * y)
      map_add' := by
        intro z z'
        rw [add_mul, map.map_add]
      map_smul' := by
        intro c z
        calc
          map ((c • z) * y) = map (c • (z * y)) := by rw [smul_mul_assoc]
          _ = c • map (z * y) := map.map_smul c (z * y) }
  let right : A →ₗ[ℂ] B :=
    { toFun := fun z => map z * map y
      map_add' := by
        intro z z'
        rw [map.map_add, add_mul]
      map_smul' := by
        intro c z
        calc
          map (c • z) * map y = (c • map z) * map y := by rw [map.map_smul]
          _ = c • (map z * map y) := smul_mul_assoc c (map z) (map y) }
  change left x = right x
  have h_left_right : left = right := by
    apply basis.ext
    intro i
    change map (basis i * y) = map (basis i) * map y
    let leftBasis : A →ₗ[ℂ] B :=
      { toFun := fun z => map (basis i * z)
        map_add' := by
          intro z z'
          rw [mul_add, map.map_add]
        map_smul' := by
          intro c z
          calc
            map (basis i * (c • z)) = map (c • (basis i * z)) := by rw [mul_smul_comm]
            _ = c • map (basis i * z) := map.map_smul c (basis i * z) }
    let rightBasis : A →ₗ[ℂ] B :=
      { toFun := fun z => map (basis i) * map z
        map_add' := by
          intro z z'
          rw [map.map_add, mul_add]
        map_smul' := by
          intro c z
          calc
            map (basis i) * map (c • z) = map (basis i) * (c • map z) := by rw [map.map_smul]
            _ = c • (map (basis i) * map z) :=
              Algebra.mul_smul_comm c (map (basis i)) (map z) }
    change leftBasis y = rightBasis y
    have h_basis_maps : leftBasis = rightBasis := by
      apply basis.ext
      intro j
      exact h_basis i j
    exact LinearMap.congr_fun h_basis_maps y
  exact LinearMap.congr_fun h_left_right x

/-- Star compatibility on a complex basis extends to arbitrary finite linear
combinations.  The relevant set is a complex submodule because both sides are
conjugate-linear in the input. -/
theorem LinearMap.map_star_of_basis
    {A B : Type*} [Semiring A] [Semiring B] [Algebra ℂ A] [Algebra ℂ B]
    [StarRing A] [StarRing B] [StarModule ℂ A] [StarModule ℂ B]
    (map : A →ₗ[ℂ] B) (basis : Module.Basis ι ℂ A)
    (h_basis : ∀ i, map (star (basis i)) = star (map (basis i))) (x : A) :
    map (star x) = star (map x) := by
  let compatible : Submodule ℂ A :=
    { carrier := { z | map (star z) = star (map z) }
      zero_mem' := by simp
      add_mem' := by
        intro z z' hz hz'
        change map (star (z + z')) = star (map (z + z'))
        change map (star z) = star (map z) at hz
        change map (star z') = star (map z') at hz'
        calc
          map (star (z + z')) = map (star z + star z') := by rw [star_add]
          _ = map (star z) + map (star z') := map.map_add (star z) (star z')
          _ = star (map z) + star (map z') := by rw [hz, hz']
          _ = star (map z + map z') := (star_add (map z) (map z')).symm
          _ = star (map (z + z')) := by rw [map.map_add]
      smul_mem' := by
        intro c z hz
        change map (star (c • z)) = star (map (c • z))
        change map (star z) = star (map z) at hz
        calc
          map (star (c • z)) = map (star c • star z) := by rw [star_smul]
          _ = star c • map (star z) := map.map_smul (star c) (star z)
          _ = star c • star (map z) := by rw [hz]
          _ = star (c • map z) := (star_smul c (map z)).symm
          _ = star (map (c • z)) := by rw [map.map_smul] }
  have h_range : Set.range basis ⊆ compatible := by
    rintro z ⟨i, rfl⟩
    exact h_basis i
  have h_top : compatible = ⊤ := by
    apply top_unique
    rw [← basis.span_eq]
    exact Submodule.span_le.2 h_range
  change x ∈ compatible
  rw [h_top]
  exact Submodule.mem_top

/-- A unital complex-linear map which is multiplicative on a basis gives a
complex algebra homomorphism. -/
noncomputable def algHomOfBasis
    (map : A →ₗ[ℂ] B) (basis : Module.Basis ι ℂ A)
    (h_one : map 1 = 1)
    (h_basis : ∀ i j, map (basis i * basis j) = map (basis i) * map (basis j)) :
    A →ₐ[ℂ] B :=
  { map with
    map_zero' := map.map_zero
    map_one' := h_one
    map_mul' := LinearMap.map_mul_of_basis map basis h_basis
    commutes' := by
      intro c
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      change map (c • (1 : A)) = c • (1 : B)
      rw [map.map_smul, h_one] }

/-- Adding star compatibility on the same basis upgrades the algebra map to a
star-algebra homomorphism. -/
noncomputable def starAlgHomOfBasis
    {A B : Type*} [Semiring A] [Semiring B] [Algebra ℂ A] [Algebra ℂ B]
    [StarRing A] [StarRing B] [StarModule ℂ A] [StarModule ℂ B]
    (map : A →ₗ[ℂ] B) (basis : Module.Basis ι ℂ A)
    (h_one : map 1 = 1)
    (h_mul : ∀ i j, map (basis i * basis j) = map (basis i) * map (basis j))
    (h_star : ∀ i, map (star (basis i)) = star (map (basis i))) :
    A →⋆ₐ[ℂ] B :=
  { algHomOfBasis map basis h_one h_mul with
    map_star' := LinearMap.map_star_of_basis map basis h_star }

/-- A bijective phase-corrected linear word map becomes a star-algebra
equivalence once multiplication and star have been checked on a word basis. -/
noncomputable def starAlgEquivOfBasis
    {A B : Type*} [Semiring A] [Semiring B] [Algebra ℂ A] [Algebra ℂ B]
    [StarRing A] [StarRing B] [StarModule ℂ A] [StarModule ℂ B]
    (map : A ≃ₗ[ℂ] B) (basis : Module.Basis ι ℂ A)
    (h_one : map 1 = 1)
    (h_mul : ∀ i j, map (basis i * basis j) = map (basis i) * map (basis j))
    (h_star : ∀ i, map (star (basis i)) = star (map (basis i))) :
    A ≃⋆ₐ[ℂ] B :=
  StarAlgEquiv.ofBijective
    (starAlgHomOfBasis map.toLinearMap basis h_one h_mul h_star) map.bijective

@[simp]
theorem algHomOfBasis_apply
    (map : A →ₗ[ℂ] B) (basis : Module.Basis ι ℂ A)
    (h_one : map 1 = 1)
    (h_basis : ∀ i j, map (basis i * basis j) = map (basis i) * map (basis j)) (x : A) :
    algHomOfBasis map basis h_one h_basis x = map x :=
  rfl

end

end StabilizerHyperfinite
