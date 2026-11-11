import Formalization.WordBasisExtension

/-!
# Layer coherence from finite Pauli-word checks

To pass a finite-stage coordinate equivalence to a quasi-local direct limit,
one must show that it commutes with enlargement of finite regions.  This module
reduces that condition to its value on a specified source word basis, provided
the target basis and both label maps are themselves coherent.
-/

namespace StabilizerHyperfinite

variable {V V' W W' A A' D D' : Type*}
variable [Semiring A] [StarRing A] [Algebra ℂ A]
variable [Semiring A'] [StarRing A'] [Algebra ℂ A']
variable [Semiring D] [StarRing D] [Algebra ℂ D]
variable [Semiring D'] [StarRing D'] [Algebra ℂ D']

/-- If a square of finite-stage star-algebra equivalences commutes on a source
word basis, then it commutes on the whole source algebra. -/
theorem starAlgEquiv_commutes_of_basis
    (sourceBasis : Module.Basis V ℂ A)
    (targetBasis : Module.Basis W ℂ D)
    (sourceBasis' : Module.Basis V' ℂ A')
    (targetBasis' : Module.Basis W' ℂ D')
    (sourceLabelMap : V → V') (targetLabelMap : W → W')
    (wordMap : V → W) (wordMap' : V' → W')
    (f : A →⋆ₐ[ℂ] A') (h : D →⋆ₐ[ℂ] D')
    (e : A ≃⋆ₐ[ℂ] D) (e' : A' ≃⋆ₐ[ℂ] D')
    (h_source : ∀ v, f (sourceBasis v) = sourceBasis' (sourceLabelMap v))
    (h_target : ∀ w, h (targetBasis w) = targetBasis' (targetLabelMap w))
    (h_word : ∀ v, e (sourceBasis v) = targetBasis (wordMap v))
    (h_word' : ∀ v', e' (sourceBasis' v') = targetBasis' (wordMap' v'))
    (h_labels : ∀ v, wordMap' (sourceLabelMap v) = targetLabelMap (wordMap v))
    (x : A) :
    e' (f x) = h (e x) := by
  let left : A →ₗ[ℂ] D' :=
    e'.toAlgEquiv.toLinearEquiv.toLinearMap.comp f.toAlgHom.toLinearMap
  let right : A →ₗ[ℂ] D' :=
    h.toAlgHom.toLinearMap.comp e.toAlgEquiv.toLinearEquiv.toLinearMap
  change left x = right x
  suffices h_left_right : left = right by
    exact LinearMap.congr_fun h_left_right x
  apply sourceBasis.ext
  intro v
  change e' (f (sourceBasis v)) = h (e (sourceBasis v))
  rw [h_source, h_word', h_word, h_target, h_labels]

/-- A version of `starAlgEquiv_commutes_of_basis` for arbitrary prescribed
target vectors.  It is useful for phase-corrected Pauli words, whose images
are scalar multiples of target basis vectors. -/
theorem starAlgEquiv_commutes_of_source_basis
    (sourceBasis : Module.Basis V ℂ A)
    (sourceBasis' : Module.Basis V' ℂ A')
    (sourceLabelMap : V → V')
    (targetVector : V → D) (targetVector' : V' → D')
    (f : A →⋆ₐ[ℂ] A') (h : D →⋆ₐ[ℂ] D')
    (e : A ≃⋆ₐ[ℂ] D) (e' : A' ≃⋆ₐ[ℂ] D')
    (h_source : ∀ v, f (sourceBasis v) = sourceBasis' (sourceLabelMap v))
    (h_word : ∀ v, e (sourceBasis v) = targetVector v)
    (h_word' : ∀ v', e' (sourceBasis' v') = targetVector' v')
    (h_target : ∀ v, h (targetVector v) = targetVector' (sourceLabelMap v))
    (x : A) :
    e' (f x) = h (e x) := by
  let left : A →ₗ[ℂ] D' :=
    e'.toAlgEquiv.toLinearEquiv.toLinearMap.comp f.toAlgHom.toLinearMap
  let right : A →ₗ[ℂ] D' :=
    h.toAlgHom.toLinearMap.comp e.toAlgEquiv.toLinearEquiv.toLinearMap
  change left x = right x
  suffices h_left_right : left = right by
    exact LinearMap.congr_fun h_left_right x
  apply sourceBasis.ext
  intro v
  change e' (f (sourceBasis v)) = h (e (sourceBasis v))
  rw [h_source, h_word', h_word, h_target]

end StabilizerHyperfinite
