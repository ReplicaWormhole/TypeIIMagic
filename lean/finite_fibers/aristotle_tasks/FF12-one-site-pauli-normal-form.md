# FF12 — one-site phased Pauli normal form

## Status

Accepted and integrated on August 5, 2026 from Aristotle project
`c091ae7a-c696-4863-a46f-72c8ab6ca624`.

- Archive: `../aristotle_responses/FF12-one-site-pauli-normal-form.tar.gz`
- Archive SHA-256:
  `624b130a2c08061fa8f60edf33397c5a2dd82b4817569c0acdcd7f14c9da6cbf`
- Quarantine: `../aristotle_responses/FF12-extracted/`

Only `AristotleCandidates/OneSitePauliNormalForm.lean` was integrated as
`formalization_finite_fibers/FiniteFiber/OneSitePauliNormalForm.lean`; the
two files are byte-identical with source SHA-256
`6d9e4ae4f3c0ae3a3c3b9d35322d42ddd8d518a07f75441b6b1a61a3984cfc99`.  The
remote README attribution, stale FF12 handoff deletion, and
`ARISTOTLE_SUMMARY.md` were rejected.  The prompt and post-result reviews are
approved at `../aristotle_responses/FF12-prompt-adversarial-review.md` and
`../aristotle_responses/FF12-integration-adversarial-review.md`.

## Source locators

- `writing/overleaf_prl_stabilizer_region_algebras/main.tex:812-885` fixes the
  one-qubit Hermitian labels \(I,X,Y,Z\), finite local tensor products, and
  local inclusions.
- `formalization_finite_fibers/FiniteFiber/FinitePauli.lean:24-54` defines
  the literal \(I,X,Y,Z\) matrices.  In particular its \(Y\) is
  \(\begin{pmatrix}0&-i\\ i&0\end{pmatrix}\).
- `formalization_finite_fibers/FiniteFiber/ProjectivePauliLattice.lean:32-65`
  defines the binary projective coordinates and chooses the Hermitian
  representative \(Y\) at \((1,1)\).
- `formalization_finite_fibers/FiniteFiber/FullPauliLattice.lean:6-16,
  21-35, 88-110` defines the separate algebraic normal form
  \(i^{\mathrm{phase}}X^x Z^z\), with a sign cocycle.  Its
  `phaseEmbed` sends \(1\) to \(2\), so it represents \(-1=i^2\), not the
  \(Y\)-normalization below.

## Exact mathematical target

For a one-site projective coordinate \(p=(x,z)\), write

~~~text
H(p) = PauliLabel.matrix (PauliLabel.ofProjectiveCoordinates p)
N(p) = (if x = 0 then I else X) * (if z = 0 then I else Z).
~~~

The factor order in \(N(p)\) is deliberately \(X\) then \(Z\), exactly as in
the existing full normal form.  The four cases are

~~~text
p       H(p)   N(p)       correction
(0,0)   I      I          0
(1,0)   X      X          0
(0,1)   Z      Z          0
(1,1)   Y      X Z        3
~~~

because \(Y=iXZ\), equivalently \(XZ=-iY=i^3Y\).  Thus define the
*normal-form-from-Hermitian* correction \(c(p)\) to be \(3\) exactly at
\((1,1)\), and prove

~~~text
N(p) = i^(c(p)) H(p).
~~~

This orientation is intentional.  A later finite-region construction, not
part of this task, would use

~~~text
i^(g.phase + sum_i c(g.label i)) * P_F(H(g.label)).
~~~

It is equivalent to subtracting the \(Y\)-count, but it must not reuse the
existing additive sign embedding `FullPauliWord.phaseEmbed`.

## Essential scope boundary

This task establishes only the literal one-site table/convention.  It does
not define a map from `FullPauliWord`, a finite-region matrix, or a
homomorphism.  In particular, it must not prove or claim:

- multiplicativity of the phase factor;
- a finite-region correction sum or padding identity;
- compatibility with `FullPauliWord.cocycle`;
- a local-group representation, faithfulness, support/local-algebra
  characterization, or self-adjointness criterion;
- three-region coherence, a colimit/quasilocal algebra, a state, GNS, a von
  Neumann algebra, finite projections, or the manuscript's main theorem.

Do not use `FullPauliWord.phaseEmbed` in the candidate.  It is a
mathematically different map: \(1\mapsto2\) for the sign \(-1\), whereas the
present correction is \(3\) for \(XZ=-iY\).  Do not silently ignore central
phase-only words: for example, the later image of
`FullPauliWord.negativeIdentity` must be \(-I\) even though its projective
label has empty support.  That later obligation is explicitly outside FF12.

## Allowed ownership

Create and modify **only**:

~~~text
AristotleCandidates/OneSitePauliNormalForm.lean
~~~

Do not modify `FiniteFiber/`, `tests/`, the package manifest, README or
handoff files, the manuscript, or any work record.  Do not add attribution
text, commits, pushes, or unrelated files.

## Required declarations

Import `FiniteFiber.FullPauliLattice`.  In namespace `FiniteFiber`, define
exactly these public declarations (private helpers and lemmas are permitted
only when indispensable):

~~~lean
noncomputable def zmod4PhaseFactor (k : ZMod 4) : ℂ :=
  Complex.I ^ k.val

def normalFormHermitianCorrection (p : ProjectivePauliLabel) : ZMod 4 :=
  if p = (1, 1) then 3 else 0

noncomputable def normalFormOneSiteMatrix (p : ProjectivePauliLabel) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (if p.1 = 0 then 1 else PauliLabel.matrix PauliLabel.X) *
    (if p.2 = 0 then 1 else PauliLabel.matrix PauliLabel.Z)

theorem normalFormOneSiteMatrix_eq_phase_smul_hermitian
    (p : ProjectivePauliLabel) :
    normalFormOneSiteMatrix p =
      zmod4PhaseFactor (normalFormHermitianCorrection p) •
        PauliLabel.matrix (PauliLabel.ofProjectiveCoordinates p)

theorem normalFormHermitianCorrection_xy :
    normalFormHermitianCorrection ((1, 1) : ProjectivePauliLabel) = 3

theorem normalFormOneSiteMatrix_xy :
    normalFormOneSiteMatrix ((1, 1) : ProjectivePauliLabel) =
      (-Complex.I) • PauliLabel.matrix PauliLabel.Y
~~~

The generic normalization theorem must be the load-bearing statement.  The
two final theorems are explicit convention regressions: the \(Y\)-row must
not accidentally become \(+iY\), \(Y\), or a Boolean sign.

## Proof constraints and useful APIs

- The literal definition above is the desired raw normal-form matrix:
  \(X^x Z^z\) in the only two possible binary exponents.  Do not reorder it
  to \(Z^z X^x\).
- A bounded proof is expected: destruct the two `ZMod 2` coordinates with
  `fin_cases`, use matrix extensionality, destruct the two `Fin 2`
  indices, and close the entries by
  `norm_num [zmod4PhaseFactor, normalFormHermitianCorrection,
  normalFormOneSiteMatrix, PauliLabel.ofProjectiveCoordinates,
  PauliLabel.matrix, Matrix.mul_apply, ZMod.val]`.
- The explicit \(Y\) regression can be obtained from the generic theorem by
simplification, including `ZMod.val`; direct expansion is also allowed.
- Keep every helper private unless it is one of the six declarations above.
- No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or
  `implemented_by` declaration is permitted.

## Verification and response

Run:

~~~bash
lake env lean AristotleCandidates/OneSitePauliNormalForm.lean
~~~

Return a compiling candidate containing exactly the six public declarations
above, plus indispensable private helpers.  If blocked, return a precise
minimal Lean API/proof-obligation report without a placeholder.
