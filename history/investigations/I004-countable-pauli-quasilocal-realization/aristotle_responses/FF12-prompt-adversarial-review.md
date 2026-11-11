# Review: FF12 one-site phased Pauli normal form prompt

Verdict: **APPROVED**

## Findings

1. **Cleared — exact phase convention.**  The artifact
   `aristotle_tasks/FF12-one-site-pauli-normal-form.md:31-61,106-125` uses
   \(N(x,z)=X^xZ^z\) in that order and the correction \(c(1,1)=3\) in the
   equality \(N(p)=i^{c(p)}H(p)\).  Direct multiplication of the live matrices
   gives \(XZ=-iY=i^3Y\), so the direction and sign are correct.  This is the
   inverse convention to \(H=iN\); the recorded later orientation
   \(i^{\mathrm{phase}+\sum c}P_F(H)\) is therefore also correct.

2. **Cleared — no phase-map conflation.**  The prompt explicitly excludes
   `FullPauliWord.phaseEmbed`.  That existing additive map sends \(1\) to
   \(2\) for the sign \(-1\); FF12's correction is a nonadditive
   \(Y\)-indicator taking \((1,1)\) to \(3\).  The explicit \(Y\) regression
   prevents a reversal to \(+iY\), \(Y\), or a Boolean sign.

3. **Cleared — source and API fidelity.**  The exact local source locators
   point to the manuscript's finite Pauli tensor convention and to the live
   matrix, projective-coordinate, and normal-form definitions.  A local
   stdin preflight compiled the six requested declarations, including the
   four-case matrix proof, against the pinned package.

4. **Cleared — scope control.**  The artifact excludes phase-factor
   multiplicativity, finite-region aggregation, cocycle compatibility, local
   group maps, locality/faithfulness, and all quasilocal/GNS/von-Neumann and
   finite-projection claims.  It also records the phase-only-word guardrail.
   Consequently it does not promote the one-site table into a representation.

## Independent review roles

- Mathematical/convention review: **APPROVED**.  It checked the direction,
  sign, factor order, source locators, and theorem boundary.
- Lean/API review: **APPROVED**.  It checked the exact six public
  declarations, import, proof strategy, and live-package compilability.

## Residual risks

FF12 will still require quarantine, a live rebuild, an axiom audit, and a
second adversarial review after Aristotle returns a candidate.  The full
phase-correct finite-region and local-group representation remains future
work.
