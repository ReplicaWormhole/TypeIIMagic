Accepted P60R at its stated conditional scope. Integrated [FullCornerSemifiniteWeight.lean](../../lean/stabilizer/AristotleCandidates/FullCornerSemifiniteWeight.lean) and recorded the audit in [P60R closeout](../../lean/stabilizer/reviews/P60R-full-corner-standard-semifiniteness-repair-closeout.md).

Live narrow and dependency-chain Lean builds passed; axiom audits show only `propext`, `Classical.choice`, and `Quot.sound`. The remaining explicit limitation is that `ComparisonFamily` is assumed, not derived from fullness.

AUTOPILOT_ACCEPTED: yes  
AUTOPILOT_DECISION: advance

