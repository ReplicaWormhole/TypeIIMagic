# Formalization semantic-audit decision

Date: 2026-08-07

The approved deliverable is a semantic audit/tutorial of the Lean
formalization, rather than another proof package or a compilation report.

The audit will provide:

1. a status summary separating proved mathematics, conditional interfaces,
   supplied data, and unformalized claims;
2. a dependency map from the manuscript's finite-coordinate argument through
   the algebraic limit, concrete C-star model, GNS transport, bicommutant
   transport, and product-factor boundary;
3. a theorem ledger mapping each important natural-language proof sentence to
   exact Lean declarations, hypotheses, intermediate lemmas, and semantic
   verdicts; and
4. a step-by-step Lean reading sequence with code excerpts and direct build or
   `#check` commands.

The audit must keep compilation separate from mathematical validity and must
identify exact manuscript locators from `SOURCE-CONTRACT.md`. In particular,
it must not call the regional hyperfinite-factor theorem proved merely because
conditional Lean interfaces compile.

The first pass will inventory the current modules and completed-package
reviews. Later passes will inspect the principal declarations and their proof
chains in dependency order.
