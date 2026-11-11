# Aristotle task packets

Each packet is a separate remote request against an immutable snapshot of this
standalone Lean project.  The request may add only the one module named in its
packet, below AristotleCandidates/; it must not modify the Overleaf repository
or existing checked modules.

Accept a result only after copying its owned module into a separate local
review directory, building it against the current project, checking that it
contains no sorry, admit, or new axiom, and inspecting its declaration axioms.
Never unpack a remote archive over this project.

For manuscript-facing work, the source of truth for scope is
`../SOURCE-CONTRACT.md`, which points to exact locators in the manuscript.
`blueprints/002-aristotle-parallel-formalization.tex` is retained as legacy
exploratory material and is not source authority. Every new packet must use
the context declaration in `TEMPLATE.md`.
