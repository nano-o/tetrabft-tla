<!-- BEGIN tla-tooling -->
<!-- Managed by tla-tooling; change it with `tla-tooling update`. -->
## TLA+

This repository holds TLA+ specifications at its root.

The workflow is in the skills `tla-setup`, `tla-modeling` and `tlaps`;
start with `tla-setup` until `"$TLA_TOOLING_ROOT/bin/tla-tooling" doctor`
passes.
<!-- END tla-tooling -->

## Project conventions

`TetraBFT.tla` is the only specification and lives at the repository root.
The protocol is being corrected against the paper before safety and
liveness proofs are developed with TLAPS. Its safety invariants are
candidates, not checked proofs.

Use the pinned tooling scripts for new checks; their outputs go under
`.tla-runs/`. The historical model-checking harness, local tool binaries,
quiescent-termination predicates and manual enabledness checks have been
removed. Report finite model-checking bounds separately from TLAPS results.

The liveness target is eventual decision under fair message delivery and
processing by correct processes, including weak fairness of `StartRound`.
Assume that `goodRound` is a valid round with a correct leader. Eventual
arrival is to follow from fairness and the round bound, which must be
established as a protocol invariant. Delivery is currently implicit and
immediate in the specification. Byzantine behavior remains possible
throughout. Proving that view change produces such a good round is outside
this target.

`proof_modules` remains empty until there is a TLAPS result to report.
Read the `tlaps` skill before adding or reporting a TLAPS proof.
