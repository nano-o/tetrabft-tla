# Sources

Assembled 2026-10-27 in a TLAPS paper repository, and moved to the TLA+
tooling on 2026-10-31. `SKILL.md`, `references/tlapm-soundness.md` and the
scripts (`tlaps-check`, `tlaps-audit`, `tlaps-report`) are original; the
rules they state draw on the resources below.

- `references/{hierarchical-proofs,other-proof-constructs,tactics,practical-hints,advanced-options,unsupported-features}.md`:
  the TLAPS documentation at https://proofs.tlapl.us/doc/web/content/Documentation/
  (tlaplus/tlapm `doc/web`, BSD-2-Clause), converted from HTML with pandoc.
- `references/hints.txt`: `hints.txt` from https://github.com/tlaplus/tlapm (BSD-2-Clause).
- `references/backends.md`: summarised from `library/TLAPS.tla` in tlaplus/tlapm.
- `references/instance-bridge.md`: `skills/tlaps-proof-hints/SKILL.md` from
  https://github.com/specula-org/TLAPS-Bench (MIT).
- `references/tlapm-soundness.md`: written for that repository's notes on
  tlapm, and the reproducer of tlapm#310 filed with
  https://github.com/tlaplus/tlapm/issues/310.
- `references/type-correctness-lemma.md`:
  `resources/knowledgebase/tla-prove-type-correctness-lemma.md` from
  https://github.com/tlaplus/vscode-tlaplus (MIT).
- Proof-driving rules (decompose one level, verify QED first, one step at a
  time, no OMITTED, bounded stretch) follow `AGENTS.md` of
  https://github.com/will62794/scimitar and the agent prompt of TLAPS-Bench.
- Reporting rules follow `skills/tla-proof/SKILL.md` of
  https://github.com/younes-io/agent-skills (MIT).
