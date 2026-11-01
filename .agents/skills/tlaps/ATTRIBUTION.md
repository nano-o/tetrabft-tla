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

## Notices

The copied and adapted files above keep their sources' licenses. Their
notices follow, as each repository's `LICENSE` gives them.

### tlaplus/tlapm (BSD-2-Clause)

For `references/{hierarchical-proofs,other-proof-constructs,tactics,practical-hints,advanced-options,unsupported-features}.md`,
`references/hints.txt` and `references/backends.md`.

```text
Copyright (c) 2008 INRIA and Microsoft Corporation
Copyright (c) 2023 Linux Foundation

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

  * Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.

  * Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in
    the documentation and/or other materials provided with the
    distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
```

### specula-org/TLAPS-Bench (MIT)

For `references/instance-bridge.md`.

```text
MIT License

Copyright (c) 2026 The tlaps-bench Authors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

### tlaplus/vscode-tlaplus (MIT)

For `references/type-correctness-lemma.md`.

```text
MIT License

Copyright (c) 2019 Andrew Lygin
Copyright (c) 2020 TLA+ Foundation


Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```
