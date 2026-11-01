---
name: tla-setup
description: Set up and check the TLA+ tooling for a project checkout — the runtime tooling clone, the install steps (the tooling at the project's pin, tla2tools, Apalache, tlapm, into the user's shared store) run only when the user asks, `--from` for an archive copied from another host, a JDK 21 or newer, the project files that `tla-tooling init` installs, running the install steps from Codex's sandbox, doctor and smoke. Use when the user asks to set up TLA+, TLC, Apalache or TLAPS for a project, after changing the tooling pin, or when doctor, smoke or a script reports a missing tool.
---

# Setting up TLA+ for a project

The tooling reaches a project as committed files: this skill, `tla-modeling`
and `tlaps` under `.agents/skills/` (Claude Code sees them through
`.claude/skills/`; Codex CLI reads them there), and a block in the root
`AGENTS.md`. They are pinned at the commit recorded as `tooling_revision`
in `tla-tooling.conf`. You never install or configure the agent host
itself.

The entry point is `"$TLA_TOOLING_ROOT/bin/tla-tooling"`, written
`tla-tooling` below.

The tooling runs on x86_64 Linux (Debian or Ubuntu-based) and on macOS 26
(Tahoe) or later on Apple silicon, with Rosetta 2. `sw_vers
-productVersion` prints the macOS version, and `uname -m` prints `arm64`
on Apple silicon. Intel Macs and Linux on arm64 are not supported, since
upstream builds no tlapm for them. Apalache needs a checkout whose path
has no whitespace, which its launcher splits.

## 1. The runtime tooling clone

`TLA_TOOLING_ROOT` names the clone of `tla-formal-tooling`, at a path the
user chose, never inside a project checkout. The scripts find the tooling
only through it.

```bash
export TLA_TOOLING_ROOT="/absolute/path/to/tooling"
test -x "$TLA_TOOLING_ROOT/bin/tla-tooling" && echo ok
git -C "$TLA_TOOLING_ROOT" rev-parse HEAD
```

Use the clone path chosen by the user. Install steps below persist the
export in a marked block in `~/.profile`, preserving unrelated settings
and backing up a changed existing profile as `~/.profile.bak`. Repeating
an install updates the block without duplicating it; `--dry-run` leaves
the profile alone. Remove the block to undo it.

If the variable is unset or wrong in an agent session, explain that the
installer cannot update its parent environment. Have the user export it
in a terminal before relaunching the agent host from that terminal;
another conversation may reuse the existing host. An export only in
`.bashrc` after its interactive-shell guard does not reach noninteractive
shells. Bash reads `~/.bash_profile` or `~/.bash_login` instead of
`~/.profile` when present: the first file it reads must source
`~/.profile` outside interactive-only conditions. Other shells and desktop
launchers may need their login or session environment setup. Persist any
needed `JAVA_HOME` or Homebrew `PATH` settings there too; the installer
only writes `TLA_TOOLING_ROOT`. Finish with doctor and smoke from the
relaunched agent session to verify its inherited environment.

The clone need not be at the project's `tooling_revision`: the tooling
at that pin is in the store (the `tooling` step below, which `init` and
`update` run), and the scripts run it from there when the clone is
elsewhere. One clone serves every project, whatever its pin. Keep it
clean, at the `stable` branch, and develop the tooling in a separate
worktree.

## 2. The tools and the install steps (only when the user asks)

Each tool version is installed once per user, in a store shared by every
project and tooling clone: `~/.local/share/tla-tooling/` (under
`XDG_DATA_HOME` when it is set), one directory per tool version and
digest, and one per pinned tooling revision under `revisions/`.
`tools.lock` at the pin names the version of each tool, with its URL and
SHA-256.

```bash
tla-tooling install STEP --dry-run   # what it would write, and the undo
tla-tooling install STEP
```

Run a step only when the user has asked for it in this session; otherwise
show the command, with what `--dry-run` prints. Each step is idempotent and
downloads nothing when the store has the entry.

| Step | What | Size |
|---|---|---|
| `tooling` | the tooling at the project's pin, cloned from the tooling clone; `init` and `update` run it too | 2.5 MB |
| `tla2tools` | `tla2tools.jar`: SANY, TLC, PlusCal | 4.5 MB |
| `apalache` | the Apalache release, unpacked | 190 MB |
| `tlapm` | the tlapm release for the host's platform, unpacked, with Zenon, Z3, LS4 and Isabelle | 47 MB, 141 MB unpacked; on macOS 37 MB, 117 MB |

`tla-parse` and `tlc` need `tlapm` too, for its proof libraries. Undo a
step by deleting its store entry, once no project's pin uses it.

tla2tools v1.8.0 and tlapm 1.6.0-pre are pre-releases that upstream
re-publishes in place. When upstream has moved, a download no longer
matches the recorded digest and the step refuses it. Then copy the pinned
archive from a host whose store has the entry (it is kept in the entry,
next to a `sha256` file) and run:

```bash
tla-tooling install STEP --from FILE
```

which checks it against the same digest. Moving to a new upstream build is
a change of the tooling (`tools.lock`), never a repair of the old pin.

**From Codex CLI.** Codex's `workspace-write` sandbox allows no network and
no writes outside the workspace, and an install step needs both. Run the
step outside the sandbox, asking the user to approve that one command
(escalated permissions); if the session cannot ask, as under `codex exec`,
show the command for the user to run. Never add the store as a writable
directory of the session. The checking scripts themselves run inside the
sandbox: they only read the store and the clone, and write in the
checkout.

**Projects that do not adopt the tooling** can use the store from their
Makefiles; `path TOOL` prints the pinned file or launcher:

```make
TLA2TOOLS ?= $(shell "$(TLA_TOOLING_ROOT)/bin/tla-tooling" path tla2tools)
APALACHE  ?= $(shell "$(TLA_TOOLING_ROOT)/bin/tla-tooling" path apalache)
```

## 3. Java (the user installs it)

The tooling never runs `sudo`. Apalache needs Java 21 or newer (tla2tools
needs 11, tlapm none). On Debian or Ubuntu, show:

```bash
sudo apt install openjdk-21-jdk-headless
```

On macOS, show these, for the user to run (the second because the Command
Line Tools ship Python 3.9, and the third because tlapm's Z3 is an x86_64
binary):

```bash
brew install --cask temurin@21
brew install python
softwareupdate --install-rosetta --agree-to-license
```

The cask lands in `/Library/Java/JavaVirtualMachines`, where
`/usr/bin/java` finds it; Homebrew's `openjdk@21` formula does not, and
needs `JAVA_HOME`. `/opt/homebrew/bin` must be on `PATH` in the profile
that the shell starting the host reads.

The scripts use `$JAVA_HOME/bin/java` when `JAVA_HOME` is set, else the
`java` on `PATH`. Python 3.11 or newer runs the tooling.

## 4. The project files

If the checkout has no `tla-tooling.conf`, the user runs, before a host
session starts there:

```bash
tla-tooling init [--tla-rel DIR]           # a new project
tla-tooling init --adopt [--tla-rel DIR]   # DIR already holds .tla modules
```

Ask for the specifications directory (default the checkout root). `init`
prints every path it touched and the `git add` command for them; it never
stages, commits or overwrites. Without `--adopt` it also renders, for the
project to own, `<tla_rel>/AGENTS.md` (unless at the root) and
`<tla_rel>/.gitignore` when absent, with the tools' outputs (`.tla-runs/`,
`.tlacache/`, `states/`, `_apalache-out/`, `*_TTrace_*`); when the file
exists, `init` names the outputs Git would not ignore, for the user to add.
`init` refuses to replace a skill directory of the same name that it did
not install: remove the project's own copy first.

`init --adopt` renders nothing, but names the same outputs, and the root
block still points agents at `<tla_rel>/AGENTS.md`. If that file does not
exist, offer to create it, starting from
`$TLA_TOOLING_ROOT/templates/AGENTS.md`.

Afterwards:

- `tla-tooling sync --check` compares the project files with the pin,
  read-only; `sync` reinstalls them and refuses to overwrite an edited one.
- `tla-tooling update REV` (or `update stable`) is the only command that
  moves the pin; it installs the tooling at REV in the store.
- `tla-tooling remove` takes the project files out, leaving the
  specifications and the instruction files.
- `tla-tooling skills list` and `skills show NAME` print the pinned skills.

`proof_modules` in `tla-tooling.conf` lists the modules whose proofs
`tlaps-report` checks; it stays empty until there is a result to report
(the `tlaps` skill).

## 5. Doctor, then smoke

```bash
tla-tooling doctor
tla-tooling smoke
```

Doctor reads only; it prints what fails and runs no checker. It checks the
descriptor, that `TLA_TOOLING_ROOT` names a clean clone, where the scripts
run (the clone, when it is at the pin, else the store) and that the store
has the pin, the host's platform and, on a Mac, its macOS; it prints the
Python running it; it checks that `java` is 21 or newer, that the store
has the entry `tools.lock` names for each tool, that tlapm and its Z3
print their versions, and the project files. Run it from the host session,
so it sees that session's `PATH` and Java. Fix what it reports, in order,
then rerun it.

Smoke copies the pin's fixtures into a run directory of the project and
runs each tool once through its script: `tla-parse` on a module that
extends `TLAPS`, `tlc` on a small model (checking its state count),
`apalache check` on a small typed specification, and `tlaps-check` on a
module that exercises every tlapm backend. It takes about ten seconds. A
green doctor and smoke is the finished setup; hand over to `tla-modeling`
and `tlaps`.

## What this skill never does

Install or configure Claude Code or Codex CLI; run `sudo`; run an install
step the user has not asked for in this session; accept an archive whose
digest differs from `tools.lock`; widen the sandbox of a Codex session;
nest the tooling clone in a project checkout.
