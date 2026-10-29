BendTT equality reference for issue #1623
========================================

This is an experimental checker with its complete Lean safety development.
It is published for independent evaluation of issue #1623 and the cases
from the review of PR #1657. It is not a proposed production replacement.
All production files on this branch remain at the historical baseline.

Start with kernel/Consolidated.lean, proof-interface.txt, and the commands
below. The proof source is self-contained apart from Lean's standard
library. It has the same bytes as the previously audited development.
No proof was removed for this publication.

Pinned versions
---------------

Historical source and kernel:
  234cb9b950800f20b15feafcb4ce2f43e76e7fae
Current-main comparison, fetched on 2026-10-29:
  4982c105b9e8e06cc1d1e2d0d63c546dac4aa377
Lean: 4.34.0. Bun used in the saved runs: 1.3.14.
Python: 3.9 or later, standard library only.
Native build and replay platform: macOS arm64.
Reference source SHA256:
  1de4fe3963eec5beaf344ef00b6fa802f07d302e6aacdaedfd388e89bc760db4

Build and replay
----------------

Clone the branch and enter the repository root:

  git clone --branch research/kernel-eta-reference https://github.com/sebastian-griego/bend.git
  cd bend

Install Lean 4.34.0 and Bun. Give build.py the directory that contains
that Lean version's lean and leanc executables:

  python3 research/kernel-eta/tools/build.py --lean-bin /path/to/lean-4.34.0/bin
  python3 research/kernel-eta/tools/run.py --bun bun

The build compiles the full revised proof and the unchanged historical
kernel. It checks all 39 selected interface declarations against the saved
raw Lean expression types and axiom sets. It checks the 37 theorem axiom
reports and the CLI contract. Generated C, Lean objects, executables, and
fresh logs stay under research/kernel-eta/build/.

The default replay runs 263 historical cases and 14 review cases. It checks
source acceptance, one shared exported book, both direct kernels, and both
normal --verdict commands. BENDTT selects the kernel executable; no exporter
or certificate is patched. The runner checks executable hashes against the
verified build record. It checks the pinned source bytes, historical export
hashes, rejection diagnostics, and agreement between verification stages.
Timeouts and process failures are errors. They do not count as rejections.
The wrapper sets BEND_NO_TELEMETRY=1 to disable unrelated update notices.

To rerun, choose a new output directory:

  python3 research/kernel-eta/tools/run.py --bun bun --output research/kernel-eta/build/replay-2

To test the newer source version, fetch that exact commit and make a separate
snapshot. This does not change the branch's production files:

  git fetch https://github.com/bendlang/bend.git 4982c105b9e8e06cc1d1e2d0d63c546dac4aa377
  mkdir -p research/kernel-eta/build/current-main
  git archive 4982c105b9e8e06cc1d1e2d0d63c546dac4aa377 | tar -x -C research/kernel-eta/build/current-main
  python3 research/kernel-eta/tools/build.py --lean-bin /path/to/lean-4.34.0/bin --current-source research/kernel-eta/build/current-main/bend2/bendtt.lean
  python3 research/kernel-eta/tools/run.py --bun bun --suite review --source-root research/kernel-eta/build/current-main --source-revision 4982c105b9e8e06cc1d1e2d0d63c546dac4aa377 --baseline-kernel research/kernel-eta/build/current-kernel/bendtt --output research/kernel-eta/build/review-current

The 14 review inputs need no syntax or quantity adaptation between the two
versions. See tests/review/README.txt for each claim and its provenance.

Results from the fresh runs
--------------------------

On the historical baseline, all 263 cases reproduce their saved results.
The revised checker accepts all 53 source translations that the original
kernel rejected. All 92 intentional negative controls remain rejected:
53 by the kernel and 39 by the source checker. Five further historical
source cases remain rejected for existing source restrictions; they are
not included in the count of intentional negative controls.

For the 14 review cases:

  Source version       Unchanged kernel   Revised kernel   Source rejects
  234cb9b9              8 accept / 4 reject 12 accept        2
  4982c105             10 accept / 2 reject 12 accept        2

At 4982c105, the unchanged kernel rejects exactly the original helper-reuse
example and viridale's generic-versus-specialized example. The revised
checker accepts both, and retains the valid field/argument cases named in
the #1657 review. Both unrelated-function controls fail source checking.
Those two controls are not independent negative tests of the kernel.

All direct-kernel and --verdict results agree. The two checkers receive the
same exported bytes for each source input. The saved review books are in
evidence/{baseline,current}/books/. The result JSON files contain every
stage's exit code, normal output, error output, and hashes. Build records
and logs are also included. Native binary hashes can differ on another
platform. Runtime measurements are not a performance claim.

Equality design
---------------

ExecutableOrder.Join is joinability under comparison reduction after
erasing Lam and App quantity tags. Comparison reduction includes eta.
Erasure retains All, Sig, Tup, and Let quantity tags. Function types with
different parameter quantities remain distinct.

The executable comparator is diagnosticCompare. diagnosticQge and
diagnosticFits use it. ExecutableOrder.NewFits changes semantic type fitting with
the equality relation; keeping the old fitting relation is not justified.
The CLI uses Candidate.checkText and Revised.checkBook. Original runtime
reduction and liveness checks remain in the safety statements.

The change therefore includes quantity handling as well as eta comparison.
It is not unrestricted eta contraction of quantity-sensitive runtime terms.
The field/argument workaround from #1657 is not part of this branch.

Proved guarantees and limits
---------------------------

The full source proves soundness of the revised comparator and checker,
typed substitution, preservation under original runtime reduction,
progress, typed eta factorization, Data canonical forms, and checked-book
consistency. It retains the original termination and reduction confluence
results. Equal values at the same revised type have the same Data
classification. The exact statements retain their typing, type formation,
value, book, and liveness premises. See proof-interface.txt and the Lean
declarations; the tests do not replace these premises.

The 39 selected declaration types and axiom sets match the prior audit.
Their only axioms are propext, Classical.choice, and Quot.sound. The proof
source has no sorry, admit, custom axiom, or unsafe declaration.

This does not prove source-checker soundness, safe.ts translation
correctness, parser correctness against a separate text specification,
comparator completeness, an adequate fixed fuel bound, native compiler
correctness, or performance. Arbitrary eta contraction does not preserve
exact quantity-sensitive typing.

Two later kernel changes are not integrated:

- #1627 added adequacy: closed live equality proofs imply conversion of
  their sides. This reference does not prove a revised version. Such a
  theorem must conclude revised Join, not the original Conv relation.
- #1892 added rigid-first comparison and a reflexive fitting fast path.
  This reference lacks that strategy. The review tests do not establish
  that it accepts every program accepted by current main.

Integration obstacle
--------------------

The complete reference has 112,488 tokens with ttok 0.3 / cl100k_base.
The repository's kernel cap is 64,000. No cap or allow-list rule changed.
The research directory is outside the production allow list. It is a
publication package, not a way to make an upstream patch pass that gate.
A production contribution still needs proof consolidation, a review of
the equality design, and integration of later kernel changes.

Contents
--------

kernel/Consolidated.lean: complete proved checker and CLI.
kernel/audited-interface.json: exact selected Lean types and axiom sets.
proof-interface.txt: theorem map and required premises.
tools/build.py: portable proof, interface, and native build checks.
tools/run.py: portable source/export/kernel/verdict regression runner.
tests/historical/: all 263 unchanged historical inputs.
tests/review/: the 14 new inputs and provenance notes.
evidence/baseline/: fresh 277-case results with the historical exporter.
evidence/current/: fresh 14-case results with source commit 4982c105.
evidence/build-verification.json: final build-script replay record.
evidence/regression-build-verification.json: exact build record used by tests.
evidence/logs/: logs from the final build-script replay.

References
----------

https://github.com/bendlang/bend/issues/1623
https://github.com/bendlang/bend/issues/1623#issuecomment-6305183385
https://github.com/bendlang/bend/issues/1623#issuecomment-6498222408
https://github.com/bendlang/bend/pull/1657#pullrequestreview-5571378389
https://github.com/bendlang/bend/pull/1627
https://github.com/bendlang/bend/pull/1892
