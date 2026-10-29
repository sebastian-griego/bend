#!/usr/bin/env python3
"""Compare unchanged exports with two kernel executables."""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time

HERE = Path(__file__).resolve().parent.parent
REPO = HERE.parent.parent
BASE = "234cb9b950800f20b15feafcb4ce2f43e76e7fae"
SOURCE_HASH = "1de4fe3963eec5beaf344ef00b6fa802f07d302e6aacdaedfd388e89bc760db4"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bun", default="bun")
    parser.add_argument("--suite", choices=["historical", "review", "all"], default="all")
    parser.add_argument("--source-root", type=Path, default=REPO)
    parser.add_argument("--source-revision", default=BASE)
    parser.add_argument("--baseline-kernel", type=Path, default=HERE / "build/bendtt-baseline")
    parser.add_argument("--candidate-kernel", type=Path, default=HERE / "build/bendtt-consolidated")
    parser.add_argument("--build-record", type=Path, default=HERE / "build/build-verification.json")
    parser.add_argument("--output", type=Path, default=HERE / "build/results-baseline")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--timeout", type=float, default=60)
    args = parser.parse_args()
    if args.jobs < 1 or args.timeout <= 0:
        parser.error("jobs and timeout must be positive")
    source = args.source_root.resolve()
    output = args.output.resolve()
    if output.exists():
        parser.error("output already exists; choose a new directory")
    bun = shutil.which(args.bun)
    if bun is None:
        parser.error("Bun executable not found")
    kernels = {"baseline": args.baseline_kernel.resolve(), "candidate": args.candidate_kernel.resolve()}
    for kernel in kernels.values():
        if not kernel.is_file():
            parser.error("kernel executable not found: " + str(kernel))
    require(sha(HERE / "kernel/Consolidated.lean") == SOURCE_HASH, "reference source changed")
    build_record = json.loads(args.build_record.read_text())
    require(build_record["revised_source"]["sha256"] == SOURCE_HASH, "build used another reference source")
    require(build_record["exact_interface_types_match"] and build_record["exact_interface_axiom_sets_match"], "build interface audit failed")
    kernel_hashes = {name: sha(path) for name, path in kernels.items()}
    require(kernel_hashes["candidate"] == build_record["revised_binary"]["sha256"], "candidate binary differs from verified build")
    baseline_records = [(build_record["baseline_source"], build_record["baseline_binary"])]
    if build_record.get("current_main"):
        current = build_record["current_main"]
        baseline_records.append((current["source"], current["binary"]))
    require(any(s["sha256"] == sha(source / "bend2/bendtt.lean") and b["sha256"] == kernel_hashes["baseline"]
                for s, b in baseline_records), "baseline source or binary differs from verified build")
    names = ["historical", "review"] if args.suite == "all" else [args.suite]
    if "historical" in names and args.source_revision != BASE:
        parser.error("historical expectations require the pinned baseline")
    cases = []
    for name in names:
        for case in json.loads((HERE / f"tests/{name}-cases.json").read_text()):
            cases.append({**case, "suite": name})
    require(len({case["id"] for case in cases}) == len(cases), "duplicate case id")
    # Verify the pinned source tree before using saved expectations.
    for name in ["main.ts", "bend.ts", "safe.ts", "comp.ts", "base.bend", "bendtt.lean"]:
        expected = subprocess.check_output(["git", "show", args.source_revision + ":bend2/" + name], cwd=REPO)
        require((source / "bend2" / name).read_bytes() == expected, "source differs: " + name)
    output.mkdir(parents=True)
    replacements = [(str(output), "$OUTPUT"), (str(source), "$SOURCE"), (str(HERE), "$EXPERIMENT"), (str(REPO), "$REPO")]
    replacements += [(str(path), "$KERNEL_" + name.upper()) for name, path in kernels.items()]

    def normalized(value):
        for before, after in sorted(replacements, key=lambda x: -len(x[0])):
            value = value.replace(before, after)
        return value

    def execute(command, dest, label):
        started = time.monotonic()
        env = {**os.environ, "LEAN_STACK_SIZE_KB": "4194304"}
        process = subprocess.Popen(command, cwd=REPO, env=env, stdin=subprocess.DEVNULL,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
        timed_out = False
        try:
            stdout, stderr = process.communicate(timeout=args.timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate()
        stdout, stderr = normalized(stdout), normalized(stderr)
        (dest / (label + ".stdout")).write_text(stdout)
        (dest / (label + ".stderr")).write_text(stderr)
        return {"code": process.returncode, "timeout": timed_out,
                "seconds": round(time.monotonic() - started, 6), "stdout": stdout, "stderr": stderr}

    def run_case(case):
        path = HERE / case["file"]
        dest = output / case["id"]
        dest.mkdir()
        stages, errors, classifications = {}, [], {}
        row = {"id": case["id"], "suite": case["suite"], "input_sha256": sha(path), "stages": stages,
               "classifications": classifications, "errors": errors}
        if case.get("sha256") and case["sha256"] != row["input_sha256"]:
            errors.append("input differs from historical fixture")
        is_source = case["language"] == "bend"
        target = dest / "export.bendtt" if is_source else path
        command = [bun, str(HERE / "tools/run-source.ts"), str(kernels["baseline"]), str(source / "bend2/main.ts"), str(path)]
        if is_source:
            stages["source"] = execute(command + ["--check-only"], dest, "source")
            stages["export"] = execute(command + ["-o", str(target)], dest, "export")
            if stages["source"]["code"] == 0 and "ALL PROOFS CHECK" not in stages["source"]["stdout"]:
                errors.append("source success without its success message")
            if (stages["source"]["code"] == 0) != case["expected_source"]:
                errors.append("unexpected source result")
            if case["suite"] == "review" and not case["expected_source"]:
                diagnostic = stages["source"]["stdout"] + stages["source"]["stderr"]
                if "expected" not in diagnostic or "observed" not in diagnostic:
                    errors.append("negative source control lacks type mismatch")
        if target.exists():
            row["export_sha256"] = sha(target)
            if case["suite"] == "historical" and is_source and case.get("expected_export_sha256") != row["export_sha256"]:
                errors.append("export differs from historical bytes")
            for name, kernel in kernels.items():
                stage = execute([str(kernel), str(target)], dest, name + "-kernel")
                stages[name + "-kernel"] = stage
                text = stage["stdout"].strip()
                valid = (stage["code"] == 0 and text == "ALL PROOFS CHECK") or (stage["code"] == 1 and text.startswith("SOME PROOFS FAIL"))
                if not valid:
                    errors.append(name + " kernel lacks a valid verdict")
        elif not is_source or stages["export"]["code"] == 0:
            errors.append("export missing")
        for name, kernel in kernels.items():
            if is_source:
                cmd = [bun, str(HERE / "tools/run-source.ts"), str(kernel), str(source / "bend2/main.ts"), str(path), "--verdict"]
                stages[name + "-verdict"] = execute(cmd, dest, name + "-verdict")
                if stages["source"]["code"] != 0:
                    result = "source_reject"
                elif stages["export"]["code"] != 0:
                    result = "translation_reject"
                elif stages.get(name + "-kernel", {}).get("code") == 0:
                    result = "all_accept"
                else:
                    result = "kernel_rejects_translation"
                if (stages[name + "-verdict"]["code"] == 0) != (result == "all_accept"):
                    errors.append(name + " verdict disagrees with separate pipeline")
                if stages[name + "-verdict"]["code"] == 0 and stages[name + "-verdict"]["stdout"].strip() != "ALL PROOFS CHECK":
                    errors.append(name + " verdict success without exact message")
            else:
                result = "kernel_accept" if stages[name + "-kernel"]["code"] == 0 else "kernel_reject"
            classifications[name] = result
            expected = case.get("expected_" + name)
            if expected and result != expected:
                errors.append(name + " classification differs from historical record")
        if case["suite"] == "review" and (classifications["candidate"] == "all_accept") != case["desired_candidate"]:
            errors.append("candidate does not meet desired review result")
        for label, stage in stages.items():
            if stage["timeout"] or stage["code"] not in [0, 1]:
                errors.append(label + " timed out or ended abnormally")
            if "BendTT infrastructure:" in stage["stdout"] + stage["stderr"]:
                errors.append(label + " infrastructure failure")
            if stage["code"] == 1 and not (stage["stdout"] + stage["stderr"]).strip().startswith("SOME PROOFS FAIL"):
                errors.append(label + " rejection lacks a normal failure message")
        if is_source:
            source_diagnostic = (stages["source"]["stdout"] + stages["source"]["stderr"]).strip()
            for name in kernels:
                stage = stages[name + "-verdict"]
                diagnostic = (stage["stdout"] + stage["stderr"]).strip()
                if stages["source"]["code"] == 1 and diagnostic != source_diagnostic:
                    errors.append(name + " rejected source diagnostic differs")
                kernel_stage = stages.get(name + "-kernel")
                if stages["source"]["code"] == 0 and kernel_stage and kernel_stage["code"] == 1:
                    if kernel_stage["stdout"].strip() not in diagnostic:
                        errors.append(name + " verdict lacks the kernel rejection diagnostic")
        if case["suite"] == "historical":
            for label, contract in case["historical_stage_contracts"].items():
                stage = stages.get({"translation": "export", "kernel": "baseline-kernel", "verdict": "baseline-verdict"}.get(label, label))
                if stage is None or stage["code"] != contract["code"]:
                    errors.append(label + " baseline status differs")
                elif any(marker not in stage["stdout"] + "\n" + stage["stderr"] for marker in contract["diagnostic_contains"]):
                    errors.append(label + " baseline diagnostic differs")
        (dest / "result.json").write_text(json.dumps(row, indent=2) + "\n")
        print(case["id"] + ": " + str(classifications) + (" CHECK FAILED" if errors else ""), flush=True)
        return row

    started = time.monotonic()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        rows = list(pool.map(run_case, cases))
    require({name: sha(path) for name, path in kernels.items()} == kernel_hashes, "kernel executable changed during run")
    negative_ids = [c["id"] for c in cases if c.get("intent") == "negative" or c.get("desired_candidate") is False]
    summary = {"source_revision": args.source_revision, "suite": args.suite, "cases": len(rows),
               "source_files": {p: sha(source / "bend2" / p) for p in ["main.ts", "bend.ts", "safe.ts", "comp.ts", "base.bend", "bendtt.lean"]},
               "kernel_binary_hashes": kernel_hashes, "binaries_match_verified_build": True,
               "runner_sha256": sha(Path(__file__)), "build_record_sha256": sha(args.build_record),
               "source_runner_sha256": sha(HERE / "tools/run-source.ts"),
               "reference_source_sha256": SOURCE_HASH, "bun_version": subprocess.check_output([bun, "--version"], text=True).strip(),
               "counts": {name: {x: sum(r["classifications"][name] == x for r in rows) for x in sorted({r["classifications"][name] for r in rows})} for name in kernels},
               "recoveries": [r["id"] for r in rows if r["classifications"]["baseline"] == "kernel_rejects_translation" and r["classifications"]["candidate"] == "all_accept"],
               "negative_controls": len(negative_ids),
               "negative_controls_preserved": all(r["classifications"]["candidate"] not in ["all_accept", "kernel_accept"] for r in rows if r["id"] in negative_ids),
               "errors": {r["id"]: r["errors"] for r in rows if r["errors"]},
               "seconds": round(time.monotonic() - started, 3)}
    (output / "results.json").write_text(json.dumps(rows, indent=2) + "\n")
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    return 1 if summary["errors"] or not summary["negative_controls_preserved"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
