#!/usr/bin/env python3
"""Build the complete Lean reference and compare its audited proof interface."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

REFERENCE = Path(__file__).resolve().parents[1]
REPOSITORY = REFERENCE.parents[1]
EXPECTED_SOURCE = "1de4fe3963eec5beaf344ef00b6fa802f07d302e6aacdaedfd388e89bc760db4"
EXPECTED_BASELINE = "cc78aa9ff3491ff1b788797bdcab4cb98107dcb1730ed99834f6933b11d88335"
EXPECTED_INTERFACE = "eb73bcf876f5de00a27f8fbebeee6f754c6d14561df1b2cc8d9c15ca5475324d"
PERMITTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_record(path, expected=None):
    digest = sha256(path)
    if expected is not None:
        require(digest == expected, f"Unexpected source hash: {path.name}: {digest}")
    source = path.read_text(encoding="utf-8")
    imports = re.findall(r"^import (.+)$", source, re.M)
    require(imports == ["Std.Data.HashMap"], f"Unexpected imports in {path.name}: {imports}")
    require(not re.search(r"^\s*(axiom|opaque|unsafe)\s|\bsorry\b|\badmit\b", source, re.M),
            f"Unproved or unsafe declaration in {path.name}")
    return {"sha256": digest, "bytes": path.stat().st_size,
            "lines": len(source.splitlines()), "imports": imports,
            "no_sorry_admit_custom_axioms_or_unsafe": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path, required=True,
                        help="Directory with Lean 4.34.0 lean and leanc executables.")
    parser.add_argument("--build-dir", type=Path, default=REFERENCE / "build")
    parser.add_argument("--current-source", type=Path,
                        help="Optional unchanged current-main bendtt.lean for comparison.")
    parser.add_argument("--timeout", type=int, default=900,
                        help="Maximum seconds for each compiler command (default: 900).")
    args = parser.parse_args()
    lean_bin = args.lean_bin.resolve()
    build = args.build_dir.resolve()
    require(build != REPOSITORY and build != REFERENCE,
            "The build directory must be separate from repository and reference roots.")
    require(not build.is_relative_to(REFERENCE / "kernel"),
            "The build directory must be outside kernel/.")
    build.mkdir(parents=True, exist_ok=True)
    logs = build / "logs"
    logs.mkdir(exist_ok=True)
    source = REFERENCE / "kernel" / "Consolidated.lean"
    baseline = REPOSITORY / "bend2" / "bendtt.lean"
    interface = REFERENCE / "kernel" / "audited-interface.json"
    require(sha256(interface) == EXPECTED_INTERFACE, "The audited interface changed.")
    audited = json.loads(interface.read_text(encoding="utf-8"))
    names = [row["name"] for row in audited]
    require(len(names) == 39 and len(set(names)) == len(names), "Invalid audited interface.")
    source_info = source_record(source, EXPECTED_SOURCE)
    baseline_info = source_record(baseline, EXPECTED_BASELINE)
    version = subprocess.check_output([str(lean_bin / "lean"), "--version"], text=True).strip()
    short_version = subprocess.check_output([str(lean_bin / "lean"), "--short-version"], text=True).strip()
    require(short_version == "4.34.0", f"Lean 4.34.0 is required; found {short_version}.")
    substitutions = [(str(build), "$BUILD"), (str(REFERENCE), "$REFERENCE"),
                     (str(REPOSITORY), "$REPOSITORY"), (str(lean_bin), "$LEAN_BIN")]
    if args.current_source is not None:
        substitutions.append((str(args.current_source.resolve()), "$CURRENT_SOURCE"))
    substitutions.sort(key=lambda pair: len(pair[0]), reverse=True)

    def portable(value):
        for path, label in substitutions:
            value = value.replace(path, label)
        return value

    stages = []

    def run(label, command, cwd, *, env=None):
        print(f"Running {label}...", flush=True)
        started = time.monotonic()
        result = subprocess.run([str(item) for item in command], cwd=cwd,
                                env=env, capture_output=True, text=True, timeout=args.timeout)
        out = portable(result.stdout)
        err = portable(result.stderr)
        (logs / f"{label}.stdout.txt").write_text(out, encoding="utf-8")
        (logs / f"{label}.stderr.txt").write_text(err, encoding="utf-8")
        stages.append({"stage": label, "command": [portable(str(item)) for item in command],
                       "cwd": portable(str(cwd)), "returncode": result.returncode,
                       "seconds": round(time.monotonic() - started, 6),
                       "stdout": f"logs/{label}.stdout.txt", "stderr": f"logs/{label}.stderr.txt"})
        require(result.returncode == 0, f"{label} failed. See {logs.name}/{label}.*.txt.\n{out}{err}")
        require(not re.search(r"(?:\b(?:error|warning)\s*:|\bsorryAx\b)", out + err),
                f"{label} produced a warning or error. See the build logs.")
        return result

    def compile_kernel(label, origin, module, binary):
        destination = build / label
        destination.mkdir(exist_ok=True)
        copied = destination / f"{module}.lean"
        shutil.copyfile(origin, copied)
        result = run(f"{label}-lean", [lean_bin / "lean", "-o", f"{module}.olean",
                     "-c", f"{module}.c", copied.name], destination)
        run(f"{label}-native", [lean_bin / "leanc", "-O2", "-o", binary,
                               f"{module}.c"], destination)
        smoke = subprocess.run([str(binary)], cwd=destination, capture_output=True, text=True,
                               timeout=args.timeout)
        require(smoke.returncode == 2 and smoke.stdout == "usage: bendtt <file.bendtt>\n"
                and smoke.stderr == "", f"{label} has an unexpected CLI contract.")
        require(sha256(origin) == sha256(copied), f"{label} source changed during compilation.")
        return {"path": portable(str(binary)), "sha256": sha256(binary),
                "usage_smoke_pass": True}, result

    revised_binary, revised_result = compile_kernel(
        "revised", source, "Consolidated", build / "bendtt-consolidated")
    printed = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", revised_result.stdout)
    require(len(printed) == 37, f"Expected 37 theorem axiom reports; found {len(printed)}.")
    require({name for name, _ in printed} == set(names[2:]), "The printed theorem set changed.")
    for name, axioms in printed:
        used = {item.strip() for item in axioms.split(",") if item.strip()}
        require(used <= PERMITTED_AXIOMS, f"Unexpected axioms for {name}: {sorted(used)}")

    declarations = ", ".join(f"``{name}" for name in names)
    interface_source = f'''import Consolidated
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let names := [{declarations}]
  let mut rows := #[]
  for n in names do
    let some c := env.find? n | throwError "missing interface declaration {{n}}"
    let axs ← Lean.collectAxioms n
    rows := rows.push (Json.mkObj [
      ("name",toJson n.toString),
      ("type",toJson (reprStr c.type)),
      ("axioms",toJson (axs.map Name.toString))])
  IO.FS.writeFile "fresh-interface.json" (Json.pretty (Json.arr rows))
'''
    revised_dir = build / "revised"
    (revised_dir / "Interface.lean").write_text(interface_source, encoding="utf-8")
    env = os.environ.copy()
    env["LEAN_PATH"] = str(revised_dir)
    run("proof-interface", [lean_bin / "lean", "Interface.lean"], revised_dir, env=env)
    fresh = json.loads((revised_dir / "fresh-interface.json").read_text(encoding="utf-8"))
    require([row["name"] for row in fresh] == names, "Fresh interface declarations differ.")
    for actual, expected in zip(fresh, audited):
        require(actual["type"] == expected["type"], f"The exact type changed: {actual['name']}")
        require(set(actual["axioms"]) == set(expected["axioms"]),
                f"The axiom dependencies changed: {actual['name']}")
        require(set(actual["axioms"]) <= PERMITTED_AXIOMS,
                f"Unexpected axioms: {actual['name']}")
    baseline_binary, _ = compile_kernel("baseline", baseline, "bendtt", build / "bendtt-baseline")
    current = None
    if args.current_source is not None:
        current_source = args.current_source.resolve()
        current_info = source_record(current_source)
        current_dir = build / "current-kernel"
        current_dir.mkdir(exist_ok=True)
        current_binary, _ = compile_kernel("current-kernel", current_source, "bendtt", current_dir / "bendtt")
        current = {"source": current_info, "binary": current_binary}

    require(sha256(source) == EXPECTED_SOURCE and sha256(baseline) == EXPECTED_BASELINE,
            "A source file changed during the build.")
    record = {
        "schema": 1, "runner_sha256": sha256(Path(__file__)),
        "python_version": sys.version.split()[0],
        "lean_version": version, "lean_short_version": short_version,
        "revised_source": source_info, "baseline_source": baseline_info,
        "revised_binary": revised_binary, "baseline_binary": baseline_binary,
        "current_main": current, "audited_interface_sha256": EXPECTED_INTERFACE,
        "interface_declarations": len(fresh), "printed_theorem_axiom_reports": len(printed),
        "exact_interface_types_match": True, "exact_interface_axiom_sets_match": True,
        "permitted_axioms": sorted(PERMITTED_AXIOMS),
        "interface": [{"name": row["name"], "axioms": row["axioms"]} for row in fresh],
        "stages": stages,
        "limits": [
            "This checks the complete Lean source and the selected audited interface.",
            "It does not prove safe.ts translation correctness or source-checker soundness.",
            "It does not prove comparator completeness or an adequate fixed fuel bound.",
            "It does not prove parsing against an independent text specification.",
            "It does not prove native compiler correctness or runtime performance.",
            "Binary hashes and build times depend on the platform and toolchain.",
        ],
    }
    output = build / "build-verification.json"
    output.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "PASS", "interface_declarations": len(fresh),
                      "revised_source_sha256": source_info["sha256"],
                      "baseline_source_sha256": baseline_info["sha256"],
                      "record": portable(str(output))}, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, subprocess.SubprocessError) as error:
        print(f"Build failed: {error}", file=sys.stderr)
        sys.exit(1)
