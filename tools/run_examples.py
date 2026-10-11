#!/usr/bin/env python3
"""Verify every program and every proof of the course.

Three kinds of artifacts are checked:

Rust examples (code/rust/examples/*.rs and code/rust/crates/*/examples/*.rs)
    carry a directive on one of their first lines:
        // harness: run [timeout=SECONDS] [args="..."]   must exit with code 0
        // harness: build-only                            only compiled
    The standard output of every `run` example is compared with the snapshot in
    code/rust/output/<name>.txt, which the book includes. `--bless` rewrites the
    snapshots from the current output.

Rust programs that must NOT compile (code/rust/compile_fail/*.rs)
    carry the error codes they must produce:
        // harness: compile-fail E0382 [E0505 ...]
    or, for diagnostics that have no error code (some lifetime errors, lints
    turned into errors with #![deny(...)]), a quoted text the output must contain:
        // harness: compile-fail "lifetime may not live long enough"
    They are compiled with rustc on their own; the diagnostics are compared with
    code/rust/compile_fail/<name>.stderr (included by the book). `--bless`
    rewrites those files. `--codes-only` checks only the error codes. Paths into
    the local copy of the standard library's source are written as rustc's
    machine-independent /rustc/<commit-hash>/library/... .

Lean files (code/lean/Book/**/*.lean)
    are built with `lake build`. Every message Lean prints (info, warning or
    error) is a failure: outputs shown in the book must be wrapped in
    `#guard_msgs`, which checks them against the doc comment above the command.
    The project depends on Mathlib: fetch the prebuilt library once with
    `lake exe cache get` (in code/lean) before the first build.

Usage:
    tools/run_examples.py                  # everything except crate tests
    tools/run_examples.py --only ch05      # only artifacts whose name starts with ch05
    tools/run_examples.py --rust           # only Rust examples (also --compile-fail, --lean)
    tools/run_examples.py --tests          # also run `cargo test` for every crate
    tools/run_examples.py --only ch05 --bless

Honours CARGO_TARGET_DIR.
"""

from __future__ import annotations

import argparse
import functools
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RUST = ROOT / "code" / "rust"
LEAN = ROOT / "code" / "lean"
OUTPUT = RUST / "output"
COMPILE_FAIL = RUST / "compile_fail"
HARNESS_RE = re.compile(r"^\s*//\s*harness:\s*(\S+)(.*)$")
LEAN_MSG_RE = re.compile(r"^(warning|info|error): (.*\.lean:\d+:\d+: .*)$")
CHAPTER_RE = re.compile(r"^ch(\d+)", re.I)


@dataclass
class Program:
    name: str
    package: str
    mode: str          # run | build-only
    opts: dict = field(default_factory=dict)
    path: Path = Path()
    root_package: bool = False


@dataclass
class Result:
    kind: str
    name: str
    ok: bool
    detail: str = ""
    seconds: float = 0.0


def parse_directive(path: Path) -> tuple[str, list[str], dict] | None:
    try:
        head = path.read_text().splitlines()[:5]
    except OSError:
        return None
    for line in head:
        m = HARNESS_RE.match(line)
        if m:
            words, opts = [], {}
            for tok in shlex.split(m.group(2)):
                if "=" in tok:
                    k, v = tok.split("=", 1)
                    opts[k] = v
                else:
                    words.append(tok)
            return m.group(1), words, opts
    return None


def package_name(crate_dir: Path) -> str:
    return tomllib.loads((crate_dir / "Cargo.toml").read_text())["package"]["name"]


def discover_rust() -> list[Program]:
    progs: list[Program] = []
    dirs = [(RUST / "examples", package_name(RUST), True)]
    for crate in sorted((RUST / "crates").iterdir()):
        if (crate / "Cargo.toml").exists() and (crate / "examples").is_dir():
            dirs.append((crate / "examples", package_name(crate), False))
    for ex_dir, pkg, is_root in dirs:
        if not ex_dir.is_dir():
            continue
        for p in sorted(ex_dir.iterdir()):
            src = p / "main.rs" if p.is_dir() else p
            if src.suffix != ".rs" or not src.exists():
                continue
            d = parse_directive(src)
            name = p.stem if p.is_file() else p.name
            if d is None:
                print(f"warning: {src.relative_to(ROOT)} has no harness directive; skipped")
                continue
            progs.append(Program(name, pkg, d[0], d[2], src, is_root))
    return progs


def cargo_env() -> dict:
    env = dict(os.environ)
    env.setdefault("CARGO_TERM_COLOR", "never")
    return env


def run_rust(prog: Program, bless: bool) -> Result:
    t0 = time.time()
    pkg_args = [] if prog.root_package else ["-p", prog.package]
    if prog.mode == "build-only":
        cmd = ["cargo", "build", "-q", *pkg_args, "--example", prog.name]
        res = subprocess.run(cmd, cwd=RUST, capture_output=True, text=True, env=cargo_env())
        ok = res.returncode == 0
        return Result("rust", prog.name, ok, "" if ok else res.stderr[-3000:], time.time() - t0)
    if prog.mode != "run":
        return Result("rust", prog.name, False, f"unknown harness mode '{prog.mode}'")
    build = subprocess.run(
        ["cargo", "build", "-q", *pkg_args, "--example", prog.name],
        cwd=RUST, capture_output=True, text=True, env=cargo_env(),
    )
    if build.returncode != 0:
        return Result("rust", prog.name, False, build.stderr[-3000:], time.time() - t0)
    if build.stderr.strip():
        # Warnings: the course examples must have none.
        return Result("rust", prog.name, False, "compiler warnings:\n" + build.stderr[-3000:])
    timeout = float(prog.opts.get("timeout", 60))
    args = shlex.split(prog.opts.get("args", ""))
    cmd = ["cargo", "run", "-q", *pkg_args, "--example", prog.name, "--", *args]
    try:
        res = subprocess.run(cmd, cwd=RUST, capture_output=True, text=True,
                             env=cargo_env(), timeout=timeout)
    except subprocess.TimeoutExpired:
        return Result("rust", prog.name, False, f"timed out after {timeout:.0f}s", time.time() - t0)
    secs = time.time() - t0
    if res.returncode != 0:
        return Result("rust", prog.name, False,
                      f"exit code {res.returncode}\n{res.stdout[-1500:]}{res.stderr[-1500:]}", secs)
    snap = OUTPUT / f"{prog.name}.txt"
    if bless:
        OUTPUT.mkdir(parents=True, exist_ok=True)
        snap.write_text(res.stdout)
        return Result("rust", prog.name, True, "blessed", secs)
    if not snap.exists():
        return Result("rust", prog.name, False, f"no snapshot {snap.relative_to(ROOT)} (run with --bless)", secs)
    if snap.read_text() != res.stdout:
        return Result("rust", prog.name, False, diff(snap.read_text(), res.stdout), secs)
    return Result("rust", prog.name, True, "", secs)


def diff(expected: str, actual: str) -> str:
    import difflib

    lines = difflib.unified_diff(expected.splitlines(), actual.splitlines(),
                                 "snapshot", "actual", lineterm="", n=2)
    return "output differs from snapshot:\n" + "\n".join(list(lines)[:40])


# --------------------------------------------------------------------------------------
# compile-fail
# --------------------------------------------------------------------------------------

TRAILER_RE = re.compile(
    r"^(error: aborting due to .*|For more information about (this|an) error.*|"
    r"Some errors have detailed explanations.*)$"
)


@functools.cache
def std_source_paths() -> tuple[str, str]:
    """The local path of the standard library's source (the rust-src component),
    which depends on the machine, and the path rustc shows without it."""
    def rustc(*args: str) -> str:
        return subprocess.run(["rustc", *args], cwd=RUST, capture_output=True,
                              text=True, check=True).stdout
    sysroot = Path(rustc("--print", "sysroot").strip())
    commit = re.search(r"^commit-hash: (\S+)$", rustc("-vV"), re.M).group(1)
    return str(sysroot / "lib" / "rustlib" / "src" / "rust"), f"/rustc/{commit}"


def normalize_stderr(text: str) -> str:
    local, portable = std_source_paths()
    text = text.replace(local, portable)
    lines = [ln.rstrip() for ln in text.splitlines()]
    lines = [ln for ln in lines if not TRAILER_RE.match(ln)]
    while lines and not lines[-1].strip():
        lines.pop()
    return "\n".join(lines) + "\n"


def run_compile_fail(path: Path, bless: bool, codes_only: bool) -> Result:
    t0 = time.time()
    d = parse_directive(path)
    rel = path.relative_to(RUST)
    if d is None or d[0] != "compile-fail" or not d[1]:
        return Result("compile-fail", path.stem, False,
                      "needs a '// harness: compile-fail E0xxx' or "
                      "'// harness: compile-fail \"message\"' directive")
    codes = [w for w in d[1] if re.fullmatch(r"E\d{4}", w)]
    texts = [w for w in d[1] if not re.fullmatch(r"E\d{4}", w)]
    with tempfile.TemporaryDirectory() as tmp:
        cmd = ["rustc", "--edition", "2024", "--crate-type", "lib", "--emit=metadata",
               "--color", "never", "-A", "warnings", "--crate-name", path.stem,
               "-o", str(Path(tmp) / "out.rmeta"), str(rel)]
        res = subprocess.run(cmd, cwd=RUST, capture_output=True, text=True)
    secs = time.time() - t0
    if res.returncode == 0:
        return Result("compile-fail", path.stem, False, "compiled successfully, but must not", secs)
    missing = [c for c in codes if f"error[{c}]" not in res.stderr]
    missing += [repr(t) for t in texts if t not in res.stderr]
    if missing:
        return Result("compile-fail", path.stem, False,
                      f"expected {', '.join(missing)}; got:\n{res.stderr[-2500:]}", secs)
    text = normalize_stderr(res.stderr)
    snap = path.with_suffix(".stderr")
    if bless:
        snap.write_text(text)
        return Result("compile-fail", path.stem, True, "blessed", secs)
    if codes_only:
        return Result("compile-fail", path.stem, True, "", secs)
    if not snap.exists():
        return Result("compile-fail", path.stem, False,
                      f"no snapshot {snap.relative_to(ROOT)} (run with --bless)", secs)
    if snap.read_text() != text:
        return Result("compile-fail", path.stem, False, diff(snap.read_text(), text), secs)
    return Result("compile-fail", path.stem, True, "", secs)


# --------------------------------------------------------------------------------------
# Lean
# --------------------------------------------------------------------------------------

def lean_modules(project: Path, lib: str, only: str | None) -> list[str]:
    mods = []
    for f in sorted((project / lib).rglob("*.lean")):
        rel = f.relative_to(project).with_suffix("")
        mod = ".".join(rel.parts)
        if only:
            m = CHAPTER_RE.match(only)
            chapter_dir = f"Ch{int(m.group(1)):02d}" if m else None
            if chapter_dir is None or chapter_dir not in rel.parts:
                continue
        mods.append(mod)
    return mods


def run_lean(only: str | None, project: Path = LEAN, lib: str = "Book",
             kind: str = "lean") -> list[Result]:
    if not shutil.which("lake"):
        return [Result(kind, "lake build", False, "lake not found (install elan)")]
    if not (project / ".lake" / "packages" / "mathlib").is_dir():
        return [Result(kind, "lake build", False,
                       f"Mathlib not fetched: run `lake exe cache get` in {project.relative_to(ROOT)}")]
    mods = lean_modules(project, lib, only)
    if not mods:
        return []
    t0 = time.time()
    cmd = ["lake", "build", *mods] if only else ["lake", "build"]
    res = subprocess.run(cmd, cwd=project, capture_output=True, text=True)
    secs = time.time() - t0
    out = res.stdout + res.stderr
    messages = [ln for ln in out.splitlines() if LEAN_MSG_RE.match(ln.strip())]
    label = "lake build" + (f" ({len(mods)} modules)" if only else "")
    if res.returncode != 0:
        return [Result(kind, label, False, out[-4000:], secs)]
    if messages:
        return [Result(kind, label, False,
                       "unguarded messages (wrap outputs in #guard_msgs, fix warnings):\n"
                       + "\n".join(messages[:40]), secs)]
    return [Result(kind, label, True, f"{len(mods)} module(s)", secs)]


# --------------------------------------------------------------------------------------
# crate tests
# --------------------------------------------------------------------------------------

def run_tests(only: str | None) -> list[Result]:
    results = []
    pkgs = [package_name(RUST)]
    pkgs += [package_name(c) for c in sorted((RUST / "crates").iterdir()) if (c / "Cargo.toml").exists()]
    for pkg in pkgs:
        t0 = time.time()
        res = subprocess.run(["cargo", "test", "-q", "-p", pkg], cwd=RUST,
                             capture_output=True, text=True, env=cargo_env())
        ok = res.returncode == 0
        results.append(Result("test", pkg, ok, "" if ok else (res.stdout + res.stderr)[-3000:],
                              time.time() - t0))
    return results


# --------------------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------------------

def selected(name: str, only: str | None) -> bool:
    """Does an artifact name match --only?

    A bare chapter (`ch2`, `ch02`) selects exactly that chapter, so that `ch2` does
    not also select chapters 20-29; anything else is a plain name prefix.
    """
    if not only:
        return True
    m = re.fullmatch(r"ch(\d+)", only, re.I)
    if m:
        return name.lower().startswith(f"ch{int(m.group(1)):02d}_")
    return name.startswith(only)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--only", help="only artifacts whose name starts with this prefix (e.g. ch05)")
    ap.add_argument("--rust", action="store_true", help="run the Rust examples")
    ap.add_argument("--compile-fail", action="store_true", help="check the compile-fail programs")
    ap.add_argument("--lean", action="store_true", help="build the Lean project")
    ap.add_argument("--tests", action="store_true", help="also run cargo test for every package")
    ap.add_argument("--bless", action="store_true", help="rewrite output and diagnostic snapshots")
    ap.add_argument("--codes-only", action="store_true",
                    help="compile-fail: check error codes but not the diagnostic text")
    a = ap.parse_args()
    everything = not (a.rust or a.compile_fail or a.lean)
    results: list[Result] = []

    if a.rust or everything:
        for prog in discover_rust():
            if not selected(prog.name, a.only):
                continue
            r = run_rust(prog, a.bless)
            results.append(r)
            report(r)
    if a.compile_fail or everything:
        for path in sorted(COMPILE_FAIL.glob("*.rs")):
            if not selected(path.stem, a.only):
                continue
            r = run_compile_fail(path, a.bless, a.codes_only)
            results.append(r)
            report(r)
    if a.lean or everything:
        for r in run_lean(a.only):
            results.append(r)
            report(r)
    if a.tests:
        for r in run_tests(a.only):
            results.append(r)
            report(r)

    failed = [r for r in results if not r.ok]
    print(f"\n{len(results) - len(failed)} passed, {len(failed)} failed")
    return 1 if failed else 0


def report(r: Result) -> None:
    status = "ok  " if r.ok else "FAIL"
    extra = f" ({r.detail})" if r.ok and r.detail else ""
    print(f"{status} {r.kind:<13} {r.name:<36} {r.seconds:5.1f}s{extra}")
    if not r.ok and r.detail:
        print("     " + r.detail.replace("\n", "\n     "))
    sys.stdout.flush()


if __name__ == "__main__":
    sys.exit(main())
