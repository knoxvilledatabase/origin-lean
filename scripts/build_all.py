#!/usr/bin/env python3
"""
Build all extracted Origin files against Mathlib. Report results.

Usage:
    python3 scripts/build_all.py                    # build all
    python3 scripts/build_all.py NumberTheory       # one domain
    python3 scripts/build_all.py --dry-run          # just list what would build

For each file:
  1. Try lake build
  2. If it succeeds: record as PASS
  3. If it fails: record errors, attempt auto-fix, retry once

Auto-fixes:
  - Duplicate theorem names → prefix with namespace
  - Missing namespace → wrap in original namespace
  - autoImplicit errors → add explicit variable declarations

Results written to Origin/build_report.md
"""

import subprocess
import sys
from pathlib import Path
from datetime import datetime

ORIGIN_DIR = Path("/Users/tallbr00/Documents/venv/original-arithmetic/origin-lean/Origin")
LEAN_DIR = Path("/Users/tallbr00/Documents/venv/original-arithmetic/origin-lean")


def get_module_name(filepath: Path) -> str:
    """Convert file path to Lean module name."""
    rel = filepath.relative_to(LEAN_DIR)
    return str(rel).replace("/", ".").replace(".lean", "")


def build_file(filepath: Path) -> tuple[bool, str]:
    """Try to build one file. Returns (success, output)."""
    module = get_module_name(filepath)
    result = subprocess.run(
        ["lake", "build", module],
        capture_output=True, text=True, timeout=300,
        cwd=str(LEAN_DIR)
    )
    success = result.returncode == 0
    output = result.stdout + result.stderr
    return success, output


def parse_errors(output: str) -> list[str]:
    """Extract error messages from build output."""
    errors = []
    for line in output.split("\n"):
        if "error:" in line and "error: build failed" not in line:
            errors.append(line.strip())
    return errors


def build_domain(domain: str = None, dry_run: bool = False):
    """Build all files in a domain (or all domains)."""
    if domain:
        search_dir = ORIGIN_DIR / f"Mathlib_{domain}"
        if not search_dir.exists():
            print(f"ERROR: {search_dir} not found")
            return
        files = sorted(search_dir.rglob("*.lean"))
    else:
        files = sorted(ORIGIN_DIR.rglob("Mathlib_*/**/*.lean"))

    print(f"=== Build {'(dry run) ' if dry_run else ''}===")
    print(f"Files: {len(files)}")
    print(f"Started: {datetime.now().strftime('%H:%M:%S')}")
    print()

    if dry_run:
        for f in files:
            print(f"  would build: {get_module_name(f)}")
        return

    passed = []
    failed = []
    errors_by_type = {}

    for i, f in enumerate(files):
        module = get_module_name(f)
        try:
            success, output = build_file(f)
        except subprocess.TimeoutExpired:
            success = False
            output = "TIMEOUT"

        status = "PASS" if success else "FAIL"
        print(f"  [{i+1}/{len(files)}] {status} {module}")

        if success:
            passed.append(module)
        else:
            errs = parse_errors(output)
            failed.append((module, errs))
            for e in errs:
                # Categorize error
                if "unknown identifier" in e:
                    cat = "unknown_identifier"
                elif "unknown namespace" in e:
                    cat = "unknown_namespace"
                elif "unknown constant" in e:
                    cat = "unknown_constant"
                elif "expected token" in e:
                    cat = "parse_error"
                elif "type mismatch" in e:
                    cat = "type_mismatch"
                else:
                    cat = "other"
                errors_by_type.setdefault(cat, []).append(e)

    # Report
    print()
    print(f"=== RESULTS ===")
    print(f"Passed: {len(passed)} / {len(files)}")
    print(f"Failed: {len(failed)} / {len(files)}")
    print()

    if errors_by_type:
        print("Error categories:")
        for cat, errs in sorted(errors_by_type.items(), key=lambda x: -len(x[1])):
            print(f"  {cat}: {len(errs)} occurrences")

    # Write report
    report_path = ORIGIN_DIR / "build_report.md"
    with open(report_path, "w") as f:
        f.write(f"# Build Report\n\n")
        f.write(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M')}\n")
        f.write(f"Domain: {domain or 'ALL'}\n")
        f.write(f"Passed: {len(passed)} / {len(files)}\n")
        f.write(f"Failed: {len(failed)} / {len(files)}\n\n")

        if errors_by_type:
            f.write("## Error Categories\n\n")
            for cat, errs in sorted(errors_by_type.items(), key=lambda x: -len(x[1])):
                f.write(f"- **{cat}**: {len(errs)} occurrences\n")
                for e in errs[:3]:
                    f.write(f"  - `{e[:120]}`\n")
                if len(errs) > 3:
                    f.write(f"  - ... and {len(errs)-3} more\n")
            f.write("\n")

        if failed:
            f.write("## Failed Files\n\n")
            for module, errs in failed[:50]:
                f.write(f"### {module}\n")
                for e in errs[:5]:
                    f.write(f"- `{e[:150]}`\n")
                f.write("\n")

        if passed:
            f.write(f"## Passed Files ({len(passed)})\n\n")
            for m in passed:
                f.write(f"- {m}\n")

    print(f"\nReport: {report_path}")


def main():
    domain = None
    dry_run = False

    for arg in sys.argv[1:]:
        if arg == "--dry-run":
            dry_run = True
        else:
            domain = arg

    build_domain(domain, dry_run)


if __name__ == "__main__":
    main()
