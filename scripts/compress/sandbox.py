"""
Sandbox: test proof compressions in isolation.

The atomic unit of the automated pipeline. Takes one declaration,
writes a minimal scratch file, tries a compressed proof, builds it,
returns pass/fail.

Usage:
    from compress.sandbox import try_compress

    result = try_compress(
        declaration="theorem foo (a b : Nat) : a + b = b + a := by rw [Nat.add_comm]",
        imports=["import Mathlib.Data.Nat.Basic"],
        replacement="by omega",
    )
    # result.passed: bool
    # result.original_lines: int
    # result.compressed_lines: int

The sandbox writes a temp file, builds it with lake, and cleans up.
lake build is the judge. The script doesn't need to understand the math.
"""

import re
import subprocess
import tempfile
from pathlib import Path
from dataclasses import dataclass


@dataclass
class CompressResult:
    """Result of a sandbox compression attempt."""
    passed: bool
    original: str
    compressed: str
    tactic: str
    error: str = ""


# Regex to find the proof body after :=
# Matches := <proof> where proof is everything after :=
PROOF_RE = re.compile(
    r':=\s*\n?(.*)',
    re.DOTALL
)

# Regex to find `by <tactic-block>` proof
BY_PROOF_RE = re.compile(
    r':=\s*by\b',
    re.DOTALL
)

PROJECT_ROOT = Path(__file__).parent.parent.parent


def _replace_proof(decl_text: str, new_proof: str) -> str | None:
    """Replace the proof of a declaration with new_proof.

    Returns the modified declaration text, or None if we can't find
    a proof to replace.
    """
    # Find := and replace everything after it
    m = re.search(r':=\s*', decl_text)
    if not m:
        return None
    return decl_text[:m.end()] + new_proof


def _write_scratch(imports: list[str], preamble: str, declaration: str, scratch_path: Path):
    """Write a minimal scratch Lean file."""
    lines = []
    for imp in imports:
        lines.append(imp if imp.startswith("import") else f"import {imp}")
    lines.append("")
    if preamble:
        lines.append(preamble)
        lines.append("")
    lines.append("noncomputable section")
    lines.append("")
    lines.append(declaration)
    lines.append("")
    scratch_path.write_text("\n".join(lines))


def _build_scratch(scratch_path: Path, timeout: int = 120) -> tuple[bool, str]:
    """Build a scratch file with lake. Returns (passed, error_msg)."""
    # Convert file path to module name for lake build
    rel = scratch_path.relative_to(PROJECT_ROOT)
    module = str(rel).replace("/", ".").replace(".lean", "")

    try:
        result = subprocess.run(
            ["lake", "build", module],
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(PROJECT_ROOT),
        )
        passed = result.returncode == 0
        error = result.stderr if not passed else ""
        return passed, error
    except subprocess.TimeoutExpired:
        return False, "timeout"
    except Exception as e:
        return False, str(e)


def try_compress(
    declaration: str,
    imports: list[str],
    replacement: str,
    preamble: str = "",
    scratch_dir: Path | None = None,
) -> CompressResult:
    """Try replacing a declaration's proof with `replacement`.

    Args:
        declaration: full declaration text (theorem foo ... := <proof>)
        imports: list of import lines the declaration needs
        replacement: new proof to try (e.g. "by simp", "by omega")
        preamble: any variable/open/namespace lines needed
        scratch_dir: where to write scratch files (default: Origin/)

    Returns:
        CompressResult with passed/failed and details
    """
    compressed = _replace_proof(declaration, replacement)
    if compressed is None:
        return CompressResult(
            passed=False,
            original=declaration,
            compressed="",
            tactic=replacement,
            error="could not find proof to replace",
        )

    if scratch_dir is None:
        scratch_dir = PROJECT_ROOT / "Origin"

    scratch_path = scratch_dir / "_sandbox_test.lean"

    try:
        _write_scratch(imports, preamble, compressed, scratch_path)
        passed, error = _build_scratch(scratch_path)

        return CompressResult(
            passed=passed,
            original=declaration,
            compressed=compressed,
            tactic=replacement,
            error=error[:500] if error else "",
        )
    finally:
        if scratch_path.exists():
            scratch_path.unlink()


def try_compress_tactics(
    declaration: str,
    imports: list[str],
    preamble: str = "",
    tactics: list[str] | None = None,
) -> CompressResult | None:
    """Try multiple tactics on a declaration, return the first that passes.

    Args:
        declaration: full declaration text
        imports: list of import lines
        preamble: variable/open/namespace lines
        tactics: ordered list of tactics to try (default: standard list)

    Returns:
        CompressResult for the first tactic that passes, or None if all fail
    """
    if tactics is None:
        tactics = [
            "by simp",
            "by omega",
            "by ring",
            "by decide",
            "by aesop",
            "by norm_num",
            "by tauto",
        ]

    for tactic in tactics:
        result = try_compress(declaration, imports, tactic, preamble)
        if result.passed:
            return result

    return None
