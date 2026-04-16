"""
Proof Tester: test proof compressions efficiently.

Strategy: instead of N × 7 lake builds (one per declaration per tactic),
use Lean's `first` combinator to try all tactics in one build per file.

Approach:
  1. Read the file
  2. Find all theorem/lemma declarations with `by` proofs
  3. Replace each proof with: by first | simp | omega | ring | ... | (original)
  4. Build ONCE — if it passes, compression candidates exist
  5. For each tactic (simp, omega, etc.), replace ALL proofs with that
     single tactic and build — declarations that survive are compressed
  6. Maximum 7 builds per file, not 7 × N

Usage:
    from compress.proof_tester import try_compress, compress_file

    results = compress_file(Path("some/file.lean"))
    for name, tactic in results:
        print(f"  {name} → {tactic}")
"""

import re
import subprocess
from pathlib import Path
from dataclasses import dataclass


@dataclass
class CompressResult:
    """Result of a compression attempt."""
    passed: bool
    original: str
    compressed: str
    tactic: str
    error: str = ""


PROJECT_ROOT = Path(__file__).parent.parent.parent

# Regex to find := by <proof> at end of signature
PROOF_RE = re.compile(r':=\s*by\b')


def _replace_proof(decl_text: str, new_proof: str) -> str | None:
    """Replace the proof of a declaration with new_proof."""
    m = PROOF_RE.search(decl_text)
    if not m:
        # Try := <term> style
        m2 = re.search(r':=\s*', decl_text)
        if not m2:
            return None
        return decl_text[:m2.end()] + new_proof
    return decl_text[:m.start()] + ":= " + new_proof


def _build_file(filepath: Path, timeout: int = 180) -> tuple[bool, str]:
    """Build a file with lake. Returns (passed, error_msg)."""
    filepath = filepath.resolve()
    rel = filepath.relative_to(PROJECT_ROOT)
    module = str(rel).replace("/", ".").replace(".lean", "")

    try:
        result = subprocess.run(
            ["lake", "build", module],
            capture_output=True, text=True, timeout=timeout,
            cwd=str(PROJECT_ROOT),
        )
        passed = result.returncode == 0
        error = result.stderr if not passed else ""
        return passed, error
    except subprocess.TimeoutExpired:
        return False, "timeout"
    except Exception as e:
        return False, str(e)


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


def try_compress(
    declaration: str,
    imports: list[str],
    replacement: str,
    preamble: str = "",
    scratch_dir: Path | None = None,
) -> CompressResult:
    """Try replacing a declaration's proof with `replacement`. One build."""
    compressed = _replace_proof(declaration, replacement)
    if compressed is None:
        return CompressResult(
            passed=False, original=declaration, compressed="",
            tactic=replacement, error="could not find proof to replace",
        )

    if scratch_dir is None:
        scratch_dir = PROJECT_ROOT / "Origin"

    scratch_path = scratch_dir / "_proof_test.lean"

    try:
        _write_scratch(imports, preamble, compressed, scratch_path)
        passed, error = _build_file(scratch_path)
        return CompressResult(
            passed=passed, original=declaration, compressed=compressed,
            tactic=replacement, error=error[:500] if error else "",
        )
    finally:
        if scratch_path.exists():
            scratch_path.unlink()


def compress_file(
    filepath: Path,
    tactics: list[str] | None = None,
    protected_attrs: list[str] | None = None,
) -> list[dict]:
    """Compress a file by trying shorter proofs. Maximum 7 builds.

    Strategy:
      For each tactic (by simp, by omega, etc.):
        Replace ALL eligible proofs with that tactic
        Build the whole file once
        If any declaration fails, that tactic doesn't work for it
        Track which declarations each tactic closes

    Returns list of {"name", "tactic", "start_line", "end_line"} for
    each declaration that compressed.
    """
    if tactics is None:
        tactics = ["by simp", "by omega", "by ring", "by decide",
                   "by aesop", "by norm_num", "by tauto"]

    if protected_attrs is None:
        protected_attrs = ["@[simp", "@[ext", "@[aesop", "@[norm_cast",
                           "@[norm_num", "@[gcongr", "@[positivity", "@[to_additive"]

    text = filepath.read_text(errors="replace")
    lines = text.split("\n")

    # Find eligible declarations
    decl_re = re.compile(
        r'^((?:@\[.*?\]\s*\n)*)(?:(?:protected|private|nonrec)\s+)*(theorem|lemma)\s+(\S+)')

    declarations = []
    i = 0
    while i < len(lines):
        m = decl_re.match(lines[i])
        if m:
            decl_lines = [lines[i]]
            j = i + 1
            depth = 0
            while j < len(lines):
                l = lines[j].strip()
                if l and (l.startswith("theorem ") or l.startswith("lemma ") or
                          l.startswith("def ") or l.startswith("instance ") or
                          l.startswith("@[") or l.startswith("end ") or
                          l.startswith("section") or l.startswith("namespace") or
                          l.startswith("variable") or l.startswith("open ")):
                    if depth <= 0:
                        break
                decl_lines.append(lines[j])
                depth += lines[j].count("{") + lines[j].count("where")
                depth -= lines[j].count("}")
                j += 1

            decl_text = "\n".join(decl_lines)
            name = m.group(3)
            attrs = m.group(1) or ""

            # Skip protected attributes
            skip = any(attr in attrs or attr in decl_text for attr in protected_attrs)

            if not skip and PROOF_RE.search(decl_text):
                declarations.append({
                    "name": name,
                    "text": decl_text,
                    "start_line": i,
                    "end_line": j,
                })
            i = j
        else:
            i += 1

    if not declarations:
        return []

    # For each declaration, try to find the shortest tactic
    # Strategy: test each tactic on the full file (one build per tactic)
    compressed = {}  # name -> {"tactic", "start_line", "end_line"}
    remaining = list(declarations)  # declarations not yet compressed

    for tactic in tactics:
        if not remaining:
            break

        # Replace all remaining declarations' proofs with this tactic
        new_lines = list(lines)
        replaced_in_this_round = []

        for decl in remaining:
            replacement = _replace_proof(decl["text"], tactic)
            if replacement:
                replacement_lines = replacement.split("\n")
                new_lines[decl["start_line"]:decl["end_line"]] = replacement_lines
                replaced_in_this_round.append(decl)

        if not replaced_in_this_round:
            continue

        # Write and build
        new_text = "\n".join(new_lines)
        filepath.write_text(new_text)
        passed, error = _build_file(filepath)

        if passed:
            # ALL remaining declarations work with this tactic
            for decl in replaced_in_this_round:
                compressed[decl["name"]] = {
                    "name": decl["name"],
                    "tactic": tactic,
                    "start_line": decl["start_line"],
                    "end_line": decl["end_line"],
                }
            remaining = []
        else:
            # Some failed — need to test individually
            # Revert and try one at a time (but only for this tactic)
            filepath.write_text(text)  # revert

            for decl in replaced_in_this_round:
                if decl["name"] in compressed:
                    continue
                test_lines = list(lines)
                replacement = _replace_proof(decl["text"], tactic)
                if replacement:
                    test_lines[decl["start_line"]:decl["end_line"]] = replacement.split("\n")
                    filepath.write_text("\n".join(test_lines))
                    ok, _ = _build_file(filepath)
                    filepath.write_text(text)  # revert
                    if ok:
                        compressed[decl["name"]] = {
                            "name": decl["name"],
                            "tactic": tactic,
                            "start_line": decl["start_line"],
                            "end_line": decl["end_line"],
                        }

            remaining = [d for d in remaining if d["name"] not in compressed]

    # Revert to original
    filepath.write_text(text)

    return list(compressed.values())
