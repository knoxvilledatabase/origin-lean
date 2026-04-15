#!/usr/bin/env python3
"""
Origin: Mathlib → Origin conversion tool.

Usage:
    python scripts/origin.py classify NumberTheory          # classify one domain
    python scripts/origin.py classify --all                 # classify all domains
    python scripts/origin.py extract Mathlib/Path/File.lean # extract one file
    python scripts/origin.py extract --domain NumberTheory  # extract whole domain
    python scripts/origin.py fruit --all 10                 # top 10 by density

One tool. Replaces triage.sh, fruit.sh, classify.sh, and does extraction.
"""

import os
import re
import sys
from pathlib import Path
from dataclasses import dataclass, field
from typing import Optional

MATHLIB_DIR = Path("/Users/tallbr00/Documents/venv/original-arithmetic/origin-mathlib/Mathlib")
ORIGIN_DIR = Path("/Users/tallbr00/Documents/venv/original-arithmetic/origin-lean/Origin")

ZERO_PATTERNS = [
    r"≠\s*0",
    r"NeZero",
    r"ne_zero",
    r"GroupWithZero",
    r"\.ne'",
    r"inv_ne_zero",
    r"cast_ne_zero",
    r"succ_ne_zero",
    r"pos_of_ne_zero",
]
ZERO_RE = re.compile("|".join(ZERO_PATTERNS))

TRIVIAL_PROOF = re.compile(
    r":=\s*(rfl|h\b|by\s+simp\s*$|by\s+rfl|by\s+exact\s+\w+\s*$|Iff\.rfl|\(rfl\s*:\))",
)

# ---------------------------------------------------------------------------
# Declaration parser
# ---------------------------------------------------------------------------

@dataclass
class Decl:
    kind: str          # "theorem", "lemma", "def", "structure", "class", "instance", "abbrev", "inductive"
    name: str
    signature: str     # full signature (may be multi-line)
    body: str          # proof/definition body
    start_line: int
    end_line: int
    is_simp: bool = False
    has_zero_mgmt: bool = False
    is_trivial: bool = False
    is_instance: bool = False
    classification: str = ""  # "genuine", "dissolves", "instance", "simp", "trivial"

    @property
    def is_genuine(self):
        return self.classification == "genuine"


def parse_declarations(text: str) -> list[Decl]:
    """Parse a Lean file into declarations."""
    lines = text.split("\n")
    decls = []
    i = 0

    # Track @[simp] on previous non-blank line
    pending_simp = False

    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        # Track @[simp]
        if stripped.startswith("@[simp"):
            pending_simp = True
            i += 1
            continue

        # Detect declaration start
        decl_match = re.match(
            r"^(protected\s+)?(noncomputable\s+)?"
            r"(theorem|lemma|def|structure|class|instance|abbrev|inductive)\s+(\S+)",
            stripped
        )
        if not decl_match:
            if stripped and not stripped.startswith("--") and not stripped.startswith("/-"):
                pending_simp = False
            i += 1
            continue

        kind = decl_match.group(3)
        name = decl_match.group(4)
        start_line = i + 1

        # Collect full declaration (signature + body)
        decl_lines = [line]
        i += 1

        # For structures/classes/inductives: collect until unindented line or end
        if kind in ("structure", "class", "inductive"):
            while i < len(lines):
                if lines[i].strip() and not lines[i][0].isspace() and not lines[i].strip().startswith("|"):
                    break
                decl_lines.append(lines[i])
                i += 1
        else:
            # For theorems/defs: collect indented continuation + proof body
            # Look for := or where, then collect proof body
            in_body = ":=" in line or line.strip().endswith("where")
            while i < len(lines):
                cur = lines[i]
                cur_stripped = cur.strip()

                # Blank line after unindented content = end
                if not cur_stripped:
                    decl_lines.append(cur)
                    i += 1
                    # Check if next line is still indented (continuation)
                    if i < len(lines) and lines[i] and lines[i][0].isspace():
                        continue
                    break

                # New declaration = end
                if not cur[0].isspace() and cur_stripped and not cur_stripped.startswith("|"):
                    break

                decl_lines.append(cur)
                i += 1

        full_text = "\n".join(decl_lines)
        # Split into signature and body at :=
        if ":=" in full_text:
            sig_end = full_text.index(":=")
            signature = full_text[:sig_end].strip()
            body = full_text[sig_end:].strip()
        else:
            signature = full_text.strip()
            body = ""

        decl = Decl(
            kind=kind,
            name=name,
            signature=signature,
            body=body,
            start_line=start_line,
            end_line=i,
            is_simp=pending_simp,
            has_zero_mgmt=bool(ZERO_RE.search(signature)),
            is_trivial=bool(TRIVIAL_PROOF.search(full_text)),
            is_instance=(kind == "instance"),
        )

        # Classify
        if decl.is_instance:
            decl.classification = "instance"
        elif decl.has_zero_mgmt:
            decl.classification = "dissolves"
        elif decl.is_simp and decl.is_trivial:
            decl.classification = "simp"
        elif decl.is_trivial and kind in ("theorem", "lemma"):
            decl.classification = "trivial"
        else:
            decl.classification = "genuine"

        decls.append(decl)
        pending_simp = False

    return decls


# ---------------------------------------------------------------------------
# File analysis
# ---------------------------------------------------------------------------

@dataclass
class FileAnalysis:
    path: str
    lines: int
    decls: list[Decl] = field(default_factory=list)
    zero_hits: int = 0

    @property
    def genuine(self): return sum(1 for d in self.decls if d.classification == "genuine")
    @property
    def dissolves(self): return sum(1 for d in self.decls if d.classification == "dissolves")
    @property
    def instances(self): return sum(1 for d in self.decls if d.classification == "instance")
    @property
    def simps(self): return sum(1 for d in self.decls if d.classification == "simp")
    @property
    def trivial(self): return sum(1 for d in self.decls if d.classification == "trivial")
    @property
    def total(self): return len(self.decls)
    @property
    def density(self): return self.zero_hits / max(self.lines, 1)


def analyze_file(filepath: Path, domain: str = "") -> FileAnalysis:
    text = filepath.read_text(errors="replace")
    lines = text.count("\n") + 1
    relpath = str(filepath).split(f"Mathlib/{domain}/")[-1] if domain else str(filepath)

    decls = parse_declarations(text)
    zero_hits = len(ZERO_RE.findall(text))

    return FileAnalysis(path=relpath, lines=lines, decls=decls, zero_hits=zero_hits)


# ---------------------------------------------------------------------------
# Commands
# ---------------------------------------------------------------------------

def cmd_classify(domain: str):
    """Classify every declaration in a domain."""
    src = MATHLIB_DIR / domain
    if not src.is_dir():
        print(f"ERROR: {src} not found", file=sys.stderr)
        return

    files = sorted(src.rglob("*.lean"))
    analyses = [analyze_file(f, domain) for f in files]

    # Sort by genuine count descending
    analyses.sort(key=lambda a: a.genuine, reverse=True)

    print(f"=== {domain}: Declaration-Level Classification ===")
    print()
    print(f"{'GENUINE':>7} | {'DISSOLVE':>8} | {'INST':>4} | {'SIMP':>4} | {'TRIV':>4} | {'TOTAL':>5} | {'LINES':>5} | PATH")
    print(f"{'-------':>7}-+-{'--------':>8}-+-{'----':>4}-+-{'----':>4}-+-{'----':>4}-+-{'-----':>5}-+-{'-----':>5}-+------")

    t = FileAnalysis(path="TOTAL", lines=0)
    f_genuine = f_dissolves_fully = f_empty = 0

    for a in analyses:
        print(f"{a.genuine:>7} | {a.dissolves:>8} | {a.instances:>4} | {a.simps:>4} | {a.trivial:>4} | {a.total:>5} | {a.lines:>5} | {a.path}")
        t.lines += a.lines
        t.zero_hits += a.zero_hits
        if a.total == 0:
            f_empty += 1
        elif a.genuine == 0:
            f_dissolves_fully += 1
        else:
            f_genuine += 1

    total_decls = sum(a.total for a in analyses)
    total_genuine = sum(a.genuine for a in analyses)
    total_dissolves = sum(a.dissolves for a in analyses)
    total_instances = sum(a.instances for a in analyses)
    total_simps = sum(a.simps for a in analyses)
    total_trivial = sum(a.trivial for a in analyses)

    print()
    print(f"--- SUMMARY: {domain} ---")
    print(f"Files:        {len(files)} total, {f_empty} empty, {f_dissolves_fully} dissolve fully, {f_genuine} have genuine content")
    print(f"Declarations: {total_decls} total")
    print(f"  Dissolves:  {total_dissolves} (≠ 0 / NeZero in signature)")
    print(f"  Instances:  {total_instances} (typeclass infrastructure)")
    print(f"  Simp:       {total_simps} (@[simp] + trivial)")
    print(f"  Trivial:    {total_trivial} (rfl / by simp / exact h)")
    print(f"  GENUINE:    {total_genuine} ← THIS IS WHAT TO WRITE IN ORIGIN")
    print(f"Lines:        {t.lines}")


def cmd_classify_all():
    """Summary across all domains."""
    print("=== ALL DOMAINS: Genuine Content ===")
    print()
    print(f"{'DOMAIN':<22} | {'GENUINE':>7} | {'DISSOLVE':>8} | {'INFRA':>5} | {'TOTAL':>5} | {'FILES':>5}")
    print(f"{'':-<22}-+-{'':-<7}-+-{'':-<8}-+-{'':-<5}-+-{'':-<5}-+-{'':-<5}")

    rows = []
    for d in sorted(MATHLIB_DIR.iterdir()):
        if not d.is_dir():
            continue
        files = list(d.rglob("*.lean"))
        if len(files) < 3:
            continue

        total_genuine = 0
        total_dissolves = 0
        total_decls = 0

        for f in files:
            a = analyze_file(f, d.name)
            total_genuine += a.genuine
            total_dissolves += a.dissolves
            total_decls += a.total

        infra = total_decls - total_genuine
        rows.append((d.name, total_genuine, total_dissolves, infra, total_decls, len(files)))

    rows.sort(key=lambda r: r[1], reverse=True)
    for name, genuine, dissolves, infra, total, files in rows:
        print(f"{name:<22} | {genuine:>7} | {dissolves:>8} | {infra:>5} | {total:>5} | {files:>5}")

    print()
    print(f"Grand total GENUINE: {sum(r[1] for r in rows)}")
    print(f"Grand total declarations: {sum(r[4] for r in rows)}")


def cmd_fruit(domain: Optional[str], top_n: int):
    """Rank files by dissolution density."""
    if domain:
        src = MATHLIB_DIR / domain
        files = sorted(src.rglob("*.lean"))
    else:
        files = sorted(MATHLIB_DIR.rglob("*.lean"))

    results = []
    for f in files:
        text = f.read_text(errors="replace")
        lines = text.count("\n") + 1
        if lines < 30:
            continue
        hits = len(ZERO_RE.findall(text))
        if hits == 0:
            continue
        thms = len(re.findall(r"^(protected\s+)?(theorem|lemma|def)\s+", text, re.MULTILINE))
        if thms == 0:
            continue
        density = hits / lines
        relpath = str(f).split("Mathlib/")[-1]
        results.append((density, hits, lines, thms, relpath))

    results.sort(reverse=True)

    title = domain or "ALL DOMAINS"
    print(f"=== {title}: Top {top_n} by dissolution density ===")
    print()
    print(f"{'DENSITY':>8} | {'HITS':>4} | {'LINES':>5} | {'THMS':>4} | PATH")
    print(f"{'--------':>8}-+-{'----':>4}-+-{'-----':>5}-+-{'----':>4}-+-----")

    for density, hits, lines, thms, path in results[:top_n]:
        print(f"{density:>7.1%} | {hits:>4} | {lines:>5} | {thms:>4} | {path}")


def cmd_extract(filepath: Path):
    """Extract genuine content from a Mathlib file."""
    if not filepath.exists():
        # Try prepending MATHLIB_DIR
        filepath = MATHLIB_DIR / filepath
    if not filepath.exists():
        print(f"ERROR: {filepath} not found", file=sys.stderr)
        return

    text = filepath.read_text(errors="replace")
    relpath = str(filepath).split("Mathlib/")[-1]
    domain = relpath.rsplit("/", 1)[0].replace("/", ".")

    decls = parse_declarations(text)
    genuine = [d for d in decls if d.is_genuine]

    print(f"/-")
    print(f"Generated by origin.py from {relpath}")
    print(f"Genuine declarations: {len(genuine)} of {len(decls)} total")
    print(f"Dissolved: {sum(1 for d in decls if d.classification == 'dissolves')}")
    print(f"Infrastructure skipped: {sum(1 for d in decls if d.classification in ('instance', 'simp', 'trivial'))}")
    print(f"-/")
    print(f"import Origin.Core")
    print()
    print(f"/-! # {domain} on Option α -/")
    print()
    print(f"universe u")
    print(f"variable {{α : Type u}}")
    print()

    for d in genuine:
        # Print the full declaration
        full = d.signature
        if d.body:
            full += " " + d.body
        # Strip NeZero from signature
        full = re.sub(r"\[NeZero [^\]]*\]\s*", "", full)
        print(full)
        print()


def cmd_extract_domain(domain: str):
    """Extract all genuine content from a domain."""
    src = MATHLIB_DIR / domain
    if not src.is_dir():
        print(f"ERROR: {src} not found", file=sys.stderr)
        return

    out_dir = ORIGIN_DIR / f"Mathlib_{domain}"
    out_dir.mkdir(parents=True, exist_ok=True)

    files = sorted(src.rglob("*.lean"))
    count = 0

    for f in files:
        a = analyze_file(f, domain)
        if a.genuine == 0:
            continue

        # Create output path
        relpath = str(f).split(f"Mathlib/{domain}/")[-1]
        outfile = out_dir / relpath
        outfile.parent.mkdir(parents=True, exist_ok=True)

        # Redirect stdout to file
        import io
        old_stdout = sys.stdout
        sys.stdout = io.StringIO()
        cmd_extract(f)
        content = sys.stdout.getvalue()
        sys.stdout = old_stdout

        outfile.write_text(content)
        count += 1

    print(f"Extracted {count} files to {out_dir}/")
    print(f"Next: lake build and fix what breaks.")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return

    cmd = sys.argv[1]

    if cmd == "classify":
        if len(sys.argv) > 2 and sys.argv[2] == "--all":
            cmd_classify_all()
        elif len(sys.argv) > 2:
            cmd_classify(sys.argv[2])
        else:
            print("Usage: origin.py classify <DOMAIN> | --all")

    elif cmd == "fruit":
        top_n = 20
        domain = None
        for arg in sys.argv[2:]:
            if arg == "--all":
                domain = None
            elif arg.isdigit():
                top_n = int(arg)
            else:
                domain = arg
        cmd_fruit(domain, top_n)

    elif cmd == "extract":
        if len(sys.argv) > 2 and sys.argv[2] == "--domain":
            cmd_extract_domain(sys.argv[3])
        elif len(sys.argv) > 2:
            cmd_extract(Path(sys.argv[2]))
        else:
            print("Usage: origin.py extract <file.lean> | --domain <DOMAIN>")

    else:
        print(f"Unknown command: {cmd}")
        print(__doc__)


if __name__ == "__main__":
    main()
