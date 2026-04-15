#!/usr/bin/env python3
"""
Origin: Mathlib → Origin conversion tool.

Usage:
    python3 scripts/origin.py classify NumberTheory
    python3 scripts/origin.py classify --all
    python3 scripts/origin.py extract NumberTheory/Harmonic/Int.lean
    python3 scripts/origin.py extract --domain NumberTheory
    python3 scripts/origin.py fruit --all 10

Smart extraction: preserves namespaces, variables, and open statements.
Strips zero-management by name AND by signature. Skips files that are
entirely infrastructure. Generates drafts that are as close to building
as a script can get. Claude fixes only what lake build says is broken.
"""

import os
import re
import sys
from pathlib import Path
from dataclasses import dataclass, field
from typing import Optional

MATHLIB_DIR = Path("/Users/tallbr00/Documents/venv/original-arithmetic/origin-mathlib/Mathlib")
ORIGIN_DIR = Path("/Users/tallbr00/Documents/venv/original-arithmetic/origin-lean/Origin")

# --self flag: audit Origin instead of Mathlib
SELF_MODE = False
def get_source_dir():
    return ORIGIN_DIR if SELF_MODE else MATHLIB_DIR

# ---------------------------------------------------------------------------
# Zero-management patterns
# ---------------------------------------------------------------------------

# Signature patterns: hypotheses that dissolve
ZERO_SIG = re.compile(r"≠\s*0|NeZero|ne_zero|GroupWithZero")

# Threading patterns: internal proof lines that simplify
ZERO_THREAD = re.compile(r"\.ne'|inv_ne_zero|cast_ne_zero|succ_ne_zero|pos_of_ne_zero")

# All zero-management
ZERO_ALL = re.compile(r"≠\s*0|NeZero|ne_zero|GroupWithZero|\.ne'|inv_ne_zero|cast_ne_zero|succ_ne_zero|pos_of_ne_zero")

# Declaration names that ARE zero-management infrastructure
INFRA_NAMES = re.compile(
    r"ne_zero|NeZero|neZero|ne_one|"
    r"GroupWithZero|groupWithZero|"
    r"NoZeroDivisors|noZeroDivisors|"
    r"NoZeroSMulDivisors|"
    r"MulZeroClass|mulZeroClass|"
    r"IsUnit.*zero|isUnit.*zero|"
    r"not_isUnit_zero|"
    r"zero_mul|mul_zero|zero_div|div_zero|"
    r"inv_zero|zero_inv|"
    r"WithZero|withZero|WithBot|withBot|WithTop|withTop|"
    r"ZeroHom|zeroHom|"
    r"CharZero|charZero"
)

# Trivial proof patterns
TRIVIAL_RE = re.compile(r":=\s*(rfl|h\b|by\s+simp\s*$|by\s+rfl|by\s+exact\s+\w+\s*$|Iff\.rfl)")

# File-level: files that are ENTIRELY about zero infrastructure
INFRA_FILE_PATTERNS = [
    "GroupWithZero", "NeZero", "NoZeroDivisors", "NoZeroSMul",
    "MulZeroClass", "WithZero", "WithBot", "WithTop",
    "ZeroHom", "CharZero", "IsUnit",
]

# ---------------------------------------------------------------------------
# Smart parser
# ---------------------------------------------------------------------------

@dataclass
class Block:
    """A block of text: could be a declaration, namespace, comment, etc."""
    kind: str  # "decl", "namespace", "variable", "open", "comment", "import", "other"
    name: str
    text: str
    classification: str = ""  # "genuine", "dissolves", "instance", "infra_name", "simp_trivial", "skip"


def is_infra_file(filepath: Path) -> bool:
    """Is this file entirely about zero-management infrastructure?"""
    name = filepath.stem
    for pat in INFRA_FILE_PATTERNS:
        if pat in str(filepath):
            return True
    return False


def classify_decl_name(name: str) -> bool:
    """Is this declaration name itself zero-management infrastructure?"""
    return bool(INFRA_NAMES.search(name))


def parse_file_smart(text: str) -> list[Block]:
    """Parse a Lean file into blocks, preserving structure."""
    lines = text.split("\n")
    blocks = []
    i = 0

    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        # Empty lines
        if not stripped:
            i += 1
            continue

        # Comments (block)
        if stripped.startswith("/-"):
            comment_lines = [line]
            if "-/" not in stripped[2:]:
                i += 1
                while i < len(lines) and "-/" not in lines[i]:
                    comment_lines.append(lines[i])
                    i += 1
                if i < len(lines):
                    comment_lines.append(lines[i])
            blocks.append(Block("comment", "", "\n".join(comment_lines)))
            i += 1
            continue

        # Line comments
        if stripped.startswith("--"):
            i += 1
            continue

        # Imports
        if stripped.startswith("import ") or stripped.startswith("public import "):
            blocks.append(Block("import", "", line))
            i += 1
            continue

        # Module/section markers
        if stripped.startswith("module") or stripped.startswith("@[expose]") or stripped.startswith("deprecated_module"):
            i += 1
            continue

        if stripped.startswith("public section") or stripped == "section":
            i += 1
            continue

        # Namespace
        if stripped.startswith("namespace "):
            ns = stripped.split("namespace ", 1)[1].strip()
            blocks.append(Block("namespace", ns, line))
            i += 1
            continue

        if stripped.startswith("end "):
            ns = stripped.split("end ", 1)[1].strip()
            blocks.append(Block("end_namespace", ns, f"end {ns}"))
            i += 1
            continue

        # Open
        if stripped.startswith("open "):
            blocks.append(Block("open", "", line))
            i += 1
            continue

        # Variable
        if stripped.startswith("variable"):
            var_lines = [line]
            i += 1
            # Multi-line variable
            while i < len(lines) and lines[i].strip() and lines[i][0].isspace():
                var_lines.append(lines[i])
                i += 1
            blocks.append(Block("variable", "", "\n".join(var_lines)))
            continue

        # Attribute line (collect and attach to next decl)
        if stripped.startswith("@["):
            attr_line = line
            i += 1
            # The next non-empty line should be the declaration
            while i < len(lines) and not lines[i].strip():
                i += 1
            if i < len(lines):
                # Prepend attribute to declaration line
                lines[i] = attr_line + "\n" + lines[i]
            continue

        # Declaration
        decl_match = re.match(
            r"^(.*?)?(protected\s+)?(noncomputable\s+)?"
            r"(theorem|lemma|def|structure|class|instance|abbrev|inductive)\s+(\S+)",
            stripped
        )
        if decl_match:
            kind = decl_match.group(4)
            name = decl_match.group(5)

            # Collect full declaration
            decl_lines = [line]
            i += 1
            while i < len(lines):
                cur = lines[i]
                cur_stripped = cur.strip()

                if not cur_stripped:
                    decl_lines.append(cur)
                    i += 1
                    if i < len(lines) and lines[i] and lines[i][0].isspace():
                        continue
                    break

                if not cur[0].isspace() and cur_stripped and not cur_stripped.startswith("|") and not cur_stripped.startswith("where"):
                    break

                decl_lines.append(cur)
                i += 1

            full_text = "\n".join(decl_lines).rstrip()
            sig_part = full_text.split(":=")[0] if ":=" in full_text else full_text

            # Classify
            if kind == "instance":
                cls = "instance"
            elif classify_decl_name(name):
                cls = "infra_name"
            elif ZERO_SIG.search(sig_part):
                cls = "dissolves"
            elif TRIVIAL_RE.search(full_text) and kind in ("theorem", "lemma"):
                is_simp = "@[simp]" in full_text
                cls = "simp_trivial" if is_simp else "trivial"
            else:
                cls = "genuine"

            blocks.append(Block("decl", name, full_text, cls))
            continue

        # Anything else
        blocks.append(Block("other", "", line))
        i += 1

    return blocks


# ---------------------------------------------------------------------------
# Smart extraction
# ---------------------------------------------------------------------------

def extract_smart(filepath: Path) -> tuple[str, dict]:
    """Extract genuine content, preserving file structure."""
    text = filepath.read_text(errors="replace")
    relpath = str(filepath).split("Mathlib/")[-1] if "Mathlib/" in str(filepath) else str(filepath)

    # Check if entire file is infrastructure
    if is_infra_file(filepath):
        stats = {"total": 0, "genuine": 0, "dissolved": 0, "infra": 0, "skipped_file": True}
        return f"-- {relpath}: entire file is zero-management infrastructure. Dissolves completely.\n", stats

    blocks = parse_file_smart(text)

    stats = {"total": 0, "genuine": 0, "dissolved": 0, "infra": 0, "skipped_file": False}
    output_parts = []

    # Header
    genuine_count = sum(1 for b in blocks if b.kind == "decl" and b.classification == "genuine")
    total_count = sum(1 for b in blocks if b.kind == "decl")
    dissolved = sum(1 for b in blocks if b.kind == "decl" and b.classification in ("dissolves", "infra_name"))
    infra = sum(1 for b in blocks if b.kind == "decl" and b.classification in ("instance", "simp_trivial", "trivial"))

    stats["total"] = total_count
    stats["genuine"] = genuine_count
    stats["dissolved"] = dissolved
    stats["infra"] = infra

    if genuine_count == 0:
        return f"-- {relpath}: 0 genuine declarations. {dissolved} dissolved, {infra} infrastructure.\n", stats

    # Collect original imports (we keep them — the file needs Mathlib's types)
    original_imports = [b.text for b in blocks if b.kind == "import"]

    # Build output preserving structure
    for b in blocks:
        if b.kind == "comment":
            # Keep the module docstring
            if "/-!" in b.text:
                output_parts.append(b.text)
            continue

        if b.kind == "import":
            continue  # We'll add our own (original + Origin.Core)

        if b.kind in ("namespace", "end_namespace"):
            output_parts.append(b.text)
            continue

        if b.kind == "open":
            output_parts.append(b.text)
            continue

        if b.kind == "variable":
            output_parts.append(b.text)
            continue

        if b.kind == "decl":
            if b.classification == "genuine":
                output_parts.append(b.text)
            elif b.classification in ("dissolves", "infra_name"):
                output_parts.append(f"-- DISSOLVED: {b.name}")
            elif b.classification == "instance":
                output_parts.append(f"-- INSTANCE (free from Core): {b.name}")
            # simp_trivial and trivial: skip silently

        if b.kind == "other":
            output_parts.append(b.text)

    # Assemble
    # Keep original Mathlib imports (the file needs Mathlib's types)
    # Add Origin.Core for the foundation
    import_block = "import Origin.Core\n"
    for imp in original_imports:
        # Convert 'public import' to 'import'
        clean = imp.strip().replace("public import ", "import ")
        import_block += clean + "\n"

    header = f"""/-
Extracted from {relpath}
Genuine: {genuine_count} of {total_count} | Dissolved: {dissolved} | Infrastructure: {infra}
-/
{import_block}"""

    body = "\n\n".join(p for p in output_parts if p.strip())
    return header + "\n" + body + "\n", stats


# ---------------------------------------------------------------------------
# Commands
# ---------------------------------------------------------------------------

def cmd_classify(domain: str):
    """Classify every declaration in a domain."""
    src = get_source_dir() / domain if not SELF_MODE else get_source_dir()
    if SELF_MODE and domain != "--all":
        # In self mode, domain is a subdirectory of Origin/
        src = get_source_dir() / domain
    if not src.is_dir():
        print(f"ERROR: {src} not found", file=sys.stderr)
        return

    mode = "ORIGIN (self-audit)" if SELF_MODE else "MATHLIB"
    files = sorted(src.rglob("*.lean"))
    rows = []

    for f in files:
        text = f.read_text(errors="replace")
        blocks = parse_file_smart(text)
        decls = [b for b in blocks if b.kind == "decl"]

        genuine = sum(1 for d in decls if d.classification == "genuine")
        dissolved = sum(1 for d in decls if d.classification in ("dissolves", "infra_name"))
        instances = sum(1 for d in decls if d.classification == "instance")
        trivial = sum(1 for d in decls if d.classification in ("simp_trivial", "trivial"))
        total = len(decls)
        lines = text.count("\n") + 1
        relpath = str(f).split(f"Mathlib/{domain}/")[-1]

        rows.append((genuine, dissolved, instances, trivial, total, lines, relpath))

    rows.sort(reverse=True)

    print(f"=== {domain} [{mode}]: Declaration-Level Classification ===\n")
    print(f"{'GEN':>4} | {'DISS':>4} | {'INST':>4} | {'TRIV':>4} | {'TOT':>4} | {'LINES':>5} | PATH")
    print(f"{'----':>4}-+-{'----':>4}-+-{'----':>4}-+-{'----':>4}-+-{'----':>4}-+-{'-----':>5}-+-----")

    for g, d, inst, t, tot, lines, path in rows:
        print(f"{g:>4} | {d:>4} | {inst:>4} | {t:>4} | {tot:>4} | {lines:>5} | {path}")

    t_gen = sum(r[0] for r in rows)
    t_dis = sum(r[1] for r in rows)
    t_inst = sum(r[2] for r in rows)
    t_triv = sum(r[3] for r in rows)
    t_tot = sum(r[4] for r in rows)
    t_lines = sum(r[5] for r in rows)
    f_genuine = sum(1 for r in rows if r[0] > 0)
    f_empty = sum(1 for r in rows if r[4] == 0)
    f_dissolves = sum(1 for r in rows if r[0] == 0 and r[4] > 0)

    print(f"\n--- SUMMARY: {domain} ---")
    print(f"Files:        {len(rows)} total, {f_empty} empty, {f_dissolves} dissolve fully, {f_genuine} have genuine content")
    print(f"Declarations: {t_tot} total")
    print(f"  Genuine:    {t_gen}  ← WHAT TO WRITE")
    print(f"  Dissolved:  {t_dis}  (≠ 0 / NeZero / infra names)")
    print(f"  Instances:  {t_inst}")
    print(f"  Trivial:    {t_triv}")
    print(f"Lines:        {t_lines}")


def cmd_classify_all():
    """Summary across all domains."""
    base = get_source_dir()
    mode = "ORIGIN (self-audit)" if SELF_MODE else "MATHLIB"
    print(f"=== ALL DOMAINS [{mode}] ===\n")
    print(f"{'DOMAIN':<22} | {'GEN':>6} | {'DISS':>5} | {'INFRA':>5} | {'TOTAL':>5} | {'FILES':>5}")
    print(f"{'':-<22}-+-{'':-<6}-+-{'':-<5}-+-{'':-<5}-+-{'':-<5}-+-{'':-<5}")

    rows = []
    for d in sorted(base.iterdir()):
        if not d.is_dir():
            continue
        files = list(d.rglob("*.lean"))
        if len(files) < 3:
            continue

        t_gen = t_dis = t_tot = 0
        for f in files:
            try:
                text = f.read_text(errors="replace")
            except:
                continue
            blocks = parse_file_smart(text)
            decls = [b for b in blocks if b.kind == "decl"]
            t_gen += sum(1 for dd in decls if dd.classification == "genuine")
            t_dis += sum(1 for dd in decls if dd.classification in ("dissolves", "infra_name"))
            t_tot += len(decls)

        infra = t_tot - t_gen
        rows.append((d.name, t_gen, t_dis, infra, t_tot, len(files)))

    rows.sort(key=lambda r: r[1], reverse=True)
    for name, gen, dis, infra, total, files in rows:
        print(f"{name:<22} | {gen:>6} | {dis:>5} | {infra:>5} | {total:>5} | {files:>5}")

    print(f"\nGrand total GENUINE: {sum(r[1] for r in rows)}")


def cmd_fruit(domain: Optional[str], top_n: int):
    """Rank files by dissolution density."""
    if domain:
        files = sorted((MATHLIB_DIR / domain).rglob("*.lean"))
    else:
        files = sorted(MATHLIB_DIR.rglob("*.lean"))

    results = []
    for f in files:
        try:
            text = f.read_text(errors="replace")
        except:
            continue
        lines = text.count("\n") + 1
        if lines < 30:
            continue
        hits = len(ZERO_ALL.findall(text))
        if hits == 0:
            continue
        thms = len(re.findall(r"^(protected\s+)?(theorem|lemma|def)\s+", text, re.MULTILINE))
        if thms == 0:
            continue
        density = hits / lines
        relpath = str(f).split("Mathlib/")[-1]
        results.append((density, hits, lines, thms, relpath))

    results.sort(reverse=True)
    title = domain or "ALL"
    print(f"=== {title}: Top {top_n} by density ===\n")
    print(f"{'DENSITY':>8} | {'HITS':>4} | {'LINES':>5} | {'THMS':>4} | PATH")
    print(f"{'--------':>8}-+-{'----':>4}-+-{'-----':>5}-+-{'----':>4}-+-----")

    for density, hits, lines, thms, path in results[:top_n]:
        print(f"{density:>7.1%} | {hits:>4} | {lines:>5} | {thms:>4} | {path}")


def cmd_extract(filepath: Path):
    """Extract one file."""
    if not filepath.exists():
        filepath = MATHLIB_DIR / filepath
    if not filepath.exists():
        print(f"ERROR: {filepath} not found", file=sys.stderr)
        return
    content, stats = extract_smart(filepath)
    print(content)


def cmd_extract_domain(domain: str):
    """Extract all genuine content from a domain."""
    src = MATHLIB_DIR / domain
    if not src.is_dir():
        print(f"ERROR: {src} not found", file=sys.stderr)
        return

    out_dir = ORIGIN_DIR / f"Mathlib_{domain}"
    # Clean previous extraction
    if out_dir.exists():
        import shutil
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    files = sorted(src.rglob("*.lean"))
    count = 0
    total_genuine = 0
    total_dissolved = 0
    total_infra = 0
    skipped_files = 0

    for f in files:
        content, stats = extract_smart(f)

        if stats.get("skipped_file") or stats["genuine"] == 0:
            skipped_files += 1
            total_dissolved += stats.get("dissolved", 0)
            total_infra += stats.get("infra", 0)
            continue

        relpath = str(f).split(f"Mathlib/{domain}/")[-1]
        outfile = out_dir / relpath
        outfile.parent.mkdir(parents=True, exist_ok=True)
        outfile.write_text(content)

        count += 1
        total_genuine += stats["genuine"]
        total_dissolved += stats["dissolved"]
        total_infra += stats["infra"]

    print(f"=== {domain} extraction ===")
    print(f"Extracted:   {count} files to {out_dir}/")
    print(f"Skipped:     {skipped_files} files (all infrastructure or empty)")
    print(f"Genuine:     {total_genuine} declarations")
    print(f"Dissolved:   {total_dissolved} declarations")
    print(f"Infra:       {total_infra} declarations")
    print(f"\nNext: lake build and fix what breaks.")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return

    # Check for --self flag
    global SELF_MODE
    if "--self" in sys.argv:
        SELF_MODE = True
        sys.argv.remove("--self")

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
            if len(sys.argv) > 3:
                cmd_extract_domain(sys.argv[3])
            else:
                print("Usage: origin.py extract --domain <DOMAIN>")
        elif len(sys.argv) > 2:
            cmd_extract(Path(sys.argv[2]))
        else:
            print("Usage: origin.py extract <file.lean> | --domain <DOMAIN>")

    else:
        print(f"Unknown command: {cmd}")
        print(__doc__)


if __name__ == "__main__":
    main()
