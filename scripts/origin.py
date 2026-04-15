#!/usr/bin/env python3
"""
Origin: Mathlib → Origin conversion tool.

Before you modify this script, answer these questions:

1. Read Origin/Core.lean (166 lines). What does the `origin` theorem prove?
   What three things do the instances give Option α?

2. What is the difference between `none` and `some 0`?
   (Hint: one is the ground. One is a measurement that happened to be zero.)

3. Why does Algebra/GroupWithZero/Units/Basic.lean dissolve entirely?
   (Hint: what are those 112 declarations managing?)

4. What makes a declaration "genuine" vs "infrastructure"?
   Run: python3 scripts/origin.py classify Dynamics
   Look at the GENUINE column. What's in it? What's not?

5. Why do extracted files keep Mathlib imports?
   (Hint: where do ℕ, padicValRat, harmonic come from?)

6. Run: python3 scripts/origin.py --self classify --all
   What does 0 in the DISS column tell you?

If you can answer all six, you understand the project.
If you can't, read CLAUDE.md first. Then read Core.lean.

Usage:
    python3 scripts/origin.py run                      THE PIPELINE. Extract all. Build all. Report.
    python3 scripts/origin.py classify NumberTheory
    python3 scripts/origin.py classify --all
    python3 scripts/origin.py --self classify --all    (audit Origin itself)
    python3 scripts/origin.py extract NumberTheory/Harmonic/Int.lean
    python3 scripts/origin.py extract --domain NumberTheory
    python3 scripts/origin.py fruit --all 10
"""

import os
import re
import sys
from pathlib import Path
from dataclasses import dataclass, field
from typing import Optional

# Use lake's Mathlib — same version that builds
LAKE_MATHLIB = Path("/Users/tallbr00/Documents/venv/original-arithmetic/origin-lean/.lake/packages/mathlib/Mathlib")
ORIGIN_MATHLIB = Path("/Users/tallbr00/Documents/venv/original-arithmetic/origin-mathlib/Mathlib")

# Default: use lake's Mathlib (guaranteed version match)
MATHLIB_DIR = LAKE_MATHLIB if LAKE_MATHLIB.exists() else ORIGIN_MATHLIB
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
    "ZeroHom", "CharZero", "IsUnit", "Deprecated",
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
    pending_attrs = []
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

        # Sections (with or without name) — preserve them for scope
        if stripped.startswith("section") and (stripped == "section" or
            stripped.startswith("section ") or stripped.startswith("public section")):
            blocks.append(Block("section", stripped.split("section", 1)[-1].strip(), line))
            i += 1
            continue

        # Namespace
        if stripped.startswith("namespace "):
            ns = stripped.split("namespace ", 1)[1].strip()
            blocks.append(Block("namespace", ns, line))
            i += 1
            continue

        if stripped == "end" or stripped.startswith("end "):
            ns = stripped.split("end", 1)[1].strip() if " " in stripped else ""
            blocks.append(Block("end_namespace", ns, stripped))
            i += 1
            continue

        # Open
        if stripped.startswith("open "):
            blocks.append(Block("open", "", line))
            i += 1
            continue

        # Strip: Mathlib-specific commands that Origin doesn't need
        strip = False
        for cmd in ("add_decl_doc ", "assert_not_exists ", "suppress_compilation",
                     "#align", "#guard_msgs", "#check", "#print",
                     "@[deprecated", "@[inherit_doc]",
                     "-- Adaptation note", "-- adaptation_note",
                     "#adaptation_note"):
            if stripped.startswith(cmd) or stripped == cmd.strip():
                strip = True
                break
        if strip:
            i += 1
            # Skip multi-line (indented continuation)
            while i < len(lines) and lines[i].strip() and lines[i][0].isspace():
                i += 1
            continue

        # Pass-through commands: Lean commands that must be preserved
        passthrough = False
        for cmd in ("set_option ", "attribute ", "alias ", "include ",
                     "omit ", "universe ", "local ", "scoped ",
                     "example ", "example"):
            if stripped.startswith(cmd) or stripped == cmd.strip():
                passthrough = True
                break
        if passthrough:
            # Collect multi-line command (indented continuation)
            cmd_lines = [line]
            i += 1
            while i < len(lines) and lines[i].strip() and lines[i][0].isspace():
                cmd_lines.append(lines[i])
                i += 1
            blocks.append(Block("other", "", "\n".join(cmd_lines)))
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
        # But NOT if the line also contains a declaration keyword (e.g., @[simp] theorem ...)
        if stripped.startswith("@[") and not re.search(
            r"\b(theorem|lemma|def|structure|class|instance|abbrev|inductive)\s+\S+",
            stripped
        ):
            attr_lines = [line]
            i += 1
            # Collect multi-line attributes (including multiline strings like
            # @[to_additive "...long string..."]) and skip blanks to next decl
            while i < len(lines):
                s = lines[i].strip()
                if not s:
                    i += 1
                    continue
                if s.startswith("@["):
                    attr_lines.append(lines[i])
                    i += 1
                    continue
                # Check if this is a continuation of a multiline attribute
                # (e.g., multiline string in @[to_additive "..."])
                # If the last attr line has unbalanced quotes or brackets, continue
                last_attr = "\n".join(attr_lines)
                if last_attr.count('"') % 2 == 1 or last_attr.count('[') > last_attr.count(']'):
                    attr_lines.append(lines[i])
                    i += 1
                    continue
                break
            # Don't modify lines[i] — just remember the attributes
            # and let the declaration handler pick them up below
            pending_attrs = attr_lines
            continue

        # Declaration
        decl_match = re.match(
            r"^(.*?)?(private\s+|protected\s+)?(noncomputable\s+)?(nonrec\s+)?(unsafe\s+)?"
            r"(theorem|lemma|def|structure|class|instance|abbrev|inductive)\s+(\S+)",
            stripped
        )
        if decl_match:
            kind = decl_match.group(6)
            name = decl_match.group(7)

            # Collect full declaration (include any pending attributes)
            decl_lines = pending_attrs + [line]
            pending_attrs = []
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

        if b.kind in ("namespace", "end_namespace", "section"):
            output_parts.append(b.text)
            continue

        if b.kind == "open":
            output_parts.append(b.text)
            continue

        if b.kind == "variable":
            output_parts.append(b.text)
            continue

        if b.kind == "decl":
            if b.classification in ("dissolves", "infra_name"):
                output_parts.append(f"-- DISSOLVED: {b.name}")
            else:
                # Keep genuine, instance, simp_trivial, trivial — all non-dissolved
                # content stays. Genuine proofs may reference simp lemmas or instances.
                output_parts.append(b.text)

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
    print()


def cmd_run():
    """The pipeline: extract all → build all → group errors → report lines."""
    import subprocess
    import time
    from collections import defaultdict

    base = MATHLIB_DIR
    if not base.exists():
        print(f"ERROR: Mathlib not found at {base}", file=sys.stderr)
        return

    import shutil
    W = shutil.get_terminal_size((80, 24)).columns

    # Step 1: Find all domains
    domains = sorted(d.name for d in base.iterdir()
                     if d.is_dir() and list(d.rglob("*.lean")))
    # Flush output immediately so progress is visible
    sys.stdout.reconfigure(line_buffering=True)

    # ── ANSI ──
    BOLD    = "\033[1m"
    DIM     = "\033[2m"
    GREEN   = "\033[32m"
    RED     = "\033[31m"
    CYAN    = "\033[36m"
    YELLOW  = "\033[33m"
    WHITE   = "\033[97m"
    RESET   = "\033[0m"
    CLEAR   = "\033[2K\r"

    def bar(current, total, width=30):
        filled = int(width * current / total) if total else 0
        return f"{GREEN}{'█' * filled}{DIM}{'░' * (width - filled)}{RESET}"

    def elapsed(t):
        s = int(t)
        if s < 60: return f"{s}s"
        return f"{s // 60}m{s % 60:02d}s"

    t_start = time.time()

    print()
    MAGENTA = "\033[35m"
    print(f"  {BOLD}{CYAN}╔{'═' * (W - 6)}╗{RESET}")
    print(f"  {BOLD}{CYAN}║{RESET}  {BOLD}{WHITE}O R I G I N{RESET}"
          f"  {DIM}powered by{RESET} {BOLD}{MAGENTA}Claude Code{RESET}"
          f"{' ' * max(1, W - 42)}{BOLD}{CYAN}║{RESET}")
    print(f"  {BOLD}{CYAN}║{RESET}  {DIM}b - b = origin  "
          f"·  the ground absorbs  "
          f"·  the script converts{RESET}"
          f"{' ' * max(1, W - 67)}{BOLD}{CYAN}║{RESET}")
    print(f"  {BOLD}{CYAN}╚{'═' * (W - 6)}╝{RESET}")
    print()

    # ── PHASE 1: EXTRACT (parallel) ─────────────────────────────────
    from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor, as_completed
    import multiprocessing

    total_extracted = 0
    total_skipped = 0
    total_genuine = 0
    total_dissolved = 0
    total_infra = 0
    domain_stats = {}

    n_cpus = multiprocessing.cpu_count()
    print(f"  {BOLD}EXTRACT{RESET}  {DIM}Mathlib → Origin  "
          f"({n_cpus} cores){RESET}")
    print(f"  {DIM}{'─' * (W - 4)}{RESET}")

    def extract_domain(domain):
        """Extract one domain — runs in a worker process."""
        src = base / domain
        out_dir = ORIGIN_DIR / f"Mathlib_{domain}"
        if out_dir.exists():
            import shutil as sh
            sh.rmtree(out_dir)
        out_dir.mkdir(parents=True, exist_ok=True)

        files = sorted(src.rglob("*.lean"))
        d_extracted = d_skipped = d_genuine = d_dissolved = d_infra = 0

        for f in files:
            content, stats = extract_smart(f)
            if stats.get("skipped_file") or stats["genuine"] == 0:
                d_skipped += 1
                d_dissolved += stats.get("dissolved", 0)
                d_infra += stats.get("infra", 0)
                continue
            relpath = str(f).split(f"Mathlib/{domain}/")[-1]
            outfile = out_dir / relpath
            outfile.parent.mkdir(parents=True, exist_ok=True)
            outfile.write_text(content)
            d_extracted += 1
            d_genuine += stats["genuine"]
            d_dissolved += stats["dissolved"]
            d_infra += stats["infra"]

        return {
            "domain": domain, "extracted": d_extracted, "skipped": d_skipped,
            "genuine": d_genuine, "dissolved": d_dissolved, "infra": d_infra,
        }

    # Run extractions in parallel across all cores
    done_count = 0
    with ThreadPoolExecutor(max_workers=n_cpus) as pool:
        futures = {pool.submit(extract_domain, d): d for d in domains}
        for future in as_completed(futures):
            done_count += 1
            r = future.result()
            domain = r["domain"]
            domain_stats[domain] = r
            total_extracted += r["extracted"]
            total_skipped += r["skipped"]
            total_genuine += r["genuine"]
            total_dissolved += r["dissolved"]
            total_infra += r["infra"]

            gen_str = f"{GREEN}{r['genuine']:,}{RESET}" if r['genuine'] > 0 else f"{DIM}0{RESET}"
            dis_str = f"{YELLOW}{r['dissolved']:,}{RESET}" if r['dissolved'] > 0 else f"{DIM}0{RESET}"
            sys.stdout.write(f"{CLEAR}  {bar(done_count, len(domains))} "
                f"{BOLD}{domain:<24}{RESET} "
                f"{r['extracted']:>4} files  {gen_str:>5} genuine  {dis_str:>4} dissolved\n")
            sys.stdout.flush()

    t_extract = time.time()
    print(f"  {DIM}{'─' * (W - 4)}{RESET}")
    print(f"  {BOLD}{WHITE}{total_extracted:,}{RESET} files  "
          f"{BOLD}{GREEN}{total_genuine:,}{RESET} genuine  "
          f"{BOLD}{YELLOW}{total_dissolved:,}{RESET} dissolved  "
          f"{DIM}{total_skipped:,} skipped{RESET}  "
          f"{DIM}{elapsed(t_extract - t_start)}{RESET}")
    print()

    # ── PHASE 2: BUILD ────────────────────────────────────────────
    # ── PHASE 2: BUILD (parallel domains) ───────────────────────────
    # Lake handles its own parallelism internally, but we can run
    # multiple domain builds concurrently. Use fewer workers than
    # cores since each lake build uses multiple threads.
    build_workers = n_cpus
    print(f"  {BOLD}BUILD{RESET}  {DIM}lake build  "
          f"({build_workers} concurrent domains){RESET}")
    print(f"  {DIM}{'─' * (W - 4)}{RESET}")

    import threading
    error_groups = defaultdict(list)
    error_files = set()
    all_extracted = []
    domains_ok = 0
    domains_fail = 0
    build_lock = threading.Lock()

    # Prepare domain build info
    domain_builds = []
    for domain in domains:
        out_dir = ORIGIN_DIR / f"Mathlib_{domain}"
        if not out_dir.exists():
            continue
        lean_files = sorted(out_dir.rglob("*.lean"))
        all_extracted.extend(lean_files)
        if not lean_files:
            continue
        modules = []
        for f in lean_files:
            rel = f.relative_to(ORIGIN_DIR.parent)
            module = str(rel).replace("/", ".").replace(".lean", "")
            modules.append((module, f))
        domain_builds.append((domain, lean_files, modules))

    # Largest domains first — start the big jobs immediately
    domain_builds.sort(key=lambda x: -len(x[1]))

    def build_domain(args):
        """Build one domain — runs in a worker thread."""
        domain, lean_files, modules = args
        module_names = [m for m, _ in modules]
        t_domain = time.time()

        try:
            result = subprocess.run(
                ["lake", "build"] + module_names,
                capture_output=True, text=True, timeout=3600,
                cwd=str(ORIGIN_DIR.parent)
            )
            build_output = result.stderr + result.stdout
            timed_out = False
        except subprocess.TimeoutExpired:
            build_output = ""
            timed_out = True
            result = None

        dt = time.time() - t_domain
        d_errors = []

        if timed_out:
            d_errors.append(("TIMEOUT (>3600s)",
                [str(f.relative_to(ORIGIN_DIR.parent)) for _, f in modules]))
            return {"domain": domain, "files": len(lean_files),
                    "ok": False, "errors": d_errors, "dt": dt, "timeout": True}

        for line in build_output.split("\n"):
            line = line.strip()
            if not line.startswith("error:"):
                continue
            m = re.match(r"error:\s*([^:]+\.lean):(\d+):(\d+):\s*(.*)", line)
            if m:
                d_errors.append((m.group(4).strip(), [m.group(1).lstrip("./")]))
            elif "build failed" not in line:
                d_errors.append((line, [domain]))

        return {"domain": domain, "files": len(lean_files),
                "ok": result.returncode == 0, "errors": d_errors,
                "dt": dt, "timeout": False}

    done_builds = 0
    with ThreadPoolExecutor(max_workers=build_workers) as pool:
        futures = {pool.submit(build_domain, db): db[0] for db in domain_builds}
        for future in as_completed(futures):
            done_builds += 1
            r = future.result()
            domain = r["domain"]

            with build_lock:
                n_errs = 0
                for pattern, files in r["errors"]:
                    error_groups[pattern].extend(files)
                    error_files.update(files)
                    n_errs += len(files)
                if r["ok"]:
                    domains_ok += 1
                    icon = f"{GREEN}OK{RESET}"
                elif r["timeout"]:
                    domains_fail += 1
                    icon = f"{RED}TIMEOUT{RESET}"
                else:
                    domains_fail += 1
                    icon = f"{RED}FAIL({n_errs}){RESET}"

            sys.stdout.write(f"{CLEAR}  {bar(done_builds, len(domain_builds))} "
                f"{icon:<18}  {BOLD}{domain:<24}{RESET} "
                f"{r['files']:>4} files  {DIM}{elapsed(r['dt'])}{RESET}\n")
            sys.stdout.flush()

    t_build = time.time()
    build_pass = len(all_extracted) - len(error_files)
    build_fail_count = len(error_files)
    print(f"  {DIM}{'─' * (W - 4)}{RESET}")
    pass_str = f"{GREEN}{build_pass:,}{RESET}"
    fail_str = f"{RED}{build_fail_count:,}{RESET}" if build_fail_count > 0 else f"{GREEN}0{RESET}"
    print(f"  {BOLD}{pass_str}{RESET} pass  {fail_str} fail  "
          f"{DIM}{elapsed(t_build - t_extract)}{RESET}")
    print()

    # ── PHASE 3: COUNT ────────────────────────────────────────────
    mathlib_lines = 0
    for f in base.rglob("*.lean"):
        try:
            mathlib_lines += f.read_text(errors="replace").count("\n") + 1
        except:
            pass

    origin_lines = 0
    for domain in domains:
        out_dir = ORIGIN_DIR / f"Mathlib_{domain}"
        if not out_dir.exists():
            continue
        for f in out_dir.rglob("*.lean"):
            try:
                origin_lines += f.read_text(errors="replace").count("\n") + 1
            except:
                pass

    # ── REPORT ────────────────────────────────────────────────────
    status = "PASS" if build_fail_count == 0 else "FAIL"
    reduction = (1 - origin_lines / mathlib_lines) * 100 if mathlib_lines > 0 else 0
    t_total = time.time() - t_start

    print(f"  {BOLD}{CYAN}╔{'═' * (W - 6)}╗{RESET}")
    print(f"  {BOLD}{CYAN}║{RESET}  {BOLD}{WHITE}R E S U L T S{RESET}"
          f"{' ' * (W - 21)}{BOLD}{CYAN}║{RESET}")
    print(f"  {BOLD}{CYAN}╚{'═' * (W - 6)}╝{RESET}")
    print()

    # The big numbers
    print(f"    {DIM}Mathlib{RESET}        {BOLD}{mathlib_lines:>12,}{RESET} {DIM}lines{RESET}")
    print(f"    {DIM}Origin{RESET}         {BOLD}{GREEN}{origin_lines:>12,}{RESET} {DIM}lines{RESET}")
    r_color = GREEN if reduction > 50 else YELLOW if reduction > 20 else RED
    print(f"    {BOLD}Reduction{RESET}      {BOLD}{r_color}{reduction:>11.1f}%{RESET}")
    print()

    # Declarations
    print(f"    {DIM}Genuine{RESET}        {GREEN}{total_genuine:>12,}{RESET}")
    print(f"    {DIM}Dissolved{RESET}      {YELLOW}{total_dissolved:>12,}{RESET}")
    print(f"    {DIM}Infrastructure{RESET} {DIM}{total_infra:>12,}{RESET}")
    print()

    # Build status
    if build_fail_count == 0:
        print(f"    {DIM}Build{RESET}          {BOLD}{GREEN}{'PASS':>12}{RESET}  "
              f"{GREEN}{build_pass:,} files{RESET}")
    else:
        print(f"    {DIM}Build{RESET}          {BOLD}{RED}{'FAIL':>12}{RESET}  "
              f"{GREEN}{build_pass:,} pass{RESET} / {RED}{build_fail_count:,} fail{RESET}")
    print(f"    {DIM}Time{RESET}           {DIM}{elapsed(t_total):>12}{RESET}  "
          f"{DIM}(extract {elapsed(t_extract - t_start)} + build {elapsed(t_build - t_extract)}){RESET}")
    print()

    if error_groups:
        print(f"  {BOLD}{RED}ERRORS{RESET}  "
              f"{BOLD}{len(error_groups)}{RESET} {DIM}patterns to fix in the script{RESET}")
        print(f"  {DIM}{'─' * (W - 4)}{RESET}")
        print()
        for pattern, files in sorted(error_groups.items(), key=lambda x: -len(x[1])):
            print(f"    {RED}{len(files):>4}{RESET} {DIM}files{RESET}  {WHITE}{pattern[:W - 20]}{RESET}")
            for f in files[:3]:
                print(f"    {DIM}     ↳ {f}{RESET}")
            if len(files) > 3:
                print(f"    {DIM}     ↳ ... and {len(files) - 3} more{RESET}")
            print()

    print(f"  {BOLD}{CYAN}╔{'═' * (W - 6)}╗{RESET}")
    if build_fail_count == 0:
        print(f"  {BOLD}{CYAN}║{RESET}  {BOLD}{GREEN}"
              f"BUILD PASSES  ·  {mathlib_lines:,} → {origin_lines:,} lines  "
              f"·  {reduction:.1f}% reduction{RESET}"
              f"{' ' * max(1, W - 65)}{BOLD}{CYAN}║{RESET}")
        print(f"  {BOLD}{CYAN}║{RESET}  {DIM}"
              f"Lean verified. Line counts objective. "
              f"The build succeeds or it doesn't.{RESET}"
              f"{' ' * max(1, W - 74)}{BOLD}{CYAN}║{RESET}")
    else:
        print(f"  {BOLD}{CYAN}║{RESET}  {BOLD}{YELLOW}"
              f"{len(error_groups)} error patterns  ·  "
              f"Fix them in the script  ·  Run again{RESET}"
              f"{' ' * max(1, W - 60)}{BOLD}{CYAN}║{RESET}")
    print(f"  {BOLD}{CYAN}╚{'═' * (W - 6)}╝{RESET}")
    print()


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

    elif cmd == "run":
        cmd_run()

    else:
        print(f"Unknown command: {cmd}")
        print(__doc__)


if __name__ == "__main__":
    main()
