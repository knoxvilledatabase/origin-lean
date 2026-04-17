#!/usr/bin/env python3
"""
Origin — the toolkit for building Origin from Mathlib.

Usage:
    python3 scripts/origin.py status                 PROGRESS REPORT
    python3 scripts/origin.py index                  generate Origin/Index.lean (the dedup)
    python3 scripts/origin.py dedup                  find duplicate definitions across Origin
    python3 scripts/origin.py list                  show all domains
    python3 scripts/origin.py audit <domain>        DRY audit one domain
    python3 scripts/origin.py audit --all           DRY audit all domains
    python3 scripts/origin.py generate <domain>     draft Origin file from Mathlib
    python3 scripts/origin.py classify <domain>     classify declarations
    python3 scripts/origin.py suggest <domain>      show uncovered genuine declarations
    python3 scripts/origin.py stub <domain>         append uncovered as def stubs
    python3 scripts/origin.py quality [domain]      show stub vs real declaration counts
    python3 scripts/origin.py show <name>          show Mathlib original for a stub name
    python3 scripts/origin.py unused               find declarations nothing references
    python3 scripts/origin.py patterns             find patterns that consolidate to Core
    python3 scripts/origin.py clean                remove stale stubs that collide with Core
"""

import re
import sys
import shutil
from pathlib import Path
from dataclasses import dataclass, field

ROOT = Path(__file__).parent.parent
EXTRACTED = ROOT / "extracted"
ORIGIN = ROOT / "Origin"

# Tooling domains — not mathematics, don't need sketches
SKIP_DOMAINS = {"Deprecated", "Lean", "Std", "Tactic", "Testing", "Util"}


# =============================================================================
# UI
# =============================================================================

class UI:
    """Terminal UI with ANSI colors for humans and AI alike."""
    BOLD    = "\033[1m"
    DIM     = "\033[2m"
    GREEN   = "\033[32m"
    RED     = "\033[31m"
    CYAN    = "\033[36m"
    YELLOW  = "\033[33m"
    WHITE   = "\033[97m"
    MAGENTA = "\033[35m"
    RESET   = "\033[0m"

    def __init__(self):
        self.W = shutil.get_terminal_size((80, 24)).columns

    def bar(self, current, total, width=30):
        filled = int(width * current / total) if total else 0
        return f"{self.GREEN}{'█' * filled}{self.DIM}{'░' * (width - filled)}{self.RESET}"

    def header(self, title="O R I G I N", subtitle="Mathlib is the demo. Origin is production."):
        W = self.W
        print()
        print(f"  {self.BOLD}{self.CYAN}╔{'═' * (W - 6)}╗{self.RESET}")
        print(f"  {self.BOLD}{self.CYAN}║{self.RESET}  {self.BOLD}{self.WHITE}{title}{self.RESET}"
              f"{' ' * max(1, W - len(title) - 8)}{self.BOLD}{self.CYAN}║{self.RESET}")
        print(f"  {self.BOLD}{self.CYAN}║{self.RESET}  {self.DIM}{subtitle}{self.RESET}"
              f"{' ' * max(1, W - len(subtitle) - 8)}{self.BOLD}{self.CYAN}║{self.RESET}")
        print(f"  {self.BOLD}{self.CYAN}╚{'═' * (W - 6)}╝{self.RESET}")
        print()

    def phase(self, title, subtitle=""):
        print(f"  {self.BOLD}{title}{self.RESET}  {self.DIM}{subtitle}{self.RESET}")
        print(f"  {self.DIM}{'─' * (self.W - 4)}{self.RESET}")

    def separator(self):
        print(f"  {self.DIM}{'─' * (self.W - 4)}{self.RESET}")

    def stat(self, label, value, color=""):
        c = getattr(self, color.upper(), "") if color else ""
        r = self.RESET if c else ""
        print(f"    {label:<22s}{c}{value}{r}")

    def ok(self, msg):
        print(f"  {self.GREEN}✓{self.RESET} {msg}")

    def fail(self, msg):
        print(f"  {self.RED}✗{self.RESET} {msg}")

    def info(self, msg):
        print(f"  {self.DIM}{msg}{self.RESET}")


ui = UI()

# Shared regex for counting Origin declarations
ORIGIN_DECL_RE = re.compile(
    r'^\s*(?:@\[.*?\]\s*)?'
    r'(?:protected\s+|private\s+|nonrec\s+|noncomputable\s+)*'
    r'(def|theorem|lemma|structure|class|inductive|abbrev)\s+(\S+)')


def count_origin_decls(filepath):
    """Count exported declarations in an Origin .lean file."""
    count = 0
    for line in filepath.read_text(errors="replace").split("\n"):
        if "private " in line:
            continue
        if ORIGIN_DECL_RE.match(line):
            count += 1
    return count


# =============================================================================
# Classifier — config-driven rule engine
# =============================================================================

class Classifier:
    """Classifies declarations. Axis 1: what dissolves."""

    INFRA_SIG = re.compile(r"\bNeZero\b|\bGroupWithZero\b")
    BARE_NEZ = re.compile(r"≠\s*0")
    INFRA_NAMES = re.compile(
        r"^ne_zero$|^NeZero|^neZero|^ne_one$|"
        r"GroupWithZero|groupWithZero|"
        r"NoZeroDivisors|noZeroDivisors|"
        r"NoZeroSMulDivisors|"
        r"MulZeroClass|mulZeroClass|"
        r"not_isUnit_zero|"
        r"^zero_mul$|^mul_zero$|^zero_div$|^div_zero$|"
        r"^inv_zero$|^zero_inv$|"
        r"WithZero|withZero|"
        r"^ZeroHom$|^zeroHom$")
    TRIVIAL_RE = re.compile(
        r":=\s*(rfl|h\b|by\s+simp\s*$|by\s+rfl|by\s+exact\s+\w+\s*$|Iff\.rfl)")
    RING_CONFLATION = re.compile(
        r"MulZeroClass\b|mulZeroClass\b|zero_ne_one|one_ne_zero|nontrivial|Nontrivial")
    SKIP_FILE_PATTERNS = [
        "GroupWithZero", "NeZero", "NoZeroDivisors", "NoZeroSMul",
        "MulZeroClass", "WithZero", "WithBot", "WithTop", "ZeroHom", "Deprecated"]

    def classify(self, kind, name, full_text):
        sig = full_text.split(":=")[0] if ":=" in full_text else full_text
        if kind == "instance": return "instance"
        if self.INFRA_NAMES.search(name): return "infra_name"
        if self.INFRA_SIG.search(sig): return "dissolves"
        if self.BARE_NEZ.search(sig) and self.INFRA_NAMES.search(name): return "dissolves"
        if self.RING_CONFLATION.search(sig): return "conflates"
        if self.TRIVIAL_RE.search(full_text) and kind in ("theorem", "lemma"):
            return "simp_trivial" if "@[simp]" in full_text else "trivial"
        return "genuine"


classifier = Classifier()


# =============================================================================
# Status — progress report: Origin vs Mathlib per domain
# =============================================================================

def cmd_status():
    """Show Origin line counts per file, sorted largest first with bar graphs."""
    skip = {"Index", "Test"}

    rows = []  # (stem, lines, decls, stubs, real)
    for f in sorted(ORIGIN.glob("*.lean")):
        if f.stem in skip:
            continue
        text = f.read_text(errors="replace")
        lines = len(text.split("\n"))
        decls = count_origin_decls(f)
        stubs = 0
        for line in text.split("\n"):
            if STUB_RE.match(line):
                stubs += 1
        rows.append((f.stem, lines, decls, stubs, decls - stubs))

    # Sort by lines descending
    rows.sort(key=lambda r: r[1], reverse=True)

    total_lines = sum(r[1] for r in rows)
    total_decls = sum(r[2] for r in rows)
    total_stubs = sum(r[3] for r in rows)
    total_real = sum(r[4] for r in rows)
    max_lines = max(r[1] for r in rows) if rows else 1

    ui.header("O R I G I N   S T A T U S",
              f"{total_lines:,} lines — {total_real:,} real / {total_decls:,} declarations")

    bar_width = max(30, ui.W - 50)

    for stem, lines, decls, stubs, real in rows:
        # Bar: real portion in green, stub portion in yellow
        real_frac = real / max(decls, 1)
        total_fill = int(bar_width * lines / max_lines)
        real_fill = int(total_fill * real_frac)
        stub_fill = total_fill - real_fill

        bar = (f"{ui.GREEN}{'█' * real_fill}{ui.RESET}"
               f"{ui.YELLOW}{'░' * stub_fill}{ui.RESET}"
               f"{ui.DIM}{'·' * (bar_width - total_fill)}{ui.RESET}")

        print(f"  {stem:<24s} {lines:>6,}  {bar}")

    ui.separator()
    print(f"  {ui.BOLD}{'TOTAL':<24s} {total_lines:>6,}{ui.RESET}")
    print()
    ui.stat("Declarations", f"{total_decls:,}")
    ui.stat("Real", f"{ui.GREEN}{total_real:,}{ui.RESET}")
    ui.stat("Stubs", f"{ui.YELLOW}{total_stubs:,}{ui.RESET}")
    ui.stat("Files", f"{len(rows)}")
    print()
    ui.info(f"{ui.GREEN}█{ui.RESET} = real declarations  "
            f"{ui.YELLOW}░{ui.RESET} = stubs  "
            f"{ui.DIM}·{ui.RESET} = comments/whitespace")
    print()


# =============================================================================
# List — show all domains and their status
# =============================================================================

def cmd_list():
    domains = sorted(d.name.replace("Mathlib_", "")
                     for d in EXTRACTED.iterdir()
                     if d.is_dir() and d.name.startswith("Mathlib_"))
    existing = {f.stem for f in ORIGIN.glob("*.lean")}
    existing.update(f.stem.rstrip("2") for f in ORIGIN.glob("*2.lean"))

    math = [d for d in domains if d not in SKIP_DOMAINS]
    skip = [d for d in domains if d in SKIP_DOMAINS]

    origin_lines = sum(len(f.read_text().split("\n")) for f in ORIGIN.glob("*.lean"))
    has_count = sum(1 for d in math if d in existing or f"{d}2" in {f.stem for f in ORIGIN.glob("*.lean")})

    ui.header()
    print(f"  {ui.BOLD}Math domains ({has_count}/{len(math)}):{ui.RESET}\n")
    for dom in math:
        has = dom in existing or f"{dom}2" in {f.stem for f in ORIGIN.glob("*.lean")}
        marker = f"  {ui.GREEN}✓{ui.RESET}" if has else f"  {ui.DIM}·{ui.RESET}"
        print(f"  {marker} {dom}")

    print(f"\n  {ui.DIM}Skipped (tooling): {', '.join(skip)}{ui.RESET}")
    ui.separator()
    ui.stat("Origin/", f"{origin_lines:,} lines", "cyan")
    print()


# =============================================================================
# Audit — DRY profile of a domain
# =============================================================================

def cmd_audit(path):
    if path == "--all":
        ui.header()
        domains = sorted(d.name.replace("Mathlib_", "")
                         for d in EXTRACTED.iterdir()
                         if d.is_dir() and d.name.startswith("Mathlib_"))
        all_stats = []
        for dom in domains:
            stats = _audit_domain(dom)
            if stats:
                all_stats.append((dom, stats))

        if all_stats:
            t = {k: sum(s[k] for _, s in all_stats) for k in
                 ["files", "lines", "genuine", "dissolved", "rfl", "iff_rfl",
                  "by_simp", "by_rfl", "by_norm_num", "multi_rw", "rw", "spec"]}
            t_trivial = t["rfl"] + t["iff_rfl"] + t["by_simp"] + t["by_rfl"] + t["by_norm_num"]
            origin_lines = sum(len(f.read_text().split("\n")) for f in ORIGIN.glob("*.lean"))

            print()
            print(f"  {ui.BOLD}{ui.CYAN}╔{'═' * (ui.W - 6)}╗{ui.RESET}")
            print(f"  {ui.BOLD}{ui.CYAN}║{ui.RESET}  {ui.BOLD}{ui.WHITE}TOTAL ACROSS ALL DOMAINS{ui.RESET}"
                  f"{' ' * max(1, ui.W - 34)}{ui.BOLD}{ui.CYAN}║{ui.RESET}")
            print(f"  {ui.BOLD}{ui.CYAN}╚{'═' * (ui.W - 6)}╝{ui.RESET}")
            ui.stat("Domains", f"{len(all_stats)}")
            ui.stat("Files", f"{t['files']:,}")
            ui.stat("Lines", f"{t['lines']:,}", "yellow")
            ui.stat("Genuine", f"{t['genuine']:,}", "green")
            ui.stat("Dissolved", f"{t['dissolved']}", "yellow")
            ui.stat("Trivial proofs", f"{t_trivial:,}")
            ui.stat("Multi-line rw", f"{t['multi_rw']:,}", "red")
            ui.stat("rw total", f"{t['rw']:,}", "yellow")
            ui.stat("Specializations", f"{t['spec']}")
            print()
            ui.stat("Origin/", f"{origin_lines:,} lines", "cyan")
            ui.separator()
    else:
        d = EXTRACTED / f"Mathlib_{path}"
        if d.exists():
            _audit_domain(path)
        else:
            ui.fail(f"Not found: {path}")


def _audit_domain(domain):
    d = EXTRACTED / f"Mathlib_{domain}"
    files = list(d.rglob("*.lean"))
    if not files:
        return None

    s = _audit_files(files)

    sketch_lines = 0
    for name in [f"{domain}.lean", f"{domain}2.lean"]:
        sc = ORIGIN / name
        if sc.exists():
            sketch_lines = len(sc.read_text().split("\n"))
            break

    _print_audit(domain, s, sketch_lines)
    return s


def _audit_files(files):
    s = {"files": len(files), "lines": 0, "genuine": 0, "dissolved": 0,
         "conflates": 0, "infra": 0, "rfl": 0, "iff_rfl": 0, "by_simp": 0,
         "by_rfl": 0, "by_norm_num": 0, "by_omega_s": 0, "by_decide_s": 0,
         "by_exact": 0, "rw": 0, "simp": 0, "exact": 0, "omega": 0,
         "ring": 0, "aesop": 0, "decide": 0, "linarith": 0,
         "multi_rw": 0, "spec": 0}

    pats = {
        "rfl": re.compile(r':=\s+rfl\s*$'), "iff_rfl": re.compile(r':=\s+Iff\.rfl\s*$'),
        "by_simp": re.compile(r'by\s+simp\s*$'), "by_rfl": re.compile(r'by\s+rfl\s*$'),
        "by_norm_num": re.compile(r'by\s+norm_num\s*$'), "by_omega_s": re.compile(r'by\s+omega\s*$'),
        "by_decide_s": re.compile(r'by\s+decide\s*$'), "by_exact": re.compile(r'by\s+exact\s+\S+\s*$'),
        "multi_rw": re.compile(r'rw\s*\[.*,.*,.*\]'),
        "spec": re.compile(r'^(?:theorem|lemma|def|abbrev)\s+\w+_(?:nat|int|real|fin)\b'),
    }
    tacs = {
        "rw": re.compile(r'\brw\b'), "simp": re.compile(r'\bsimp\b'),
        "exact": re.compile(r'\bexact\b'), "omega": re.compile(r'\bomega\b'),
        "ring": re.compile(r'\bring\b'), "aesop": re.compile(r'\baesop\b'),
        "decide": re.compile(r'\bdecide\b'), "linarith": re.compile(r'\blinarith\b'),
    }

    for f in files:
        text = f.read_text(errors="replace")
        lines = text.split("\n")
        s["lines"] += len(lines)
        for line in lines[:5]:
            for key, label in [("genuine", "Genuine"), ("dissolved", "Dissolved"),
                               ("conflates", "Conflates"), ("infra", "Infrastructure")]:
                m = re.search(rf'{label}:\s*(\d+)', line)
                if m: s[key] += int(m.group(1))
        for line in lines:
            for key, pat in pats.items():
                if pat.search(line): s[key] += 1
            for key, pat in tacs.items():
                s[key] += len(pat.findall(line))
    return s


def _print_audit(name, s, sketch_lines):
    trivial = s["rfl"] + s["iff_rfl"] + s["by_simp"] + s["by_rfl"] + s["by_norm_num"]
    genuine = max(s["genuine"], 1)

    print()
    ui.phase(f"DRY AUDIT: {name}")
    ui.stat("Files", f"{s['files']:,}")
    ui.stat("Lines", f"{s['lines']:,}")
    ui.stat("Genuine", f"{s['genuine']:,}", "green")
    ui.stat("Dissolved", f"{s['dissolved']}", "yellow" if s['dissolved'] else "")
    ui.stat("Conflates", f"{s['conflates']}", "magenta" if s['conflates'] else "")
    ui.stat("Infrastructure", f"{s['infra']:,}")
    if sketch_lines:
        pct = (1 - sketch_lines / max(s["lines"], 1)) * 100
        ui.stat("Sketch", f"{sketch_lines} lines ({pct:.1f}% reduction)", "cyan")
    print()
    print(f"    {ui.BOLD}Layer 1{ui.RESET} {ui.DIM}— Trivial proofs:{ui.RESET} {trivial} ({trivial * 100 // genuine}% of genuine)")
    for k, label in [("rfl","rfl"), ("iff_rfl","Iff.rfl"), ("by_simp","by simp"),
                     ("by_rfl","by rfl"), ("by_norm_num","by norm_num"),
                     ("by_exact","by exact <term>"), ("by_omega_s","by omega"), ("by_decide_s","by decide")]:
        ui.stat(f"  {label}", f"{s[k]}")
    print()
    print(f"    {ui.BOLD}Layer 2{ui.RESET} {ui.DIM}— Tactic profile:{ui.RESET}")
    ui.stat("  rw", f"{s['rw']:,}", "yellow")
    ui.stat("  simp", f"{s['simp']:,}")
    ui.stat("  exact", f"{s['exact']:,}")
    ui.stat("  omega", f"{s['omega']}", "green" if s['omega'] > 50 else "")
    ui.stat("  ring", f"{s['ring']}")
    ui.stat("  aesop", f"{s['aesop']}")
    ui.stat("  decide", f"{s['decide']}")
    ui.stat("  linarith", f"{s['linarith']}")
    ui.stat("  Multi-line rw", f"{s['multi_rw']:,} chains", "red" if s['multi_rw'] > 100 else "yellow")
    print()
    print(f"    {ui.BOLD}Layer 3{ui.RESET} {ui.DIM}— Specialization:{ui.RESET}")
    ui.stat("  foo_nat/int/real", f"{s['spec']}", "yellow" if s['spec'] > 10 else "")


# =============================================================================
# Generate — draft an Origin file from a Mathlib domain
# =============================================================================

def cmd_generate(domain):
    sys.path.insert(0, str(Path(__file__).parent))
    from compress.generator import cmd_generate as _gen
    _gen(domain, EXTRACTED, ORIGIN)


# =============================================================================
# Classify — show classification for declarations
# =============================================================================

def cmd_classify(path):
    d = EXTRACTED / f"Mathlib_{path}"
    if not d.exists():
        ui.fail(f"Not found: {path}")
        return

    decl_re = re.compile(
        r'^(?:.*?)?(private\s+|protected\s+)?(noncomputable\s+)?'
        r'(theorem|lemma|def|structure|class|instance|abbrev|inductive)\s+(\S+)')

    for f in sorted(d.rglob("*.lean"))[:5]:
        text = f.read_text(errors="replace")
        print(f"\n  {ui.BOLD}{f.relative_to(EXTRACTED)}{ui.RESET}:")
        for line in text.split("\n"):
            m = decl_re.match(line.strip())
            if m:
                kind, name = m.group(3), m.group(4)
                ctx = text[text.find(line):text.find(line) + 500]
                label = classifier.classify(kind, name, ctx)
                marker = {"genuine": "  ", "dissolves": "✗ ", "conflates": "~ ",
                           "infra_name": "✗ ", "instance": "  ", "trivial": "△ ",
                           "simp_trivial": "△ "}.get(label, "  ")
                print(f"    {marker}{kind:10s} {name:40s} [{label}]")


# =============================================================================
# Suggest — show uncovered Mathlib declarations for a domain
# =============================================================================

def _normalize_lean_name(name):
    """Strip guillemets so «foo'» and foo' compare equal, as Lean sees them."""
    if name.startswith('«') and name.endswith('»'):
        return name[1:-1]
    return name


def _stub_name(mathlib_name):
    """Convert a Mathlib declaration name to a stub name for Origin.

    Takes the last component (after the final dot), appends ' if it
    doesn't already end with one.  Returns None for unparseable names.
    E.g. "Foo.bar_baz" -> "bar_baz'".
    """
    stem = mathlib_name.split(".")[-1]
    if stem.startswith("_root_."):
        stem = stem[len("_root_."):]
    # Strip leading underscores
    stem = stem.lstrip("_")
    if not stem:
        return None
    # Filter out parser artifacts — must start with letter or Unicode identifier start
    if not (stem[0].isalpha() or stem[0] == '«'):
        return None
    # Filter names with commas, backticks, braces, colons — not valid identifiers
    if any(c in stem for c in '`,{}:;()[]⟨⟩'):
        return None
    # Append ' to avoid collisions with Lean/Mathlib builtins
    if stem.startswith('«') and stem.endswith('»'):
        # Guillemet-quoted: put ' inside: «Foo» -> «Foo'»
        stem = '«' + stem[1:-1] + "'»"
    elif not stem.endswith("'"):
        stem = stem + "'"
    return stem


def _get_uncovered(domain):
    """Return (covered, uncovered, origin_stems, all_origin_names) for a domain.

    Each item in covered/uncovered is (kind, name, filename).
    origin_stems: set of lowercase name stems in this domain's Origin file(s).
    all_origin_names: dict mapping name -> module for ALL Origin files (for collision detection).
    """
    d = EXTRACTED / f"Mathlib_{domain}"
    if not d.exists():
        return None, None, None, None

    # 1. Collect genuine Mathlib declarations
    mathlib_decl_re = re.compile(
        r'^(?:.*?)?(private\s+|protected\s+)?(noncomputable\s+)?'
        r'(theorem|lemma|def|structure|class|instance|abbrev|inductive)\s+(\S+)')

    mathlib_decls = []
    for f in sorted(d.rglob("*.lean")):
        text = f.read_text(errors="replace")
        fname = f.relative_to(EXTRACTED)
        for line in text.split("\n"):
            m = mathlib_decl_re.match(line.strip())
            if m:
                kind, name = m.group(3), m.group(4)
                ctx = text[text.find(line):text.find(line) + 500]
                label = classifier.classify(kind, name, ctx)
                if label == "genuine":
                    mathlib_decls.append((kind, name, str(fname)))

    # 2. Collect this domain's Origin declarations
    origin_names = set()
    for fname in [f"{domain}.lean", f"{domain}2.lean"]:
        p = ORIGIN / fname
        if p.exists():
            for line in p.read_text(errors="replace").split("\n"):
                m = ORIGIN_DECL_RE.match(line)
                if m and "private " not in line:
                    origin_names.add(m.group(2))

    origin_stems = {n.split(".")[-1].lower() for n in origin_names}

    # 3. Collect ALL Origin names across all files (for collision detection)
    #    Normalize guillemets: «foo'» and foo' are the same to Lean
    all_origin_names = {}  # normalized_name -> module
    for lean_file in sorted(ORIGIN.glob("*.lean")):
        if lean_file.stem in {"Index", "Test"}:
            continue
        for line in lean_file.read_text(errors="replace").split("\n"):
            m = ORIGIN_DECL_RE.match(line)
            if m and "private " not in line:
                norm = _normalize_lean_name(m.group(2))
                all_origin_names[norm] = lean_file.stem

    # 4. Partition into covered/uncovered
    covered = []
    uncovered = []
    for kind, name, fname in mathlib_decls:
        stem = name.split(".")[-1].lower()
        if stem in origin_stems:
            covered.append((kind, name, fname))
        else:
            uncovered.append((kind, name, fname))

    return covered, uncovered, origin_stems, all_origin_names


def cmd_suggest(domain):
    """Show Mathlib genuine declarations not yet covered by Origin."""
    covered, uncovered, _, all_origin_names = _get_uncovered(domain)
    if covered is None:
        ui.fail(f"Not found: {domain}")
        return

    # Display
    total = len(covered) + len(uncovered)
    n_covered = len(covered)
    n_uncovered = len(uncovered)

    ui.header("S U G G E S T", f"{domain} — {n_covered}/{total} genuine covered, {n_uncovered} uncovered")

    # Check for potential name collisions (normalize guillemets)
    collisions = []
    for kind, name, fname in uncovered:
        stub_name = _stub_name(name)
        if stub_name:
            norm = _normalize_lean_name(stub_name)
            if norm in all_origin_names:
                collisions.append((norm, all_origin_names[norm]))

    if uncovered:
        # Group by file
        from collections import defaultdict
        by_file = defaultdict(list)
        for kind, name, fname in uncovered:
            by_file[fname].append((kind, name))

        for fname in sorted(by_file.keys()):
            decls = by_file[fname]
            print(f"\n  {ui.BOLD}{fname}{ui.RESET} ({len(decls)} uncovered):")
            for kind, name in decls[:15]:  # cap display at 15 per file
                stub = _stub_name(name)
                warn = ""
                if stub:
                    norm = _normalize_lean_name(stub)
                    if norm in all_origin_names:
                        warn = f"  {ui.YELLOW}⚠ collision: {all_origin_names[norm]}.lean{ui.RESET}"
                print(f"    {kind:10s} {name}{warn}")
            if len(decls) > 15:
                ui.info(f"    ... and {len(decls) - 15} more")

    if collisions:
        seen = set()
        unique = [(n, m) for n, m in collisions if n not in seen and not seen.add(n)]
        print()
        ui.info(f"{len(unique)} name(s) would collide — rename with domain suffix if stubbing")

    print()
    ui.separator()
    ui.stat("Total genuine", f"{total}")
    ui.stat("Covered", f"{ui.GREEN}{n_covered}{ui.RESET}")
    ui.stat("Uncovered", f"{ui.YELLOW}{n_uncovered}{ui.RESET}" if n_uncovered else "0")
    pct = n_covered / max(total, 1) * 100
    ui.stat("Coverage", f"{pct:.0f}%")
    print()


# =============================================================================
# Stub — append uncovered declarations as stubs to existing Origin file
# =============================================================================

def cmd_stub(domain):
    """Append uncovered Mathlib declarations as def stubs to Origin/<domain>.lean."""
    covered, uncovered, _, all_origin_names = _get_uncovered(domain)
    if covered is None:
        ui.fail(f"Not found: {domain}")
        return

    if not uncovered:
        ui.ok(f"{domain}: fully covered, nothing to stub")
        return

    # Find the Origin file to append to
    origin_file = ORIGIN / f"{domain}.lean"
    if not origin_file.exists():
        origin_file = ORIGIN / f"{domain}2.lean"
    if not origin_file.exists():
        ui.fail(f"No Origin file found for {domain}")
        return

    # Read existing file
    existing = origin_file.read_text(errors="replace")

    # Remove trailing comment if present (we'll re-add it)
    trail = "-- None absorbs (mul, neg, map): Core.lean's @[simp] set handles all cases."
    if existing.rstrip().endswith(trail):
        existing = existing[:existing.rstrip().rfind(trail)]

    # Group uncovered by Mathlib file for section headers
    from collections import defaultdict
    by_file = defaultdict(list)
    for kind, name, fname in uncovered:
        by_file[fname].append((kind, name))

    # Generate stubs
    lines = []
    lines.append("")
    lines.append("-- ============================================================================")
    lines.append("-- STUBS — auto-generated by: python3 scripts/origin.py stub " + domain)
    lines.append("-- Upgrade key declarations from stubs to real structures/theorems.")
    lines.append("-- ============================================================================")
    lines.append("")

    seen_names = set()
    n_added = 0
    n_skipped_collision = 0
    n_skipped_dup = 0

    for fname in sorted(by_file.keys()):
        decls = by_file[fname]
        short_fname = fname.split("/", 1)[-1] if "/" in fname else fname
        lines.append(f"-- {short_fname}")

        for kind, name in decls:
            stub = _stub_name(name)

            # Skip unparseable names
            if stub is None:
                n_skipped_dup += 1
                continue

            # Normalize for collision checking (guillemets)
            norm_stub = _normalize_lean_name(stub)

            # Skip if we've already generated this stub name
            if norm_stub in seen_names:
                n_skipped_dup += 1
                continue
            seen_names.add(norm_stub)

            # Check for collision with existing Origin declarations (any file)
            if norm_stub in all_origin_names:
                lines.append(f"-- COLLISION: {stub} already in {all_origin_names[norm_stub]}.lean — rename needed")
                n_skipped_collision += 1
                continue

            docstring = name.split(".")[-1]
            lines.append(f"/-- {docstring} (abstract). -/")
            lines.append(f"def {stub} : Prop := True")

            n_added += 1

        lines.append("")

    lines.append(trail)
    lines.append("")

    # Write
    origin_file.write_text(existing.rstrip() + "\n" + "\n".join(lines))

    ui.header("S T U B", f"{domain} — {n_added} stubs appended")
    ui.stat("File", str(origin_file), "cyan")
    ui.stat("Stubs added", f"{ui.GREEN}{n_added}{ui.RESET}")
    if n_skipped_collision:
        ui.stat("Skipped (collision)", f"{ui.YELLOW}{n_skipped_collision}{ui.RESET}")
    if n_skipped_dup:
        ui.stat("Skipped (duplicate)", f"{n_skipped_dup}")
    print()
    ui.info("Review stubs, upgrade key ones, then: lake build Origin." + domain)
    print()


# =============================================================================
# Quality — show stub vs real declaration counts
# =============================================================================

# Stub detection: catches True in any disguise.
# Matches: def X' : Prop := True
#          def X' (α : Type*) : Prop := True
#          def X' {α : Type u} : Prop := True
#          def X' [Foo α] : Prop := True
# The test: does the body carry mathematical content? If it's True, no.
STUB_RE = re.compile(r'^\s*def\s+\S+\s*(?:\([^)]*\)\s*|\{[^}]*\}\s*|\[[^\]]*\]\s*)*:\s*Prop\s*:=\s*True\s*$')

# Tier 1: structures, classes, inductives, defs, abbrevs in Mathlib.
# These define types and computations — stubs hiding them are the worst.
# A model needs the actual type shape, not `Prop := True`.
#
# Tier 2: theorems and lemmas. `Prop := True` reserves the name.
# The real proof is better, but the name reservation has value.
TIER1_KINDS = {"structure", "class", "inductive", "def", "abbrev"}
TIER2_KINDS = {"theorem", "lemma"}


def _build_mathlib_kind_map(domain, detailed=False):
    """Build a map from stub_name -> mathlib_kind for a domain.

    Scans the extracted Mathlib files for the domain, collects
    genuine declarations, and maps their stub names to their kinds.

    If detailed=True, returns stub_name -> (kind, mathlib_file) instead.
    """
    d = EXTRACTED / f"Mathlib_{domain}"
    if not d.exists():
        return {}

    mathlib_decl_re = re.compile(
        r'^(?:.*?)?(private\s+|protected\s+)?(noncomputable\s+)?'
        r'(theorem|lemma|def|structure|class|instance|abbrev|inductive)\s+(\S+)')

    kind_map = {}  # stub_name -> kind (or (kind, file) if detailed)
    for f in sorted(d.rglob("*.lean")):
        text = f.read_text(errors="replace")
        fname = str(f.relative_to(EXTRACTED))
        for line in text.split("\n"):
            m = mathlib_decl_re.match(line.strip())
            if m:
                kind, name = m.group(3), m.group(4)
                ctx = text[text.find(line):text.find(line) + 500]
                label = classifier.classify(kind, name, ctx)
                if label == "genuine":
                    stub = _stub_name(name)
                    norm = _normalize_lean_name(stub) if stub else None
                    if norm and norm not in kind_map:
                        kind_map[norm] = (kind, fname) if detailed else kind
    return kind_map


def _collect_stubs(filepath):
    """Collect stub names from an Origin file.

    Returns a list of normalized stub names.
    """
    stubs = []
    for line in filepath.read_text(errors="replace").split("\n"):
        if "private " in line:
            continue
        if STUB_RE.match(line):
            m = ORIGIN_DECL_RE.match(line)
            if m:
                stubs.append(_normalize_lean_name(m.group(2)))
    return stubs


def _count_quality(filepath):
    """Count stubs vs real declarations in an Origin file.

    Returns (total, stubs, real).
    A stub is: def name : Prop := True
    Everything else (structures, theorems, defs with bodies) is real.
    """
    total = 0
    stubs = 0
    for line in filepath.read_text(errors="replace").split("\n"):
        if "private " in line:
            continue
        if ORIGIN_DECL_RE.match(line):
            total += 1
            if STUB_RE.match(line):
                stubs += 1
    return total, stubs, total - stubs


def cmd_quality(domain=None):
    """Show stub vs real declaration counts per domain, with tier breakdown."""
    skip = {"Index", "Test", "Physics"}

    # Map domain stems to extracted domain names
    stem_to_domain = {}
    for d in EXTRACTED.iterdir():
        if d.is_dir() and d.name.startswith("Mathlib_"):
            dname = d.name.replace("Mathlib_", "")
            if dname not in SKIP_DOMAINS:
                stem_to_domain[dname] = dname
                stem_to_domain[dname + "2"] = dname

    # Collect per-file stats with tier info
    stats = []  # (domain_name, stem, total, stubs, real, t1_stubs, t2_stubs)
    for f in sorted(ORIGIN.glob("*.lean")):
        if f.stem in skip or f.stem == "Core":
            continue
        total, stubs, real = _count_quality(f)

        # Determine the Mathlib domain for this file
        mathlib_domain = stem_to_domain.get(f.stem)
        t1_stubs = 0
        t2_stubs = 0
        unknown_stubs = 0

        if mathlib_domain and stubs > 0:
            kind_map = _build_mathlib_kind_map(mathlib_domain)
            stub_names = _collect_stubs(f)
            for sname in stub_names:
                mk = kind_map.get(sname, "")
                if mk in TIER1_KINDS:
                    t1_stubs += 1
                elif mk in TIER2_KINDS:
                    t2_stubs += 1
                else:
                    unknown_stubs += 1
        else:
            unknown_stubs = stubs

        dname = f.stem.rstrip("2") if f.stem.endswith("2") and f.stem != "2" else f.stem
        stats.append((dname, f.stem, total, stubs, real, t1_stubs, t2_stubs))

    # Filter to one domain if requested
    if domain:
        stats = [(d, s, t, st, r, t1, t2) for d, s, t, st, r, t1, t2 in stats
                 if d == domain or s == domain]
        if not stats:
            ui.fail(f"Not found: {domain}")
            return

    # Totals
    t_total = sum(t for _, _, t, _, _, _, _ in stats)
    t_stubs = sum(st for _, _, _, st, _, _, _ in stats)
    t_real = sum(r for _, _, _, _, r, _, _ in stats)
    t_t1 = sum(t1 for _, _, _, _, _, t1, _ in stats)
    t_t2 = sum(t2 for _, _, _, _, _, _, t2 in stats)

    ui.header("Q U A L I T Y",
              f"{t_real} real / {t_total} total — {t_t1} Tier 1 stubs remaining")

    print(f"  {'Domain':<22s} {'Total':>6s} {'Real':>6s} "
          f"{ui.BOLD}{'T1':>5s}{ui.RESET} {'T2':>5s} {'Real%':>6s}")
    ui.separator()

    for dname, stem, total, stubs, real, t1, t2 in stats:
        rpct = real / max(total, 1) * 100
        if rpct >= 80:
            color = ui.GREEN
        elif rpct >= 20:
            color = ui.YELLOW
        else:
            color = ui.RED
        t1_str = f"{ui.RED}{t1:>5d}{ui.RESET}" if t1 > 0 else f"{ui.GREEN}{'0':>5s}{ui.RESET}"
        print(f"  {dname:<22s} {total:>6d} {color}{real:>6d}{ui.RESET} "
              f"{t1_str} {t2:>5d} {color}{rpct:>5.0f}%{ui.RESET}")

    ui.separator()
    t1_color = ui.RED if t_t1 > 0 else ui.GREEN
    print(f"  {'TOTAL':<22s} {t_total:>6d} {ui.GREEN}{t_real:>6d}{ui.RESET} "
          f"{t1_color}{t_t1:>5d}{ui.RESET} {t_t2:>5d} {t_real / max(t_total,1) * 100:>5.0f}%")
    print()

    print(f"  {ui.BOLD}T1{ui.RESET} = structure/class/inductive/def/abbrev stubs "
          f"(need real types) — {ui.RED}{t_t1}{ui.RESET}")
    print(f"  {ui.BOLD}T2{ui.RESET} = theorem/lemma stubs "
          f"(name reserved, proof optional) — {t_t2}")
    print(f"  {ui.BOLD}Finish line:{ui.RESET} T1 = 0")
    print()

    if domain:
        # Single domain: show detailed T1 stub listing
        for dname, stem, total, stubs, real, t1, t2 in stats:
            if t1 == 0:
                continue
            # Build detailed kind map (with Mathlib file locations)
            mathlib_domain = stem_to_domain.get(stem)
            if not mathlib_domain:
                continue
            detail_map = _build_mathlib_kind_map(mathlib_domain, detailed=True)
            stub_names = _collect_stubs(ORIGIN / f"{stem}.lean")

            # Collect T1 stubs with their Origin line numbers
            origin_path = ORIGIN / f"{stem}.lean"
            origin_lines = origin_path.read_text(errors="replace").split("\n")
            stub_line_map = {}  # normalized_name -> line_number
            for ln, line in enumerate(origin_lines):
                if STUB_RE.match(line):
                    m = ORIGIN_DECL_RE.match(line)
                    if m and "private " not in line:
                        stub_line_map[_normalize_lean_name(m.group(2))] = ln + 1

            # Group T1 stubs by kind
            from collections import defaultdict
            by_kind = defaultdict(list)
            for sname in stub_names:
                info = detail_map.get(sname)
                if not info:
                    continue
                mk, mfile = info
                if mk not in TIER1_KINDS:
                    continue
                origin_ln = stub_line_map.get(sname, 0)
                by_kind[mk].append((sname, mfile, origin_ln))

            if by_kind:
                print(f"  {ui.BOLD}T1 stubs to upgrade:{ui.RESET}")
                print()
                for mk in ["structure", "class", "inductive", "abbrev", "def"]:
                    items = by_kind.get(mk, [])
                    if not items:
                        continue
                    color = ui.MAGENTA if mk in ("structure", "class", "inductive") else ui.YELLOW
                    print(f"  {color}{mk}{ui.RESET} ({len(items)}):")
                    for sname, mfile, origin_ln in items:
                        short_file = mfile.split("/", 1)[-1] if "/" in mfile else mfile
                        ln_str = f":{origin_ln}" if origin_ln else ""
                        print(f"    {sname:<40s} {ui.DIM}{short_file}{ui.RESET}  "
                              f"{ui.DIM}{stem}.lean{ln_str}{ui.RESET}")
                    print()
    else:
        by_t1 = sorted(stats, key=lambda x: x[5], reverse=True)
        needs_work = [(d, t1, r) for d, _, _, _, r, t1, _ in by_t1 if t1 > 0][:5]
        if needs_work:
            print(f"  {ui.BOLD}Most Tier 1 stubs to upgrade:{ui.RESET}")
            for dname, t1, real in needs_work:
                print(f"    {dname:<22s} {ui.RED}{t1:>5d}{ui.RESET} T1 stubs, {real:>4d} real")
            print()


# =============================================================================
# Clean — remove stale stubs that now collide with Core
# =============================================================================

def cmd_clean():
    """Remove stubs from domain files that collide with Core declarations.

    When Core evolves (new classes, theorems, primitives), existing stubs
    in domain files become collisions. This command finds and removes them.
    Core is the foundation — it always wins.
    """
    core_path = ORIGIN / "Core.lean"
    if not core_path.exists():
        ui.fail("Core.lean not found")
        return

    # Collect all Core declaration names (normalized)
    core_names = set()
    for line in core_path.read_text(errors="replace").split("\n"):
        m = ORIGIN_DECL_RE.match(line)
        if m and "private " not in line:
            core_names.add(_normalize_lean_name(m.group(2)))

    skip = {"Core.lean", "Index.lean", "Test.lean", "Physics.lean"}
    total_removed = 0
    files_changed = 0

    for f in sorted(ORIGIN.glob("*.lean")):
        if f.name in skip:
            continue

        lines = f.read_text(errors="replace").split("\n")
        new_lines = []
        removed = []
        i = 0

        while i < len(lines):
            line = lines[i]

            # Check if this is a stub that collides with Core
            if STUB_RE.match(line):
                m = ORIGIN_DECL_RE.match(line)
                if m:
                    norm = _normalize_lean_name(m.group(2))
                    if norm in core_names:
                        # Remove the stub and its docstring
                        if new_lines and new_lines[-1].strip().startswith("/--"):
                            new_lines.pop()
                        removed.append(m.group(2))
                        i += 1
                        continue

            new_lines.append(line)
            i += 1

        if removed:
            # Clean trailing blank lines
            while new_lines and new_lines[-1].strip() == "":
                new_lines.pop()
            new_lines.append("")
            f.write_text("\n".join(new_lines))
            total_removed += len(removed)
            files_changed += 1
            print(f"  {f.stem}: removed {len(removed)} stale stubs")
            for name in removed[:5]:
                print(f"    {ui.DIM}{name}{ui.RESET}")
            if len(removed) > 5:
                ui.info(f"    ... and {len(removed) - 5} more")

    if total_removed == 0:
        ui.ok("No stale stubs found — all clean")
    else:
        print()
        ui.stat("Stubs removed", f"{ui.GREEN}{total_removed}{ui.RESET}")
        ui.stat("Files changed", f"{files_changed}")
        print()


# =============================================================================
# Patterns — find structural patterns that could consolidate to Core
# =============================================================================

def cmd_patterns():
    """Scan Origin files for repeated structural patterns on Option."""
    import re as _re
    from collections import defaultdict

    skip = {"Index.lean", "Test.lean", "Core.lean"}

    # Pattern detectors — each returns list of (decl_name, context_snippet)
    # We scan each def/theorem looking at its body for characteristic patterns.

    # Pattern 1: Predicate lift — match on Option, some => pred, none => False
    pred_lift_re = _re.compile(
        r'\|\s*some\s+\w+\s*=>\s*\w+.*\n\s*\|\s*none\s*=>\s*False')

    # Pattern 2: Binary lift — match on (Option, Option), some/some => some f, _ => none
    binary_lift_re = _re.compile(
        r'\|\s*some\s+\w+\s*,\s*some\s+\w+\s*=>\s*some')

    # Pattern 3: Match-and-absorb — none branch returns none (not in Core.lean)
    absorb_re = _re.compile(
        r'\|\s*(?:none\s*,\s*_|_\s*,\s*none|none)\s*=>\s*none')

    # Pattern 4: Named Option.map wrapper — def foo ... := ... Option.map or .map
    map_wrapper_re = _re.compile(
        r'^\s*(?:def|abbrev)\s+(\S+).*:=\s*(?:Option\.map|\.map)\s')

    # Pattern 5: cases <;> simp pattern — the standard Option proof pattern
    cases_simp_re = _re.compile(
        r'cases\s+\w+\s*<;>\s*(?:cases\s+\w+\s*<;>\s*)?(?:cases\s+\w+\s*<;>\s*)?simp')

    results = {
        'pred_lift': defaultdict(list),     # file -> [decl_names]
        'binary_lift': defaultdict(list),
        'absorb': defaultdict(list),
        'map_wrapper': defaultdict(list),
        'cases_simp': defaultdict(list),
    }

    for f in sorted(ORIGIN.glob("*.lean")):
        if f.name in skip:
            continue
        text = f.read_text(errors="replace")
        fname = f.stem

        # Find all declarations and their bodies
        lines = text.split("\n")
        i = 0
        while i < len(lines):
            m = ORIGIN_DECL_RE.match(lines[i])
            if m and "private " not in lines[i]:
                kind, name = m.group(1), m.group(2)
                # Collect body until next declaration or section marker
                body_lines = [lines[i]]
                j = i + 1
                while j < len(lines):
                    line = lines[j]
                    if (line.strip() == "" and j > i + 1) or "=====" in line:
                        break
                    if ORIGIN_DECL_RE.match(line) and j > i + 1:
                        break
                    body_lines.append(line)
                    j += 1
                body = "\n".join(body_lines)

                # Check patterns
                if pred_lift_re.search(body):
                    results['pred_lift'][fname].append(name)
                if binary_lift_re.search(body):
                    results['binary_lift'][fname].append(name)
                if absorb_re.search(body) and kind in ("def", "abbrev"):
                    results['absorb'][fname].append(name)
                if map_wrapper_re.match(lines[i]):
                    results['map_wrapper'][fname].append(name)
                if cases_simp_re.search(body) and kind in ("theorem", "lemma"):
                    results['cases_simp'][fname].append(name)

                i = j
            else:
                i += 1

    # Display
    ui.header("P A T T E R N S", "Structural patterns that could consolidate to Core")

    patterns = [
        ('pred_lift',
         'Predicate lift (| some a => pred a, | none => False)',
         'Candidate for Core: liftPred'),
        ('binary_lift',
         'Binary lift (| some a, some b => some (f a b), ...)',
         'Already in Core: liftBin₂ — these should use it'),
        ('absorb',
         'Match-and-absorb (none branch returns none)',
         'Already in Core: mul/add instances — check if redundant'),
        ('map_wrapper',
         'Named Option.map wrapper (def foo := Option.map f)',
         'Should use .map directly — eliminate the wrapper'),
        ('cases_simp',
         'cases <;> simp proof pattern',
         'Standard — no consolidation needed, but count is useful'),
    ]

    total_consolidatable = 0
    for key, description, recommendation in patterns:
        data = results[key]
        count = sum(len(v) for v in data.values())
        files = len(data)
        if count == 0:
            continue

        if key in ('pred_lift', 'binary_lift', 'map_wrapper'):
            total_consolidatable += count

        print(f"  {ui.BOLD}{description}{ui.RESET}")
        print(f"  {count} occurrences across {files} files")

        for fname in sorted(data.keys()):
            names = data[fname]
            names_str = ", ".join(names[:5])
            if len(names) > 5:
                names_str += f", ... +{len(names) - 5} more"
            print(f"    {fname}: {names_str}")

        print(f"  {ui.DIM}→ {recommendation}{ui.RESET}")
        print()

    ui.separator()
    print(f"  {ui.BOLD}Consolidatable:{ui.RESET} {total_consolidatable} definitions "
          f"could move to Core or use existing Core primitives")
    print(f"  {ui.BOLD}Core today:{ui.RESET} {sum(1 for _ in (ORIGIN / 'Core.lean').read_text().split(chr(10)) if ORIGIN_DECL_RE.match(_))} declarations in {sum(1 for _ in (ORIGIN / 'Core.lean').read_text().split(chr(10)))} lines")
    print()


# =============================================================================
# Dedup — find duplicate definitions across Origin files
# =============================================================================

def cmd_dedup():
    """Scan all Origin/*.lean files for duplicate definitions."""
    decl_re = re.compile(
        r"^\s*(?:@\[.*?\]\s*)?"
        r"(def|theorem|structure|abbrev|inductive|class)\s+"
        r"(\S+)"
    )

    # Collect all declarations with their bodies
    declarations = []  # (name, kind, file, line, body)

    for lean_file in sorted(ORIGIN.glob("*.lean")):
        lines = lean_file.read_text(errors="replace").split("\n")
        i = 0
        while i < len(lines):
            m = decl_re.match(lines[i])
            if m:
                kind, name = m.group(1), m.group(2)
                # Collect body: from this line until next blank line or next decl
                body_lines = [lines[i]]
                j = i + 1
                while j < len(lines):
                    line = lines[j]
                    if line.strip() == "" or line.startswith("--") and "====" in line:
                        break
                    if decl_re.match(line) and j > i + 1:
                        break
                    body_lines.append(line)
                    j += 1
                body = "\n".join(body_lines).strip()
                declarations.append((name, kind, lean_file.name, i + 1, body))
                i = j
            else:
                i += 1

    ui.header("O R I G I N   D E D U P", "Find duplicate definitions across Origin files")

    # 1. Exact name duplicates
    from collections import defaultdict
    name_groups = defaultdict(list)
    for name, kind, fname, line, body in declarations:
        # Strip namespace prefixes for comparison
        short = name.split(".")[-1]
        name_groups[short].append((name, kind, fname, line, body))

    exact_dupes = {k: v for k, v in name_groups.items() if len(v) > 1}

    if exact_dupes:
        ui.phase("EXACT NAME DUPLICATES", f"{len(exact_dupes)} names appear in multiple files")
        for short, entries in sorted(exact_dupes.items()):
            print(f"\n    {ui.YELLOW}{short}{ui.RESET}")
            for name, kind, fname, line, _ in entries:
                print(f"      {kind:10s} {name:40s} {ui.DIM}{fname}:{line}{ui.RESET}")
    else:
        ui.ok("No exact name duplicates found")

    # 2. Identical bodies (different names, same definition)
    body_groups = defaultdict(list)
    for name, kind, fname, line, body in declarations:
        # Normalize: strip comments, collapse whitespace
        normalized = re.sub(r"--.*", "", body)
        normalized = re.sub(r"/\-.*?\-/", "", normalized, flags=re.DOTALL)
        normalized = " ".join(normalized.split())
        # Remove the declaration name to compare only the body
        normalized = re.sub(r"^(def|theorem|structure|abbrev|inductive|class)\s+\S+", "", normalized)
        normalized = normalized.strip()
        if len(normalized) > 20:  # skip trivial one-liners
            body_groups[normalized].append((name, kind, fname, line))

    body_dupes = {k: v for k, v in body_groups.items() if len(v) > 1}

    print()
    if body_dupes:
        ui.phase("IDENTICAL BODIES", f"{len(body_dupes)} definition bodies appear more than once")
        for body_norm, entries in sorted(body_dupes.items(), key=lambda x: -len(x[1])):
            print(f"\n    {ui.YELLOW}Body appears {len(entries)} times:{ui.RESET}")
            for name, kind, fname, line in entries:
                print(f"      {kind:10s} {name:40s} {ui.DIM}{fname}:{line}{ui.RESET}")
            # Show a snippet of the body
            snippet = body_norm[:80] + ("..." if len(body_norm) > 80 else "")
            print(f"      {ui.DIM}→ {snippet}{ui.RESET}")
    else:
        ui.ok("No identical definition bodies found")

    # Summary
    print()
    ui.separator()
    total = len(declarations)
    ui.stat("Total declarations", f"{total}")
    ui.stat("Unique names", f"{len(name_groups)}")
    ui.stat("Name duplicates", f"{ui.YELLOW}{len(exact_dupes)}{ui.RESET}" if exact_dupes else "0")
    ui.stat("Body duplicates", f"{ui.YELLOW}{len(body_dupes)}{ui.RESET}" if body_dupes else "0")
    print()


# =============================================================================
# Index — auto-generate Origin/Index.lean
# =============================================================================

def cmd_index():
    """Generate Origin/Index.lean — one import, all declarations.

    Reads all Origin/*.lean files, extracts every exported declaration,
    writes an index that re-exports everything. If two files export
    the same name, lake build fails — the compiler IS the dedup.
    """
    decl_re = ORIGIN_DECL_RE

    # Skip files that shouldn't be in the index
    skip = {"Index", "Test"}

    # Collect declarations per file
    modules = {}  # stem -> list of (kind, name)
    for f in sorted(ORIGIN.glob("*.lean")):
        if f.stem in skip:
            continue
        names = []
        for line in f.read_text(errors="replace").split("\n"):
            m = decl_re.match(line)
            if m:
                kind, name = m.group(1), m.group(2)
                # Skip private declarations and @[simp] only theorems
                if "private " in line:
                    continue
                names.append((kind, name))
        if names:
            modules[f.stem] = names

    # Check for name collisions before writing
    # Normalize guillemets: «foo'» and foo' are the same to Lean
    all_names = {}  # normalized_name -> (module, kind)
    collisions = []
    for mod, decls in modules.items():
        for kind, name in decls:
            norm = _normalize_lean_name(name)
            if norm in all_names:
                other_mod, other_kind = all_names[norm]
                if other_mod != mod:
                    collisions.append((name, mod, other_mod))
            else:
                all_names[norm] = (mod, kind)

    if collisions:
        ui.header("I N D E X   E R R O R", "Duplicate names — fix before index can build")
        for name, mod1, mod2 in collisions:
            ui.fail(f"`{name}` in both {mod1}.lean and {mod2}.lean")
        print()
        ui.info(f"{len(collisions)} collisions. Fix these first, then run index again.")
        print()
        return False

    # Generate the index file
    total = sum(len(v) for v in modules.values())
    lines = []
    lines.append("/-")
    lines.append("Auto-generated by: python3 scripts/origin.py index")
    lines.append(f"Total: {total} declarations from {len(modules)} files")
    lines.append("Do not edit manually. Regenerate after any change.")
    lines.append("-/")
    lines.append("")

    # Import all modules
    for mod in sorted(modules.keys()):
        # Handle the "2" suffix naming
        lean_name = mod
        lines.append(f"import Origin.{lean_name}")

    lines.append("")

    index_path = ORIGIN / "Index.lean"
    index_path.write_text("\n".join(lines))

    ui.header("O R I G I N   I N D E X", f"{total} declarations from {len(modules)} files")
    for mod in sorted(modules.keys()):
        count = len(modules[mod])
        print(f"    {ui.GREEN}✓{ui.RESET} Origin.{mod:<28s} {count:>3} declarations")
    ui.separator()
    ui.stat("Total declarations", f"{total}")
    ui.stat("Index file", str(index_path), "cyan")
    ui.info("Run: lake build Origin.Index")
    print()
    return True


# =============================================================================
# Show — display the Mathlib original for a stub name
# =============================================================================

def cmd_show(name):
    """Show the Mathlib original declaration for a given Origin stub name.

    Searches all extracted domains for the Mathlib declaration that
    corresponds to the stub. Prints the full declaration with surrounding
    context so the session can see exactly what the Origin version needs.
    """
    # Strip trailing ' to get the Mathlib name stem
    stem = name.rstrip("'")
    if name.startswith('«') and name.endswith('»'):
        stem = name[1:-1].rstrip("'")

    mathlib_decl_re = re.compile(
        r'^(?:.*?)?(private\s+|protected\s+)?(noncomputable\s+)?'
        r'(theorem|lemma|def|structure|class|instance|abbrev|inductive)\s+(\S+)')

    found = []

    for domain_dir in sorted(EXTRACTED.iterdir()):
        if not domain_dir.is_dir() or not domain_dir.name.startswith("Mathlib_"):
            continue
        for f in sorted(domain_dir.rglob("*.lean")):
            text = f.read_text(errors="replace")
            lines = text.split("\n")
            for i, line in enumerate(lines):
                m = mathlib_decl_re.match(line.strip())
                if m:
                    decl_name = m.group(4)
                    # Match: the last component of the Mathlib name equals our stem
                    mathlib_stem = decl_name.split(".")[-1]
                    if mathlib_stem == stem:
                        kind = m.group(3)
                        fname = str(f.relative_to(EXTRACTED))
                        # Collect the declaration body (up to next blank line or next decl)
                        body_lines = []
                        j = i
                        while j < len(lines):
                            body_lines.append(lines[j])
                            j += 1
                            if j < len(lines):
                                next_line = lines[j].strip()
                                # Stop at blank line after we have some content
                                if next_line == "" and j > i + 1:
                                    break
                                # Stop at next top-level declaration
                                if j > i + 1 and mathlib_decl_re.match(next_line):
                                    break
                                # Stop at section markers
                                if next_line.startswith("end ") or next_line.startswith("section"):
                                    break
                            # Cap at 30 lines
                            if j - i > 30:
                                body_lines.append("  ...")
                                break
                        found.append((kind, decl_name, fname, i + 1, "\n".join(body_lines)))

    if not found:
        ui.fail(f"No Mathlib declaration found matching '{stem}'")
        ui.info(f"Searched for last component == '{stem}' across all extracted domains")
        return

    ui.header("S H O W", f"Mathlib original for '{name}'")

    for kind, decl_name, fname, line_num, body in found:
        short_file = fname.split("/", 1)[-1] if "/" in fname else fname
        print(f"  {ui.BOLD}{kind}{ui.RESET} {ui.CYAN}{decl_name}{ui.RESET}")
        print(f"  {ui.DIM}{short_file}:{line_num}{ui.RESET}")
        print()
        for bline in body.split("\n"):
            print(f"    {bline}")
        print()
        ui.separator()

    if len(found) > 1:
        ui.info(f"{len(found)} matches found — the stub may correspond to any of these")
    print()


# =============================================================================
# Unused — find declarations that nothing references
# =============================================================================

def cmd_unused():
    """Find declarations that are never referenced by any other declaration.

    Scans all Origin files, collects every declaration name, then checks
    which names never appear in any other declaration's body. These are
    candidates for removal — they don't earn their weight.

    Excludes: @[simp] declarations (used invisibly by simp),
    Core.lean (foundation — everything references it implicitly),
    structures/classes (used by typeclass resolution),
    instances (used by typeclass resolution).
    """
    skip = {"Index", "Test"}

    decl_re = ORIGIN_DECL_RE

    # Pass 1: collect all declarations with their bodies
    all_decls = {}  # name -> (kind, file, line, body_text)
    all_bodies = []  # (file, full_text) for searching

    for f in sorted(ORIGIN.glob("*.lean")):
        if f.stem in skip:
            continue
        text = f.read_text(errors="replace")
        all_bodies.append((f.stem, text))
        lines = text.split("\n")
        i = 0
        while i < len(lines):
            m = decl_re.match(lines[i])
            if m and "private " not in lines[i]:
                kind, name = m.group(1), m.group(2)
                # Collect body
                body_lines = [lines[i]]
                j = i + 1
                while j < len(lines):
                    line = lines[j]
                    if line.strip() == "" or "=====" in line:
                        break
                    if decl_re.match(line) and j > i + 1:
                        break
                    body_lines.append(line)
                    j += 1
                body = "\n".join(body_lines)
                # Skip @[simp] — invisible dependencies
                if "@[simp]" in lines[i] or (i > 0 and "@[simp]" in lines[i-1]):
                    i = j
                    continue
                all_decls[name] = (kind, f.stem, i + 1, body)
                i = j
            else:
                i += 1

    # Pass 2: for each declaration, check if its name appears in any other body
    unused = []
    for name, (kind, fname, line, body) in all_decls.items():
        # Skip kinds that are used implicitly
        if kind in ("structure", "class", "inductive", "instance"):
            continue
        # Skip Core — everything depends on it implicitly
        if fname == "Core":
            continue
        # Check if name appears in any other declaration's body
        short = name.split(".")[-1]
        found = False
        for other_name, (_, _, _, other_body) in all_decls.items():
            if other_name == name:
                continue
            if short in other_body:
                found = True
                break
        if not found:
            # Also check if it appears anywhere in any file body (theorems reference defs)
            for _, file_text in all_bodies:
                # Count occurrences — at least 2 means it's defined + referenced
                count = file_text.count(short)
                if count >= 2:
                    found = True
                    break
        if not found:
            unused.append((name, kind, fname, line))

    # Display
    ui.header("U N U S E D", f"{len(unused)} declarations with no references")

    if not unused:
        ui.ok("Every declaration is referenced by at least one other")
        print()
        return

    # Group by file
    from collections import defaultdict
    by_file = defaultdict(list)
    for name, kind, fname, line in unused:
        by_file[fname].append((name, kind, line))

    for fname in sorted(by_file.keys()):
        items = by_file[fname]
        print(f"  {ui.BOLD}{fname}.lean{ui.RESET} ({len(items)} unused):")
        for name, kind, line in sorted(items, key=lambda x: x[2]):
            print(f"    {kind:10s} {name:45s} :{line}")
        print()

    ui.separator()
    ui.stat("Total unused", f"{ui.YELLOW}{len(unused)}{ui.RESET}")
    ui.stat("Total declarations", f"{len(all_decls)}")
    pct = len(unused) / max(len(all_decls), 1) * 100
    ui.stat("Unused %", f"{pct:.0f}%")
    print()


# =============================================================================
# Main
# =============================================================================

def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return

    cmd = sys.argv[1]

    if cmd == "status":
        cmd_status()
    elif cmd == "index":
        cmd_index()
    elif cmd == "dedup":
        cmd_dedup()
    elif cmd == "list":
        cmd_list()
    elif cmd == "audit":
        if len(sys.argv) > 2:
            cmd_audit(sys.argv[2])
        else:
            print("Usage: origin.py audit <DOMAIN> | --all")
    elif cmd == "generate":
        if len(sys.argv) > 2:
            cmd_generate(sys.argv[2])
        else:
            print("Usage: origin.py generate <DOMAIN>")
    elif cmd == "classify":
        if len(sys.argv) > 2:
            cmd_classify(sys.argv[2])
        else:
            print("Usage: origin.py classify <DOMAIN>")
    elif cmd == "suggest":
        if len(sys.argv) > 2:
            cmd_suggest(sys.argv[2])
        else:
            print("Usage: origin.py suggest <DOMAIN>")
    elif cmd == "stub":
        if len(sys.argv) > 2:
            cmd_stub(sys.argv[2])
        else:
            print("Usage: origin.py stub <DOMAIN>")
    elif cmd == "quality":
        if len(sys.argv) > 2:
            cmd_quality(sys.argv[2])
        else:
            cmd_quality()
    elif cmd == "show":
        if len(sys.argv) > 2:
            cmd_show(sys.argv[2])
        else:
            print("Usage: origin.py show <NAME>")
    elif cmd == "unused":
        cmd_unused()
    elif cmd == "patterns":
        cmd_patterns()
    elif cmd == "clean":
        cmd_clean()
    else:
        print(f"Unknown command: {cmd}")
        print(__doc__)


if __name__ == "__main__":
    main()
