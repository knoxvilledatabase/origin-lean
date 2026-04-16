#!/usr/bin/env python3
"""
Origin — the toolkit for building Origin from Mathlib.

Usage:
    python3 scripts/origin.py status                 PROGRESS REPORT
    python3 scripts/origin.py dedup                  find duplicate definitions across Origin
    python3 scripts/origin.py list                  show all domains
    python3 scripts/origin.py audit <domain>        DRY audit one domain
    python3 scripts/origin.py audit --all           DRY audit all domains
    python3 scripts/origin.py generate <domain>     draft Origin file from Mathlib
    python3 scripts/origin.py classify <domain>     classify declarations
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
    """Show Origin vs Mathlib line counts for every domain."""
    domains = sorted(d.name.replace("Mathlib_", "")
                     for d in EXTRACTED.iterdir()
                     if d.is_dir() and d.name.startswith("Mathlib_")
                     and d.name.replace("Mathlib_", "") not in SKIP_DOMAINS)

    ui.header("O R I G I N   S T A T U S", "Origin vs Mathlib — every domain at a glance")

    total_mathlib = 0
    total_origin = 0
    total_genuine = 0
    rows = []

    for dom in domains:
        # Mathlib lines and genuine count
        mathlib_dir = EXTRACTED / f"Mathlib_{dom}"
        mathlib_lines = 0
        genuine = 0
        for f in mathlib_dir.rglob("*.lean"):
            text = f.read_text(errors="replace")
            mathlib_lines += len(text.split("\n"))
            for line in text.split("\n")[:5]:
                m = re.search(r'Genuine:\s*(\d+)', line)
                if m:
                    genuine += int(m.group(1))

        # Origin lines
        origin_lines = 0
        for name in [f"{dom}.lean", f"{dom}2.lean"]:
            p = ORIGIN / name
            if p.exists():
                origin_lines = len(p.read_text().split("\n"))
                break

        total_mathlib += mathlib_lines
        total_origin += origin_lines
        total_genuine += genuine

        pct = (1 - origin_lines / max(mathlib_lines, 1)) * 100 if mathlib_lines else 0
        rows.append((dom, mathlib_lines, genuine, origin_lines, pct))

    # Print table
    print(f"  {ui.BOLD}{'Domain':<24s} {'Mathlib':>10s} {'Genuine':>8s} {'Origin':>8s} {'Reduction':>10s}{ui.RESET}")
    ui.separator()

    for dom, ml, gen, ol, pct in rows:
        # Color code: green if deep (origin > 200), yellow if sketch, dim if minimal
        if ol > 200:
            color = ui.GREEN
        elif ol > 100:
            color = ui.YELLOW
        else:
            color = ui.DIM
        print(f"  {dom:<24s} {ml:>10,} {gen:>8,} {color}{ol:>8,}{ui.RESET} {pct:>9.1f}%")

    ui.separator()
    total_pct = (1 - total_origin / max(total_mathlib, 1)) * 100
    print(f"  {ui.BOLD}{'TOTAL':<24s} {total_mathlib:>10,} {total_genuine:>8,} {ui.CYAN}{total_origin:>8,}{ui.RESET} {total_pct:>9.1f}%{ui.RESET}")
    print()
    ui.info(f"Green = deepened (>200 lines)  Yellow = sketch (100-200)  Dim = minimal (<100)")
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
# Main
# =============================================================================

def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return

    cmd = sys.argv[1]

    if cmd == "status":
        cmd_status()
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
    else:
        print(f"Unknown command: {cmd}")
        print(__doc__)


if __name__ == "__main__":
    main()
