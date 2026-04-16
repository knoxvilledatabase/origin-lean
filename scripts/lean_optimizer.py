#!/usr/bin/env python3
"""
Lean Proof Optimizer — generic tool for compressing Lean proofs.

Takes any Lean project and makes every proof as short as possible,
verified by lake build. Project-specific rules (like Origin's 17
dissolved typeclasses) are configuration, not code.

Usage:
    python3 scripts/lean_optimizer.py audit <domain>          DRY audit
    python3 scripts/lean_optimizer.py audit --all             all domains
    python3 scripts/lean_optimizer.py compress <domain>       compress domain
    python3 scripts/lean_optimizer.py generate <domain>       GENERATE ORIGIN DRAFT
    python3 scripts/lean_optimizer.py classify <domain>       classify declarations

Architecture:
    Generic Lean Optimizer (Axis 2 — works on any Lean project)
      + Config (Axis 1 — dissolution rules, project-specific)
      = Origin pipeline
"""

import re
import sys
import shutil
import subprocess
from pathlib import Path
from dataclasses import dataclass, field
from collections import Counter


# =============================================================================
# UI — production terminal output
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
    CLEAR   = "\033[2K\r"

    def __init__(self):
        self.W = shutil.get_terminal_size((80, 24)).columns

    def bar(self, current, total, width=30):
        filled = int(width * current / total) if total else 0
        return f"{self.GREEN}{'█' * filled}{self.DIM}{'░' * (width - filled)}{self.RESET}"

    def header(self):
        W = self.W
        print()
        print(f"  {self.BOLD}{self.CYAN}╔{'═' * (W - 6)}╗{self.RESET}")
        print(f"  {self.BOLD}{self.CYAN}║{self.RESET}  {self.BOLD}{self.WHITE}L E A N   O P T I M I Z E R{self.RESET}"
              f"{' ' * max(1, W - 38)}{self.BOLD}{self.CYAN}║{self.RESET}")
        print(f"  {self.BOLD}{self.CYAN}║{self.RESET}  {self.DIM}generic proof optimizer  ·  config-driven  ·  lake build verifies{self.RESET}"
              f"{' ' * max(1, W - 74)}{self.BOLD}{self.CYAN}║{self.RESET}")
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

    def domain_line(self, idx, total, domain, files, genuine, dissolved):
        gen = f"{self.GREEN}{genuine:,}{self.RESET}" if genuine else f"{self.DIM}0{self.RESET}"
        dis = f"{self.YELLOW}{dissolved:,}{self.RESET}" if dissolved else f"{self.DIM}0{self.RESET}"
        print(f"  {self.bar(idx, total)} "
              f"{self.BOLD}{domain:<24}{self.RESET} "
              f"{files:>4} files  {gen:>5} genuine  {dis:>4} dissolved")


ui = UI()


# =============================================================================
# Configuration — everything project-specific lives here
# =============================================================================

@dataclass
class ProjectConfig:
    """All project-specific settings. No hardcoded paths or patterns."""

    # Paths
    source_dir: Path = field(default_factory=Path)
    output_dir: Path = field(default_factory=Path)
    project_root: Path = field(default_factory=Path)

    # Axis 1: Dissolution rules — patterns that identify infrastructure
    # Each rule: {"pattern": regex_string, "scope": "signature"|"name"|"file", "label": str}
    dissolution_rules: list[dict] = field(default_factory=list)

    # Conflation rules — patterns that identify ground=zero assumptions
    conflation_rules: list[dict] = field(default_factory=list)

    # File-level skip patterns — entire files that are infrastructure
    skip_file_patterns: list[str] = field(default_factory=list)

    # Import substitutions — what to strip, what to add
    strip_imports: list[str] = field(default_factory=list)
    add_imports: list[str] = field(default_factory=list)

    # Tactic priority for compression (Axis 2)
    tactics: list[str] = field(default_factory=lambda: [
        "by simp", "by omega", "by ring", "by decide",
        "by aesop", "by norm_num", "by tauto",
    ])

    # Commands to strip from source (project-specific boilerplate)
    strip_commands: list[str] = field(default_factory=list)

    # Commands to pass through (must be preserved)
    passthrough_commands: list[str] = field(default_factory=list)

    # Attributes that create invisible dependencies — never compress
    protected_attributes: list[str] = field(default_factory=lambda: [
        "@[simp", "@[ext", "@[aesop", "@[norm_cast", "@[norm_num",
        "@[gcongr", "@[positivity", "@[to_additive",
    ])


def origin_config() -> ProjectConfig:
    """The Origin project configuration — Mathlib to Origin."""
    root = Path(__file__).parent.parent
    lake_mathlib = root / ".lake/packages/mathlib/Mathlib"
    origin_mathlib = Path(root).parent / "origin-mathlib/Mathlib"
    source = lake_mathlib if lake_mathlib.exists() else origin_mathlib

    return ProjectConfig(
        source_dir=source,
        output_dir=root / "extracted",  # Mathlib_* dirs in extracted/
        project_root=root,

        dissolution_rules=[
            # Infrastructure typeclasses in signatures
            {"pattern": r"\bNeZero\b", "scope": "signature", "label": "zero-management"},
            {"pattern": r"\bGroupWithZero\b", "scope": "signature", "label": "zero-management"},
            # Declaration names that ARE infrastructure
            {"pattern": r"^ne_zero$|^NeZero|^neZero|^ne_one$", "scope": "name", "label": "zero-management"},
            {"pattern": r"GroupWithZero|groupWithZero", "scope": "name", "label": "zero-management"},
            {"pattern": r"NoZeroDivisors|noZeroDivisors", "scope": "name", "label": "zero-management"},
            {"pattern": r"NoZeroSMulDivisors", "scope": "name", "label": "zero-management"},
            {"pattern": r"MulZeroClass|mulZeroClass", "scope": "name", "label": "zero-management"},
            {"pattern": r"not_isUnit_zero", "scope": "name", "label": "zero-management"},
            {"pattern": r"^zero_mul$|^mul_zero$|^zero_div$|^div_zero$", "scope": "name", "label": "zero-management"},
            {"pattern": r"^inv_zero$|^zero_inv$", "scope": "name", "label": "zero-management"},
            {"pattern": r"WithZero|withZero", "scope": "name", "label": "zero-management"},
            {"pattern": r"^ZeroHom$|^zeroHom$", "scope": "name", "label": "zero-management"},
        ],

        conflation_rules=[
            {"pattern": r"MulZeroClass\b|mulZeroClass\b", "label": "ground=zero"},
            {"pattern": r"zero_ne_one|one_ne_zero", "label": "ground=zero"},
            {"pattern": r"nontrivial|Nontrivial", "label": "ground=zero"},
        ],

        skip_file_patterns=[
            "GroupWithZero", "NeZero", "NoZeroDivisors", "NoZeroSMul",
            "MulZeroClass", "WithZero", "WithBot", "WithTop",
            "ZeroHom", "Deprecated",
        ],

        strip_imports=["Mathlib.Algebra.GroupWithZero"],

        add_imports=["import Origin.Core"],

        strip_commands=[
            "add_decl_doc ", "assert_not_exists ", "suppress_compilation",
            "#align", "#guard_msgs", "#check", "#print",
            "@[deprecated",
            "-- Adaptation note", "-- adaptation_note", "#adaptation_note",
            "library_note ", 'library_note"',
        ],

        passthrough_commands=[
            "set_option ", "attribute ", "alias ", "include ",
            "omit ", "universe ", "local ", "scoped ",
            "example ", "example",
            "notation ", "infixl ", "infixr ", "prefix ", "postfix ",
            "macro_rules", "macro ", "syntax ", "elab ",
        ],
    )


# =============================================================================
# Classifier — config-driven rule engine
# =============================================================================

class Classifier:
    """Classifies declarations using config-driven rules."""

    TRIVIAL_RE = re.compile(
        r":=\s*(rfl|h\b|by\s+simp\s*$|by\s+rfl|by\s+exact\s+\w+\s*$|Iff\.rfl)")
    BARE_NEZ = re.compile(r"≠\s*0")

    def __init__(self, config: ProjectConfig):
        self.config = config
        # Compile dissolution rules by scope
        self._sig_rules = []
        self._name_rules = []
        self._name_all = []  # combined name patterns for bare ≠ 0 check
        for rule in config.dissolution_rules:
            compiled = re.compile(rule["pattern"])
            if rule["scope"] == "signature":
                self._sig_rules.append((compiled, rule["label"]))
            elif rule["scope"] == "name":
                self._name_rules.append((compiled, rule["label"]))
                self._name_all.append(compiled)
        # Compile conflation rules
        self._conflation_rules = [
            (re.compile(rule["pattern"]), rule["label"])
            for rule in config.conflation_rules
        ]

    def is_skip_file(self, filepath: Path) -> bool:
        return any(pat in str(filepath) for pat in self.config.skip_file_patterns)

    def is_infra_name(self, name: str) -> bool:
        return any(r.search(name) for r in self._name_all)

    def classify(self, kind: str, name: str, full_text: str) -> str:
        """Classify a declaration using config rules."""
        sig_part = full_text.split(":=")[0] if ":=" in full_text else full_text

        if kind == "instance":
            return "instance"

        # Check name-based dissolution
        for regex, label in self._name_rules:
            if regex.search(name):
                return "infra_name"

        # Check signature-based dissolution
        for regex, label in self._sig_rules:
            if regex.search(sig_part):
                return "dissolves"

        # Bare ≠ 0 only dissolves if name is also infrastructure
        if self.BARE_NEZ.search(sig_part) and self.is_infra_name(name):
            return "dissolves"

        # Conflation check
        for regex, label in self._conflation_rules:
            if regex.search(sig_part):
                return "conflates"

        # Trivial proof detection
        if self.TRIVIAL_RE.search(full_text) and kind in ("theorem", "lemma"):
            return "simp_trivial" if "@[simp]" in full_text else "trivial"

        return "genuine"


# =============================================================================
# DRY Audit — generic, works on any Lean files
# =============================================================================

def cmd_audit(path: str, config: ProjectConfig):
    """Audit Lean files for DRY compression opportunities."""
    output_dir = config.output_dir

    if path == "--all":
        ui.header()
        domains = sorted(d.name.replace("Mathlib_", "")
                         for d in output_dir.iterdir()
                         if d.is_dir() and d.name.startswith("Mathlib_"))
        all_stats = []
        for dom in domains:
            stats = _audit_domain(dom, config)
            if stats:
                all_stats.append((dom, stats))

        # Print summary
        if all_stats:
            t_files = sum(s["files"] for _, s in all_stats)
            t_lines = sum(s["lines"] for _, s in all_stats)
            t_genuine = sum(s["genuine"] for _, s in all_stats)
            t_dissolved = sum(s["dissolved"] for _, s in all_stats)
            t_trivial = sum(s["rfl"] + s["iff_rfl"] + s["by_simp"] + s["by_rfl"] + s["by_norm_num"] for _, s in all_stats)
            t_multi_rw = sum(s["multi_rw"] for _, s in all_stats)
            t_spec = sum(s["spec"] for _, s in all_stats)
            t_rw = sum(s["rw"] for _, s in all_stats)

            # Count Origin lines
            origin_dir = config.project_root / "Origin"
            origin_lines = sum(len(f.read_text().split("\n")) for f in origin_dir.glob("*.lean"))

            print()
            print(f"  {ui.BOLD}{ui.CYAN}╔{'═' * (ui.W - 6)}╗{ui.RESET}")
            print(f"  {ui.BOLD}{ui.CYAN}║{ui.RESET}  {ui.BOLD}{ui.WHITE}TOTAL ACROSS ALL DOMAINS{ui.RESET}"
                  f"{' ' * max(1, ui.W - 34)}{ui.BOLD}{ui.CYAN}║{ui.RESET}")
            print(f"  {ui.BOLD}{ui.CYAN}╚{'═' * (ui.W - 6)}╝{ui.RESET}")
            ui.stat("Domains", f"{len(all_stats)}")
            ui.stat("Files", f"{t_files:,}")
            ui.stat("Lines", f"{t_lines:,}", "yellow")
            ui.stat("Genuine", f"{t_genuine:,}", "green")
            ui.stat("Dissolved", f"{t_dissolved}", "yellow")
            ui.stat("Trivial proofs", f"{t_trivial:,}")
            ui.stat("Multi-line rw", f"{t_multi_rw:,}", "red")
            ui.stat("rw total", f"{t_rw:,}", "yellow")
            ui.stat("Specializations", f"{t_spec}")
            print()
            ui.stat("Origin/", f"{origin_lines:,} lines", "cyan")
            ui.separator()
            print(f"\n  {ui.BOLD}Next:{ui.RESET} python3 scripts/lean_optimizer.py compress Combinatorics")
    else:
        # Could be a domain name or a file path
        d = output_dir / f"Mathlib_{path}"
        if d.exists():
            _audit_domain(path, config)
        elif Path(path).exists():
            _audit_file(Path(path), config)
        else:
            print(f"  ✗ Not found: {path}")


def _audit_domain(domain: str, config: ProjectConfig) -> dict | None:
    """Audit a single domain. Returns stats dict."""
    d = config.output_dir / f"Mathlib_{domain}"
    files = list(d.rglob("*.lean"))
    if not files:
        return None

    stats = _audit_files(files)

    # Check for sketch
    sketch_lines = 0
    origin_dir = config.project_root / "Origin"
    for name in [f"{domain}.lean", f"{domain}2.lean"]:
        sc = origin_dir / name
        if sc.exists():
            sketch_lines = len(sc.read_text().split("\n"))
            break

    _print_audit(domain, stats, sketch_lines)
    return stats


def _audit_file(filepath: Path, config: ProjectConfig):
    """Audit a single file."""
    stats = _audit_files([filepath])
    _print_audit(filepath.name, stats, 0)


def _audit_files(files: list[Path]) -> dict:
    """Collect DRY stats across a list of files."""
    s = {
        "files": len(files), "lines": 0,
        "genuine": 0, "dissolved": 0, "conflates": 0, "infra": 0,
        "rfl": 0, "iff_rfl": 0, "by_simp": 0, "by_rfl": 0,
        "by_norm_num": 0, "by_omega_s": 0, "by_decide_s": 0, "by_exact": 0,
        "rw": 0, "simp": 0, "exact": 0, "omega": 0, "ring": 0,
        "aesop": 0, "decide": 0, "linarith": 0,
        "multi_rw": 0, "spec": 0,
    }

    patterns = {
        "rfl": re.compile(r':=\s+rfl\s*$'),
        "iff_rfl": re.compile(r':=\s+Iff\.rfl\s*$'),
        "by_simp": re.compile(r'by\s+simp\s*$'),
        "by_rfl": re.compile(r'by\s+rfl\s*$'),
        "by_norm_num": re.compile(r'by\s+norm_num\s*$'),
        "by_omega_s": re.compile(r'by\s+omega\s*$'),
        "by_decide_s": re.compile(r'by\s+decide\s*$'),
        "by_exact": re.compile(r'by\s+exact\s+\S+\s*$'),
        "multi_rw": re.compile(r'rw\s*\[.*,.*,.*\]'),
        "spec": re.compile(r'^(?:theorem|lemma|def|abbrev)\s+\w+_(?:nat|int|real|fin)\b'),
    }
    tactic_res = {
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
                if m:
                    s[key] += int(m.group(1))

        for line in lines:
            for key, pat in patterns.items():
                if pat.search(line):
                    s[key] += 1
            for key, pat in tactic_res.items():
                s[key] += len(pat.findall(line))

    return s


def _print_audit(name: str, s: dict, sketch_lines: int):
    """Print audit results with production UI."""
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
    ui.stat("  rfl", f"{s['rfl']}")
    ui.stat("  Iff.rfl", f"{s['iff_rfl']}")
    ui.stat("  by simp", f"{s['by_simp']}")
    ui.stat("  by rfl", f"{s['by_rfl']}")
    ui.stat("  by norm_num", f"{s['by_norm_num']}")
    ui.stat("  by exact <term>", f"{s['by_exact']}")
    ui.stat("  by omega", f"{s['by_omega_s']}")
    ui.stat("  by decide", f"{s['by_decide_s']}")
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
# Compress — sandbox-based proof compression
# =============================================================================

def cmd_compress(path: str, config: ProjectConfig):
    """Compress files by trying shorter proofs. Max 7 builds per file."""
    sys.path.insert(0, str(Path(__file__).parent))
    from compress.proof_tester import compress_file

    output_dir = config.output_dir

    if path.startswith("--domain"):
        return  # handled by main()

    # Single file or domain
    d = output_dir / f"Mathlib_{path}"
    if d.exists() and d.is_dir():
        files = sorted(d.rglob("*.lean"))
    elif Path(path).exists():
        files = [Path(path).resolve()]
    else:
        print(f"  {ui.RED}✗{ui.RESET} Not found: {path}")
        return

    ui.header()
    ui.phase("COMPRESS", f"{len(files)} files")

    total_files = 0
    files_improved = 0
    total_compressed = 0
    total_lines_saved = 0

    for idx, f in enumerate(files):
        total_files += 1
        original_lines = len(f.read_text(errors="replace").split("\n"))

        results = compress_file(f, config.tactics, config.protected_attributes)

        if results:
            files_improved += 1
            total_compressed += len(results)
            new_lines = len(f.read_text(errors="replace").split("\n"))
            saved = original_lines - new_lines
            total_lines_saved += saved
            short = str(f.relative_to(config.project_root))
            ui.ok(f"{short}: {len(results)} compressed, {saved} lines saved")
            for r in results:
                print(f"      {ui.DIM}{r['name']} → {r['tactic']}{ui.RESET}")
        elif idx < 5 or (idx + 1) % 20 == 0:
            # Show progress for first few files and periodically
            short = str(f.relative_to(config.project_root))
            ui.info(f"{short}: no compressions found")

    ui.separator()
    ui.phase("RESULTS")
    ui.stat("Files scanned", f"{total_files}")
    ui.stat("Files improved", f"{files_improved}", "green" if files_improved else "")
    ui.stat("Declarations compressed", f"{total_compressed}", "green" if total_compressed else "")
    ui.stat("Lines saved", f"{total_lines_saved}", "cyan" if total_lines_saved else "")


# =============================================================================
# Classify — show classification for a file or domain
# =============================================================================

def cmd_classify(path: str, config: ProjectConfig):
    """Classify declarations in a file."""
    classifier = Classifier(config)

    if Path(path).is_file():
        _classify_file(Path(path), classifier)
    else:
        d = config.output_dir / f"Mathlib_{path}"
        if d.exists():
            for f in sorted(d.rglob("*.lean"))[:5]:
                _classify_file(f, classifier)
                print()


def _classify_file(filepath: Path, classifier: Classifier):
    """Classify and print declarations in one file."""
    text = filepath.read_text(errors="replace")
    decl_re = re.compile(
        r'^(?:.*?)?(private\s+|protected\s+)?(noncomputable\s+)?'
        r'(theorem|lemma|def|structure|class|instance|abbrev|inductive)\s+(\S+)')

    print(f"  {filepath.name}:")
    for line in text.split("\n"):
        m = decl_re.match(line.strip())
        if m:
            kind = m.group(3)
            name = m.group(4)
            # Get a few lines of context for classification
            idx = text.find(line)
            context = text[idx:idx + 500]
            label = classifier.classify(kind, name, context)
            marker = {"genuine": "  ", "dissolves": "✗ ", "conflates": "~ ",
                       "infra_name": "✗ ", "instance": "  ", "trivial": "△ ",
                       "simp_trivial": "△ "}.get(label, "  ")
            print(f"    {marker}{kind:10s} {name:40s} [{label}]")


# =============================================================================
# Main
# =============================================================================

def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return

    # Load config — default is Origin's Mathlib config
    config = origin_config()

    cmd = sys.argv[1]

    if cmd == "audit":
        if len(sys.argv) > 2:
            cmd_audit(sys.argv[2], config)
        else:
            print("Usage: origin3.py audit <DOMAIN|path> | --all")
    elif cmd == "compress":
        if len(sys.argv) > 2 and sys.argv[2] == "--domain":
            if len(sys.argv) > 3:
                cmd_compress(sys.argv[3], config)
            else:
                print("Usage: origin3.py compress --domain <DOMAIN>")
        elif len(sys.argv) > 2:
            cmd_compress(sys.argv[2], config)
        else:
            print("Usage: origin3.py compress <DOMAIN|path> | --domain <DOMAIN>")
    elif cmd == "generate":
        if len(sys.argv) > 2:
            sys.path.insert(0, str(Path(__file__).parent))
            from compress.generator import cmd_generate
            cmd_generate(sys.argv[2], config.output_dir, config.project_root / "Origin")
        else:
            print("Usage: lean_optimizer.py generate <DOMAIN>")
    elif cmd == "classify":
        if len(sys.argv) > 2:
            cmd_classify(sys.argv[2], config)
        else:
            print("Usage: lean_optimizer.py classify <DOMAIN|path>")
    else:
        print(f"Unknown command: {cmd}")
        print(__doc__)


if __name__ == "__main__":
    main()
