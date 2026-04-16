#!/usr/bin/env python3
"""
Origin v3: Generic Lean proof optimizer.

A general-purpose tool that takes any Lean project and makes every proof
as short as possible, verified by lake build. Project-specific rules
(like Origin's 17 dissolved typeclasses) are configuration, not code.

Usage:
    python3 scripts/origin3.py audit <path>               DRY audit
    python3 scripts/origin3.py audit --all                all domains
    python3 scripts/origin3.py compress <path>            compress one file
    python3 scripts/origin3.py compress --domain <name>   compress domain
    python3 scripts/origin3.py classify <path>            classify declarations

Config: reads from origin3_config.py in the same directory, or uses
defaults for Origin's Mathlib configuration.

Architecture:
    Generic Lean Optimizer (Axis 2 — works on any Lean project)
      + Config (Axis 1 — dissolution rules, project-specific)
      = Origin pipeline

See origin2.py for the Mathlib-specific reference implementation.
"""

import re
import sys
import subprocess
from pathlib import Path
from dataclasses import dataclass, field
from collections import Counter


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
        output_dir=root / "Origin",
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
        domains = sorted(d.name.replace("Mathlib_", "")
                         for d in output_dir.iterdir()
                         if d.is_dir() and d.name.startswith("Mathlib_"))
        for dom in domains:
            _audit_domain(dom, config)
    else:
        # Could be a domain name or a file path
        d = output_dir / f"Mathlib_{path}"
        if d.exists():
            _audit_domain(path, config)
        elif Path(path).exists():
            _audit_file(Path(path), config)
        else:
            print(f"  ✗ Not found: {path}")


def _audit_domain(domain: str, config: ProjectConfig):
    """Audit a single domain."""
    d = config.output_dir / f"Mathlib_{domain}"
    files = list(d.rglob("*.lean"))
    if not files:
        return

    stats = _audit_files(files)

    # Check for sketch
    sketch_lines = 0
    for name in [f"{domain}.lean", f"{domain}2.lean"]:
        sc = config.output_dir / name
        if sc.exists():
            sketch_lines = len(sc.read_text().split("\n"))
            break

    _print_audit(domain, stats, sketch_lines)


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
    """Print audit results."""
    trivial = s["rfl"] + s["iff_rfl"] + s["by_simp"] + s["by_rfl"] + s["by_norm_num"]
    genuine = max(s["genuine"], 1)

    print(f"\n{'=' * 60}")
    print(f"  DRY AUDIT: {name}")
    print(f"{'=' * 60}")
    print(f"  Files:              {s['files']:,}")
    print(f"  Lines:              {s['lines']:,}")
    print(f"  Genuine:            {s['genuine']:,}")
    print(f"  Dissolved:          {s['dissolved']}")
    print(f"  Conflates:          {s['conflates']}")
    print(f"  Infrastructure:     {s['infra']:,}")
    if sketch_lines:
        pct = (1 - sketch_lines / max(s["lines"], 1)) * 100
        print(f"  Sketch:             {sketch_lines} lines ({pct:.1f}% reduction)")
    print()
    print(f"  Layer 1 — Trivial proofs: {trivial} ({trivial * 100 // genuine}% of genuine)")
    print(f"    rfl:              {s['rfl']}")
    print(f"    Iff.rfl:          {s['iff_rfl']}")
    print(f"    by simp:          {s['by_simp']}")
    print(f"    by rfl:           {s['by_rfl']}")
    print(f"    by norm_num:      {s['by_norm_num']}")
    print(f"    by exact <term>:  {s['by_exact']}")
    print(f"    by omega:         {s['by_omega_s']}")
    print(f"    by decide:        {s['by_decide_s']}")
    print()
    print(f"  Layer 2 — Tactic profile:")
    print(f"    rw:               {s['rw']:,}")
    print(f"    simp:             {s['simp']:,}")
    print(f"    exact:            {s['exact']:,}")
    print(f"    omega:            {s['omega']}")
    print(f"    ring:             {s['ring']}")
    print(f"    aesop:            {s['aesop']}")
    print(f"    decide:           {s['decide']}")
    print(f"    linarith:         {s['linarith']}")
    print(f"    Multi-line rw:    {s['multi_rw']} chains (3+ rewrites)")
    print()
    print(f"  Layer 3 — Specialization:")
    print(f"    foo_nat/int/real: {s['spec']}")
    print(f"{'=' * 60}")


# =============================================================================
# Compress — sandbox-based proof compression
# =============================================================================

def cmd_compress(path: str, config: ProjectConfig):
    """Compress files by trying shorter proofs in sandbox."""
    sys.path.insert(0, str(Path(__file__).parent))
    from compress.sandbox import try_compress

    output_dir = config.output_dir

    if path.startswith("--domain"):
        return  # handled by main()

    # Single file or domain
    d = output_dir / f"Mathlib_{path}"
    if d.exists() and d.is_dir():
        files = sorted(d.rglob("*.lean"))
    elif Path(path).exists():
        files = [Path(path)]
    else:
        print(f"  ✗ Not found: {path}")
        return

    _compress_files(files, config)


def _compress_files(files: list[Path], config: ProjectConfig):
    """Run sandbox compression across a list of files."""
    sys.path.insert(0, str(Path(__file__).parent))
    from compress.sandbox import try_compress

    decl_re = re.compile(
        r'^((?:@\[.*?\]\s*\n)*)(?:(?:protected|private|nonrec)\s+)*(theorem|lemma)\s+(\S+)')
    proof_re = re.compile(r':=\s*by\b', re.DOTALL)

    total_files = 0
    files_improved = 0
    total_tested = 0
    total_compressed = 0
    total_lines_saved = 0

    print(f"\n{'=' * 60}")
    print(f"  COMPRESS ({len(files)} files)")
    print(f"{'=' * 60}")

    for f in files:
        text = f.read_text(errors="replace")
        lines = text.split("\n")
        original_count = len(lines)

        # Extract imports and preamble
        imports = [l for l in lines if l.startswith("import ")]
        preamble_lines = []
        first_decl = None

        for i, line in enumerate(lines):
            if decl_re.match(line):
                first_decl = i
                break
            elif not line.startswith("import ") and not line.startswith("/-") and \
                 not line.startswith("-/") and not line.startswith("--"):
                preamble_lines.append(line)

        if first_decl is None:
            total_files += 1
            continue

        preamble = "\n".join(preamble_lines)

        # Find declarations with by-proofs
        declarations = []
        i = first_decl
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
                skip = any(attr in attrs or attr in decl_text
                           for attr in config.protected_attributes)

                if not skip and proof_re.search(decl_text):
                    declarations.append({
                        "name": name, "text": decl_text,
                        "start_line": i, "end_line": j,
                    })
                i = j
            else:
                i += 1

        if not declarations:
            total_files += 1
            continue

        total_files += 1
        total_tested += len(declarations)

        # Try compressing each declaration
        compressions = []
        for decl in declarations:
            for tactic in config.tactics:
                result = try_compress(
                    declaration=decl["text"],
                    imports=imports,
                    replacement=tactic,
                    preamble=preamble,
                )
                if result.passed:
                    compressions.append({
                        "name": decl["name"],
                        "start_line": decl["start_line"],
                        "end_line": decl["end_line"],
                        "original": decl["text"],
                        "compressed": result.compressed,
                        "tactic": tactic,
                    })
                    total_compressed += 1
                    break

        if not compressions:
            continue

        # Apply compressions (reverse order to preserve line numbers)
        backup = text
        new_lines = list(lines)
        for comp in sorted(compressions, key=lambda c: c["start_line"], reverse=True):
            new_lines[comp["start_line"]:comp["end_line"]] = comp["compressed"].split("\n")

        new_text = "\n".join(new_lines)
        lines_saved = original_count - len(new_lines)

        # Write and build
        f.write_text(new_text)
        rel = f.relative_to(config.project_root)
        module = str(rel).replace("/", ".").replace(".lean", "")

        try:
            result = subprocess.run(
                ["lake", "build", module],
                capture_output=True, text=True, timeout=180,
                cwd=str(config.project_root),
            )
            if result.returncode == 0:
                files_improved += 1
                total_lines_saved += lines_saved
                short = str(f.relative_to(config.output_dir))
                print(f"  ✓ {short}: {len(compressions)} compressed, {lines_saved} lines saved")
                for comp in compressions:
                    print(f"      {comp['name']} → {comp['tactic']}")
            else:
                f.write_text(backup)
                short = str(f.relative_to(config.output_dir))
                print(f"  ✗ {short}: build failed, reverted")
        except subprocess.TimeoutExpired:
            f.write_text(backup)
            short = str(f.relative_to(config.output_dir))
            print(f"  ✗ {short}: timeout, reverted")

    print(f"\n{'=' * 60}")
    print(f"  RESULTS")
    print(f"{'=' * 60}")
    print(f"  Files scanned:          {total_files}")
    print(f"  Files improved:         {files_improved}")
    print(f"  Declarations tested:    {total_tested}")
    print(f"  Declarations compressed:{total_compressed}")
    print(f"  Lines saved:            {total_lines_saved}")
    print(f"{'=' * 60}")


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
    elif cmd == "classify":
        if len(sys.argv) > 2:
            cmd_classify(sys.argv[2], config)
        else:
            print("Usage: origin3.py classify <DOMAIN|path>")
    else:
        print(f"Unknown command: {cmd}")
        print(__doc__)


if __name__ == "__main__":
    main()
