#!/usr/bin/env python3
"""
Origin v2: Mathlib → Origin conversion tool (class-based architecture).

Built in parallel with origin.py (the reference). Same behavior, extensible design.
Each classification/compression pattern is a method — add a method, it applies to all files.

Usage:
    python3 scripts/origin2.py run                      THE PIPELINE
    python3 scripts/origin2.py classify NumberTheory
    python3 scripts/origin2.py classify --all
    python3 scripts/origin2.py --self classify --all
    python3 scripts/origin2.py extract NumberTheory/Harmonic/Int.lean
    python3 scripts/origin2.py extract --domain NumberTheory
    python3 scripts/origin2.py fruit --all 10
    python3 scripts/origin2.py audit Combinatorics          DRY AUDIT
    python3 scripts/origin2.py audit --all
    python3 scripts/origin2.py compress Combinatorics       STAGE 1 COMPRESS
    python3 scripts/origin2.py compress --domain Combinatorics
"""

import os
import re
import sys
import time
import shutil
import subprocess
import threading
import multiprocessing
from pathlib import Path
from dataclasses import dataclass
from typing import Optional
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed


# =============================================================================
# Configuration
# =============================================================================

class Config:
    """All paths and settings in one place."""

    LAKE_MATHLIB = Path("/Users/tallbr00/Documents/venv/original-arithmetic/origin-lean/.lake/packages/mathlib/Mathlib")
    ORIGIN_MATHLIB = Path("/Users/tallbr00/Documents/venv/original-arithmetic/origin-mathlib/Mathlib")
    ORIGIN_DIR = Path("/Users/tallbr00/Documents/venv/original-arithmetic/origin-lean/Origin")
    # Extracted Mathlib files live at project root, not inside Origin/
    EXTRACT_DIR = Path("/Users/tallbr00/Documents/venv/original-arithmetic/origin-lean")

    @classmethod
    def mathlib_dir(cls) -> Path:
        return cls.LAKE_MATHLIB if cls.LAKE_MATHLIB.exists() else cls.ORIGIN_MATHLIB

    @classmethod
    def project_root(cls) -> Path:
        return cls.ORIGIN_DIR.parent

    @classmethod
    def extract_dir(cls) -> Path:
        """Where extracted Mathlib_* directories live."""
        return cls.EXTRACT_DIR


# =============================================================================
# Block: the unit of parsed Lean
# =============================================================================

@dataclass
class Block:
    kind: str           # decl, namespace, end_namespace, section, variable, open, comment, import, other
    name: str
    text: str
    classification: str = ""  # genuine, dissolves, instance, infra_name, simp_trivial, trivial


# =============================================================================
# Classifier: determines what dissolves, what's infrastructure, what's genuine
# =============================================================================

class Classifier:
    """Classifies declarations. Override methods to change classification rules."""

    # Infrastructure typeclasses in signatures — these ARE the ground-management
    # layer. They dissolve because they exist to manage origin being inside the
    # counting domain. Once origin is outside (none), they have nothing to manage.
    # Uses \b word boundaries to prevent matching inside parameter names (hp_ne_zero).
    INFRA_SIG = re.compile(r"\bNeZero\b|\bGroupWithZero\b")

    # Bare ≠ 0 in a signature — this is ambiguous. Could be:
    #   Type 1: genuine measurement constraint ("nonzero denominator") — KEEP
    #   Type 2: ground guard (only exists because origin leaked in) — DISSOLVE
    # We only dissolve ≠ 0 when the declaration name is ALSO infrastructure.
    # Otherwise it's a legitimate mathematical precondition on some 0.
    BARE_NEZ = re.compile(r"≠\s*0")

    # All zero-management (for density counting)
    ZERO_ALL = re.compile(
        r"≠\s*0|NeZero|ne_zero|GroupWithZero|\.ne'|inv_ne_zero|"
        r"cast_ne_zero|succ_ne_zero|pos_of_ne_zero")

    # Declaration names that ARE zero-management infrastructure.
    # Uses ^ or \b to prevent matching inside compound names like card_ne_zero.
    # card_ne_zero proves a card is nonzero — genuine math.
    # ne_zero / NeZero are the typeclass — infrastructure.
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

    # Trivial proof patterns
    TRIVIAL_RE = re.compile(
        r":=\s*(rfl|h\b|by\s+simp\s*$|by\s+rfl|by\s+exact\s+\w+\s*$|Iff\.rfl)")

    # Ring-conflation patterns: theorems that DEFINE or ENCODE the
    # assumption that ground = zero. NOT theorems that merely USE
    # Ring as a hypothesis — those are genuine math on `some 0`.
    #
    # The origin theorem proves n * zero = zero for any zero satisfying
    # cancellation. In Option α, that zero is some 0, not none. Theorems
    # with [Ring α] work on some 0. That's algebra, not conflation.
    #
    # The conflation is narrow: theorems that specifically state or
    # require the additive identity to be the multiplicative absorber.
    RING_CONFLATION = re.compile(
        r"MulZeroClass\b|mulZeroClass\b|"           # the typeclass that encodes the conflation
        r"zero_ne_one|one_ne_zero|"                  # assumes 0 is in the domain as distinct from 1
        r"nontrivial|Nontrivial"                     # often via 0 ≠ 1
    )

    # Files that are ENTIRELY about zero infrastructure.
    # CharZero has useful instances for genuine math.
    # IsUnit can contain genuine algebra.
    INFRA_FILE_PATTERNS = [
        "GroupWithZero", "NeZero", "NoZeroDivisors", "NoZeroSMul",
        "MulZeroClass", "WithZero", "WithBot", "WithTop",
        "ZeroHom", "Deprecated",
    ]

    def is_infra_file(self, filepath: Path) -> bool:
        return any(pat in str(filepath) for pat in self.INFRA_FILE_PATTERNS)

    def is_infra_name(self, name: str) -> bool:
        return bool(self.INFRA_NAMES.search(name))

    def classify(self, kind: str, name: str, full_text: str) -> str:
        """Classify a declaration. Override to add new classification rules.

        Categories:
          dissolves    — ground-management infrastructure. Vanishes with none.
          conflates    — assumes ground = zero (Ring axiom). Needs rewriting.
          genuine      — real math. Keeps as-is or compresses.
          instance     — typeclass instance.
          infra_name   — declaration name is zero infrastructure.
          simp_trivial — trivial simp lemma.
          trivial      — trivial proof.

        The key distinction: ≠ 0 in a signature is ambiguous.
          - NeZero, GroupWithZero in a signature → always dissolves (infrastructure typeclass)
          - Bare ≠ 0 → only dissolves if the declaration name is also infrastructure.
            Otherwise it's a genuine measurement constraint ("nonzero denominator").
            A field theory theorem saying (h : x ≠ 0) is real math about some 0.
        """
        sig_part = full_text.split(":=")[0] if ":=" in full_text else full_text

        if kind == "instance":
            return "instance"
        if self.is_infra_name(name):
            return "infra_name"
        # Infrastructure typeclasses in signature → always dissolves
        if self.INFRA_SIG.search(sig_part):
            return "dissolves"
        # Bare ≠ 0 only dissolves if the name is also infrastructure
        if self.BARE_NEZ.search(sig_part) and self.INFRA_NAMES.search(name):
            return "dissolves"
        if self.RING_CONFLATION.search(sig_part):
            return "conflates"
        if self.TRIVIAL_RE.search(full_text) and kind in ("theorem", "lemma"):
            return "simp_trivial" if "@[simp]" in full_text else "trivial"
        return "genuine"


# =============================================================================
# Parser: reads Lean files into Blocks
# =============================================================================

class Parser:
    """Parses Lean files into blocks. Override methods to handle new constructs."""

    # Commands to strip (Mathlib-specific, not needed in Origin)
    STRIP_COMMANDS = (
        "add_decl_doc ", "assert_not_exists ", "suppress_compilation",
        "#align", "#guard_msgs", "#check", "#print",
        "@[deprecated",
        "-- Adaptation note", "-- adaptation_note", "#adaptation_note",
        "library_note ", "library_note\"",
    )

    # Commands to pass through (Lean commands that must be preserved)
    PASSTHROUGH_COMMANDS = (
        "set_option ", "attribute ", "alias ", "include ",
        "omit ", "universe ", "local ", "scoped ",
        "example ", "example",
        "notation ", "infixl ", "infixr ", "prefix ", "postfix ",
        "macro_rules", "macro ", "syntax ", "elab ",
    )

    # Declaration keyword regex
    DECL_RE = re.compile(
        r"^(.*?)?(private\s+|protected\s+)?(noncomputable\s+)?(nonrec\s+)?(unsafe\s+)?"
        r"(theorem|lemma|def|structure|class|instance|abbrev|inductive|alias)\s+(\S+)")

    # Regex to check if a line contains a declaration keyword (for attribute handling)
    DECL_KEYWORD_RE = re.compile(
        r"\b(theorem|lemma|def|structure|class|instance|abbrev|inductive|alias)\s+\S+")

    def __init__(self, classifier: Classifier = None):
        self.classifier = classifier or Classifier()

    def parse(self, text: str) -> list[Block]:
        """Parse a Lean file into blocks."""
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

            # Try each handler in order
            result = (
                self._try_comment(lines, i, stripped, blocks) or
                self._try_line_comment(lines, i, stripped) or
                self._try_import(lines, i, stripped, blocks) or
                self._try_module(lines, i, stripped) or
                self._try_section(lines, i, stripped, line, blocks) or
                self._try_namespace(lines, i, stripped, line, blocks) or
                self._try_end(lines, i, stripped, blocks) or
                self._try_open(lines, i, stripped, line, blocks) or
                self._try_strip(lines, i, stripped) or
                self._try_passthrough(lines, i, stripped, line, blocks) or
                self._try_variable(lines, i, stripped, line, blocks) or
                self._try_attribute(lines, i, stripped, line, pending_attrs) or
                self._try_bare_modifier(lines, i, stripped, line, pending_attrs) or
                self._try_declaration(lines, i, stripped, line, blocks, pending_attrs) or
                self._fallback(lines, i, line, blocks)
            )

            i = result[0]
            if result[1] is not None:
                pending_attrs = result[1]

        return blocks

    def _try_comment(self, lines, i, stripped, blocks) -> tuple[int, list] | None:
        if not stripped.startswith("/-"):
            return None
        comment_lines = [lines[i]]
        # Track nesting depth for nested comments (Lean supports /- /- -/ -/)
        depth = lines[i].count("/-") - lines[i].count("-/")
        i += 1
        while i < len(lines) and depth > 0:
            comment_lines.append(lines[i])
            depth += lines[i].count("/-") - lines[i].count("-/")
            i += 1
        blocks.append(Block("comment", "", "\n".join(comment_lines)))
        return (i, None)

    def _try_line_comment(self, lines, i, stripped) -> tuple[int, list] | None:
        if not stripped.startswith("--"):
            return None
        return (i + 1, None)

    def _try_import(self, lines, i, stripped, blocks) -> tuple[int, list] | None:
        if not (stripped.startswith("import ") or stripped.startswith("public import ")):
            return None
        blocks.append(Block("import", "", lines[i]))
        return (i + 1, None)

    def _try_module(self, lines, i, stripped) -> tuple[int, list] | None:
        if stripped.startswith("module") or stripped.startswith("@[expose]") or stripped.startswith("deprecated_module"):
            return (i + 1, None)
        return None

    def _try_section(self, lines, i, stripped, line, blocks) -> tuple[int, list] | None:
        if stripped.startswith("section") and (
            stripped == "section" or stripped.startswith("section ") or
            stripped.startswith("public section")):
            blocks.append(Block("section", stripped.split("section", 1)[-1].strip(), line))
            return (i + 1, None)
        return None

    def _try_namespace(self, lines, i, stripped, line, blocks) -> tuple[int, list] | None:
        if not stripped.startswith("namespace "):
            return None
        ns = stripped.split("namespace ", 1)[1].strip()
        blocks.append(Block("namespace", ns, line))
        return (i + 1, None)

    def _try_end(self, lines, i, stripped, blocks) -> tuple[int, list] | None:
        if stripped != "end" and not stripped.startswith("end "):
            return None
        ns = stripped.split("end", 1)[1].strip() if " " in stripped else ""
        blocks.append(Block("end_namespace", ns, stripped))
        return (i + 1, None)

    def _try_open(self, lines, i, stripped, line, blocks) -> tuple[int, list] | None:
        if not stripped.startswith("open "):
            return None
        # Single-line open — don't consume continuations (they're separate declarations).
        # "open ... in" scopes to the next command, but we let the parser handle that
        # naturally — the next line becomes its own block which is fine.
        blocks.append(Block("open", "", line))
        return (i + 1, None)

    # Keywords that make an @[inherit_doc] line load-bearing (don't strip)
    INHERIT_DOC_KEEP = re.compile(
        r"\b(notation|scoped|instance|def|theorem|lemma|abbrev|alias|inductive|structure|class|"
        r"infixl|infixr|prefix|postfix|macro|syntax|elab)\b")

    def _try_strip(self, lines, i, stripped) -> tuple[int, list] | None:
        for cmd in self.STRIP_COMMANDS:
            if stripped.startswith(cmd) or stripped == cmd.strip():
                # @[inherit_doc] attached to a notation/declaration is load-bearing
                if cmd == "@[deprecated" and stripped.startswith("@[deprecated"):
                    # Deprecated aliases wrap to column 0 on the next line.
                    # Pattern: @[deprecated ...] alias\nname := target
                    # Consume the @[deprecated] line + indented continuation +
                    # one column-0 alias body line.
                    all_text = lines[i]
                    i += 1
                    # Skip indented continuation
                    while i < len(lines) and lines[i].strip() and lines[i][0].isspace():
                        all_text += " " + lines[i].strip()
                        i += 1
                    # If the collected text ends with 'alias', consume the next
                    # non-blank line (the alias body at column 0)
                    if all_text.rstrip().endswith("alias"):
                        while i < len(lines) and not lines[i].strip():
                            i += 1
                        if i < len(lines):
                            i += 1  # consume the alias body line
                    return (i, None)
                elif "@[inherit_doc" in stripped and self.INHERIT_DOC_KEEP.search(stripped):
                    return None  # don't strip — let passthrough/declaration handle it
                # Consume the stripped command and any attached doc comment.
                # Pattern: library_note "..."/-- ... multi-line ... -/
                # Also handles #adaptation_note /-- ... \n  ... -/
                cur_line = lines[i]
                has_doc = "/--" in cur_line
                doc_closed = has_doc and "-/" in cur_line and cur_line.index("-/") > cur_line.index("/--")
                i += 1
                # Skip indented continuation lines, watching for doc close
                while i < len(lines) and lines[i].strip() and lines[i][0].isspace():
                    if "/--" in lines[i]:
                        has_doc = True
                    if "-/" in lines[i]:
                        doc_closed = True
                        i += 1
                        break
                    i += 1
                # Check if next non-blank line starts a doc comment
                if not has_doc and not doc_closed and i < len(lines) and lines[i].strip().startswith("/--"):
                    has_doc = True
                # Consume until -/ if a doc comment was opened but not yet closed
                if has_doc and not doc_closed:
                    while i < len(lines) and "-/" not in lines[i]:
                        i += 1
                    if i < len(lines):
                        i += 1  # skip the -/ line
                return (i, None)
        # Also strip standalone @[inherit_doc] NOT on same line as declaration
        if stripped == "@[inherit_doc]":
            return (i + 1, None)
        return None

    def _try_passthrough(self, lines, i, stripped, line, blocks) -> tuple[int, list] | None:
        for cmd in self.PASSTHROUGH_COMMANDS:
            if stripped.startswith(cmd) or stripped == cmd.strip():
                cmd_lines = [line]
                i += 1
                while i < len(lines) and lines[i].strip() and lines[i][0].isspace():
                    cmd_lines.append(lines[i])
                    i += 1
                # If the command ends with "in", attach the next non-blank line
                # (set_option ... in scopes to the next command — blank line breaks it)
                joined = "\n".join(cmd_lines)
                if joined.rstrip().endswith(" in"):
                    while i < len(lines) and not lines[i].strip():
                        i += 1
                    if i < len(lines):
                        cmd_lines.append(lines[i])
                        i += 1
                        # Continue collecting indented continuation
                        while i < len(lines) and lines[i].strip() and lines[i][0].isspace():
                            cmd_lines.append(lines[i])
                            i += 1
                blocks.append(Block("other", "", "\n".join(cmd_lines)))
                return (i, None)
        return None

    def _try_variable(self, lines, i, stripped, line, blocks) -> tuple[int, list] | None:
        if not stripped.startswith("variable"):
            return None
        var_lines = [line]
        i += 1
        while i < len(lines) and lines[i].strip() and lines[i][0].isspace():
            var_lines.append(lines[i])
            i += 1
        blocks.append(Block("variable", "", "\n".join(var_lines)))
        return (i, None)

    def _try_attribute(self, lines, i, stripped, line, pending_attrs) -> tuple[int, list] | None:
        if not stripped.startswith("@["):
            return None
        if self.DECL_KEYWORD_RE.search(stripped):
            return None  # Let declaration handler take it
        # @[inherit_doc ...] with notation/scoped/infixr etc — pass through as-is
        if "@[inherit_doc" in stripped and self.INHERIT_DOC_KEEP.search(stripped):
            return None  # Let passthrough/fallback handler take it

        attr_lines = [line]
        i += 1
        while i < len(lines):
            s = lines[i].strip()
            if not s:
                i += 1
                continue
            if s.startswith("@["):
                attr_lines.append(lines[i])
                i += 1
                continue
            last_attr = "\n".join(attr_lines)
            if last_attr.count('"') % 2 == 1 or last_attr.count('[') > last_attr.count(']'):
                attr_lines.append(lines[i])
                i += 1
                continue
            break
        return (i, attr_lines)

    # Bare modifiers that apply to the next declaration
    BARE_MODIFIER_RE = re.compile(r"^(noncomputable|private|protected|unsafe)\s*$")

    def _try_bare_modifier(self, lines, i, stripped, line, pending_attrs) -> tuple[int, list] | None:
        """Handle standalone modifiers (e.g. 'noncomputable' on its own line)."""
        if not self.BARE_MODIFIER_RE.match(stripped):
            return None
        return (i + 1, pending_attrs + [line])

    def _try_declaration(self, lines, i, stripped, line, blocks, pending_attrs) -> tuple[int, list] | None:
        decl_match = self.DECL_RE.match(stripped)
        if not decl_match:
            return None

        kind = decl_match.group(6)
        name = decl_match.group(7)

        decl_lines = pending_attrs + [line]
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

        # Collapse consecutive blank lines to prevent string gap errors
        cleaned = []
        prev_blank = False
        for dl in decl_lines:
            is_blank = not dl.strip()
            if is_blank and prev_blank:
                continue  # skip consecutive blanks
            cleaned.append(dl)
            prev_blank = is_blank
        full_text = "\n".join(cleaned).rstrip()
        cls = self.classifier.classify(kind, name, full_text)
        blocks.append(Block("decl", name, full_text, cls))
        return (i, [])  # Clear pending attrs

    def _fallback(self, lines, i, line, blocks) -> tuple[int, list]:
        blocks.append(Block("other", "", line))
        return (i + 1, None)


# =============================================================================
# Extractor: turns parsed blocks into Origin output
# =============================================================================

class Extractor:
    """Extracts Origin code from parsed Lean files."""

    def __init__(self, parser: Parser = None, classifier: Classifier = None):
        self.classifier = classifier or Classifier()
        self.parser = parser or Parser(self.classifier)
        # Load compression patterns
        try:
            import sys
            sys.path.insert(0, str(Path(__file__).parent))
            from compress.patterns import get_patterns
            self.patterns = get_patterns()
        except ImportError:
            self.patterns = []

    def extract(self, filepath: Path) -> tuple[str, dict]:
        """Extract genuine content from a Mathlib file."""
        text = filepath.read_text(errors="replace")
        relpath = str(filepath).split("Mathlib/")[-1] if "Mathlib/" in str(filepath) else str(filepath)

        if self.classifier.is_infra_file(filepath):
            return (f"-- {relpath}: entire file is zero-management infrastructure. Dissolves completely.\n",
                    {"total": 0, "genuine": 0, "dissolved": 0, "conflates": 0, "infra": 0, "skipped_file": True})

        blocks = self.parser.parse(text)

        # Dependency analysis: un-dissolve declarations referenced by genuine code.
        # If a genuine proof uses a dissolved name, that name is load-bearing — keep it.
        self._resolve_dependencies(blocks)

        stats = {"total": 0, "genuine": 0, "dissolved": 0, "conflates": 0, "infra": 0, "skipped_file": False}

        decls = [b for b in blocks if b.kind == "decl"]
        genuine_count = sum(1 for d in decls if d.classification == "genuine")
        dissolved = sum(1 for d in decls if d.classification in ("dissolves", "infra_name"))
        conflates = sum(1 for d in decls if d.classification == "conflates")
        infra = sum(1 for d in decls if d.classification in ("instance", "simp_trivial", "trivial"))

        stats.update(total=len(decls), genuine=genuine_count, dissolved=dissolved,
                     conflates=conflates, infra=infra)

        if genuine_count == 0 and conflates == 0:
            return (f"-- {relpath}: 0 genuine declarations. {dissolved} dissolved, {infra} infrastructure.\n", stats)

        imports = [b.text for b in blocks if b.kind == "import"]
        parts = []

        # Dependency guard for compression: collect text from ALL blocks that
        # will survive (non-dissolved decls that aren't compressed, plus all
        # other/variable/open blocks) so we can check if a compressed decl
        # is referenced anywhere in the surviving output.
        if self.patterns:
            surviving_parts = []
            for b in blocks:
                if b.kind == "decl":
                    if b.classification in ("dissolves", "infra_name"):
                        continue  # dissolved — skip
                    if any(p.match(b) for p in self.patterns):
                        continue  # would be compressed — skip
                    surviving_parts.append(b.text)
                elif b.kind in ("other", "variable", "open"):
                    surviving_parts.append(b.text)
            non_compressed_text = "\n".join(surviving_parts)
        else:
            non_compressed_text = ""

        # Iterative dependency guard: rescue compressed decls that surviving
        # code references. Iterate because rescuing A may make B's reference
        # to A visible, requiring B to be rescued too.
        if self.patterns:
            compressed = {b.name: b for b in blocks
                          if b.kind == "decl" and b.name
                          and any(p.match(b) for p in self.patterns)}
            rescued = set()
            changed = True
            while changed:
                changed = False
                # Rebuild surviving text including rescued decls
                surv = []
                for b in blocks:
                    if b.kind == "decl":
                        if b.classification in ("dissolves", "infra_name"):
                            continue
                        if b.name in compressed and b.name not in rescued:
                            continue
                        surv.append(b.text)
                    elif b.kind in ("other", "variable", "open"):
                        surv.append(b.text)
                surv_text = "\n".join(surv)
                for name in list(compressed.keys()):
                    if name in rescued:
                        continue
                    if re.search(r'\b' + re.escape(name) + r'\b', surv_text):
                        rescued.add(name)
                        changed = True
        else:
            compressed = {}
            rescued = set()

        last_dissolved = False
        for b in blocks:
            # Suppress orphaned bodies after dissolved declarations
            if b.kind == "other" and last_dissolved:
                s = b.text.strip()
                if s.startswith("{") or s.startswith("where") or s.startswith("|"):
                    continue
            last_dissolved = (b.kind == "decl" and b.classification in ("dissolves", "infra_name"))
            # Apply compression — but rescue if dependency guard saved it
            if b.kind == "decl" and b.name in compressed and b.name not in rescued:
                continue  # compressed away — safe to delete
            text_out = self._emit_block(b)
            if text_out is not None:
                parts.append(text_out)

        import_block = "import Origin.Core\n"
        for imp in imports:
            clean = imp.strip().replace("public import ", "import ")
            import_block += clean + "\n"
        import_block += "\nnoncomputable section\n"

        header = (f"/-\nExtracted from {relpath}\n"
                  f"Genuine: {genuine_count} | Conflates: {conflates} | "
                  f"Dissolved: {dissolved} | Infrastructure: {infra}\n"
                  f"-/\n{import_block}")
        body = "\n\n".join(p for p in parts if p.strip())
        return (header + "\n" + body + "\n", stats)

    def _resolve_dependencies(self, blocks: list[Block]):
        """Un-dissolve declarations that genuine code depends on.

        If a genuine declaration references a dissolved declaration's name,
        the dissolved declaration is load-bearing and must be kept.
        Iterates until stable (transitive dependencies).
        """
        dissolved = {b.name: b for b in blocks
                     if b.kind == "decl" and b.classification in ("dissolves", "infra_name") and b.name}
        if not dissolved:
            return

        changed = True
        while changed:
            changed = False
            # Collect all text from non-dissolved blocks (decls, aliases, other)
            live_text = "\n".join(
                b.text for b in blocks
                if not (b.kind == "decl" and b.classification in ("dissolves", "infra_name"))
            )
            for name, b in list(dissolved.items()):
                # Check if this dissolved name appears in live code
                # Use word boundary to avoid false positives
                if re.search(r'\b' + re.escape(name) + r'\b', live_text):
                    b.classification = "genuine"
                    del dissolved[name]
                    changed = True

    def _emit_block(self, b: Block) -> str | None:
        """Emit a block. Compression deletion is handled by the dependency
        guard loop above. This method handles everything else."""
        if b.kind == "comment":
            return b.text if "/-!" in b.text else None
        if b.kind == "import":
            return None
        if b.kind in ("namespace", "end_namespace", "section", "open", "variable"):
            return b.text
        if b.kind == "decl":
            if b.classification in ("dissolves", "infra_name"):
                return f"-- DISSOLVED: {b.name}"
            if b.classification == "conflates":
                return f"-- CONFLATES (assumes ground = zero): {b.name}\n{b.text}"
            return b.text
        if b.kind == "other":
            return b.text
        return None


# =============================================================================
# UI: terminal output formatting
# =============================================================================

class UI:
    """Terminal UI with ANSI colors and progress bars."""

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
        sys.stdout.reconfigure(line_buffering=True)

    def bar(self, current, total, width=30):
        filled = int(width * current / total) if total else 0
        return f"{self.GREEN}{'█' * filled}{self.DIM}{'░' * (width - filled)}{self.RESET}"

    @staticmethod
    def elapsed(t):
        s = int(t)
        return f"{s}s" if s < 60 else f"{s // 60}m{s % 60:02d}s"

    def header(self):
        W = self.W
        print()
        print(f"  {self.BOLD}{self.CYAN}╔{'═' * (W - 6)}╗{self.RESET}")
        print(f"  {self.BOLD}{self.CYAN}║{self.RESET}  {self.BOLD}{self.WHITE}O R I G I N{self.RESET}"
              f"  {self.DIM}powered by{self.RESET} {self.BOLD}{self.MAGENTA}Claude Code{self.RESET}"
              f"{' ' * max(1, W - 42)}{self.BOLD}{self.CYAN}║{self.RESET}")
        print(f"  {self.BOLD}{self.CYAN}║{self.RESET}  {self.DIM}b - b = origin  "
              f"·  the ground absorbs  "
              f"·  the script converts{self.RESET}"
              f"{' ' * max(1, W - 67)}{self.BOLD}{self.CYAN}║{self.RESET}")
        print(f"  {self.BOLD}{self.CYAN}╚{'═' * (W - 6)}╝{self.RESET}")
        print()

    def phase(self, title, subtitle):
        print(f"  {self.BOLD}{title}{self.RESET}  {self.DIM}{subtitle}{self.RESET}")
        print(f"  {self.DIM}{'─' * (self.W - 4)}{self.RESET}")

    def domain_done(self, idx, total, domain, files, genuine, dissolved):
        gen = f"{self.GREEN}{genuine:,}{self.RESET}" if genuine > 0 else f"{self.DIM}0{self.RESET}"
        dis = f"{self.YELLOW}{dissolved:,}{self.RESET}" if dissolved > 0 else f"{self.DIM}0{self.RESET}"
        sys.stdout.write(f"{self.CLEAR}  {self.bar(idx, total)} "
            f"{self.BOLD}{domain:<24}{self.RESET} "
            f"{files:>4} files  {gen:>5} genuine  {dis:>4} dissolved\n")
        sys.stdout.flush()

    def build_done(self, idx, total, domain, files, ok, n_errs, dt, timeout=False):
        if ok:
            icon = f"{self.GREEN}OK{self.RESET}"
        elif timeout:
            icon = f"{self.RED}TIMEOUT{self.RESET}"
        else:
            icon = f"{self.RED}FAIL({n_errs}){self.RESET}"
        sys.stdout.write(f"{self.CLEAR}  {self.bar(idx, total)} "
            f"{icon:<18}  {self.BOLD}{domain:<24}{self.RESET} "
            f"{files:>4} files  {self.DIM}{self.elapsed(dt)}{self.RESET}\n")
        sys.stdout.flush()

    def build_progress(self, idx, total, domain, files):
        sys.stdout.write(f"{self.CLEAR}  {self.bar(idx, total)} "
            f"{self.CYAN}building{self.RESET} {self.BOLD}{domain}{self.RESET} "
            f"{self.DIM}({files} files)...{self.RESET}")
        sys.stdout.flush()

    def separator(self):
        print(f"  {self.DIM}{'─' * (self.W - 4)}{self.RESET}")

    def summary_extract(self, extracted, genuine, dissolved, skipped, dt):
        print(f"  {self.BOLD}{self.WHITE}{extracted:,}{self.RESET} files  "
              f"{self.BOLD}{self.GREEN}{genuine:,}{self.RESET} genuine  "
              f"{self.BOLD}{self.YELLOW}{dissolved:,}{self.RESET} dissolved  "
              f"{self.DIM}{skipped:,} skipped{self.RESET}  "
              f"{self.DIM}{self.elapsed(dt)}{self.RESET}")
        print()

    def summary_build(self, passed, failed, dt):
        p = f"{self.GREEN}{passed:,}{self.RESET}"
        f = f"{self.RED}{failed:,}{self.RESET}" if failed > 0 else f"{self.GREEN}0{self.RESET}"
        print(f"  {self.BOLD}{p}{self.RESET} pass  {f} fail  "
              f"{self.DIM}{self.elapsed(dt)}{self.RESET}")
        print()

    def report(self, mathlib_lines, origin_lines, genuine, dissolved, infra,
               build_pass, build_fail, error_groups, t_extract, t_build, t_total):
        W = self.W
        status = "PASS" if build_fail == 0 else "FAIL"
        reduction = (1 - origin_lines / mathlib_lines) * 100 if mathlib_lines > 0 else 0

        print(f"  {self.BOLD}{self.CYAN}╔{'═' * (W - 6)}╗{self.RESET}")
        print(f"  {self.BOLD}{self.CYAN}║{self.RESET}  {self.BOLD}{self.WHITE}R E S U L T S{self.RESET}"
              f"{' ' * (W - 21)}{self.BOLD}{self.CYAN}║{self.RESET}")
        print(f"  {self.BOLD}{self.CYAN}╚{'═' * (W - 6)}╝{self.RESET}")
        print()

        print(f"    {self.DIM}Mathlib{self.RESET}        {self.BOLD}{mathlib_lines:>12,}{self.RESET} {self.DIM}lines{self.RESET}")
        print(f"    {self.DIM}Origin{self.RESET}         {self.BOLD}{self.GREEN}{origin_lines:>12,}{self.RESET} {self.DIM}lines{self.RESET}")
        r_color = self.GREEN if reduction > 50 else self.YELLOW if reduction > 20 else self.RED
        print(f"    {self.BOLD}Reduction{self.RESET}      {self.BOLD}{r_color}{reduction:>11.1f}%{self.RESET}")
        print()

        print(f"    {self.DIM}Genuine{self.RESET}        {self.GREEN}{genuine:>12,}{self.RESET}")
        print(f"    {self.DIM}Dissolved{self.RESET}      {self.YELLOW}{dissolved:>12,}{self.RESET}")
        print(f"    {self.DIM}Infrastructure{self.RESET} {self.DIM}{infra:>12,}{self.RESET}")
        print()

        if build_fail == 0:
            print(f"    {self.DIM}Build{self.RESET}          {self.BOLD}{self.GREEN}{'PASS':>12}{self.RESET}  "
                  f"{self.GREEN}{build_pass:,} files{self.RESET}")
        else:
            print(f"    {self.DIM}Build{self.RESET}          {self.BOLD}{self.RED}{'FAIL':>12}{self.RESET}  "
                  f"{self.GREEN}{build_pass:,} pass{self.RESET} / {self.RED}{build_fail:,} fail{self.RESET}")
        print(f"    {self.DIM}Time{self.RESET}           {self.DIM}{self.elapsed(t_total):>12}{self.RESET}  "
              f"{self.DIM}(extract {self.elapsed(t_extract)} + build {self.elapsed(t_build)}){self.RESET}")
        print()

        if error_groups:
            print(f"  {self.BOLD}{self.RED}ERRORS{self.RESET}  "
                  f"{self.BOLD}{len(error_groups)}{self.RESET} {self.DIM}patterns to fix in the script{self.RESET}")
            self.separator()
            print()
            for pattern, files in sorted(error_groups.items(), key=lambda x: -len(x[1])):
                print(f"    {self.RED}{len(files):>4}{self.RESET} {self.DIM}files{self.RESET}  "
                      f"{self.WHITE}{pattern[:W - 20]}{self.RESET}")
                for fp in files[:3]:
                    print(f"    {self.DIM}     ↳ {fp}{self.RESET}")
                if len(files) > 3:
                    print(f"    {self.DIM}     ↳ ... and {len(files) - 3} more{self.RESET}")
                print()

        print(f"  {self.BOLD}{self.CYAN}╔{'═' * (W - 6)}╗{self.RESET}")
        if build_fail == 0:
            print(f"  {self.BOLD}{self.CYAN}║{self.RESET}  {self.BOLD}{self.GREEN}"
                  f"BUILD PASSES  ·  {mathlib_lines:,} → {origin_lines:,} lines  "
                  f"·  {reduction:.1f}% reduction{self.RESET}"
                  f"{' ' * max(1, W - 65)}{self.BOLD}{self.CYAN}║{self.RESET}")
            print(f"  {self.BOLD}{self.CYAN}║{self.RESET}  {self.DIM}"
                  f"Lean verified. Line counts objective. "
                  f"The build succeeds or it doesn't.{self.RESET}"
                  f"{' ' * max(1, W - 74)}{self.BOLD}{self.CYAN}║{self.RESET}")
        else:
            print(f"  {self.BOLD}{self.CYAN}║{self.RESET}  {self.BOLD}{self.YELLOW}"
                  f"{len(error_groups)} error patterns  ·  "
                  f"Fix them in the script  ·  Run again{self.RESET}"
                  f"{' ' * max(1, W - 60)}{self.BOLD}{self.CYAN}║{self.RESET}")
        print(f"  {self.BOLD}{self.CYAN}╚{'═' * (W - 6)}╝{self.RESET}")
        print()


# =============================================================================
# Pipeline: extract → build → report
# =============================================================================

class Pipeline:
    """The full pipeline. Override phases to customize behavior."""

    def __init__(self):
        self.classifier = Classifier()
        self.parser = Parser(self.classifier)
        self.extractor = Extractor(self.parser, self.classifier)
        self.ui = UI()
        self.mathlib = Config.mathlib_dir()
        self.origin = Config.extract_dir()  # Mathlib_* dirs at project root
        self.n_cpus = multiprocessing.cpu_count()

    def run(self):
        t_start = time.time()
        self.ui.header()

        domains = sorted(d.name for d in self.mathlib.iterdir()
                         if d.is_dir() and list(d.rglob("*.lean")))

        # Phase 1: Extract
        extract_stats = self.phase_extract(domains)
        t_extract = time.time() - t_start

        # Phase 2: Build
        build_stats = self.phase_build(domains)
        t_build = time.time() - t_start - t_extract

        # Phase 3: Count & Report
        mathlib_lines = self._count_lines(self.mathlib)
        origin_lines = sum(self._count_lines(self.origin / f"Mathlib_{d}")
                           for d in domains if (self.origin / f"Mathlib_{d}").exists())

        self.ui.report(
            mathlib_lines, origin_lines,
            extract_stats["genuine"], extract_stats["dissolved"], extract_stats["infra"],
            build_stats["pass"], build_stats["fail"],
            build_stats["error_groups"],
            t_extract, t_build, time.time() - t_start)

    def phase_extract(self, domains) -> dict:
        self.ui.phase("EXTRACT", f"Mathlib → Origin  ({self.n_cpus} cores)")

        totals = {"extracted": 0, "skipped": 0, "genuine": 0, "dissolved": 0, "infra": 0}
        t0 = time.time()
        done = 0

        with ThreadPoolExecutor(max_workers=self.n_cpus) as pool:
            futures = {pool.submit(self._extract_domain, d): d for d in domains}
            for future in as_completed(futures):
                done += 1
                r = future.result()
                for k in totals:
                    totals[k] += r[k]
                self.ui.domain_done(done, len(domains), r["domain"],
                                    r["extracted"], r["genuine"], r["dissolved"])

        self.ui.separator()
        self.ui.summary_extract(totals["extracted"], totals["genuine"],
                                totals["dissolved"], totals["skipped"],
                                time.time() - t0)
        return totals

    def _extract_domain(self, domain) -> dict:
        src = self.mathlib / domain
        out_dir = self.origin / f"Mathlib_{domain}"
        if out_dir.exists():
            shutil.rmtree(out_dir)
        out_dir.mkdir(parents=True, exist_ok=True)

        files = sorted(src.rglob("*.lean"))
        d = {"domain": domain, "extracted": 0, "skipped": 0,
             "genuine": 0, "dissolved": 0, "infra": 0}

        for f in files:
            content, stats = self.extractor.extract(f)
            if stats.get("skipped_file") or stats["genuine"] == 0:
                d["skipped"] += 1
                d["dissolved"] += stats.get("dissolved", 0)
                d["infra"] += stats.get("infra", 0)
                continue
            relpath = str(f).split(f"Mathlib/{domain}/")[-1]
            outfile = out_dir / relpath
            outfile.parent.mkdir(parents=True, exist_ok=True)
            outfile.write_text(content)
            d["extracted"] += 1
            d["genuine"] += stats["genuine"]
            d["dissolved"] += stats["dissolved"]
            d["infra"] += stats["infra"]

        return d

    def phase_build(self, domains) -> dict:
        self.ui.phase("BUILD", f"lake build  ({self.n_cpus} concurrent domains)")

        error_groups = defaultdict(list)
        error_files = set()
        all_files = []
        lock = threading.Lock()

        builds = []
        for domain in domains:
            out_dir = self.origin / f"Mathlib_{domain}"
            if not out_dir.exists():
                continue
            lean_files = sorted(out_dir.rglob("*.lean"))
            all_files.extend(lean_files)
            if not lean_files:
                continue
            modules = [(str(f.relative_to(Config.project_root())).replace("/", ".").replace(".lean", ""), f)
                       for f in lean_files]
            builds.append((domain, lean_files, modules))

        builds.sort(key=lambda x: -len(x[1]))

        done = 0
        with ThreadPoolExecutor(max_workers=self.n_cpus) as pool:
            futures = {pool.submit(self._build_domain, b): b[0] for b in builds}
            for future in as_completed(futures):
                done += 1
                r = future.result()
                with lock:
                    n_errs = 0
                    for pattern, files in r["errors"]:
                        error_groups[pattern].extend(files)
                        error_files.update(files)
                        n_errs += len(files)

                self.ui.build_done(done, len(builds), r["domain"],
                                   r["files"], r["ok"], n_errs, r["dt"], r["timeout"])

        bp = len(all_files) - len(error_files)
        bf = len(error_files)
        self.ui.separator()
        self.ui.summary_build(bp, bf, time.time())
        return {"pass": bp, "fail": bf, "error_groups": error_groups}

    def _build_domain(self, args) -> dict:
        domain, lean_files, modules = args
        module_names = [m for m, _ in modules]
        t0 = time.time()

        try:
            result = subprocess.run(
                ["lake", "build"] + module_names,
                capture_output=True, text=True, timeout=3600,
                cwd=str(Config.project_root()))
            output = result.stderr + result.stdout
            timed_out = False
        except subprocess.TimeoutExpired:
            output = ""
            timed_out = True
            result = None

        dt = time.time() - t0
        errors = []

        if timed_out:
            errors.append(("TIMEOUT (>3600s)",
                [str(f.relative_to(Config.project_root())) for _, f in modules]))
            return {"domain": domain, "files": len(lean_files),
                    "ok": False, "errors": errors, "dt": dt, "timeout": True}

        for line in output.split("\n"):
            line = line.strip()
            if not line.startswith("error:"):
                continue
            m = re.match(r"error:\s*([^:]+\.lean):(\d+):(\d+):\s*(.*)", line)
            if m:
                errors.append((m.group(4).strip(), [m.group(1).lstrip("./")]))
            elif "build failed" not in line:
                errors.append((line, [domain]))

        return {"domain": domain, "files": len(lean_files),
                "ok": result.returncode == 0, "errors": errors,
                "dt": dt, "timeout": False}

    @staticmethod
    def _count_lines(path: Path) -> int:
        total = 0
        if not path.exists():
            return 0
        for f in path.rglob("*.lean"):
            try:
                total += f.read_text(errors="replace").count("\n") + 1
            except:
                pass
        return total


# =============================================================================
# Legacy commands (classify, fruit, extract) — thin wrappers
# =============================================================================

def cmd_classify(domain: str, self_mode: bool = False):
    base = Config.ORIGIN_DIR if self_mode else Config.mathlib_dir()
    src = base if self_mode and domain == "--all" else base / domain
    if not src.is_dir():
        print(f"ERROR: {src} not found", file=sys.stderr)
        return

    classifier = Classifier()
    parser = Parser(classifier)
    mode = "ORIGIN (self-audit)" if self_mode else "MATHLIB"
    files = sorted(src.rglob("*.lean"))
    rows = []

    for f in files:
        text = f.read_text(errors="replace")
        blocks = parser.parse(text)
        decls = [b for b in blocks if b.kind == "decl"]
        genuine = sum(1 for d in decls if d.classification == "genuine")
        dissolved = sum(1 for d in decls if d.classification in ("dissolves", "infra_name"))
        instances = sum(1 for d in decls if d.classification == "instance")
        trivial = sum(1 for d in decls if d.classification in ("simp_trivial", "trivial"))
        lines = text.count("\n") + 1
        relpath = str(f).split(f"Mathlib/{domain}/")[-1]
        rows.append((genuine, dissolved, instances, trivial, len(decls), lines, relpath))

    rows.sort(reverse=True)
    print(f"=== {domain} [{mode}]: Declaration-Level Classification ===\n")
    print(f"{'GEN':>4} | {'DISS':>4} | {'INST':>4} | {'TRIV':>4} | {'TOT':>4} | {'LINES':>5} | PATH")
    print(f"{'----':>4}-+-{'----':>4}-+-{'----':>4}-+-{'----':>4}-+-{'----':>4}-+-{'-----':>5}-+-----")
    for g, d, inst, t, tot, lines, path in rows:
        print(f"{g:>4} | {d:>4} | {inst:>4} | {t:>4} | {tot:>4} | {lines:>5} | {path}")

    t_gen = sum(r[0] for r in rows)
    t_dis = sum(r[1] for r in rows)
    t_tot = sum(r[4] for r in rows)
    print(f"\n--- SUMMARY: {domain} ---")
    print(f"Files: {len(rows)} | Declarations: {t_tot} | Genuine: {t_gen} | Dissolved: {t_dis}")


def cmd_classify_all(self_mode: bool = False):
    base = Config.ORIGIN_DIR if self_mode else Config.mathlib_dir()
    classifier = Classifier()
    parser = Parser(classifier)
    mode = "ORIGIN (self-audit)" if self_mode else "MATHLIB"
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
                blocks = parser.parse(f.read_text(errors="replace"))
            except:
                continue
            decls = [b for b in blocks if b.kind == "decl"]
            t_gen += sum(1 for dd in decls if dd.classification == "genuine")
            t_dis += sum(1 for dd in decls if dd.classification in ("dissolves", "infra_name"))
            t_tot += len(decls)
        rows.append((d.name, t_gen, t_dis, t_tot - t_gen, t_tot, len(files)))

    rows.sort(key=lambda r: r[1], reverse=True)
    for name, gen, dis, infra, total, files in rows:
        print(f"{name:<22} | {gen:>6} | {dis:>5} | {infra:>5} | {total:>5} | {files:>5}")
    print(f"\nGrand total GENUINE: {sum(r[1] for r in rows)}")


def cmd_fruit(domain: Optional[str], top_n: int):
    classifier = Classifier()
    base = Config.mathlib_dir()
    files = sorted((base / domain).rglob("*.lean")) if domain else sorted(base.rglob("*.lean"))
    results = []
    for f in files:
        try:
            text = f.read_text(errors="replace")
        except:
            continue
        lines = text.count("\n") + 1
        if lines < 30:
            continue
        hits = len(classifier.ZERO_ALL.findall(text))
        if hits == 0:
            continue
        thms = len(re.findall(r"^(protected\s+)?(theorem|lemma|def)\s+", text, re.MULTILINE))
        if thms == 0:
            continue
        relpath = str(f).split("Mathlib/")[-1]
        results.append((hits / lines, hits, lines, thms, relpath))

    results.sort(reverse=True)
    title = domain or "ALL"
    print(f"=== {title}: Top {top_n} by density ===\n")
    print(f"{'DENSITY':>8} | {'HITS':>4} | {'LINES':>5} | {'THMS':>4} | PATH")
    print(f"{'--------':>8}-+-{'----':>4}-+-{'-----':>5}-+-{'----':>4}-+-----")
    for density, hits, lines, thms, path in results[:top_n]:
        print(f"{density:>7.1%} | {hits:>4} | {lines:>5} | {thms:>4} | {path}")


def cmd_extract(filepath: Path):
    extractor = Extractor()
    if not filepath.exists():
        filepath = Config.mathlib_dir() / filepath
    if not filepath.exists():
        print(f"ERROR: {filepath} not found", file=sys.stderr)
        return
    content, _ = extractor.extract(filepath)
    print(content)


def cmd_extract_domain(domain: str):
    extractor = Extractor()
    src = Config.mathlib_dir() / domain
    if not src.is_dir():
        print(f"ERROR: {src} not found", file=sys.stderr)
        return
    out_dir = Config.extract_dir() / f"Mathlib_{domain}"
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    count = total_genuine = total_dissolved = total_infra = skipped = 0
    for f in sorted(src.rglob("*.lean")):
        content, stats = extractor.extract(f)
        if stats.get("skipped_file") or stats["genuine"] == 0:
            skipped += 1
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
    print(f"Extracted: {count} files | Genuine: {total_genuine} | Dissolved: {total_dissolved} | Skipped: {skipped}")


# =============================================================================
# DRY Audit
# =============================================================================

def cmd_audit(domain: str):
    """Audit a domain for DRY compression opportunities.

    Scans extracted Origin/Mathlib_<domain>/ files and reports:
    - File/line/declaration counts
    - Dissolved/conflated/genuine breakdown
    - Trivial proof counts (rfl, by simp, etc.)
    - Tactic profile (rw, simp, omega, ring, etc.)
    - Multi-line rw chain count
    - Specialization family count (foo_nat/foo_int/foo_real)

    Usage: python3 scripts/origin2.py audit Combinatorics
           python3 scripts/origin2.py audit --all
    """
    extract_dir = Config.extract_dir()

    if domain == "--all":
        domains = sorted(d.name.replace("Mathlib_", "")
                         for d in extract_dir.iterdir()
                         if d.is_dir() and d.name.startswith("Mathlib_"))
    else:
        domains = [domain]

    for dom in domains:
        d = extract_dir / f"Mathlib_{dom}"
        if not d.exists():
            print(f"  ✗ Mathlib_{dom}/ not found")
            continue

        files = list(d.rglob("*.lean"))
        if not files:
            continue

        # Counters
        total_lines = 0
        genuine = 0
        dissolved = 0
        conflates = 0
        infra = 0

        # Trivial proofs
        rfl_count = 0
        iff_rfl_count = 0
        by_simp_count = 0
        by_rfl_count = 0
        by_norm_num_count = 0
        by_omega_standalone = 0
        by_decide_standalone = 0
        by_exact_count = 0

        # Tactic uses
        rw_uses = 0
        simp_uses = 0
        exact_uses = 0
        omega_uses = 0
        ring_uses = 0
        aesop_uses = 0
        decide_uses = 0
        linarith_uses = 0

        # Multi-line rw chains (3+ rewrites)
        multi_rw = 0

        # Specialization families
        spec_families = 0

        re_rfl = re.compile(r':=\s+rfl\s*$')
        re_iff_rfl = re.compile(r':=\s+Iff\.rfl\s*$')
        re_by_simp = re.compile(r'by\s+simp\s*$')
        re_by_rfl = re.compile(r'by\s+rfl\s*$')
        re_by_norm_num = re.compile(r'by\s+norm_num\s*$')
        re_by_omega = re.compile(r'by\s+omega\s*$')
        re_by_decide = re.compile(r'by\s+decide\s*$')
        re_by_exact = re.compile(r'by\s+exact\s+\S+\s*$')
        re_multi_rw = re.compile(r'rw\s*\[.*,.*,.*\]')
        re_spec = re.compile(r'^(?:theorem|lemma|def|abbrev)\s+\w+_(?:nat|int|real|fin)\b')
        re_rw = re.compile(r'\brw\b')
        re_simp = re.compile(r'\bsimp\b')
        re_exact = re.compile(r'\bexact\b')
        re_omega = re.compile(r'\bomega\b')
        re_ring = re.compile(r'\bring\b')
        re_aesop = re.compile(r'\baesop\b')
        re_decide = re.compile(r'\bdecide\b')
        re_linarith = re.compile(r'\blinarith\b')

        for f in files:
            text = f.read_text(errors="replace")
            lines = text.split("\n")
            total_lines += len(lines)

            # Header stats
            for line in lines[:5]:
                m = re.search(r'Genuine:\s*(\d+)', line)
                if m: genuine += int(m.group(1))
                m = re.search(r'Dissolved:\s*(\d+)', line)
                if m: dissolved += int(m.group(1))
                m = re.search(r'Conflates:\s*(\d+)', line)
                if m: conflates += int(m.group(1))
                m = re.search(r'Infrastructure:\s*(\d+)', line)
                if m: infra += int(m.group(1))

            for line in lines:
                # Trivial proofs
                if re_rfl.search(line): rfl_count += 1
                if re_iff_rfl.search(line): iff_rfl_count += 1
                if re_by_simp.search(line): by_simp_count += 1
                if re_by_rfl.search(line): by_rfl_count += 1
                if re_by_norm_num.search(line): by_norm_num_count += 1
                if re_by_omega.search(line): by_omega_standalone += 1
                if re_by_decide.search(line): by_decide_standalone += 1
                if re_by_exact.search(line): by_exact_count += 1

                # Tactic uses
                rw_uses += len(re_rw.findall(line))
                simp_uses += len(re_simp.findall(line))
                exact_uses += len(re_exact.findall(line))
                omega_uses += len(re_omega.findall(line))
                ring_uses += len(re_ring.findall(line))
                aesop_uses += len(re_aesop.findall(line))
                decide_uses += len(re_decide.findall(line))
                linarith_uses += len(re_linarith.findall(line))

                # Multi-line rw
                if re_multi_rw.search(line): multi_rw += 1

                # Specialization families
                if re_spec.match(line.strip()): spec_families += 1

        trivial_total = rfl_count + iff_rfl_count + by_simp_count + by_rfl_count + by_norm_num_count

        # Check for sketch
        sketch_lines = 0
        sketch_candidates = [
            Config.ORIGIN_DIR / f"{dom}.lean",
            Config.ORIGIN_DIR / f"{dom}2.lean",
        ]
        for sc in sketch_candidates:
            if sc.exists():
                sketch_lines = len(sc.read_text().split("\n"))
                break

        # Report
        print(f"\n{'=' * 60}")
        print(f"  DRY AUDIT: {dom}")
        print(f"{'=' * 60}")
        print(f"  Files:              {len(files):,}")
        print(f"  Lines:              {total_lines:,}")
        print(f"  Genuine:            {genuine:,}")
        print(f"  Dissolved:          {dissolved}")
        print(f"  Conflates:          {conflates}")
        print(f"  Infrastructure:     {infra:,}")
        if sketch_lines:
            pct = (1 - sketch_lines / total_lines) * 100 if total_lines else 0
            print(f"  Sketch:             {sketch_lines} lines ({pct:.1f}% reduction)")
        print()
        print(f"  Layer 1 — Trivial proofs: {trivial_total} ({trivial_total*100//max(genuine,1)}% of genuine)")
        print(f"    rfl:              {rfl_count}")
        print(f"    Iff.rfl:          {iff_rfl_count}")
        print(f"    by simp:          {by_simp_count}")
        print(f"    by rfl:           {by_rfl_count}")
        print(f"    by norm_num:      {by_norm_num_count}")
        print(f"    by exact <term>:  {by_exact_count}")
        print(f"    by omega:         {by_omega_standalone}")
        print(f"    by decide:        {by_decide_standalone}")
        print()
        print(f"  Layer 2 — Tactic profile:")
        print(f"    rw:               {rw_uses:,}")
        print(f"    simp:             {simp_uses:,}")
        print(f"    exact:            {exact_uses:,}")
        print(f"    omega:            {omega_uses}")
        print(f"    ring:             {ring_uses}")
        print(f"    aesop:            {aesop_uses}")
        print(f"    decide:           {decide_uses}")
        print(f"    linarith:         {linarith_uses}")
        print(f"    Multi-line rw:    {multi_rw} chains (3+ rewrites)")
        print()
        print(f"  Layer 3 — Specialization:")
        print(f"    foo_nat/int/real: {spec_families}")
        print(f"{'=' * 60}")


# =============================================================================
# Stage 1: File-Level Compression
# =============================================================================

def cmd_compress(domain: str):
    """Compress an extracted domain by trying shorter proofs.

    For each file in Origin/Mathlib_<domain>/:
      1. Find declarations with proofs (`:= by ...` or `:= <term>`)
      2. For each, try: by simp, by omega, by ring, by decide, by aesop
      3. Test each attempt in the sandbox (isolation)
      4. Apply all successful compressions to the file
      5. Build the full compressed file with lake build
      6. If build passes: keep, report lines saved
      7. If build fails: revert, report what broke

    Usage: python3 scripts/origin2.py compress --domain Combinatorics
    """
    import sys
    sys.path.insert(0, str(Path(__file__).parent))
    from compress.sandbox import try_compress, CompressResult

    extract_dir = Config.extract_dir()
    d = extract_dir / f"Mathlib_{domain}"
    if not d.exists():
        print(f"  ✗ Mathlib_{domain}/ not found")
        return

    files = sorted(d.rglob("*.lean"))
    print(f"\n{'=' * 60}")
    print(f"  COMPRESS: {domain} ({len(files)} files)")
    print(f"{'=' * 60}")

    # Regex to find declarations with proofs
    decl_start_re = re.compile(r'^((?:@\[.*?\]\s*\n)*)(?:(?:protected|private|nonrec)\s+)*(theorem|lemma)\s+(\S+)')
    proof_re = re.compile(r':=\s*by\b', re.DOTALL)

    tactics = ["by simp", "by omega", "by ring", "by decide", "by aesop", "by norm_num", "by tauto"]

    total_files = 0
    total_compressed = 0
    total_lines_saved = 0
    total_declarations_tested = 0
    total_declarations_compressed = 0
    files_improved = 0

    for f in files:
        text = f.read_text(errors="replace")
        lines = text.split("\n")
        original_line_count = len(lines)

        # Extract imports and preamble (everything before first theorem/lemma)
        imports = []
        preamble_lines = []
        first_decl_line = None

        for i, line in enumerate(lines):
            if line.startswith("import "):
                imports.append(line)
            elif decl_start_re.match(line):
                first_decl_line = i
                break
            elif not line.startswith("/-") and not line.startswith("-/") and not line.startswith("--"):
                preamble_lines.append(line)

        if first_decl_line is None:
            continue

        preamble = "\n".join(preamble_lines)

        # Find declarations with by-proofs
        declarations = []
        i = first_decl_line
        while i < len(lines):
            m = decl_start_re.match(lines[i])
            if m:
                # Collect the full declaration
                decl_lines = [lines[i]]
                j = i + 1
                depth = 0
                while j < len(lines):
                    l = lines[j].strip()
                    if l.startswith("theorem ") or l.startswith("lemma ") or \
                       l.startswith("def ") or l.startswith("instance ") or \
                       l.startswith("@[") or l.startswith("end ") or \
                       l.startswith("section") or l.startswith("namespace") or \
                       l.startswith("variable") or l.startswith("open "):
                        if depth <= 0:
                            break
                    decl_lines.append(lines[j])
                    # Track brace/where depth roughly
                    depth += lines[j].count("{") + lines[j].count("where")
                    depth -= lines[j].count("}")
                    j += 1

                decl_text = "\n".join(decl_lines)
                name = m.group(3)
                attrs = m.group(1) or ""

                # Skip @[simp] and friends — invisible dependencies
                skip = False
                for attr in ("@[simp", "@[ext", "@[aesop", "@[norm_cast",
                             "@[norm_num", "@[gcongr", "@[positivity", "@[to_additive"):
                    if attr in attrs or attr in decl_text:
                        skip = True
                        break

                if not skip and proof_re.search(decl_text):
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
            total_files += 1
            continue

        total_files += 1
        total_declarations_tested += len(declarations)

        # Try compressing each declaration in the sandbox
        compressions = []
        for decl in declarations:
            for tactic in tactics:
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
                    total_declarations_compressed += 1
                    break  # first tactic wins

        if not compressions:
            continue

        # Apply compressions to the file
        backup = text
        new_lines = list(lines)
        # Apply in reverse order so line numbers stay valid
        for comp in sorted(compressions, key=lambda c: c["start_line"], reverse=True):
            compressed_lines = comp["compressed"].split("\n")
            new_lines[comp["start_line"]:comp["end_line"]] = compressed_lines

        new_text = "\n".join(new_lines)
        new_line_count = len(new_lines)
        lines_saved = original_line_count - new_line_count

        # Write compressed version
        f.write_text(new_text)

        # Build the full file
        rel = f.relative_to(extract_dir)
        module = str(rel).replace("/", ".").replace(".lean", "")

        try:
            result = subprocess.run(
                ["lake", "build", module],
                capture_output=True, text=True, timeout=180,
                cwd=str(Config.project_root()),
            )
            if result.returncode == 0:
                files_improved += 1
                total_compressed += len(compressions)
                total_lines_saved += lines_saved
                short_path = str(f.relative_to(extract_dir))
                print(f"  ✓ {short_path}: {len(compressions)} compressed, {lines_saved} lines saved")
                for comp in compressions:
                    print(f"      {comp['name']} → {comp['tactic']}")
            else:
                # Build failed — revert
                f.write_text(backup)
                short_path = str(f.relative_to(extract_dir))
                print(f"  ✗ {short_path}: build failed after compression, reverted")
        except subprocess.TimeoutExpired:
            f.write_text(backup)
            short_path = str(f.relative_to(extract_dir))
            print(f"  ✗ {short_path}: build timeout, reverted")

    print(f"\n{'=' * 60}")
    print(f"  RESULTS: {domain}")
    print(f"{'=' * 60}")
    print(f"  Files scanned:          {total_files}")
    print(f"  Files improved:         {files_improved}")
    print(f"  Declarations tested:    {total_declarations_tested}")
    print(f"  Declarations compressed:{total_declarations_compressed}")
    print(f"  Lines saved:            {total_lines_saved}")
    print(f"{'=' * 60}")


# =============================================================================
# Main
# =============================================================================

def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return

    self_mode = "--self" in sys.argv
    if self_mode:
        sys.argv.remove("--self")

    cmd = sys.argv[1]

    if cmd == "run":
        Pipeline().run()
    elif cmd == "classify":
        if len(sys.argv) > 2 and sys.argv[2] == "--all":
            cmd_classify_all(self_mode)
        elif len(sys.argv) > 2:
            cmd_classify(sys.argv[2], self_mode)
        else:
            print("Usage: origin2.py classify <DOMAIN> | --all")
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
            cmd_extract_domain(sys.argv[3]) if len(sys.argv) > 3 else print("Usage: origin2.py extract --domain <DOMAIN>")
        elif len(sys.argv) > 2:
            cmd_extract(Path(sys.argv[2]))
        else:
            print("Usage: origin2.py extract <file.lean> | --domain <DOMAIN>")
    elif cmd == "audit":
        if len(sys.argv) > 2:
            cmd_audit(sys.argv[2])
        else:
            print("Usage: origin2.py audit <DOMAIN> | --all")
    elif cmd == "compress":
        if len(sys.argv) > 2 and sys.argv[2] == "--domain":
            cmd_compress(sys.argv[3]) if len(sys.argv) > 3 else print("Usage: origin2.py compress --domain <DOMAIN>")
        elif len(sys.argv) > 2:
            cmd_compress(sys.argv[2])
        else:
            print("Usage: origin2.py compress --domain <DOMAIN>")
    else:
        print(f"Unknown command: {cmd}")
        print(__doc__)


if __name__ == "__main__":
    main()
