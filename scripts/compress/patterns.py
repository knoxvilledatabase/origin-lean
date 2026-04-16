"""
Compression patterns for Origin extraction.

Each pattern is a self-contained class:
  - name: what it's called
  - description: what it detects and why it's safe to compress
  - match(): does this block qualify?
  - compress(): return None to delete, or return compressed text

Patterns are registered in get_patterns(). The Extractor iterates them
in order — first match wins. A pattern that returns None deletes the
declaration entirely. A pattern that returns a string replaces it.

The dependency guard (in Extractor) prevents deletion of any declaration
that other non-trivial declarations reference by name.

To add a new pattern:
  1. Create a class inheriting CompressionPattern
  2. Implement match() and compress()
  3. Add it to get_patterns()
  4. Run the pipeline: python3 scripts/origin2.py run
  5. Update README.md with before/after numbers
"""

import re
import sys
sys.path.insert(0, str(__import__('pathlib').Path(__file__).parent.parent))
from origin2 import Block


class CompressionPattern:
    """Base class for compression patterns."""
    name: str = ""
    description: str = ""

    def match(self, block: Block) -> bool:
        """Return True if this pattern applies to the block."""
        raise NotImplementedError

    def compress(self, block: Block) -> str | None:
        """Return None to delete, or return compressed replacement text."""
        raise NotImplementedError


class CoreTrivialProof(CompressionPattern):
    """
    Declarations whose entire proof is already handled by Core.lean.

    Core.lean provides:
      - Instances for *, +, -, on Option α
      - @[simp] lemmas: mul_none_left, mul_none_right, add_none_left, etc.
      - The origin theorem: n * zero = zero

    Any declaration whose proof is just `rfl`, `Iff.rfl`, `by simp`,
    `by rfl`, `by trivial`, `by exact <single-term>`, or `by norm_num`
    is already derivable from Core.lean's simp set. Keeping it verbatim
    is duplication.

    Safety: only matches theorem/lemma/def/abbrev (not instances, classes,
    structures). Does NOT delete declarations referenced by other
    non-trivial declarations in the same file (dependency guard in Extractor).

    First measurement (2026-04-15):
      21,649 declarations match out of 160,525 genuine (13.5%)
      - 14,601 rfl
      - 1,253 Iff.rfl
      - 1,251 by simp (variants)
      - 170 by rfl
      - 42 by norm_num
    """
    name = "core_trivial_proof"
    description = "Declarations whose proof Core.lean's simp set already handles"

    TRIVIAL_PROOF = re.compile(
        r':=\s*('
        r'rfl'
        r'|Iff\.rfl'
        r'|by\s+simp\s*$'
        r'|by\s+rfl\s*$'
        r'|by\s+trivial\s*$'
        r'|by\s+exact\s+\S+\s*$'
        r'|by\s+norm_num\s*$'
        r')',
        re.MULTILINE
    )

    DECL_KEYWORDS = ("theorem ", "lemma ", "def ", "abbrev ")

    def match(self, block: Block) -> bool:
        if block.kind != "decl":
            return False
        if block.classification not in ("genuine", "simp_trivial", "trivial"):
            return False
        if not any(kw in block.text[:60] for kw in self.DECL_KEYWORDS):
            return False
        return bool(self.TRIVIAL_PROOF.search(block.text))

    def compress(self, block: Block) -> str | None:
        return None  # delete — Core.lean already proves it


def get_patterns() -> list[CompressionPattern]:
    """Return all registered compression patterns in priority order."""
    return [
        CoreTrivialProof(),
    ]
