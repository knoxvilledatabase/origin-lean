#!/usr/bin/env python3
"""
Generate an Origin draft file from a Mathlib domain.

Reads extracted Mathlib files, collects domain-specific definitions,
outputs a draft Origin file importing only Core. The draft is ~80%
done — Claude Code rewrites it, lake build verifies in under a second.

Usage:
    python3 scripts/generate_origin.py Probability
    python3 scripts/generate_origin.py --list              show available domains
"""

import sys
from pathlib import Path

ROOT = Path(__file__).parent.parent
EXTRACTED = ROOT / "extracted"
ORIGIN = ROOT / "Origin"

sys.path.insert(0, str(Path(__file__).parent))
from compress.generator import generate_origin_draft, cmd_generate


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return

    if sys.argv[1] == "--list":
        # Meta/tooling domains — not mathematics, don't need sketches
        SKIP_DOMAINS = {"Deprecated", "Lean", "Std", "Tactic", "Testing", "Util"}

        domains = sorted(d.name.replace("Mathlib_", "")
                         for d in EXTRACTED.iterdir()
                         if d.is_dir() and d.name.startswith("Mathlib_"))
        existing = {f.stem for f in ORIGIN.glob("*.lean")}
        existing.update(f.stem.rstrip("2") for f in ORIGIN.glob("*2.lean"))

        math_domains = [d for d in domains if d not in SKIP_DOMAINS]
        skip_domains = [d for d in domains if d in SKIP_DOMAINS]

        print(f"\n  Math domains ({len(math_domains)}):\n")
        for dom in math_domains:
            has_sketch = dom in existing or f"{dom}2" in {f.stem for f in ORIGIN.glob("*.lean")}
            marker = "  ✓" if has_sketch else "  ·"
            print(f"  {marker} {dom}")

        print(f"\n  Skipped (tooling, not math): {', '.join(skip_domains)}")
        print(f"\n  ✓ = has sketch   · = needs sketch")
        return

    cmd_generate(sys.argv[1], EXTRACTED, ORIGIN)


if __name__ == "__main__":
    main()
