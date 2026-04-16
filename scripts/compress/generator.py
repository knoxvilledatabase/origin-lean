"""
Origin Draft Generator: reads a Mathlib domain, writes an Origin file.

Reverse-engineers the sketch pattern:
  - Keep: domain-specific definitions (def, structure, class, inductive)
  - Skip: theorems/lemmas (derivable from Core or demonstrations)
  - Add: a few demonstration theorems showing Option lift works
  - Output: a single Origin file importing only Core

The generator produces ~80% of the Origin file. The human refines
the remaining 20% — domain-specific definitions that need adjustment,
non-trivial proofs, Goal B classification headers.

Usage:
    from compress.generator import generate_origin_draft

    text = generate_origin_draft("Combinatorics", extracted_dir, origin_dir)
"""

import re
from pathlib import Path
from collections import defaultdict


def generate_origin_draft(
    domain: str,
    extracted_dir: Path,
    origin_dir: Path,
) -> str:
    """Generate an Origin draft file for a Mathlib domain.

    Reads all extracted files in extracted/Mathlib_<domain>/,
    collects domain-specific definitions, and outputs a draft
    Origin file structured like the existing sketches.

    Returns the file content as a string.
    """
    src = extracted_dir / f"Mathlib_{domain}"
    if not src.exists():
        return f"-- ERROR: {src} not found\n"

    files = sorted(src.rglob("*.lean"))
    if not files:
        return f"-- ERROR: no .lean files in {src}\n"

    # Collect stats
    total_genuine = 0
    total_dissolved = 0
    total_files = len(files)

    # Collect definitions by category
    definitions = []    # (name, kind, text, source_file)
    demonstrations = [] # sample theorems for Option lift

    decl_re = re.compile(
        r'^(?:protected\s+|private\s+|nonrec\s+|noncomputable\s+)*'
        r'(def|structure|class|inductive|abbrev)\s+(\S+)')

    theorem_re = re.compile(
        r'^(?:protected\s+|private\s+|nonrec\s+|noncomputable\s+)*'
        r'(theorem|lemma)\s+(\S+)')

    for f in files:
        text = f.read_text(errors="replace")
        lines = text.split("\n")

        # Parse header stats
        for line in lines[:5]:
            m = re.search(r'Genuine:\s*(\d+)', line)
            if m:
                total_genuine += int(m.group(1))
            m = re.search(r'Dissolved:\s*(\d+)', line)
            if m:
                total_dissolved += int(m.group(1))

        # Collect definitions
        i = 0
        while i < len(lines):
            line = lines[i]
            stripped = line.strip()

            # Skip imports, comments, sections, etc.
            if (stripped.startswith("import ") or stripped.startswith("/-") or
                stripped.startswith("--") or stripped.startswith("open ") or
                stripped.startswith("variable") or stripped.startswith("namespace") or
                stripped.startswith("end ") or stripped.startswith("section") or
                stripped.startswith("noncomputable") or stripped.startswith("set_option") or
                stripped.startswith("attribute") or stripped.startswith("instance") or
                not stripped):
                i += 1
                continue

            # Check for definition
            m = decl_re.match(stripped)
            if m:
                kind = m.group(1)
                name = m.group(2)

                # Collect the full declaration
                decl_lines = [lines[i]]
                j = i + 1
                depth = 0
                while j < len(lines):
                    l = lines[j].strip()
                    if l and decl_re.match(l) or theorem_re.match(l):
                        if depth <= 0:
                            break
                    if l.startswith("end ") or l.startswith("section") or l.startswith("namespace"):
                        if depth <= 0:
                            break
                    decl_lines.append(lines[j])
                    depth += lines[j].count("{") + lines[j].count("where")
                    depth -= lines[j].count("}")
                    j += 1

                decl_text = "\n".join(decl_lines).strip()
                rel_file = str(f.relative_to(src))
                definitions.append((name, kind, decl_text, rel_file))
                i = j
                continue

            i += 1

    # Group definitions by subdomain (based on file path)
    by_subdir = defaultdict(list)
    for name, kind, text, source in definitions:
        # Use first path component as section name
        parts = source.replace(".lean", "").split("/")
        section = parts[0] if len(parts) > 1 else "Core"
        by_subdir[section].append((name, kind, text))

    # Generate the draft
    out = []
    out.append("/-")
    out.append("Released under MIT license.")
    out.append("-/")
    out.append("import Origin.Core")
    out.append("")
    out.append("/-!")
    out.append(f"# {domain} on Option α (Core-based)")
    out.append(f"")
    out.append(f"**Goal B classification:** TODO — classify Category 1 vs 2")
    out.append(f"")
    out.append(f"Generated from {total_files} Mathlib files.")
    out.append(f"Genuine: {total_genuine} | Dissolved: {total_dissolved}")
    out.append(f"Definitions extracted: {len(definitions)}")
    out.append(f"")
    out.append(f"This is a DRAFT. Human review required:")
    out.append(f"- Verify each definition is domain-specific (not infrastructure)")
    out.append(f"- Add Goal B classification to the header")
    out.append(f"- Add demonstration theorems showing Option lift")
    out.append(f"- Remove definitions that Core.lean already handles")
    out.append(f"- Run: lake build Origin.{domain}")
    out.append(f"-/")
    out.append("")
    out.append("universe u")
    out.append("variable {α : Type u}")
    out.append("")

    # Write definitions grouped by section
    section_num = 0
    for section, defs in sorted(by_subdir.items()):
        if not defs:
            continue
        section_num += 1
        out.append(f"-- ============================================================================")
        out.append(f"-- {section_num}. {section.upper()}")
        out.append(f"-- ============================================================================")
        out.append("")
        for name, kind, text in defs[:10]:  # Cap at 10 per section to keep drafts manageable
            # Clean up: remove Mathlib-specific imports from the text
            cleaned = text
            out.append(cleaned)
            out.append("")
        if len(defs) > 10:
            out.append(f"-- ... and {len(defs) - 10} more definitions in {section}/")
            out.append("")

    # Add demonstration section
    out.append(f"-- ============================================================================")
    out.append(f"-- DEMONSTRATIONS: Option lift works for this domain")
    out.append(f"-- ============================================================================")
    out.append("")
    out.append(f"-- TODO: Add 3-5 demonstration theorems showing:")
    out.append(f"-- 1. none absorbs under domain operations (by simp)")
    out.append(f"-- 2. some values compute (by simp)")
    out.append(f"-- 3. A domain law lifts through Option (cases <;> simp [h])")
    out.append("")

    return "\n".join(out)


def cmd_generate(domain: str, extracted_dir: Path, origin_dir: Path):
    """Generate and write an Origin draft file."""
    # Check if sketch already exists
    for name in [f"{domain}.lean", f"{domain}2.lean"]:
        existing = origin_dir / name
        if existing.exists():
            lines = len(existing.read_text().split("\n"))
            print(f"  Sketch already exists: {existing} ({lines} lines)")
            print(f"  To regenerate, delete it first.")
            return

    draft = generate_origin_draft(domain, extracted_dir, origin_dir)
    draft_lines = len(draft.split("\n"))

    # Write to Origin/
    out_path = origin_dir / f"{domain}.lean"
    out_path.write_text(draft)

    print(f"  Generated: {out_path}")
    print(f"  Lines: {draft_lines}")
    print(f"  Next: review the draft, then run: lake build Origin.{domain}")
