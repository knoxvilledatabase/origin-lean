#!/bin/bash
# Classify every declaration in a Mathlib domain.
#
# Usage: ./scripts/classify.sh NumberTheory
#        ./scripts/classify.sh --all
#        ./scripts/classify.sh Algebra > report.txt
#
# For each .lean file, counts:
#   DISSOLVES  — declarations with ≠ 0 / NeZero in signature
#   INSTANCE   — typeclass instances (infrastructure)
#   SIMP       — @[simp] lemmas (likely infrastructure)
#   TRIVIAL    — proofs that are rfl, h, or single-line by simp
#   GENUINE    — everything else (real content to write in Origin)
#
# Output: per-file summary + domain totals
# The GENUINE count is what the next session needs to write.

MATHLIB_DIR="/Users/tallbr00/Documents/venv/original-arithmetic/origin-mathlib/Mathlib"
ZERO_PATTERN="≠ 0\|NeZero\|ne_zero\|GroupWithZero"

classify_file() {
    local f="$1"
    local lines=$(wc -l < "$f" | tr -d ' ')

    # Count declaration types
    local total_decls=$(grep -c "^theorem\|^lemma\|^def\|^noncomputable def\|^instance\|^abbrev\|^protected theorem\|^protected lemma\|^protected def" "$f" 2>/dev/null)
    [ "$total_decls" -eq "0" ] && echo "EMPTY|0|0|0|0|0|$lines" && return

    # Instances (typeclass infrastructure)
    local instances=$(grep -c "^instance\|^noncomputable instance" "$f" 2>/dev/null)

    # @[simp] declarations
    local simps=$(grep -B1 "^theorem\|^lemma\|^protected theorem\|^protected lemma" "$f" 2>/dev/null | grep -c "@\[simp\]")

    # Declarations with ≠ 0 / NeZero in their signature line
    local dissolves=$(grep "^theorem\|^lemma\|^def\|^protected theorem\|^protected lemma" "$f" 2>/dev/null | grep -c "$ZERO_PATTERN")

    # Also count declarations whose NEXT few lines contain ≠ 0 (multi-line signatures)
    local dissolves_multi=$(grep -A3 "^theorem\|^lemma\|^protected theorem\|^protected lemma" "$f" 2>/dev/null | grep -c "$ZERO_PATTERN")
    dissolves=$((dissolves > dissolves_multi ? dissolves : dissolves_multi))

    # Trivial proofs: := rfl, := h, := by simp, := by rfl, := by exact h
    local trivial=$(grep -c ":= rfl\|:= h\b\|:= by simp\b\|:= by rfl\|:= by exact\|:= Iff.rfl\|:= (rfl :)" "$f" 2>/dev/null)

    # Genuine = total - instances - dissolves - trivial (floor at 0)
    # Note: some overlap possible, so we floor at 0
    local infra=$((instances + dissolves + trivial + simps))
    local genuine=$((total_decls - infra))
    [ "$genuine" -lt "0" ] && genuine=0

    echo "FILE|$total_decls|$dissolves|$instances|$simps|$trivial|$genuine|$lines"
}

classify_domain() {
    local domain="$1"
    local dir="$MATHLIB_DIR/$domain"

    if [ ! -d "$dir" ]; then
        echo "ERROR: $dir not found" >&2
        return 1
    fi

    local t_total=0 t_dissolves=0 t_instances=0 t_simps=0 t_trivial=0 t_genuine=0 t_lines=0
    local f_total=0 f_empty=0 f_dissolves_fully=0 f_has_genuine=0

    echo "=== $domain: Declaration-Level Classification ==="
    echo ""
    echo "GENUINE | DISSOLVE | INST | SIMP | TRIV | TOTAL | LINES | PATH"
    echo "--------|----------|------|------|------|-------|-------|-----"

    local tmpfile=$(mktemp)

    for f in $(find "$dir" -name "*.lean" | sort); do
        local result=$(classify_file "$f")
        local tag=$(echo "$result" | cut -d'|' -f1)
        local path=$(echo "$f" | sed "s|.*Mathlib/$domain/||")

        f_total=$((f_total + 1))

        if [ "$tag" = "EMPTY" ]; then
            f_empty=$((f_empty + 1))
            continue
        fi

        local decls=$(echo "$result" | cut -d'|' -f2)
        local dissolves=$(echo "$result" | cut -d'|' -f3)
        local instances=$(echo "$result" | cut -d'|' -f4)
        local simps=$(echo "$result" | cut -d'|' -f5)
        local trivial=$(echo "$result" | cut -d'|' -f6)
        local genuine=$(echo "$result" | cut -d'|' -f7)
        local lines=$(echo "$result" | cut -d'|' -f8)

        t_total=$((t_total + decls))
        t_dissolves=$((t_dissolves + dissolves))
        t_instances=$((t_instances + instances))
        t_simps=$((t_simps + simps))
        t_trivial=$((t_trivial + trivial))
        t_genuine=$((t_genuine + genuine))
        t_lines=$((t_lines + lines))

        if [ "$genuine" -eq "0" ]; then
            f_dissolves_fully=$((f_dissolves_fully + 1))
        else
            f_has_genuine=$((f_has_genuine + 1))
        fi

        printf "%7s | %8s | %4s | %4s | %4s | %5s | %5s | %s\n" \
            "$genuine" "$dissolves" "$instances" "$simps" "$trivial" "$decls" "$lines" "$path" >> "$tmpfile"
    done

    sort -rn "$tmpfile"
    rm -f "$tmpfile"

    echo ""
    echo "--- SUMMARY: $domain ---"
    echo "Files:        $f_total total, $f_empty empty, $f_dissolves_fully dissolve fully, $f_has_genuine have genuine content"
    echo "Declarations: $t_total total"
    echo "  Dissolves:  $t_dissolves (≠ 0 / NeZero in signature)"
    echo "  Instances:  $t_instances (typeclass infrastructure)"
    echo "  Simp:       $t_simps (@[simp] lemmas)"
    echo "  Trivial:    $t_trivial (rfl / by simp / exact h)"
    echo "  GENUINE:    $t_genuine ← THIS IS WHAT TO WRITE IN ORIGIN"
    echo "Lines:        $t_lines"
    echo ""
    echo "Files with genuine content (sorted by GENUINE desc) — these are the work."
}

classify_all_summary() {
    echo "=== ALL DOMAINS: Genuine Content Summary ==="
    echo ""
    echo "DOMAIN               | GENUINE | DISSOLVE | INFRA | TOTAL DECLS | FILES w/ CONTENT"
    echo "---------------------|---------|----------|-------|-------------|----------------"

    for dir in "$MATHLIB_DIR"/*/; do
        local domain=$(basename "$dir")
        local files=$(find "$dir" -name "*.lean" 2>/dev/null | wc -l | tr -d ' ')
        [ "$files" -lt "3" ] && continue

        local t_total=0 t_dissolves=0 t_genuine=0 t_infra=0 f_genuine=0

        for f in $(find "$dir" -name "*.lean"); do
            local result=$(classify_file "$f")
            local tag=$(echo "$result" | cut -d'|' -f1)
            [ "$tag" = "EMPTY" ] && continue

            local decls=$(echo "$result" | cut -d'|' -f2)
            local dissolves=$(echo "$result" | cut -d'|' -f3)
            local genuine=$(echo "$result" | cut -d'|' -f7)

            t_total=$((t_total + decls))
            t_dissolves=$((t_dissolves + dissolves))
            t_genuine=$((t_genuine + genuine))
            t_infra=$((t_infra + decls - genuine))
            [ "$genuine" -gt "0" ] && f_genuine=$((f_genuine + 1))
        done

        printf "%-20s | %7s | %8s | %5s | %11s | %s/%s\n" \
            "$domain" "$t_genuine" "$t_dissolves" "$t_infra" "$t_total" "$f_genuine" "$files"
    done | sort -t'|' -k2 -rn
}

# Main
if [ "$1" = "--all" ]; then
    classify_all_summary
elif [ -n "$1" ]; then
    classify_domain "$1"
else
    echo "Usage: ./scripts/classify.sh <DOMAIN>"
    echo "       ./scripts/classify.sh --all"
    echo ""
    echo "Classifies every declaration in every file:"
    echo "  GENUINE  — real content to write in Origin"
    echo "  DISSOLVE — ≠ 0 / NeZero hypotheses (vanish with none)"
    echo "  INSTANCE — typeclass infrastructure (free from Core)"
    echo "  SIMP     — @[simp] lemmas (free from Core)"
    echo "  TRIVIAL  — rfl / by simp / exact h (nothing to write)"
fi
