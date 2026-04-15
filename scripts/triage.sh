#!/bin/bash
# Triage a Mathlib domain for Origin conversion.
#
# Usage: ./scripts/triage.sh NumberTheory
#        ./scripts/triage.sh Algebra
#        ./scripts/triage.sh --all
#
# Reads from: origin-mathlib/Mathlib/<DOMAIN>/
# Outputs: Type A/B classification, hit count, theorem count, line count
#
# The pattern: ≠ 0, NeZero, .ne', inv_ne_zero, cast_ne_zero, etc.
# Every hit is a line touching zero-management — the collapse's surface area.

MATHLIB_DIR="/Users/tallbr00/Documents/venv/original-arithmetic/origin-mathlib/Mathlib"
PATTERN="≠ 0\|NeZero\|ne_zero\|GroupWithZero\|\.ne'\|inv_ne_zero\|cast_ne_zero\|succ_ne_zero\|pos_of_ne_zero"

triage_domain() {
    local domain="$1"
    local dir="$MATHLIB_DIR/$domain"

    if [ ! -d "$dir" ]; then
        echo "ERROR: $dir not found" >&2
        return 1
    fi

    local typeA=0 typeB=0 totalHits=0 totalLines=0 totalTheorems=0

    echo "=== $domain ==="
    echo ""
    echo "TYPE | HITS | THMS | LINES | PATH"
    echo "-----|------|------|-------|-----"

    for f in $(find "$dir" -name "*.lean" | sort); do
        local hits=$(grep -c "$PATTERN" "$f" 2>/dev/null)
        local theorems=$(grep -c "theorem\|lemma\|def " "$f" 2>/dev/null)
        local lines=$(wc -l < "$f" | tr -d ' ')
        local path=$(echo "$f" | sed "s|.*Mathlib/$domain/||")

        if [ "$hits" -eq "0" ]; then
            echo "A    |    0 | $(printf '%4s' $theorems) | $(printf '%5s' $lines) | $path"
            typeA=$((typeA + 1))
        else
            echo "B    | $(printf '%4s' $hits) | $(printf '%4s' $theorems) | $(printf '%5s' $lines) | $path"
            typeB=$((typeB + 1))
            totalHits=$((totalHits + hits))
        fi
        totalLines=$((totalLines + lines))
        totalTheorems=$((totalTheorems + theorems))
    done | sort -t'|' -k2 -rn

    echo ""
    echo "--- SUMMARY ---"
    echo "Type A (pure math):         $typeA files"
    echo "Type B (collapse involved): $typeB files"
    echo "Total hits:                 $totalHits"
    echo "Total theorems:             $totalTheorems"
    echo "Total lines:                $totalLines"
    echo "Collapse density:           $(( totalHits * 100 / (totalLines + 1) ))% of lines"
}

triage_all() {
    echo "=== ALL DOMAINS ==="
    echo ""
    echo "DOMAIN               | FILES |  TYPE_B |   HITS | DENSITY"
    echo "---------------------|-------|---------|--------|--------"

    for dir in "$MATHLIB_DIR"/*/; do
        local domain=$(basename "$dir")
        local files=$(find "$dir" -name "*.lean" | wc -l | tr -d ' ')
        [ "$files" -lt "3" ] && continue

        local typeB=$(find "$dir" -name "*.lean" -exec grep -l "$PATTERN" {} + 2>/dev/null | wc -l | tr -d ' ')
        local hits=$(find "$dir" -name "*.lean" -exec grep -c "$PATTERN" {} + 2>/dev/null | awk -F: '{sum+=$NF} END {print sum+0}')
        local lines=$(find "$dir" -name "*.lean" -exec cat {} + 2>/dev/null | wc -l | tr -d ' ')
        local sigs=$(find "$dir" -name "*.lean" -exec grep -c "≠ 0\|NeZero\|ne_zero\|GroupWithZero" {} + 2>/dev/null | awk -F: '{sum+=$NF} END {print sum+0}')
        local thread=$((hits - sigs))
        local pct=$((typeB * 100 / files))

        printf "%-20s | %5s | %3s/%s | %6s | %s%% (%s sigs + %s threading)\n" \
            "$domain" "$files" "$typeB" "$files" "$hits" "$pct" "$sigs" "$thread"
    done | sort -t'|' -k4 -rn
}

# Main
if [ "$1" = "--all" ]; then
    triage_all
elif [ -n "$1" ]; then
    triage_domain "$1"
else
    echo "Usage: ./scripts/triage.sh <DOMAIN>"
    echo "       ./scripts/triage.sh --all"
    echo ""
    echo "Examples:"
    echo "  ./scripts/triage.sh NumberTheory"
    echo "  ./scripts/triage.sh Algebra"
    echo "  ./scripts/triage.sh --all"
fi
