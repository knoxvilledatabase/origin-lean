#!/bin/bash
# Find the lowest-hanging fruit in a Mathlib domain.
#
# Usage: ./scripts/fruit.sh NumberTheory
#        ./scripts/fruit.sh NumberTheory 20    (top N, default 20)
#        ./scripts/fruit.sh --all              (top fruit across ALL domains)
#
# Ranks files by dissolution density: hits/lines.
# High density + small file = quick conversion, high payoff.

MATHLIB_DIR="/Users/tallbr00/Documents/venv/original-arithmetic/origin-mathlib/Mathlib"
PATTERN="≠ 0\|NeZero\|ne_zero\|GroupWithZero\|\.ne'\|inv_ne_zero\|cast_ne_zero\|succ_ne_zero\|pos_of_ne_zero"

fruit_domain() {
    local domain="$1"
    local top="${2:-20}"
    local dir="$MATHLIB_DIR/$domain"

    if [ ! -d "$dir" ]; then
        echo "ERROR: $dir not found" >&2
        return 1
    fi

    echo "=== $domain: Top $top by dissolution density ==="
    echo ""
    echo "DENSITY | HITS | LINES | THMS | PATH"
    echo "--------|------|-------|------|-----"

    for f in $(find "$dir" -name "*.lean"); do
        local hits=$(grep -c "$PATTERN" "$f" 2>/dev/null)
        [ "$hits" -eq "0" ] && continue
        local lines=$(wc -l < "$f" | tr -d ' ')
        [ "$lines" -lt "30" ] && continue
        local thms=$(grep -c "theorem\|lemma\|def " "$f" 2>/dev/null)
        [ "$thms" -eq "0" ] && continue
        local density=$((hits * 1000 / lines))
        local path=$(echo "$f" | sed "s|.*Mathlib/$domain/||")
        printf "%4s.%s%% | %4s | %5s | %4s | %s\n" \
            $((density/10)) $((density%10)) "$hits" "$lines" "$thms" "$path"
    done | sort -rn | head -"$top"
}

fruit_all() {
    local top="${1:-30}"
    echo "=== ALL DOMAINS: Top $top by dissolution density ==="
    echo ""
    echo "DENSITY | HITS | LINES | THMS | DOMAIN/PATH"
    echo "--------|------|-------|------|------------"

    for dir in "$MATHLIB_DIR"/*/; do
        local domain=$(basename "$dir")
        for f in $(find "$dir" -name "*.lean"); do
            local hits=$(grep -c "$PATTERN" "$f" 2>/dev/null)
            [ "$hits" -eq "0" ] && continue
            local lines=$(wc -l < "$f" | tr -d ' ')
            [ "$lines" -lt "30" ] && continue
            local thms=$(grep -c "theorem\|lemma\|def " "$f" 2>/dev/null)
            [ "$thms" -eq "0" ] && continue
            local density=$((hits * 1000 / lines))
            local path=$(echo "$f" | sed "s|.*Mathlib/||")
            printf "%4s.%s%% | %4s | %5s | %4s | %s\n" \
                $((density/10)) $((density%10)) "$hits" "$lines" "$thms" "$path"
        done
    done | sort -rn | head -"$top"
}

if [ "$1" = "--all" ]; then
    fruit_all "${2:-30}"
elif [ -n "$1" ]; then
    fruit_domain "$1" "${2:-20}"
else
    echo "Usage: ./scripts/fruit.sh <DOMAIN> [top_N]"
    echo "       ./scripts/fruit.sh --all [top_N]"
    echo ""
    echo "Ranks files by dissolution density (hits/lines)."
    echo "High density + small file = lowest hanging fruit."
fi
