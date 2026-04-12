#!/bin/bash
# Duplication audit for origin-lean
# Run after any change: ./scripts/audit.sh
# Exit code 0 = clean, 1 = duplicates found

set -e
cd "$(dirname "$0")/.."

FOUND=0
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

echo "=== origin-lean duplication audit ==="
echo ""

# 1. rfl theorems restating mul_contents_contents
echo "--- Check 1: rfl restates of mul_contents_contents ---"
while IFS= read -r line; do
    file=$(echo "$line" | cut -d: -f1)
    lnum=$(echo "$line" | cut -d: -f2)
    # Skip Foundation.lean's own definition
    if [[ "$file" == "Val/Foundation.lean" ]]; then continue; fi
    echo -e "${RED}DUPLICATE${NC} $file:$lnum — rfl restatement of mul_contents_contents"
    FOUND=1
done < <(grep -n "mul .* (contents .*) (contents .*) = contents .* := rfl" Val/**/*.lean Val/*.lean 2>/dev/null | grep -v "smul " || true)

# 2. rfl theorems restating add_contents_contents
echo "--- Check 2: rfl restates of add_contents_contents ---"
while IFS= read -r line; do
    file=$(echo "$line" | cut -d: -f1)
    lnum=$(echo "$line" | cut -d: -f2)
    if [[ "$file" == "Val/Foundation.lean" ]]; then continue; fi
    echo -e "${RED}DUPLICATE${NC} $file:$lnum — rfl restatement of add_contents_contents"
    FOUND=1
done < <(grep -n "add .* (contents .*) (contents .*) = contents .* := rfl" Val/**/*.lean Val/*.lean 2>/dev/null || true)

# 3. rfl theorems restating valMap_contents
echo "--- Check 3: rfl restates of valMap_contents ---"
while IFS= read -r line; do
    file=$(echo "$line" | cut -d: -f1)
    lnum=$(echo "$line" | cut -d: -f2)
    if [[ "$file" == "Val/Foundation.lean" ]]; then continue; fi
    echo -e "${RED}DUPLICATE${NC} $file:$lnum — rfl restatement of valMap_contents"
    FOUND=1
done < <(grep -n "valMap .* (contents .*) = contents .* := rfl" Val/**/*.lean Val/*.lean 2>/dev/null || true)

# 4. _ne_origin theorems (Foundation has @[simp] contents_ne_origin)
echo "--- Check 4: _ne_origin theorems ---"
while IFS= read -r line; do
    file=$(echo "$line" | cut -d: -f1)
    lnum=$(echo "$line" | cut -d: -f2)
    if [[ "$file" == "Val/Foundation.lean" ]]; then continue; fi
    echo -e "${RED}DUPLICATE${NC} $file:$lnum — _ne_origin (Foundation has contents_ne_origin)"
    FOUND=1
done < <(grep -n "contents .* ≠ origin\|contents .* ≠ (origin" Val/**/*.lean Val/*.lean 2>/dev/null | grep "theorem\|lemma" || true)

# 5. _exists theorems (Foundation has contents_exists)
echo "--- Check 5: trivial _exists theorems ---"
while IFS= read -r line; do
    file=$(echo "$line" | cut -d: -f1)
    lnum=$(echo "$line" | cut -d: -f2)
    if [[ "$file" == "Val/Foundation.lean" ]]; then continue; fi
    echo -e "${RED}DUPLICATE${NC} $file:$lnum — trivial exists (Foundation has contents_exists)"
    FOUND=1
done < <(grep -n "∃ r, .* = contents r.*⟨.*, rfl⟩" Val/**/*.lean Val/*.lean 2>/dev/null || true)

# 6. Theorems that are just "by intro h; cases h" (= contents_ne_origin)
echo "--- Check 6: manual _ne_origin proofs ---"
while IFS= read -r line; do
    file=$(echo "$line" | cut -d: -f1)
    lnum=$(echo "$line" | cut -d: -f2)
    if [[ "$file" == "Val/Foundation.lean" ]]; then continue; fi
    echo -e "${YELLOW}SUSPECT${NC} $file:$lnum — manual ne_origin proof (use by simp)"
    FOUND=1
done < <(grep -n "by intro h; cases h$\|by intro h₁; cases h₁$" Val/**/*.lean Val/*.lean 2>/dev/null || true)

# 7. Cross-file theorem name collisions
echo "--- Check 7: cross-file name collisions ---"
grep -h "^theorem \|^lemma " Val/**/*.lean Val/*.lean 2>/dev/null | \
    sed 's/^theorem //;s/^lemma //;s/ .*//' | \
    sort | uniq -d | while read -r name; do
    files=$(grep -l "^theorem $name \|^lemma $name " Val/**/*.lean Val/*.lean 2>/dev/null | tr '\n' ', ')
    echo -e "${RED}COLLISION${NC} '$name' defined in: $files"
    FOUND=1
done

# 8. Identical abbrev aliases (two abbrevs pointing to same thing)
echo "--- Check 8: duplicate abbrev aliases ---"
grep -h "^abbrev .* := valMap\|^abbrev .* := mul\|^abbrev .* := valPair" Val/**/*.lean Val/*.lean 2>/dev/null | \
    sed 's/^abbrev [^ ]* //;s/ :.*:= /→/' | \
    sort | uniq -d | while read -r target; do
    echo -e "${YELLOW}SUSPECT${NC} multiple abbrevs pointing to: $target"
    FOUND=1
done

# 9. Theorems restating valMap_comp
echo "--- Check 9: restates of valMap_comp ---"
while IFS= read -r line; do
    file=$(echo "$line" | cut -d: -f1)
    lnum=$(echo "$line" | cut -d: -f2)
    if [[ "$file" == "Val/Foundation.lean" || "$file" == "Val/Category.lean" ]]; then continue; fi
    echo -e "${RED}DUPLICATE${NC} $file:$lnum — restatement of valMap_comp"
    FOUND=1
done < <(grep -n "valMap (.*∘.*) = valMap .* ∘ valMap\|valMap_comp" Val/**/*.lean Val/*.lean 2>/dev/null | grep ":= valMap_comp" || true)

# Summary
echo ""
echo "=== Line count ==="
total=$(cat Val/**/*.lean Val/*.lean | wc -l | tr -d ' ')
echo "Total: $total lines across $(ls Val/**/*.lean Val/*.lean | wc -l | tr -d ' ') files"
echo ""

if [ $FOUND -eq 0 ]; then
    echo -e "${GREEN}CLEAN${NC} — no duplicates found"
    exit 0
else
    echo -e "${RED}DUPLICATES FOUND${NC} — fix before proceeding"
    exit 1
fi
