/-
Extracted from Util/Superscript.lean
Genuine: 17 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Init
import Batteries.Tactic.Lint

noncomputable section

/-!
# A parser for superscripts and subscripts

This is intended for use in local notations. Basic usage is:
```
local syntax:arg term:max superscript(term) : term
local macro_rules | `($a:term $b:superscript) => `($a ^ $b)
```
where `superscript(term)` indicates that it will parse a superscript, and the `$b:superscript`
antiquotation binds the `term` argument of the superscript. Given a notation like this,
the expression `2⁶⁴` parses and expands to `2 ^ 64`.

The superscript body is considered to be the longest contiguous sequence of superscript tokens and
whitespace, so no additional bracketing is required (unless you want to separate two superscripts).
However, note that Unicode has a rather restricted character set for superscripts and subscripts
(see `Mapping.superscript` and `Mapping.subscript` in this file), so you should not use this
parser for complex expressions.
-/

universe u

namespace Mathlib.Tactic

open Lean Parser PrettyPrinter Std

namespace Superscript

instance : Hashable Char := ⟨fun c => hash c.1⟩

structure Mapping where
  /-- Map from "special" (e.g. superscript) characters to "normal" characters. -/
  toNormal : Std.HashMap Char Char := {}
  /-- Map from "normal" text to "special" (e.g. superscript) characters. -/
  toSpecial : Std.HashMap Char Char := {}
  deriving Inhabited

def mkMapping (s₁ s₂ : String) : Mapping := Id.run do
  let mut toNormal := {}
  let mut toSpecial := {}
  assert! s₁.length == s₂.length
  for sp in s₁.toSubstring, nm in s₂ do
    assert! !toNormal.contains sp
    assert! !toSpecial.contains nm
    toNormal := toNormal.insert sp nm
    toSpecial := toSpecial.insert nm sp
  pure { toNormal, toSpecial }

def Mapping.superscript := mkMapping
  "⁰¹²³⁴⁵⁶⁷⁸⁹ᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖ𐞥ʳˢᵗᵘᵛʷˣʸᶻᴬᴮᴰᴱᴳᴴᴵᴶᴷᴸᴹᴺᴼᴾꟴᴿᵀᵁⱽᵂᵝᵞᵟᵋᶿᶥᶹᵠᵡ⁺⁻⁼⁽⁾"
  "0123456789abcdefghijklmnopqrstuvwxyzABDEGHIJKLMNOPQRTUVWβγδεθιυφχ+-=()"

def Mapping.subscript := mkMapping
  "₀₁₂₃₄₅₆₇₈₉ₐₑₕᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓᴀʙᴄᴅᴇꜰɢʜɪᴊᴋʟᴍɴᴏᴘꞯʀꜱᴛᴜᴠᴡʏᴢᵦᵧᵨᵩᵪ₊₋₌₍₎"
  "0123456789aehijklmnoprstuvxABCDEFGHIJKLMNOPQRSTUVWYZβγρφχ+-=()"

partial def satisfyTokensFn (p : Char → Bool) (errorMsg : String) (many := true)
    (k : Array (String.Pos × String.Pos × String.Pos) → ParserState → ParserState) :
    ParserFn := fun c s =>
  let start := s.pos
  let s := takeWhile1Fn p errorMsg c s
  if s.hasError then s else
  let stop := s.pos
  let s := whitespace c s
  let toks := #[(start, stop, s.pos)]
  if many then
    let rec /-- Loop body of `satisfyTokensFn` -/
    loop (toks) (s : ParserState) : ParserState :=
      let start := s.pos
      let s := takeWhileFn p c s
      if s.pos == start then k toks s else
        let stop := s.pos
        let s := whitespace c s
        let toks := toks.push (start, stop, s.pos)
        loop toks s
    loop toks s
  else k toks s

variable {α : Type u} [Inhabited α] (as : Array α) (leftOfPartition : α → Bool) in

@[specialize]
def partitionPoint (lo := 0) (hi := as.size) : Nat :=
  if lo < hi then
    let m := (lo + hi)/2
    let a := as.get! m
    if leftOfPartition a then
      partitionPoint (m+1) hi
    else
      partitionPoint lo m
  else lo
  termination_by hi - lo

partial def scriptFnNoAntiquot (m : Mapping) (errorMsg : String) (p : ParserFn)
    (many := true) : ParserFn := fun c s =>
  let start := s.pos
  satisfyTokensFn m.toNormal.contains errorMsg many c s (k := fun toks s => Id.run do
    let input := c.input
    let mut newStr := ""
    -- This consists of a sorted array of `(from, to)` pairs, where indexes `from+i` in `newStr`
    -- such that `from+i < from'` for the next element of the array, are mapped to `to+i`.
    let mut aligns := #[((0 : String.Pos), start)]
    for (start, stopTk, stopWs) in toks do
      let mut pos := start
      while pos < stopTk do
        let c := input.get pos
        let c' := m.toNormal[c]!
        newStr := newStr.push c'
        pos := pos + c
        if c.utf8Size != c'.utf8Size then
          aligns := aligns.push (newStr.endPos, pos)
      newStr := newStr.push ' '
      if stopWs.1 - stopTk.1 != 1 then
        aligns := aligns.push (newStr.endPos, stopWs)
    let ictx := mkInputContext newStr "<superscript>"
    let s' := p.run ictx c.toParserModuleContext c.tokens (mkParserState newStr)
    let rec /-- Applies the alignment mapping to a position. -/
    align (pos : String.Pos) :=
      let i := partitionPoint aligns (·.1 ≤ pos)
      let (a, b) := aligns[i - 1]!
      pos - a + b
    let s := { s with pos := align s'.pos, errorMsg := s'.errorMsg }
    if s.hasError then return s
    let rec
    /-- Applies the alignment mapping to a `Substring`. -/
    alignSubstr : Substring → Substring
      | ⟨_newStr, start, stop⟩ => ⟨input, align start, align stop⟩,
    /-- Applies the alignment mapping to a `SourceInfo`. -/
    alignInfo : SourceInfo → SourceInfo
      | .original leading pos trailing endPos =>
        -- Marking these as original breaks semantic highlighting,
        -- marking them as canonical breaks the unused variables linter. :(
        .original (alignSubstr leading) (align pos) (alignSubstr trailing) (align endPos)
      | .synthetic pos endPos canonical =>
        .synthetic (align pos) (align endPos) canonical
      | .none => .none,
     /-- Applies the alignment mapping to a `Syntax`. -/
     alignSyntax : Syntax → Syntax
      | .missing => .missing
      | .node info kind args => .node (alignInfo info) kind (args.map alignSyntax)
      | .atom info val =>
        -- We have to preserve the unsubscripted `val` even though it breaks `Syntax.reprint`
        -- because basic parsers like `num` read the `val` directly
        .atom (alignInfo info) val
      | .ident info rawVal val preresolved =>
        .ident (alignInfo info) (alignSubstr rawVal) val preresolved
    s.pushSyntax (alignSyntax s'.stxStack.back)
  )

def scriptParser (m : Mapping) (antiquotName errorMsg : String) (p : Parser)
    (many := true) (kind : SyntaxNodeKind := by exact decl_name%) : Parser :=
  let tokens := "$" :: (m.toNormal.toArray.map (·.1.toString) |>.qsort (·<·)).toList
  let antiquotP := mkAntiquot antiquotName `term (isPseudoKind := true)
  let p := Superscript.scriptFnNoAntiquot m errorMsg p.fn many
  node kind {
    info.firstTokens := .tokens tokens
    info.collectTokens := (tokens ++ ·)
    fn := withAntiquotFn antiquotP.fn p (isCatAntiquot := true)
  }

def scriptParser.parenthesizer (k : SyntaxNodeKind) (p : Parenthesizer) : Parenthesizer :=
  Parenthesizer.node.parenthesizer k p

def _root_.Std.Format.mapStringsM {m} [Monad m] (f : Format) (f' : String → m String) : m Format :=
  match f with
  | .group f b => (.group · b) <$> Std.Format.mapStringsM f f'
  | .tag t g => .tag t <$> Std.Format.mapStringsM g f'
  | .append f g => .append <$> Std.Format.mapStringsM f f' <*> Std.Format.mapStringsM g f'
  | .nest n f => .nest n <$> Std.Format.mapStringsM f f'
  | .text s => .text <$> f' s
  | .align _ | .line | .nil => pure f

def scriptParser.formatter (name : String) (m : Mapping) (k : SyntaxNodeKind) (p : Formatter) :
    Formatter := do
  let stack ← modifyGet fun s => (s.stack, {s with stack := #[]})
  Formatter.node.formatter k p
  let st ← get
  let transformed : Except String _ := st.stack.mapM (·.mapStringsM fun s => do
    let .some s := s.toList.mapM (m.toSpecial.insert ' ' ' ').get? | .error s
    .ok ⟨s⟩)
  match transformed with
  | .error err =>
    -- TODO: this only appears if the caller explicitly calls the pretty-printer
    Lean.logErrorAt (← get).stxTrav.cur s!"Not a {name}: '{err}'"
    set { st with stack := stack ++ st.stack }
  | .ok newStack =>
    set { st with stack := stack ++ newStack }

end Superscript

def superscript (p : Parser) : Parser :=
  Superscript.scriptParser .superscript "superscript" "expected superscript character" p

@[combinator_parenthesizer superscript]
def superscript.parenthesizer := Superscript.scriptParser.parenthesizer ``superscript

@[combinator_formatter superscript]
def superscript.formatter :=
  Superscript.scriptParser.formatter "superscript" .superscript ``superscript

def subscript (p : Parser) : Parser :=
  Superscript.scriptParser .subscript "subscript" "expected subscript character" p

@[combinator_parenthesizer subscript]
def subscript.parenthesizer := Superscript.scriptParser.parenthesizer ``subscript

@[combinator_formatter subscript]
def subscript.formatter := Superscript.scriptParser.formatter "subscript" .subscript ``subscript

initialize

  registerAlias `superscript ``superscript superscript

  registerAliasCore Formatter.formatterAliasesRef `superscript superscript.formatter

  registerAliasCore Parenthesizer.parenthesizerAliasesRef `superscript superscript.parenthesizer

  registerAlias `subscript ``subscript subscript

  registerAliasCore Formatter.formatterAliasesRef `subscript subscript.formatter

  registerAliasCore Parenthesizer.parenthesizerAliasesRef `subscript subscript.parenthesizer

end Mathlib.Tactic
