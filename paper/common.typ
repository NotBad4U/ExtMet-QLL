// Shared imports and definitions, imported by every section and by spreadsheet.typ with
//   #import "common.typ": *
// Set/show rules live in main.typ, since they only apply where they are written.

#import "lib.typ": *

#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/curryst:0.6.0": prooftree, rule

// Lays out inference rules side by side, wrapping onto new lines
// (replaces curryst's own rule-set).
#let rule-set(column-gutter: 3em, row-gutter: 2em, ..rules) = {
  set par(leading: row-gutter)
  block(rules.pos().map(box).join(h(column-gutter, weak: true)))
}

// ---------------- notation ----------------

#let emptyctx = $chevron.l chevron.r$

// typing colon:  tcol(r) renders ":" with sensitivity r on top
#let tcol(r) = $attach(:, tr: #r)$

#let prop = "Prop"

// graded turnstile and soft connectives
#let ent(p) = $attach(tack.r, br: #p)$
#let psum(s) = $attach(plus.o, tr: #s)$
#let fa(s) = $attach(forall, tr: #s)$
#let ex(s) = $attach(exists, tr: #s)$

// ---------------- layout ----------------

#let tb(..args) = table(
  inset: 5pt,
  stroke: 0.4pt + rgb("#cbd5e1"),
  ..args,
)
