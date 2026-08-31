# PLDI 2026 format conversion

[SUPERSEDED → `2026-08-31-oseair-compiler-rules.md`] The format remains
unchanged, but the paper was subsequently expanded from seven to eleven pages
with derived OSEA-IR and compiler rules plus projection flattening. This entry
records the initial PLDI reflow.

[OBS] Reflowed `mirlite-oseair-correctness.typ` from a custom six-page A4
overview into the PLDI 2026 research-paper submission layout.

## Format decision

[FACT] PLDI 2026 permits at most 20 pages of main text, excluding the
bibliography. Its research-paper format is the PACMPL-compatible `acmsmall`
layout: single column, 10 pt text, 12 pt baseline spacing, anonymous review,
and the ACM trim geometry. This differs from the older two-column SIGPLAN
proceedings format.

The document now imports `@preview/faithful-acmart:0.1.0` with
`format: "acmsmall"`, `anonymous: true`, `review: true`, `screen: true`, and
`nonacm: true`. The former overview box is ACM front matter: title, anonymous
author marker, abstract, and keywords. Forced one-topic-per-page breaks were
removed so the paper flows naturally.

## Reproducibility boundary

The Typst package is an unofficial port, not an ACM-supported template. It is
tested against the real `acmart` class and tracks its fonts, page geometry,
spacing, front matter, headers, folios, and review line numbers. The required
Libertinus and Inconsolatazi4 font files and their OFL license are vendored in
`assets/fonts/acm/`. Build from the repository root with:

```sh
typst compile --font-path assets/fonts/acm mirlite-oseair-correctness.typ
```

For final ACM production/TAPS, conversion to the official LaTeX or Word source
workflow may still be required even though the review PDF matches the format.

## Verification

[EMP] Verified against repository commit `40b1035` using Typst 0.15.1 and
`faithful-acmart` 0.1.0. The PDF compiles without warnings, uses the actual
Libertinus Serif/Sans/Math and Inconsolatazi4 fonts, and renders as seven
single-column pages. All seven 110-PPI page renders were visually inspected;
the inference rules, tables, and callout boxes have no overflow or unintended
split. Seven pages is safely below PLDI's 20-page main-text limit.

The concurrent modification to `src/obseq3/proof/ref.lean` was not touched.
