# Public note — build instructions

`mobius-cpt-note.tex` is a mathematician-facing research note on the formalisation of the
Möbius-covariant PCT theorem ([T26] Theorem 3.10). English title and abstract, Japanese body.
The PDF is a build artefact and is not tracked; build it as below.

## Requirements

| Component | Version used | Where it comes from |
|---|---|---|
| Engine | Tectonic 0.17.0 (`x86_64-unknown-linux-musl`) | <https://github.com/tectonic-typesetting/tectonic/releases> |
| Underlying TeX engine | XeTeX (Tectonic's engine; packages fetched on demand) | Tectonic's bundle |
| Japanese fonts | Noto Serif CJK JP, Noto Sans CJK JP — Regular and Bold, OTF | <https://github.com/notofonts/noto-cjk> |

LaTeX packages (`fontspec`, `xeCJK`, `amsmath`, `amssymb`, `amsthm`, `mathrsfs`, `geometry`,
`tikz`, `hyperref`) are fetched by Tectonic on first run and need no separate installation.
A working network connection is required for that first run.

Any XeLaTeX installation with the same packages also works; Tectonic is not required.
LuaLaTeX is not supported by this file as written, because font loading goes through `xeCJK`.

## Fonts

The document resolves Japanese fonts by file name from the directory `\jafontdir`, which
defaults to `fonts/` relative to the `.tex` file. Place (or symlink) these four files there:

```
fonts/NotoSerifCJKjp-Regular.otf
fonts/NotoSerifCJKjp-Bold.otf
fonts/NotoSansCJKjp-Regular.otf
fonts/NotoSansCJKjp-Bold.otf
```

They are gitignored. To fetch them:

```sh
cd docs/note && mkdir -p fonts && cd fonts
base=https://github.com/notofonts/noto-cjk/raw/main
curl -LO $base/Serif/OTF/Japanese/NotoSerifCJKjp-Regular.otf
curl -LO $base/Serif/OTF/Japanese/NotoSerifCJKjp-Bold.otf
curl -LO $base/Sans/OTF/Japanese/NotoSansCJKjp-Regular.otf
curl -LO $base/Sans/OTF/Japanese/NotoSansCJKjp-Bold.otf
```

To use fonts installed elsewhere, override the directory instead of editing the file:
`\providecommand{\jafontdir}{...}` takes the first definition, so defining `\jafontdir`
before `\input`ting the document, or editing that one line, is enough. Font lookup is by
file name and not by family name, because the reference environment has no fontconfig.

## Build

```sh
cd docs/note
tectonic -X compile mobius-cpt-note.tex
```

Produces `mobius-cpt-note.pdf` (20 pages). The build is single-pass from the caller's point
of view; Tectonic reruns TeX internally until references settle. It takes a few seconds and
a few hundred megabytes of memory.

The bibliography is a `thebibliography` environment inside the `.tex`, so no BibTeX or Biber
run is needed. `mobius-cpt-note.bib` carries the same five entries in BibTeX form for reuse
and for the archival deposit; it is not read during the build, and the two must be kept in
step by hand.

## Not part of CI

This build is deliberately outside `scripts/check.sh` and outside the CI `check` job. The
repository gate covers Lean sources and the textual guards; adding a TeX toolchain to it is
out of scope.

## Status pinning

The note's Section 7 quotes a repository commit, a date and a count of audited declarations.
Those three values are defined once, as `\pinnedcommit`, `\pinneddate` and `\auditcount` near
the top of the `.tex`. When the note is revised against a newer revision, update them there
and re-check the claims in Sections 7 and 8 against that revision — in particular
`grep -c '^#print axioms' scripts/print_axioms.lean` for the count, and the CI `check` run on
that commit for the audit result.
