# Public note — build instructions

`mobius-cpt-note.tex` is a mathematician-facing research note on the formalisation of the
Möbius-covariant PCT theorem ([T26] Theorem 3.10). English title and abstract, Japanese body.
The PDF is a build artefact and is not tracked; build it as below.

## Requirements

The file builds with **XeLaTeX**. Two toolchains are supported and both are verified.

| | Reference build | Ordinary TeX Live |
|---|---|---|
| Engine | Tectonic 0.17.0 (`x86_64-unknown-linux-musl`) | TeX Live 2022 or later, `xelatex` |
| Where it comes from | <https://github.com/tectonic-typesetting/tectonic/releases> | your distribution |
| Packages | fetched on demand by Tectonic (network needed on first run) | installed with the distribution |
| Japanese fonts | the four Noto CJK JP OTFs in `fonts/` (below) | `fonts/`, or Harano Aji, or system Noto |

The archival PDF is produced by the reference build. LuaLaTeX is not supported by this file as
written, because font loading goes through `xeCJK`.

LaTeX packages used: `fontspec`, `xeCJK`, `amsmath`, `amssymb`, `amsthm`, `geometry`, `tikz`,
`hyperref`. On Debian and Ubuntu the packages that supply them, and nothing more, are

```sh
sudo apt-get install --no-install-recommends \
  texlive-xetex texlive-pictures texlive-lang-japanese texlive-lang-chinese \
  texlive-fonts-recommended latexmk
```

Two of those are less obvious than they look and were found by building on a bare container:
`texlive-lang-chinese` supplies `ctexhook.sty`, which `xeCJK` loads unconditionally, and
`texlive-fonts-recommended` supplies `pzdr.tfm` (Zapf Dingbats), which `hyperref`'s XeTeX driver
loads for link borders. Without either, `xelatex` stops with a file-not-found error.
`texlive-latex-extra` is *not* required: no file from it is read during the build.

## Fonts

The document picks a Japanese font by trying three routes in order, so that the same file builds
in the reference environment and on a stock TeX Live without being edited:

1. **`\jafontdir/NotoSerifCJKjp-Regular.otf` and `-Bold.otf`, `\jafontdir/NotoSansCJKjp-Regular.otf`
   and `-Bold.otf`, by file name.** `\jafontdir` defaults to `fonts/` relative to the `.tex` file.
   This is the reference route and the one the archival PDF uses.
2. **`HaranoAjiMincho-Regular.otf` and `-Bold.otf`, `HaranoAjiGothic-Regular.otf` and `-Bold.otf`,
   by file name.** Part of every TeX Live since 2020 (the `haranoaji` package, in
   `texlive-lang-japanese` on Debian), so this route needs no download.
3. **The `Noto Serif CJK JP` and `Noto Sans CJK JP` families, by family name.** This one goes
   through fontconfig, so it needs the families installed system-wide (`fonts-noto-cjk`) and a
   populated fontconfig cache (`fontconfig`, then `fc-cache -f`).

**A route is taken only when every face it needs is present.** Each is guarded by one probe per
face, and any failing probe drops the whole route. A half-installed route — an interrupted
download into `fonts/`, a partial manual font installation — therefore falls through to the next
one instead of being selected and then failing on the missing face. If no route is available in
full the build stops with a `\PackageError` naming all three and the files each needs.

For route 1, place these four files in `fonts/`:

```
fonts/NotoSerifCJKjp-Regular.otf
fonts/NotoSerifCJKjp-Bold.otf
fonts/NotoSansCJKjp-Regular.otf
fonts/NotoSansCJKjp-Bold.otf
```

They are gitignored — the ignore pattern is `fonts` with no trailing slash, so that a `fonts`
symlink is ignored too and cannot be committed by accident. To fetch them:

```sh
cd docs/note && mkdir -p fonts && cd fonts
base=https://github.com/notofonts/noto-cjk/raw/main
curl -LO $base/Serif/OTF/Japanese/NotoSerifCJKjp-Regular.otf
curl -LO $base/Serif/OTF/Japanese/NotoSerifCJKjp-Bold.otf
curl -LO $base/Sans/OTF/Japanese/NotoSansCJKjp-Regular.otf
curl -LO $base/Sans/OTF/Japanese/NotoSansCJKjp-Bold.otf
```

To use Noto files installed elsewhere, override the directory instead of editing the file:
`\providecommand{\jafontdir}{...}` takes the first definition, so defining `\jafontdir` before
`\input`ting the document, or editing that one line, is enough. Route 1 looks fonts up by file
name and not by family name, because the reference environment has no fontconfig.

## Build

Reference build, which produces the archival PDF:

```sh
cd docs/note
tectonic -X compile mobius-cpt-note.tex
```

Ordinary TeX Live:

```sh
cd docs/note
latexmk -xelatex mobius-cpt-note.tex     # latexmk -C cleans up
```

Either produces `mobius-cpt-note.pdf`, 23 pages. Both are single-pass from the caller's point of
view — Tectonic reruns TeX internally until references settle, and `latexmk` does the same — and
each takes a few seconds and a few hundred megabytes of memory. A clean build emits no warning,
no missing character and no overfull or underfull box; treat any of those as a defect.

The bibliography is a `thebibliography` environment inside the `.tex`, so no BibTeX or Biber
run is needed. `mobius-cpt-note.bib` carries the same five entries in BibTeX form for reuse
and for the archival deposit; it is not read during the build, and the two must be kept in
step by hand.

## Not part of CI

This build is deliberately outside `scripts/check.sh` and outside the CI `check` job. The
repository gate covers Lean sources and the textual guards; adding a TeX toolchain to it is
out of scope.

## Status pinning

Section 7 quotes a repository commit, a date and two counts. All four values are defined once, as
`\pinnedcommit`, `\pinneddate`, `\auditcount` and `\coveragecount` near the top of the `.tex`.
When the note is revised against a newer revision, update them there and re-check the claims in
Sections 7 and 8 against that revision. The two counts are obtained as

```sh
git show <commit>:scripts/print_axioms.lean | grep -c '^#print axioms'   # \auditcount
```

for the number of declarations the live axiom audit queries, and the `COVERAGE OK — <n> public
theorems, all pinned` line of the CI `check` run on that commit for `\coveragecount`, the number
of public theorems the coverage guard enumerates and verifies as pinned. They count different
things and the note says so: every counted public theorem is among the audited declarations, and
the difference is made up of definitions and instances, which are pinned too. Do not substitute
one for the other.

`CITATION.cff` (`commit:`, `date-released:`) and the release bundle's `zenodo-metadata.json` and
`MANIFEST.md` quote the same revision and must be updated with it.

## Numbering

Definitions, lemmas and theorems carry [T26]'s own numbers rather than sequential ones, so that
a cross-reference and a citation of the same result read alike. `\srcnum{<number>}` fixes the
number of the environment that follows it; every such environment is preceded by one. Items
belonging to this note rather than to the source are lettered (`\srcnum{A}`, `\srcnum{B}`).
