# Original paper and TeX source

**Strictly Convex Steklov-Isospectral Plane Domains**

Authors: **Tao Hu, Jiachen Shi, Quanyu Tang**. Version: **arXiv:2608.10557v2**, revised 15 August 2026.

- [Versioned record](https://arxiv.org/abs/2608.10557v2)
- [PDF](https://arxiv.org/pdf/2608.10557v2)
- [Original source download](https://arxiv.org/src/2608.10557v2)
- DOI: [10.48550/arXiv.2608.10557](https://doi.org/10.48550/arXiv.2608.10557)

## Files

| Path | Description |
| --- | --- |
| `2608.10557v2.pdf` | Original PDF, unchanged. |
| `2608.10557v2-source.tar` | Original downloaded source archive, unchanged; content is gzip-compressed despite its `.tar` suffix. |
| `2608.10557v2-tex.zip` | Convenient ZIP of the two unmodified TeX-source files, suitable for importing into a TeX editor. |
| `tex/pdes40_arxiv_v2.tex` | Original TeX, byte-identical to the archived file. |
| `tex/00README.json` | arXiv compilation metadata, unchanged. |

The source package contains these two source files and no separate bibliography or external figures; the bibliography is inline and diagrams use TikZ. Checksums are in `../SOURCE_SHA256SUMS`.

## Compile the paper

The supplied arXiv metadata specifies **pdfLaTeX / TeX Live 2025**. With a TeX installation including the packages used by the source, run from `paper/tex/`:

```sh
pdflatex -interaction=nonstopmode -halt-on-error pdes40_arxiv_v2.tex
pdflatex -interaction=nonstopmode -halt-on-error pdes40_arxiv_v2.tex
```

Compilation of the original TeX is separate from checking the Lean proof. The original PDF is included; no new PDF compilation is claimed by the packaging check.

## Rights

The [arXiv record](https://arxiv.org/abs/2608.10557v2) lists [arXiv's non-exclusive distribution license](https://arxiv.org/licenses/nonexclusive-distrib/1.0/license.html). That is the grant to arXiv, not a general Creative Commons or open-source license. These original paper files retain the authors' rights and are **excluded from the repository's Apache-2.0 grant**. Their inclusion follows the project owner's request; no additional permission from the coauthors is asserted here. Public redistribution requires the publisher's own rights or permission.
