#!/usr/bin/env python3
"""Apply the documented corrections to the exact 25-page Wishart manuscript.

Usage: python3 verification/correct_manuscript.py ORIGINAL.pdf
The output is paper.pdf. Only the listed page regions are changed.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess

import fitz

ROOT = Path(__file__).resolve().parent.parent

PATCHES = [
    {
        "name": "anderson_sections",
        "page": 14,
        "rect": [105.2, 267.1, 508.8, 405.0],
        "position": [106.2, 268.1],
        "width": 399.6,
        "max_height": 136.0,
        "anchor": "concave even function",
        "text": r"""Its sublevel sets are symmetric and convex. To compare Gaussian masses,
intersect the set translated by $-rv$ with a centered ellipsoidal density
level set $E$ in the Gaussian support. These sections satisfy
$A_{-r}=-A_r$ and
$\theta A_{r_1}+(1-\theta)A_{r_2}\subseteq A_{\theta r_1+(1-\theta)r_2}$.
For $0\le s\le r$, $r>0$, choose $\theta=(1+s/r)/2$. Then
$\theta A_r+(1-\theta)A_{-r}\subseteq A_s$. If $|A_r|>0$,
Brunn--Minkowski and symmetry give $|A_s|\ge |A_r|$; if $|A_r|=0$,
this is automatic. Integrating the ellipsoidal layers proves the Gaussian
assertion; zero-dimensional support is immediate. Thus the shifted row's
gauge is stochastically increasing, and any nondecreasing outer function
preserves the comparison.""",
    },
    {
        "name": "effective_rank_threshold",
        "page": 18,
        "rect": [105.2, 390.5, 507.0, 421.0],
        "position": [106.2, 391.8],
        "width": 399.6,
        "max_height": 29.0,
        "anchor": "joint finite-moment condition",
        "text": r"""\noindent
\makebox[\linewidth][c]{$\displaystyle 2\sum_{i:\,k_i>0}\nu_i<\beta-p+1,$}\makebox[0pt][r]{(18)}""",
    },
    {
        "name": "effective_rank_proof",
        "page": 18,
        "rect": [105.2, 500.5, 509.0, 549.5],
        "position": [106.2, 501.5],
        "width": 399.6,
        "max_height": 47.0,
        "anchor": "For positive powers",
        "text": r"""\textit{Proof.} The spectral factors $\prod_j(\lambda_j+c_i)^{\nu_i}$ have the required
common monotonicity. Put $s=\sum_{i:\,k_i>0}\nu_i$; empty determinants are $1$.
Interlacing after orthonormalization and bounding the shifts by scalar matrices gives""",
    },
    {
        "name": "beta_ii_empty_compressions",
        "page": 20,
        "rect": [105.2, 210.5, 508.5, 302.0],
        "position": [106.2, 212.0],
        "width": 399.6,
        "max_height": 89.0,
        "anchor": "joint finiteness is equivalent",
        "text": r"""A zero-column determinant is $1$, with every moment finite. For nonnegative
powers the joint criterion is (18), with no overlap restriction. Indeed, take
$X=Y^{1/2}ZY^{1/2}$ with independent $Z\sim W_p(\alpha,I)$.
The bound $X\preceq\|Z\|Y$ and the finite moments of $\|Z\|$ give
sufficiency. The event $Z\succeq I$ has positive probability and gives necessity.""",
    },
]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("original", type=Path)
    args = parser.parse_args()
    original = args.original.resolve()
    expected = json.loads((ROOT / "verification/manuscript-input.json").read_text())
    actual = hashlib.sha256(original.read_bytes()).hexdigest()
    if actual != expected["sha256"]:
        raise ValueError("Input differs from the reviewed 25-page manuscript")
    work = ROOT / ".lake/reports/manuscript"
    work.mkdir(parents=True, exist_ok=True)
    doc = fitz.open(original)
    if len(doc) != 25:
        raise ValueError("Expected exactly 25 manuscript pages")
    output_records = []
    for patch in PATCHES:
        page = doc[patch["page"] - 1]
        if patch["anchor"] not in page.get_text():
            raise ValueError(f"Missing reviewed text anchor: {patch['name']}")
        tex = (
            r"\documentclass[11pt,border=0pt]{standalone}" + "\n"
            r"\usepackage{amsmath,amssymb,microtype}" + "\n"
            r"\begin{document}" + "\n"
            + rf"\begin{{minipage}}{{{patch['width']}bp}}" + "\n"
            r"\fontsize{10.95}{15.65}\selectfont\setlength{\parindent}{0pt}" + "\n"
            + patch["text"] + "\n"
            r"\end{minipage}" + "\n"
            r"\end{document}" + "\n"
        )
        tex_path = work / (patch["name"] + ".tex")
        tex_path.write_text(tex)
        process = subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", tex_path.name],
            cwd=work, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        )
        (work / (patch["name"] + ".console.log")).write_text(process.stdout)
        if process.returncode:
            raise RuntimeError(f"TeX failed for {patch['name']}")
        if "Overfull \\hbox" in process.stdout:
            raise RuntimeError(f"TeX overfull line in {patch['name']}")
        snippet = fitz.open(tex_path.with_suffix(".pdf"))
        height = snippet[0].rect.height
        if height > patch["max_height"]:
            raise RuntimeError(f"Correction {patch['name']} too tall: {height:.3f} pt")
        x, y = patch["position"]
        destination = fitz.Rect(x, y, x+patch["width"], y+height)
        page.add_redact_annot(fitz.Rect(patch["rect"]), fill=(1, 1, 1))
        page.apply_redactions(images=0, graphics=0)
        page.show_pdf_page(destination, snippet, 0)
        output_records.append({"name": patch["name"], "page": patch["page"],
                               "redaction_rectangle": patch["rect"],
                               "replacement_rectangle": list(destination),
                               "replacement_text": patch["text"]})
        snippet.close()
    output = ROOT / "paper.pdf"
    doc.save(output, garbage=4, deflate=True)
    doc.close()
    with fitz.open(original) as old, fitz.open(output) as new:
        changed = []
        for i in range(len(old)):
            a = old[i].get_pixmap(matrix=fitz.Matrix(1, 1), alpha=False)
            b = new[i].get_pixmap(matrix=fitz.Matrix(1, 1), alpha=False)
            if a.samples != b.samples:
                changed.append(i+1)
        if changed != [14, 18, 20]:
            raise RuntimeError(f"Unexpected changed pages: {changed}")
        for i in changed:
            new[i-1].get_pixmap(matrix=fitz.Matrix(1.5, 1.5)).save(work / f"page-{i}.png")
    record = {"original_sha256": actual,
              "corrected_sha256": hashlib.sha256(output.read_bytes()).hexdigest(),
              "page_count": 25,
              "changed_pages": changed,
              "unchanged_page_render_comparison": "Exact pixel equality at 72 dpi for all 22 unmodified pages",
              "patches": output_records}
    (ROOT / "verification/manuscript-corrections.json").write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps({"output": str(output), "changed_pages": changed,
                      "sha256": record["corrected_sha256"]}, indent=2))


if __name__ == "__main__":
    main()
