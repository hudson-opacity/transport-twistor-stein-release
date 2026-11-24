#!/usr/bin/env python3
"""Build the manuscript with Python packages typst==0.15.2 and pypandoc_binary==1.17."""
from pathlib import Path
import json
import re
import tempfile

import pypandoc
import typst


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "STEIN-INTERIOR.md"
OUTPUT = ROOT / "output/pdf/stein-transport-twistor.pdf"

STYLE = r"""
#set page(paper: "us-letter", margin: (x: 0.84in, top: 0.73in, bottom: 0.73in),
  footer: context [
    #line(length: 100%, stroke: 0.5pt + rgb("#c6d1d4"))
    #v(1pt)#text(size: 8.5pt, fill: rgb("#446069"))[STEIN INTERIORS OF TRANSPORT TWISTOR SPACES]
    #h(1fr)#text(size: 9pt)[#counter(page).display()]
  ])
#set text(font: "STIX Two Text", size: 11.8pt, lang: "en", fill: rgb("#172c31"))
#set par(justify: false, leading: 0.56em, spacing: 0.98em)
#show heading: set text(fill: rgb("#173e49"))
#show link: set text(fill: rgb("#146272"))
#show raw: set text(size: 0.82em)
"""


def print_reference(match):
    label, url = match.groups()
    if url.startswith(("https://", "http://", "#")):
        return match.group(0)
    if not (ROOT / url).is_file():
        raise ValueError(f"Missing manuscript reference {url}")
    # The printed file can be read independently or beside the source archive.
    return f"`{Path(url).name}`"


def typeset(markdown):
    markdown = re.sub(r'\[([^\]]+)\]\(([^\s)]+)\)', print_reference, markdown)
    markdown = re.sub(r'\\tag\{(\d+)\}', r'\\qquad \\text{(\1)}', markdown)
    markdown = markdown.replace("smallmatrix}", "matrix}")
    content = pypandoc.convert_text(markdown, "typst", format="markdown+tex_math_dollars",
                                    extra_args=["--wrap=none"])
    # Pandoc uses obsolete Typst names for tensor, flat and intersection here.
    return content.replace("times.circle", "⊗").replace("^flat", "^♭").replace(" sect ", " ∩ ").replace("#h(-1em)", "")


def build():
    source = SOURCE.read_text(encoding="utf-8")
    preamble, *sections = re.split(r'^## (\d+\. [^\n]+)\n', source, flags=re.MULTILINE)
    title, byline, dateline, abstract = preamble.strip().split("\n\n", maxsplit=3)
    title = title.removeprefix("# ")
    authors = byline.split(" and ")
    name_list = ", ".join(json.dumps(name) for name in authors)
    parts = [f'#set document(title: {json.dumps(title)}, author: ({name_list}))', STYLE,
             f'#align(center)[#text(size: 23.5pt, weight: "bold", {json.dumps(title)})'
             f'\n\n#text(size: 13.5pt, {json.dumps(byline)})'
             f'\n\n#text(size: 10.5pt, {json.dumps(dateline, ensure_ascii=False)})]']
    parts.append(typeset(abstract))
    for idx in range(0, len(sections), 2):
        heading, markdown = sections[idx:idx + 2]
        if idx >= 4:
            parts.append("#pagebreak()")
        parts.append(f'= {heading}')
        # Split the two distinct arguments in §9 at a subsection boundary.
        for pos, fragment in enumerate(markdown.split("### An everywhere strictly plurisubharmonic exhaustion")):
            if pos:
                parts.extend(("#pagebreak()", "== An everywhere strictly plurisubharmonic exhaustion"))
            parts.append(typeset(fragment))
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=OUTPUT.parent) as scratch:
        work = Path(scratch)
        manuscript = work / "manuscript.typ"
        manuscript.write_text("\n\n".join(parts), encoding="utf-8")
        result = work / "manuscript.pdf"
        typst.compile(str(manuscript), output=str(result))
        result.replace(OUTPUT)


if __name__ == "__main__":
    build()
