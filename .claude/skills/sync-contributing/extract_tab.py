#!/usr/bin/env python3
"""Pull one tab out of a Google Docs markdown export and tidy it for GitHub.

Drive's markdown export concatenates every tab of the Doc and drops the tab
titles, so the tab is found by its first heading. It runs until the next H1
(other tabs open with one) or until the footnote and image definitions that
Drive appends at the very end of the export.

Usage, from the repo root:
    python3 .claude/skills/sync-contributing/extract_tab.py EXPORT.md -o OUT.md

The wording is never changed. Only the formatting is: the tab's first heading
becomes the H1, Google's needless backslash escapes and invisible characters
go, lists become tight "-" lists, links that point nowhere or at an email
address are reduced to their text, and footnotes and images used by the tab
are carried over. A report (outline, footnotes, images) goes to stderr.
"""
from __future__ import annotations

import argparse
import base64
import re
import sys
from pathlib import Path

START_HEADING = "Best practices for maintaining our codebase"
IMAGES_DIR = "assets/contributing"

HEADING = re.compile(r"^(#{1,6})\s+(.*?)\s*$")
LIST_ITEM = re.compile(r"^(\s*)([-*+]|\d+[.)])\s+")
FENCE = re.compile(r"^\s*(```|~~~)")
RULE = re.compile(r"^\s*([-*_]\s*){3,}$")
FOOTNOTE_DEF = re.compile(r"^\[\^([^\]]+)\]:\s*(.*)$")
FOOTNOTE_REF = re.compile(r"\[\^([^\]]+)\]")
IMAGE_DEF = re.compile(r"^\[(image\d+)\]:\s*<data:(image/[\w.+-]+);base64,([^>]*)>\s*$")
IMAGE_DEF_START = re.compile(r"^\[image\d+\]:")
IMAGE_REF = re.compile(r"!\[([^\]]*)\]\[(image\d+)\]")
EMPTY_LINK = re.compile(r"\[([^\]]*)\]\(\)")
MAILTO_LINK = re.compile(r"\[([^\]]*)\]\(mailto:[^)]*\)")
# A line that opens a new block, so a line break before it is not a hard break.
BLOCK_START = re.compile(r"^\s*(#{1,6}\s|[-*+]\s|\d+[.)]\s|\||>|```|~~~)")
# List and quote markers that can sit in front of the text of a line.
LINE_PREFIX = re.compile(r"^(?:\s*(?:[-*+]|\d+[.)]|>)\s+)*\s*")
# Zero width space, word joiner and BOM are dropped; a no-break space becomes a space.
INVISIBLE = {0x200B: None, 0x2060: None, 0xFEFF: None, 0xA0: " "}
# Characters Google escapes although running text never needs it.
UNESCAPE = set("+-=!.():#|")


def unescape(line: str) -> str:
    """Drop the backslashes Google adds where markdown does not need them."""
    safe = UNESCAPE - {"|"} if line.lstrip().startswith("|") else UNESCAPE
    prefix_end = LINE_PREFIX.match(line).end()
    out, i = [], 0
    while i < len(line):
        ch = line[i]
        if ch != "\\" or i + 1 == len(line):
            out.append(ch)
            i += 1
            continue
        nxt = line[i + 1]
        before = line[prefix_end:i].strip()
        keep = (
            nxt not in safe
            or (nxt in "-+#=" and not before)  # would open a list, heading or setext rule
            or (nxt in ".)" and before.isdigit())  # would open an ordered list
            or (nxt == "!" and line[i + 2 : i + 3] == "[")  # would turn a link into an image
        )
        out.append(ch + nxt if keep else nxt)
        i += 2
    return "".join(out)


def find_tab(lines: list[str], start: str) -> tuple[int, int]:
    """Line range [first, last) of the tab whose first heading is `start`."""
    hits = [
        i
        for i, line in enumerate(lines)
        if (m := HEADING.match(line)) and unescape(m[2]).strip() == start
    ]
    if len(hits) != 1:
        found = "no heading" if not hits else f"{len(hits)} headings"
        sys.exit(
            f"error: expected exactly one heading '{start}' in the export, found {found}. "
            "If the tab's first heading was renamed, pass --start."
        )
    first = hits[0]
    in_fence = False
    for i in range(first + 1, len(lines)):
        line = lines[i]
        if FENCE.match(line):
            in_fence = not in_fence
        elif not in_fence and (
            line.startswith("# ") or FOOTNOTE_DEF.match(line) or IMAGE_DEF_START.match(line)
        ):
            return first, i
    return first, len(lines)


def tidy(lines: list[str]) -> list[tuple[str, bool]]:
    """Clean each line. Returns (line, is_code) pairs; code is left alone."""
    out = []
    in_fence = False
    for idx, raw in enumerate(lines):
        if FENCE.match(raw):
            in_fence = not in_fence
            out.append((raw.rstrip(), True))
            continue
        if in_fence:
            out.append((raw, True))
            continue
        line = raw.translate(INVISIBLE)
        following = lines[idx + 1] if idx + 1 < len(lines) else ""
        # Two trailing spaces are a line break inside a paragraph only when the
        # paragraph goes on. Google also leaves them at the end of list items.
        hard_break = (
            line.endswith("  ")
            and line.strip()
            and not HEADING.match(line)
            and not line.lstrip().startswith("|")
            and following.strip()
            and not BLOCK_START.match(following)
        )
        line = unescape(line.rstrip())
        if not RULE.match(line):
            line = re.sub(r"^(\s*)\*(?=\s)", r"\1-", line)
        line = EMPTY_LINK.sub(r"\1", line)
        line = MAILTO_LINK.sub(r"\1", line)
        out.append((line + "\\" if hard_break else line, False))
    return out


def tighten(pairs: list[tuple[str, bool]]) -> list[str]:
    """Drop blank lines between items of one list and collapse blank runs."""
    lines = [line for line, _ in pairs]
    code = [is_code for _, is_code in pairs]
    out: list[str] = []
    for i, line in enumerate(lines):
        if line.strip() or code[i]:
            out.append(line)
            continue
        if not out or out[-1] == "":
            continue  # leading blank, or second blank in a row
        nxt = next((l for l in lines[i + 1 :] if l.strip()), "")
        a, b = LIST_ITEM.match(out[-1]), LIST_ITEM.match(nxt)
        if a and b:
            same_kind = a[2][0].isdigit() == b[2][0].isdigit()
            if same_kind or len(a[1]) != len(b[1]):
                continue
        out.append("")
    while out and out[-1] == "":
        out.pop()
    return out


def read_definitions(lines: list[str]) -> tuple[dict[str, str], dict[str, tuple[str, str]]]:
    """Footnote texts and image data, which Drive puts at the end of the export."""
    footnotes: dict[str, str] = {}
    images: dict[str, tuple[str, str]] = {}
    current = None
    for line in lines:
        if m := IMAGE_DEF.match(line):
            images[m[1]] = (m[2], m[3])
            current = None
        elif m := FOOTNOTE_DEF.match(line):
            current = m[1]
            footnotes[current] = m[2].strip()
        elif current and line.startswith((" ", "\t")) and line.strip():
            footnotes[current] += " " + line.strip()
        else:
            current = None
    return footnotes, images


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("export", type=Path, help="markdown export of the whole Google Doc")
    ap.add_argument("-o", "--output", type=Path, help="where to write the tab (default: stdout)")
    ap.add_argument("--start", default=START_HEADING, help="first heading of the tab")
    ap.add_argument(
        "--images-dir",
        default=IMAGES_DIR,
        help="repo-relative folder for images used by the tab (default: %(default)s)",
    )
    args = ap.parse_args()

    lines = args.export.read_text(encoding="utf-8").splitlines()
    first, last = find_tab(lines, args.start)
    footnote_defs, image_defs = read_definitions(lines[last:])

    body = tighten(tidy(lines[first:last]))
    body[0] = "# " + HEADING.match(body[0])[2]
    text = "\n".join(body)

    # Footnotes: renumber from 1 in order of appearance, append their texts.
    order: list[str] = []
    for ref in FOOTNOTE_REF.findall(text):
        if ref not in order:
            order.append(ref)
    text = FOOTNOTE_REF.sub(lambda m: f"[^{order.index(m[1]) + 1}]", text)
    notes = [(n, unescape(footnote_defs.get(ref, ""))) for n, ref in enumerate(order, 1)]
    if notes:
        text += "\n\n" + "\n".join(f"[^{n}]: {note}" for n, note in notes)

    # Images: GitHub does not render data URIs, so write them out as files.
    names: dict[str, str] = {}
    for _, ref in IMAGE_REF.findall(text):
        if ref in names or ref not in image_defs:
            continue
        mime, data = image_defs[ref]
        ext = {"jpeg": "jpg", "svg+xml": "svg"}.get(mime.split("/")[1], mime.split("/")[1])
        names[ref] = f"{args.images_dir}/image{len(names) + 1}.{ext}"
        Path(names[ref]).parent.mkdir(parents=True, exist_ok=True)
        Path(names[ref]).write_bytes(base64.b64decode(data))
    text = IMAGE_REF.sub(
        lambda m: f"![{m[1]}]({names[m[2]]})" if m[2] in names else m[0], text
    )
    missing = sorted({ref for _, ref in IMAGE_REF.findall(text)})

    text += "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)

    report = [f"tab: export lines {first + 1} to {last} ({len(body)} lines after cleanup)", "outline:"]
    in_fence = False
    for line in body:
        if FENCE.match(line):
            in_fence = not in_fence
        elif not in_fence and HEADING.match(line):
            report.append("  " + line)
    report.append(f"footnotes: {len(notes)}")
    report += [f"  [^{n}] {note or '(no text found in the export)'}" for n, note in notes]
    report.append(f"images: {len(names)}")
    report += [f"  {path}" for path in names.values()]
    report += [f"  warning: no image data in the export for {ref}" for ref in missing]
    print("\n".join(report), file=sys.stderr)


if __name__ == "__main__":
    main()
