#!/usr/bin/env python3
"""Lint Markdown math so it renders on GitHub, GitLab, and KaTeX previews.

Static implementation of the rules in .claude/skills/gh-markdown-math/SKILL.md.
Zero dependencies for the default lint. Optional modes:

  --katex           validate every math span with katex.renderToString via node
                    (needs `npm install katex` in the repo root)
  --render-github   faithful render audit through `gh api markdown` (needs gh auth)
  --render-gitlab   faithful render audit through `glab api markdown` (needs glab auth)
  --context X/Y     repo context for the render APIs (default: pevogam/xorformer)

Exit status: 0 = clean, 1 = findings, 2 = usage/tooling error.
"""

import argparse
import html as html_lib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

DEFAULT_CONTEXT = "pevogam/xorformer"

ALNUM = re.compile(r"[A-Za-z0-9]")

# (rule-id, regex, message) applied to the raw TeX of every math span.
IN_MATH_RULES = [
    ("brace", re.compile(r"\\[{}]"),
     r"\{ \} get unescaped by GitHub; use \lbrace \rbrace"),
    ("spacing", re.compile(r"\\[,;!]"),
     r"\, \; \! get unescaped to literal punctuation; delete them"),
    ("star", re.compile(r"\*"),
     r"literal * is Markdown emphasis; use \ast"),
    ("operatorname", re.compile(r"\\operatorname\b"),
     r"\operatorname is unreliable on GitHub; use \mathrm"),
    ("hash", re.compile(r"\\#"),
     r"\# unescapes to a TeX error; use \lvert\lbrace...\rbrace\rvert"),
    ("angle", re.compile(r"(?<!\\)[<>]"),
     r"bare < > double-escape into KaTeX errors; use \lt \gt"),
    ("rowsep", re.compile(r"\\\\"),
     r"\\ row separators lose a backslash on GitHub; use \cr"),
    ("entity", re.compile(r"&#\w+;|&[A-Za-z]+;"),
     "HTML entity inside math breaks KaTeX previews; use the character or a TeX macro"),
]


class Finding:
    def __init__(self, path, line, col, rule, message, excerpt=""):
        self.path, self.line, self.col = path, line, col
        self.rule, self.message, self.excerpt = rule, message, excerpt

    def __str__(self):
        loc = f"{self.path}:{self.line}:{self.col}"
        tail = f"  [{self.excerpt}]" if self.excerpt else ""
        return f"{loc}: {self.rule}: {self.message}{tail}"


class Span:
    """One math span on a single source line (multi-line blocks are joined).

    line is 1-based. start0 is the 0-based index of the opening delimiter,
    after0 the 0-based index one past the closing delimiter, both on `line`.
    content_off is the 0-based offset of content[0] from start0 (1 for $, 2
    for $$), so content index k sits at 1-based column start0 + content_off
    + k + 1.
    """

    def __init__(self, line, start0, after0, content, display, standalone=False):
        self.line, self.start0, self.after0 = line, start0, after0
        self.content, self.display, self.standalone = content, display, standalone
        self.content_off = 2 if display else 1

    @property
    def col(self):
        return self.start0 + 1

    def content_col(self, k):
        return self.start0 + self.content_off + k + 1


def mask_fenced_blocks(lines):
    """Blank out fenced code blocks (``` / ~~~), keeping line count."""
    out, fence = [], None
    for raw in lines:
        stripped = raw.lstrip()
        if fence is None:
            m = re.match(r"(`{3,}|~{3,})", stripped)
            if m:
                fence = m.group(1)
                out.append("")
                continue
            out.append(raw)
        else:
            if stripped.startswith(fence) and stripped.rstrip("`~ ") == "":
                fence = None
            out.append("")
    return out


def mask_inline_code(line):
    """Blank out `code` spans (any backtick run length), keeping length."""
    return re.sub(r"(`+)(?!`).*?(?<!`)\1(?!`)",
                  lambda m: " " * len(m.group(0)), line)


def blank_region(line, start, end):
    return line[:start] + " " * (end - start) + line[end:]


def extract_spans(masked, path, findings):
    """Return (spans, prose): all math spans, and lines with math blanked."""
    spans = []
    prose = list(masked)
    open_display = None  # (line_idx, col) of an unclosed $$

    # Display spans first.
    for i, line in enumerate(masked):
        pos = 0
        while True:
            j = line.find("$$", pos)
            if j < 0:
                break
            if open_display is None:
                open_display = (i, j)
                pos = j + 2
            else:
                oi, oj = open_display
                if oi == i:
                    content = line[oj + 2:j]
                    standalone = (line[:oj].strip() == ""
                                  and line[j + 2:].strip() == "")
                    spans.append(Span(i + 1, oj, j + 2, content, True, standalone))
                    prose[i] = blank_region(prose[i], oj, j + 2)
                else:
                    findings.append(Finding(
                        path, oi + 1, oj + 1, "multiline-display",
                        "multi-line $$ block; collapse it onto a single line "
                        "(GitHub leaks headings/bullets into it)"))
                    content = " ".join(
                        [masked[oi][oj + 2:]] + masked[oi + 1:i] + [line[:j]])
                    spans.append(Span(oi + 1, oj, oj + 2, content, True, True))
                    for k in range(oi, i + 1):
                        lo = oj if k == oi else 0
                        hi = j + 2 if k == i else len(prose[k])
                        prose[k] = blank_region(prose[k], lo, hi)
                open_display = None
                pos = j + 2
    if open_display is not None:
        oi, oj = open_display
        findings.append(Finding(path, oi + 1, oj + 1, "unclosed-display",
                                "unclosed $$ delimiter"))

    # Inline spans on what remains.
    for i, line in enumerate(prose):
        cols = [m.start() for m in re.finditer(r"(?<!\\)\$", line)]
        if not cols:
            continue
        if len(cols) % 2 == 1:
            findings.append(Finding(
                path, i + 1, cols[-1] + 1, "wrapped-span",
                "odd number of $ on this line; an inline span wrapped across a "
                "line break does not render - join it onto one line"))
        for a, b in zip(cols[0::2], cols[1::2]):
            spans.append(Span(i + 1, a, b + 1, line[a + 1:b], False))
            prose[i] = blank_region(prose[i], a, b + 1)

    spans.sort(key=lambda s: (s.line, s.start0))
    return spans, prose


def check_span_contents(spans, path, findings):
    for s in spans:
        for rule, rx, msg in IN_MATH_RULES:
            for m in rx.finditer(s.content):
                findings.append(Finding(path, s.line, s.content_col(m.start()),
                                        rule, msg, excerpt=m.group(0)))
        if not s.display:
            m = re.search(r"\\begin\{(\w+)", s.content)
            if m:
                findings.append(Finding(
                    path, s.line, s.content_col(m.start()), "inline-env",
                    f"\\begin{{{m.group(1)}}} does not render in inline $...$ "
                    "on GitHub; use a standalone $$...$$ line (not in a list) "
                    "or rewrite as prose"))


def check_delimiters(spans, masked, path, findings):
    for s in spans:
        if s.display:
            continue
        line = masked[s.line - 1]
        before = line[s.start0 - 1] if s.start0 > 0 else ""
        after = line[s.after0] if s.after0 < len(line) else ""
        if before and (ALNUM.match(before) or before == "-"):
            findings.append(Finding(
                path, s.line, s.col, "open-delim",
                f"opening $ abuts '{before}'; it must be preceded by whitespace "
                "(reword, e.g. 'degree-$d$' -> 'degree $d$')"))
        if after and after.isalpha():
            findings.append(Finding(
                path, s.line, s.after0 + 1, "close-delim",
                f"letter '{after}' immediately after closing $; "
                "add a hyphen ('$b$-th') or space"))
        if s.content.rstrip().endswith(")") and after == ")":
            findings.append(Finding(
                path, s.line, s.after0 + 1, "close-delim-paren",
                "')$)' pattern: closing $ with punctuation on both sides fails; "
                "reword so the span is followed by a space or word"))


def underscore_flanks(content, k):
    """(can_open, can_close) for the _ at content[k], per cmark flanking.

    Approximates cmark: intraword _ (alnum both sides) is inert; punctuation
    before + alnum after can only open; alnum before + punctuation after can
    only close; punctuation on BOTH sides can open AND close (verified on
    GitHub: \\underbrace{...}_{a\\text{-only}} pairs emphasis with a later
    }_{ in the same paragraph). A _ preceded by whitespace can never close.
    """
    prev = content[k - 1] if k > 0 else "$"
    nxt = content[k + 1] if k + 1 < len(content) else "$"
    if prev == "\\":
        return False, False
    prev_ws, nxt_ws = prev.isspace(), nxt.isspace()
    prev_punct = not prev_ws and not ALNUM.match(prev)
    nxt_punct = not nxt_ws and not ALNUM.match(nxt)
    left = not nxt_ws and (not nxt_punct or prev_ws or prev_punct)
    right = not prev_ws and (not prev_punct or nxt_ws or nxt_punct)
    return (left and (not right or prev_punct),
            right and (not left or nxt_punct))


def paragraph_blocks(masked):
    """Group line indices into emphasis-pairing blocks (paragraph-ish).

    Blank lines separate blocks; each heading and each table row is its own
    block; a list item plus its continuation lines is one block (a wrapped
    list item is one paragraph for emphasis pairing).
    """
    blocks, cur = [], []

    def flush():
        if cur:
            blocks.append(list(cur))
            cur.clear()

    for i, line in enumerate(masked):
        stripped = line.strip()
        if stripped == "":
            flush()
        elif re.match(r"#{1,6}\s", stripped) or stripped.startswith("|"):
            flush()
            blocks.append([i])
        elif re.match(r"[-*+]\s|\d+[.)]\s", stripped):
            flush()
            cur.append(i)
        else:
            cur.append(i)
    flush()
    return blocks


def check_underscores(spans, masked, path, findings):
    by_line = {}
    for s in spans:
        by_line.setdefault(s.line - 1, []).append(s)
    for block in paragraph_blocks(masked):
        opener_at = None
        for i in block:
            for s in by_line.get(i, []):
                if s.display and s.standalone:
                    continue  # own block: emphasis cannot pair across it
                for m in re.finditer("_", s.content):
                    can_open, can_close = underscore_flanks(s.content, m.start())
                    if can_close and opener_at is not None:
                        findings.append(Finding(
                            path, s.line, s.content_col(m.start()),
                            "underscore-pair",
                            "this _ can close emphasis opened by the _ at line "
                            f"{opener_at[0]} in the same paragraph, corrupting "
                            "the math into <em>. Insert a space before this _ "
                            "(e.g. '$T _{n,1}$')"))
                    elif can_open and opener_at is None:
                        opener_at = (s.line, s.content_col(m.start()))


def check_structure(spans, masked, prose, path, findings):
    by_line = {}
    for s in spans:
        by_line.setdefault(s.line - 1, []).append(s)

    for i, line in enumerate(masked):
        stripped = line.strip()
        if re.match(r"#{1,6}\s", stripped) and by_line.get(i):
            findings.append(Finding(
                path, i + 1, 1, "heading-math",
                "math in a heading is unreliable on GitHub; use plain text/Unicode"))
        if re.match(r"[-*+]\s|\d+[.)]\s", stripped):
            for s in by_line.get(i, []):
                if s.display:
                    findings.append(Finding(
                        path, s.line, s.col, "list-display",
                        "display $$ does not render inside list items; "
                        "use inline $...$"))
        if re.match(r"\[\^[^\]]+\]:", stripped) and by_line.get(i):
            findings.append(Finding(
                path, i + 1, 1, "footnote-math",
                "math inside a footnote definition never renders on GitHub "
                "(verified July 2026); use plain text/Unicode or move the "
                "math to the body"))

    # \( \) / \[ \] delimiters are not math on GitHub, GitLab, or VS Code.
    for i, line in enumerate(prose):
        for m in re.finditer(r"\\[()\[\]]", line):
            findings.append(Finding(
                path, i + 1, m.start() + 1, "paren-delim",
                r"\( \) / \[ \] delimiters do not render as math on "
                "GitHub/GitLab; use $...$ or $$...$$", excerpt=m.group(0)))

    # Math inside *italic* / _italic_ (bold ** is fine). prose has math and
    # code blanked, so the emphasis markers are prose-level by construction.
    for i, line in enumerate(prose):
        italics = list(re.finditer(
            r"(?<![*\\])\*(?!\*)[^*\n]+?(?<![*\\])\*(?!\*)", line))
        italics += list(re.finditer(
            r"(?<![\w\\])_(?!_)[^_\n]+?(?<!\\)_(?![\w])", line))
        for m in italics:
            for s in by_line.get(i, []):
                if m.start() < s.start0 and s.after0 <= m.end() - 1:
                    findings.append(Finding(
                        path, s.line, s.col, "italic-math",
                        "math inside single-* or _ italics is left raw on "
                        "GitHub; move it outside the emphasis (bold ** is fine)"))


def lint_file(path):
    findings = []
    text = Path(path).read_text(encoding="utf-8")
    lines = text.split("\n")
    masked = mask_fenced_blocks(lines)
    masked = [mask_inline_code(l) for l in masked]
    spans, prose = extract_spans(masked, path, findings)
    check_span_contents(spans, path, findings)
    check_delimiters(spans, masked, path, findings)
    check_underscores(spans, masked, path, findings)
    check_structure(spans, masked, prose, path, findings)
    return findings, spans


KATEX_JS = r"""
const fs = require('fs');
let katex;
try { katex = require('katex'); }
catch (e) { console.error('NOKATEX'); process.exit(3); }
const spans = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
let bad = 0;
for (const s of spans) {
  try {
    katex.renderToString(s.tex, {throwOnError: true, displayMode: s.display});
  } catch (e) {
    console.log(`${s.file}:${s.line}:${s.col}: katex: ` +
                String(e.message).split('\n')[0]);
    bad = 1;
  }
}
process.exit(bad);
"""


def run_katex(all_spans, repo_root):
    payload = [
        {"file": p, "line": s.line, "col": s.col, "tex": s.content,
         "display": s.display}
        for p, spans in all_spans for s in spans
    ]
    with tempfile.TemporaryDirectory() as td:
        js = Path(td) / "kcheck.js"
        data = Path(td) / "spans.json"
        js.write_text(KATEX_JS)
        data.write_text(json.dumps(payload))
        env = dict(os.environ)
        env["NODE_PATH"] = str(Path(repo_root) / "node_modules")
        proc = subprocess.run(["node", str(js), str(data)],
                              capture_output=True, text=True, env=env)
    if proc.returncode == 3:
        print("katex: node module 'katex' not found; run `npm install katex` "
              "in the repo root (or skip --katex)", file=sys.stderr)
        return 2
    sys.stdout.write(proc.stdout)
    if proc.stderr.strip():
        sys.stderr.write(proc.stderr)
    return 1 if proc.returncode else 0


MATH_PAYLOAD_GH = re.compile(
    r"<math-renderer[^>]*>(?P<tex>.*?)</math-renderer>", re.S)
MATH_PAYLOAD_GL = re.compile(
    r"<(span|code|pre)[^>]*data-math-style=\"(?:inline|display)\"[^>]*>"
    r"(?P<tex>.*?)</\1>", re.S)
CODEBLOCK = re.compile(r"<pre[^>]*>.*?</pre>|<code[^>]*>.*?</code>", re.S)


def render_audit(path, html, payload_rx):
    """Skill audit: residual $, double-escaped payloads.

    A healthy alignment & appears as &amp; in the raw HTML (normal escaping,
    decoded by the browser before the math engine sees it) on both GitHub
    and GitLab. Genuine double-escaping is an entity that SURVIVES one
    decode, e.g. raw &amp;lt; -> decoded &lt; -> KaTeX parse error.
    """
    findings = []
    payloads = [m.group("tex") for m in payload_rx.finditer(html)]
    stripped = payload_rx.sub(" ", html)
    stripped = CODEBLOCK.sub(" ", stripped)
    if "$" in stripped:
        ctx = re.search(r".{0,60}\$.{0,60}", stripped, re.S)
        findings.append(f"{path}: render: {stripped.count('$')} residual $ "
                        "outside math (unrecognized delimiter) e.g. "
                        f"...{ctx.group(0).strip()!r}...")
    for p in payloads:
        decoded = html_lib.unescape(p)
        m = re.search(r"&(?:[A-Za-z]+|#\w+);", decoded)
        if m:
            findings.append(f"{path}: render: double-escaped entity "
                            f"{m.group(0)!r} inside math payload: {p[:80]!r}")
    return findings, len(payloads)


def render_github(path, context):
    body = json.dumps({"text": Path(path).read_text(encoding="utf-8"),
                       "mode": "gfm", "context": context})
    proc = subprocess.run(["gh", "api", "markdown", "--input", "-"],
                          input=body, capture_output=True, text=True)
    if proc.returncode:
        raise RuntimeError(f"gh api markdown failed for {path}: "
                           f"{proc.stderr.strip()}")
    return render_audit(path, proc.stdout, MATH_PAYLOAD_GH)


def render_gitlab(path, context):
    body = json.dumps({"text": Path(path).read_text(encoding="utf-8"),
                       "gfm": True, "project": context})
    proc = subprocess.run(
        ["glab", "api", "markdown", "--method", "POST", "--input", "-",
         "-H", "Content-Type: application/json"],
        input=body, capture_output=True, text=True)
    if proc.returncode:
        raise RuntimeError(f"glab api markdown failed for {path}: "
                           f"{proc.stderr.strip()}")
    html = json.loads(proc.stdout).get("html", "")
    return render_audit(path, html, MATH_PAYLOAD_GL)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("files", nargs="+")
    ap.add_argument("--katex", action="store_true",
                    help="also validate spans with KaTeX via node")
    ap.add_argument("--render-github", action="store_true",
                    help="faithful GitHub render audit via `gh api markdown`")
    ap.add_argument("--render-gitlab", action="store_true",
                    help="faithful GitLab render audit via `glab api markdown`")
    ap.add_argument("--context", default=DEFAULT_CONTEXT,
                    help=f"repo context for render APIs (default {DEFAULT_CONTEXT})")
    args = ap.parse_args()

    status = 0
    all_spans = []
    for f in args.files:
        findings, spans = lint_file(f)
        all_spans.append((f, spans))
        for fd in sorted(findings, key=lambda x: (x.line, x.col)):
            print(fd)
        if findings:
            status = 1

    n_files = len(args.files)
    n_spans = sum(len(s) for _, s in all_spans)

    if args.katex:
        status = max(status, run_katex(all_spans,
                                       Path(__file__).resolve().parents[2]))

    for flag, renderer, name in (
            (args.render_github, render_github, "github"),
            (args.render_gitlab, render_gitlab, "gitlab")):
        if not flag:
            continue
        total_math = 0
        for f in args.files:
            try:
                probs, n_math = renderer(f, args.context)
            except RuntimeError as e:
                print(e, file=sys.stderr)
                status = max(status, 2)
                continue
            total_math += n_math
            for p in probs:
                print(p)
            if probs:
                status = max(status, 1)
        print(f"[{name}] {n_files} files, {total_math} rendered math spans",
              file=sys.stderr)

    print(f"[lint] {n_files} files, {n_spans} math spans, "
          f"{'FINDINGS' if status else 'clean'}", file=sys.stderr)
    return status


if __name__ == "__main__":
    sys.exit(main())
