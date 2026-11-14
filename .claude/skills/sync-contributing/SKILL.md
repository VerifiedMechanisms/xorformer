---
name: sync-contributing
description: Sync CONTRIBUTING.md from the "Maintaining the code" tab (first heading "Best practices for maintaining our codebase") of the Verified Mechanisms Docs Google Doc. Use when asked to sync, refresh or update CONTRIBUTING.md, when the best practices doc has changed, or to push CONTRIBUTING.md to the Doc.
---

# Sync CONTRIBUTING.md from the Google Doc

`CONTRIBUTING.md` mirrors one tab of a Google Doc and holds nothing else. The
default direction is Doc to file (the steps below). When the file was edited
locally and the user asks to push it, see "Pushing the file to the Doc".

- Doc: "Verified Mechanisms Docs", file ID `1FPSgvMyE11FtgyeEL6VSQGB2p6GnjvlS3gYrP606yYo`
- Tab: "Maintaining the code" (`tab=t.5f94ft85v3hq`), which opens with the
  heading "Best practices for maintaining our codebase"
- Link: https://docs.google.com/document/d/1FPSgvMyE11FtgyeEL6VSQGB2p6GnjvlS3gYrP606yYo/edit?tab=t.5f94ft85v3hq

## Steps

1. Export the whole Doc as markdown with the Google Drive connector:
   `download_file_content` with the file ID above and
   `exportMimeType: "text/markdown"`. The result names a saved `.md` file.
   Do not use `read_file_content` for this (see Gotchas). If the session has
   no Drive connector, ask the user to paste the tab's text and format it by
   hand to match what the script would produce.

2. From the repo root, extract the tab into a scratch file, not straight over
   `CONTRIBUTING.md`:

   ```
   python3 .claude/skills/sync-contributing/extract_tab.py <export.md> -o <scratch>/CONTRIBUTING.md
   ```

   The script does all the formatting and never touches the wording. It
   prints the outline of what it extracted, plus the footnotes and images it
   carried over.

3. Read the outline. It should be this tab and only this tab. Sections about
   something else (meeting notes, check-ins, run logs) mean a neighbouring
   tab was glued on: cut the scratch file back to the tab, and tell the user.

4. Make only these two kinds of hand edit to the scratch file, and list each
   one in the report so it can be fixed in the Doc as well:
   - Correct unambiguous misspellings, for example "xorforner" for this
     repo's name. Never rephrase.
   - Drop footnotes that are drafting notes about the Doc itself (a note to
     self about word choice, a TODO), together with their `[^n]` markers.
     Keep footnotes that carry content.

5. Diff the scratch file against the current `CONTRIBUTING.md`. If the current
   file has text that is in neither the Doc nor the previous sync (someone
   edited the file directly), stop and ask, because replacing the file would
   discard it. Otherwise replace `CONTRIBUTING.md` with the scratch file. If
   the script wrote images to `assets/contributing/`, delete any older images
   there that the new file no longer references.

6. Report what changed since the last sync (sections added, removed or
   reworded), the hand edits from step 4, and anything worth fixing in the
   Doc. Do not commit unless asked.

## Pushing the file to the Doc

Only when asked. The Drive connector cannot edit an existing Doc, so this goes
through Claude in Chrome (if the session has a Google Docs connector, use that
instead).

1. Export the Doc (step 1 above) and diff the extracted tab against
   `CONTRIBUTING.md` to see what the Doc lacks. Keep this export as the
   "before" copy.
2. Open the Doc link in a new Chrome tab and check that the sidebar has
   "Maintaining the code" selected. Click in the body. `cmd+Down` goes to the
   end of the tab, which ends with two empty paragraphs: press `Up` once and
   type on the first.
3. Type the missing text with shortcuts, not Markdown: `cmd+alt+2` and
   `cmd+alt+3` for headings (Return after a heading gives normal text),
   `cmd+b` to toggle bold, `cmd+shift+7` for a numbered list, Return twice to
   leave a list. Take a screenshot after the first heading before typing the
   rest.
4. Do not delete anything from the Doc that the file lacks (for example the
   drafting footnote) unless asked.
5. Export again. The extracted tab must match the file apart from whitespace
   and whatever was deliberately left, and a diff of the whole export before
   and after must show changes only inside this tab.

Docs turns some typed prefixes into lists (learned 2026-11-14):

- "A. " or "1. " at the start of a paragraph starts a list. For a heading
  such as "A. General guidelines", type "xA. General guidelines" and then
  delete the x (`cmd+Left`, `Right`, `Backspace`). If a list did start,
  `cmd+shift+7` removes it but also swallows the "A. ".
- "5. " at the start of a paragraph starts a numbered list at 5, which is how
  to continue numbering under a new heading.

## Gotchas (learned 2026-11-13)

- `read_file_content` cuts the Doc off at about 98k characters. The Doc is
  about 105k and this tab is the last one, so the tab arrives truncated in
  the middle of a sentence. `download_file_content` returns all of it.
- The markdown export concatenates every tab and has no tab titles or
  boundaries. The script finds the tab by its first heading and stops at the
  next H1, or at the footnote and image definitions that close the export.
  That is exact while this tab is last. A tab placed after it that does not
  open with an H1 (in this Doc: "Investigating runs", "Known-answer
  questions") would be glued on, which is what step 3 guards against.
- If the tab's first heading is renamed, the script exits with an error. Pass
  `--start "<new heading>"`, then update `START_HEADING` in the script and
  the description above.
- The Doc is shared with named accounts only, so it cannot be fetched without
  the connector's credentials (no `curl`, no WebFetch).
- People chips export as `[Name](mailto:...)`. The script keeps the name and
  drops the address, so no email address reaches the repo.
- Images arrive as base64 data URIs, which GitHub does not render. The script
  writes them to `assets/contributing/` and links them relatively.
