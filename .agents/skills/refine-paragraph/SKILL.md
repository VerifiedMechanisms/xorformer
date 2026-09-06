---
name: refine-paragraph
description: Refine academic paragraphs into clear, self-contained, high-level prose that preserves the claim and reuses terminology already established in the surrounding text. Use for paragraph rewrites, continuity fixes, de-jargoning, or making technical prose sound natural; also use literature-language-refiner whenever field-specific language may matter, and err on the side of using it when uncertain.
---

# Refine Paragraph

Refine the supplied paragraph in the style preferred for this project: self-consistent, concrete, concise, and understandable without introducing unnecessary terminology.

## Read the Paragraph in Context

When surrounding manuscript text is available, read enough of it to determine:

- the paragraph's role in the argument;
- which facts, qualifications, citations, references, and distinctions must be preserved;
- which terms and artifacts have already been introduced; and
- how the paragraph should connect to the preceding and following text.

For a `.tex` manuscript, always inspect the instructional `%` comments beneath the relevant section or subsection heading. Treat these comments as the editorial brief for that part of the manuscript. Before rewriting, audit all existing prose in the section or subsection against each requested point and classify it as addressed, partially addressed, or missing. Account for material already covered elsewhere in the subsection so that the revision fills genuine gaps without repeating existing content. After rewriting, repeat the audit against the complete subsection, not only the edited paragraph, and flag any requirement that remains unaddressed.

Preserve the instructional comments unless the user asks to remove them. If the brief requests information that is not available, do not invent it; identify the missing information or use appropriately limited wording.

Do not rewrite a paragraph as an isolated passage when doing so would make its terminology, attribution, or transition inconsistent with the manuscript.

## Verify Field-Specific Language When Needed

Also use `$literature-language-refiner` when the user asks whether wording is standard in the field, requests terminology used in the research literature, or when field-specific language could affect how an expert reader interprets the paragraph. If it is unclear whether checking the literature would improve the revision, err on the side of using the literature refiner. First establish the paragraph's intended claim and role using this skill, then use the literature refiner to verify the terminology that matters. Integrate the verified language without adding unnecessary jargon.

Skip the literature refiner only when the requested change is purely grammatical or structural and does not depend on field-specific usage.

## Refine the Prose

- Preserve the underlying claim, evidence level, and scope. Do not make a result, attribution, or causal claim stronger for rhetorical effect.
- Reuse the manuscript's established vocabulary. Avoid introducing a new technical label for an idea that can be stated using terms the reader already knows.
- Prefer a high-level statement when technical details are not needed for the paragraph's purpose. Retain details only when they establish the claim, explain the method, or support reproducibility.
- Make references concrete. Replace vague phrases such as ``this process,'' ``these mechanisms,'' or ``this discipline'' with the prompt, agent, authors, proof, check, or construction actually responsible.
- Keep attribution precise. Distinguish what came from the prompt, agent, harness, human intervention, computational checks, and formal verification. If the evidence does not support an attribution, use conservative wording or flag the ambiguity.
- Ensure that named files, tools, quantities, and technical terms are introduced before they are used. If an explanation would require substantial new terminology, state the point at a higher level instead.
- Prefer direct sentences with clear subjects and verbs. Use two short sentences instead of one clause-heavy sentence when that reads more naturally.
- Remove repetition, generic transitions, and details that merely restate a table or nearby sentence.
- Do not use em dashes.

## Check the Result

Read the revision as part of the surrounding section and confirm that:

- every pronoun and referring phrase has an unambiguous antecedent;
- each sentence advances the paragraph's purpose;
- terminology is consistent across the paragraph and nearby tables or definitions;
- the complete section or subsection addresses every item in its instructional comment without unnecessary repetition;
- the prose does not imply evidence or certainty absent from the source; and
- the transition into and out of the paragraph remains natural.

For LaTeX, preserve citation commands, labels, references, macros, and mathematical notation. When editing a file, change only the intended passage, compile when the local workflow supports it, and check the rendered lines for awkward wrapping or isolated words.

## Deliver the Refinement

Unless the user requests otherwise, provide one recommended version. Add a brief explanation only when a non-obvious ambiguity, attribution choice, or loss of detail materially affects the revision. When working from a `.tex` instructional comment, report any requested item that the resulting subsection still does not address. If the user requests alternatives, make them differ in emphasis rather than offering superficial synonyms.
