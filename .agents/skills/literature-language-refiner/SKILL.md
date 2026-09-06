---
name: literature-language-refiner
description: Refine scientific sentences using terminology verified against relevant primary research literature. Use when a user asks to align prose with established field language, make a claim sound natural to expert readers, or check whether technical phrasing is standard; do not use for ordinary copyediting that needs no literature review.
---

# Literature Language Refiner

Refine the supplied sentence so that its terminology and framing match how the relevant research community writes, without changing the underlying claim.

## Establish the Intended Claim

Identify the sentence's subject, evidence level, scope, and intended implication before changing its language. Use nearby manuscript text, the bibliography, and papers already named by the user when available. If the technical meaning remains genuinely ambiguous, offer conservative alternatives or ask one focused question instead of silently choosing a stronger claim.

Preserve distinctions such as:

- observed correlation versus causal mechanism;
- empirical finding versus theoretical guarantee;
- representability versus learnability;
- model output, activation, feature, circuit, and mechanism;
- necessary condition, sufficient condition, and exact characterization.

## Skim the Literature

Search the local paper corpus first when the request concerns a manuscript or repository. Then browse primary sources to confirm current field usage, because terminology and citation prominence can change.

Prefer sources in this order:

1. Papers directly studying the same object and claim.
2. Canonical or widely cited papers that established the terminology.
3. Recent papers from established venues or research groups that show current usage.

Use relevance and methodological credibility as the main criteria. Do not substitute institutional prestige for evidence, and do not rely on search snippets, blogs, or survey paraphrases when the original paper is available. Skim the title, abstract, introduction, and the section where the candidate term is actually used. Look across several independent papers when feasible, especially before describing a phrase as standard.

For technical searches, rely on original papers, official proceedings, and author-hosted manuscripts. Record enough source information to cite the terminology claims in the response.

## Choose Language

Collect candidate phrases only when their definitions match the user's claim and model setup. Prefer the clearest widely used term, not the most specialized wording. Reuse field terminology at the level of a short phrase, then write the sentence independently rather than imitating a source's syntax.

Do not:

- add jargon merely to make prose sound prestigious;
- strengthen generality, certainty, novelty, causality, or empirical support;
- import a term whose standard definition requires assumptions absent from the work;
- claim that wording is standard based on a single paper;
- copy distinctive or extended source phrasing.

When no consensus term exists, say so and use precise plain language. When adjacent subfields use different terms, identify the variant most appropriate for the target audience.

## Deliver the Refinement

Unless the user requests another format, provide:

1. A recommended sentence.
2. One concise explanation of the terminology choices.
3. Direct links to the primary papers that support those choices.

Add one or two alternatives only when they express a meaningful difference in emphasis, such as mechanistic versus expressivity framing. If the user asks for an inline suggestion, keep the response compact. If the user asks to update a file, edit only the intended passage, preserve the surrounding style and citation commands, and verify that the revised sentence remains grammatically continuous in context.

