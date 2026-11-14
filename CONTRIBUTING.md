# Best practices for maintaining our codebase

**Problem:** Our current codebase and results are distributed in the form of Ramanujan runs, pdf files and different repositories. This results in inefficiency in terms of iterating on top of existing results and sometimes the decentralised results are leading to confusion as to where to contribute. This document is a proposal to make things clearer, both in terms of what are the repos to maintain going forward and making clear who contributes what.

**Solution:** We are going to work with one repository ([xorformer on GitHub](https://github.com/VerifiedMechanisms/xorformer)), and primarily on one branch (main) that would contain all the results that we generate. As soon as one generates a *significant* result (md file with the math statement + Lean stuff), you/Ramanujan would create a PR which would be reviewed by

1. Scientist: They would judge if the result is relevant or not, and needs to be merged
2. Lean engineer: Assess whether the Lean code is written well (modular, efficient, etc.)

We would aim for 1 PR per 1 significant result. Architecture variants (RoPE, full causal mask, MLPs) live on their own branches.

UPDATE: Given that we are working on results with multiple architectures, I'm thinking having a separate mech interp dojo would be better, and xorformer would now import from mech interp dojo.

## What are the next steps?

1. Clean up the current xorformer/main. For instance, our favourite Theorem 10 will be Theorem 1. The ordering of theorems will be more structured, and the high level idea is to represent the information in the branch that is most compressed and generalisable. We will do the cleanup in xorformer/clean and then copy that into main.
2. Import the transformer components from [mech-interp-dojo](https://github.com/VerifiedMechanisms/mech-interp-dojo) for the transformer aspects of the Lean code, and the math parts from existing code by Plamen and Stefano’s PR.
3. Afterwards, we would start merging significant results from the autoresearch branch. (I expect the **scientists to be heavily involved here onwards**).
4. Merging research done in the last month: we would then merge existing results that are in pdfs. This would provide a nice base for Ramanujan to iterate on.
5. Merge interesting results from the rs-takehome
6. Merge results that are on Ramanujan.
7. We can iterate and merge on top of this base using Ramanujan!

### Why start with cleaning? Can’t we start with step 3 directly instead?

While this idea is the easier way out, I would like a stronger base to iterate our results on. Otherwise it can be quite some effort to revert if the base is not sufficiently audited. A primary cause of inefficiency in the current main branch stems from allowing Codex to generate responses unguided from a problem statement and using that as our baseline.

In hindsight, unconstrained reasoning often fails to present information concisely. For example, H\*(XOR\_n) = n was derived 3 or 4 different ways in the first 12 theorems. We also asked to formalise these theorems without restructuring/refining them, meaning that the inefficiency in the natural language ended up reflecting in the Lean code as well. The fix to this would be one “structuring” step after autoresearch to make sure that the logic and the Lean code is modular.

- Before: Autoresearch → Pull request
- Proposed: Autoresearch → Restructure → Pull request

## Overall Take

I think this might look like we are taking a step back, but taking a week or two off to set things right will pay off in the long run.

## Some nice skills to have for Ramanujan

I would expect that refining/restructuring both the natural language proof and the Lean code to be automated at some point. It would be nice to have some skills.md file to do this. For example, some skills at the natural language level to use subproofs if they already exist and organise things in a nice manner would be great for this purpose. Similarly, at the Lean level, it would be good to have a skill that writes optimal code.

## Concrete guidelines that we can follow from now

For research contributions, the workflow is: **research → restructure the mathematical argument → formalize or reuse existing Lean proofs → review → merge**. 

### A. General guidelines

1. **Keep each result PR focused on one significant result.**
2. **This PR will be reviewed by one scientist and one Lean engineer.**
3. **Use a separate branch for a separate architecture**.
4. **Restructure natural language autoresearch run to be more efficient before formalizing and submitting for review.** Refine the natural-language statement and proof into a concise, complete argument. Identify its assumptions, dependencies, and reusable steps before translating its structure into Lean. Complete this pass before marking a result PR ready for review.
5. **Each PR will be reviewed by a scientist and an engineer.**


### B. Guidelines for the Lean coders
6. **Import mech interp dojo to code in the transformer components.**
7. **Faithfully translate natural-language proofs into Lean when they are not already formalized.** Mention when you use tactics or deviate from the natural language proof in the Lean code
8. **Reuse existing results and extract shared lemmas.** Search the mathematical writeups and Lean code before adding a proof. Reuse a result when its assumptions and conclusion match what is needed, and cite it explicitly. Extract substantial arguments used by multiple proofs into named lemmas with their own statements and proofs.

