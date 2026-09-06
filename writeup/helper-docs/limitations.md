# Limitations of autonomous theory research

This note studies **one extended research trajectory**, using the [theorem rollout][rollout], [approach registry][registry], and [final answer][answer]. The focus is open-ended theoretical mechanistic interpretability: choosing useful abstractions and explanations, rather than resolving a fixed yes/no conjecture.

**Evidence standard:** each recommended limitation below identifies an observed undesirable consequence: a missed construction, effort spent on a target that could not achieve its stated objective, or continued runtime without an improved result. Most episodes were corrected autonomously. The evidence supports temporary problems within the trajectory, not a claim that the final theorems were invalid.

Source links identify physical file lines. All timestamps are UTC on 25 August 2026.

## Selected wording for the paper

1. **Opacity and review burden.** The volume of generated reasoning makes long autonomous runs difficult to inspect and steer. Our theorem-generation run produced approximately 640,000 output tokens, including reasoning. Reconstructing which ideas advanced, failed, or were abandoned therefore requires substantial review. Tools that summarize research branches, track the status of claims, and link conclusions to supporting evidence could make this review more manageable and help identify where human guidance would be useful.

2. **Human direction of the research agenda.** The authors initiated the targeted counterexample search that led to the compact separation reported in this paper, as described in the manuscript's Human interventions subsection. The agent constructed the example, while the decision to pursue this follow-up question and refine it toward a smaller example with a Lean-friendly proof came from the authors. Autonomous execution of the search therefore left an important part of the research agenda to human judgment.

3. **Repetition and premature claims of progress.** Extended runs can produce repetitive updates and apparent progress that does not survive scrutiny. The retained rollout contains prolonged monitoring of stalled searches, an incorrect explanation repeated before correction, and a proposed new bound later removed because an existing bound was stronger. These episodes added work without a corresponding improvement in the final result. A monitor that tracks new evidence, flags repetitive or unsupported claims, and recommends redirection or stopping could help guide the search. Whether such monitoring improves research outcomes remains untested.

Together, these limitations motivate treating autoresearch itself as an object of scientific study. Controlled comparisons of prompts, tools, monitoring, human steering, and stopping rules are needed to determine which workflows produce useful, reliable results and how much computational and human effort they require.

Evidence: repetition and corrected claims are documented at [L6480][t6480], [L6944][t6944], [L4919][t4919], and [L4602][t4602]. The targeted counterexample search begins with an explicit [human prompt](../../system-design/rollouts/separation-rollout.jsonl#L10); the compact example and subsequent refinement are described by the authors. This does not imply that the theorem-generation run failed to construct other explicit separations. Monitoring is a proposed aid, not an evaluated intervention.

## Expanding the earlier completeness point

The [original question][problem] asks what property of a Boolean function controls the minimum number of attention heads needed to compute it. At the start, the agent recognizes that this is a broad research question with several possible kinds of answer, rather than a single statement with a predetermined proof obligation ([L34][t34]).

The agent eventually gives an exact algebraic reformulation and several substantial theorems. It calls the result a complete affirmative answer ([L7038][t7038]). However, one important quantitative question remains unresolved: **how many heads do the hardest functions actually require as the number of input bits grows?**

Its lower bound establishes that some functions require many heads. Its upper bound gives a construction for every function using a larger number of heads. The ratio between these bounds grows approximately as **three times the number of input bits**, rather than staying within a fixed constant ([answer][a1679]). Consequently, the result leaves a growing multiplicative uncertainty about the worst-case number of heads. The exact reformulation does not close that uncertainty.

The same issue arises for a motivating natural family: [addressing functions][a1073]. Their general lower bound grows linearly in the number of address bits, while the upper bound grows exponentially. The result therefore does not determine whether their head requirements grow linearly, exponentially, or at an intermediate rate.

**What is the undesirable consequence?** The delivered theory leaves the optimal worst-case scaling and the general scaling of this natural family unresolved. These are observable limitations of the mathematical results.

**What is not established?** The record does not show that the agent caused this gap by stopping prematurely, that a different search would have closed it, or that closing it was necessary to satisfy the original problem. The final answer also displays the gap explicitly. Therefore, this example is **context about the scope of the results**, rather than strong evidence of a harmful autoresearch behavior. Under the requirement to show an observed undesirable consequence of the research process, the examples below are better candidates.

## Three main limitations with observed consequences

| Limitation | Observed undesirable consequence | Evidence | Comment |
|---|---|---|---|
| **1. A narrow search parameterization can miss an attainable construction.** | **600 trials** fail to find a four-head indexing model, although an exact four-head model is later found after changing the search. | The initial code fixes positively oriented denominators and searches numerator coefficients ([L2191][t2191], [result L2193][t2193]). Joint optimization across denominator orientations later succeeds ([L3575][t3575], [exact certificate L3617][t3617]). | This is an observed search miss, corrected by an autonomous pivot. It does not prove that mixed orientations are necessary or that any particular change alone caused success. |
| **2. The agent can pursue a local target that cannot deliver its intended improvement.** | A covering search runs for about **eleven minutes** before the agent recognizes that even success would not improve the governing worst-case constant. | It launches the 14-by-11 search to improve the universal constant at **12:13** ([L6243][t6243]), then identifies the mismatch and redirects at **12:24** ([L6372][t6372]). | The observed cost is effort directed at an unsuitable target. This does not imply that the search had no other mathematical value. |
| **3. Continued runtime can be spent monitoring stalled searches without improving the result.** | For roughly **45 minutes**, the agent launches no new experiment and makes no file edits. The heuristic produces no better cover, while the exact solver remains unresolved. | Between [L6480][t6480] and [L6944][t6944], tool activity consists of **72 process polls, four budget checks, and one wait**. The heuristic ends at 60 of 64 covered points, matching a simple modification of an existing certificate. | The eight-hour minimum partly explains the persistence ([L10][t10], [L6542][t6542]). The elapsed time and lack of improvement are observed; the benefit of an alternative allocation is unknown. |

## Three backups with observed consequences

| Limitation | Observed undesirable consequence | Evidence | Comment |
|---|---|---|---|
| **4. Self-review can repeat an incorrect account of why a method is limited.** | A false counting-ceiling explanation survives for approximately **39 minutes** and is repeated as an audited conclusion before retraction. | The argument appears at **09:18**, recurs at **09:57**, and is then corrected ([L4322][t4322], [L4909][t4909], [L4919][t4919]). | The undesirable outcome is an incorrect intermediate explanation. It was corrected before delivery; the record does not establish that it caused a later search failure. |
| **5. A proposed new bound can survive testing while adding no improvement over an existing bound.** | The agent develops and tests a boundary invariant, then removes the proposed bound because ordinary sign rank already gives a stronger estimate. | The candidate is introduced at [L4576][t4576], its finite checks pass at [L4593][t4593], and its redundancy is identified at [L4602][t4602]. | The claimed improvement did not survive comparison. The structural identity remained useful, so not all of the work was wasted. |
| **6. A stronger-than-needed intermediate goal can leave a construction blocked.** | The proposed addressing proof depends on a full-surjectivity statement that remains unproved. A weaker two-point relation later completes the construction without that statement. | The missing proof is reported at [L2330][t2330]; the sufficient weaker relation appears at [L3353][t3353]. The [registry][r512] explicitly records that the stronger statement was unnecessary. | The consequence is a temporary, unnecessary proof obligation. The agent removed it autonomously. The record does not establish how much time could have been saved or whether pursuing it helped the later discovery. |

## Search patterns and possible tunnel vision

These patterns make the limitations more specific. They concern the selection of intermediate goals and allocation of effort, rather than the correctness of the final theorems.

### A. Getting stuck on a stronger intermediate statement than needed

The addressing construction initially targeted **surjectivity of an entire first-order map**. At **06:36**, the agent had checked small cases but lacked the uniform proof ([L2330][t2330]). At **07:53**, it found that a much weaker two-point relation supplying opposite signs was sufficient ([L3353][t3353]); the resulting theorem was proved by **08:02** ([L3488][t3488]).

The [registry explicitly acknowledges][r512] that the stronger statement remained blocked and was unnecessary.

**Observed consequence:** this proof route remained blocked on an obligation that the final construction did not need. It became complete after the agent weakened the intermediate requirement.

**Qualification:** the agent made the simplifying conceptual move autonomously. These timestamps bracket the development; they do not establish 77 minutes of exclusive work on that lemma.

### B. Mistaking a local improvement for progress on the main bound

At **12:13**, the agent launched a **14-by-11 covering search**, saying success would improve the universal **3/2** constant ([L6243][t6243]). At **12:24**, it recognized that this cover would improve only a later interval, **not the transition controlling the worst-case constant**, and redirected the search ([L6372][t6372]).

**Observed consequence:** the agent invested approximately eleven minutes before recognizing that the proposed local improvement could not achieve its stated objective. It then had to redirect the experiment.

The broader pattern is concentration on an accessible construction. The answer proves strong results about [fixed-denominator interpolation][a914], but explicitly notes that [cover optimality does not lower-bound head complexity][a867]. Sharpening this construction need not resolve the remaining characterization gap.

**Qualification:** earlier cover searches produced valuable theorems. This episode does not establish that the overall allocation was inefficient, and the agent corrected the mismatch.

### C. A diverse portfolio can narrow into prolonged monitoring

The registry contains thirteen approach families, and the agent audits their diversity at **11:40** ([L5591][t5591]). Nevertheless, from **12:35:21 to 13:20:02**, roughly **45 minutes**, the recorded tool activity consists only of:

- **72 polls** of two existing search processes.
- **4 checks** of the goal budget.
- **1 wait** for a running tool call.

There are **no new experiment launches or file edits in that interval**. These counts come from the tool-call records between [L6480][t6480] and [L6944][t6944], not from keyword counts. The heuristic finishes at **60 of 64** covered points, no improvement over deleting a column from an existing certificate; the exact solver remains unresolved.

**Observed consequence:** roughly 45 additional minutes produced no improved cover or new experiment. Having several approaches in a registry did not prevent this later concentration on monitoring two stalled searches.

**Qualification:** the human prompt imposed an eight-hour minimum ([L10][t10]). At **12:41**, the agent explicitly says the proof is releasable but it is honoring the audit window ([L6542][t6542]). This implicates the stopping instruction and workflow as well as the agent's choices. It does not show that another allocation would have succeeded.

### A recurring mathematical bottleneck

Several distinct techniques lose some of the structure that makes this architecture special:

- **Threshold degree** discards enough structure that it cannot capture exponential head requirements ([registry B][r34]).
- **Generic parameter counting** ignores the shared-product structure needed to improve its bound ([registry E][r119]).
- **Boundary matrix rank** discards shared exterior-minor relations and yields a bound already dominated by ordinary sign rank ([registry M][r568]).

**Interpretation:** different mathematical techniques can encounter related information-loss barriers. Naming more approach families does not by itself resolve those barriers. The agent recognized them, so this supports a limitation of its available methods, not a claim that all thirteen routes were cosmetic variations.

## Evidence against a broad tunnel-vision claim

The run also changed mathematical mechanisms. A blocked generic interpolation route gave way to a successful neighborhood-localization construction ([L638][t638]). An obstruction within the first-order addressing construction was followed by an exact four-head solution outside that construction ([registry K][r520]). Even late in the run, the agent noticed and repaired a missing mixed-sign threshold-composition case ([L5905][t5905], [L6086][t6086]).

The supported conclusion is **local anchoring that was sometimes corrected**, with a particularly clear late period of concentrated monitoring. It is not a general inability to develop new mechanisms.

## Correction to the proposed human-counterexample example

This rollout does **not** show that explicit separations required a separate human suggestion. The agent reports a threshold-degree-two family with growing head complexity at **04:00** ([L187][t187]) and writes an explicit Walsh-Hadamard separation at **04:10** ([L285][t285], [successful write L287][t287]).

The [initial problem][problem] already requested classical comparisons and explicit separating families. Thus the agenda was human-framed, while the construction was autonomous. The provenance of a **separate compact counterexample idea** is not established by this record.


## Other scope limits without a demonstrated harmful outcome

These remain useful context, but do not meet the stronger standard of showing an undesirable consequence caused by the research process.

- **Finite evidence left a general statement unresolved.** Sharp interpolation certificates reached dimension twelve ([L3083][t3083]), but one proposed uniform construction had rank 62 instead of 63 ([L3152][t3152], [L3175][t3175]). The agent recognized the need for a structural argument ([L3059][t3059]). A failed construction is part of research; this episode alone does not establish a deficient search strategy.
- **Discovery reliability was not measured.** Certificate reruns succeeded ([L4550][t4550], [L7038][t7038]), but the record contains no independent repetitions of the discovery task. This prevents estimating reliability across runs; it does not show a failure to reproduce.
- **The retained Lean follow-up had limited scope.** A separate human request initiated formalization ([L7046][t7046]), and the follow-up covered the algebraic core ([L7079][t7079], [L7421][t7421]). No resulting false theorem is identified here. This scope must also be distinguished from the later formalization of the paper's main theorems.

## Brief external context

The evidence above is local to this case. **RE-Bench** reports slowing progress in extended agent attempts and distinguishes its well-defined optimization tasks from messier research objectives; its ML-engineering results are not a performance estimate for this mathematical run. See [Wijk et al., Sections 4.1, 4.2, and 6.1](https://arxiv.org/html/2411.15114v1). **The AI Scientist** authors identify major conceptual advances as an unresolved capability question. See [Lu et al., Limitations](https://www.nature.com/articles/s41586-026-10265-5).

One retained trajectory cannot establish success rates, superiority to humans, benefits from independent restarts, or a general incapacity for conceptual research.

[rollout]: ../../system-design/rollouts/theorems-rollout.jsonl
[registry]: ../../system-design/approach_registry.md
[answer]: ../../system-design/answer.md
[problem]: ../../system-design/problem_statement.md#L33
[a867]: ../../system-design/answer.md#L867
[a914]: ../../system-design/answer.md#L914
[a1073]: ../../system-design/answer.md#L1073
[a1679]: ../../system-design/answer.md#L1679
[r34]: ../../system-design/approach_registry.md#L34
[r119]: ../../system-design/approach_registry.md#L119
[r512]: ../../system-design/approach_registry.md#L512
[r520]: ../../system-design/approach_registry.md#L520
[r568]: ../../system-design/approach_registry.md#L568
[t10]: ../../system-design/rollouts/theorems-rollout.jsonl#L10
[t34]: ../../system-design/rollouts/theorems-rollout.jsonl#L34
[t187]: ../../system-design/rollouts/theorems-rollout.jsonl#L187
[t285]: ../../system-design/rollouts/theorems-rollout.jsonl#L285
[t287]: ../../system-design/rollouts/theorems-rollout.jsonl#L287
[t638]: ../../system-design/rollouts/theorems-rollout.jsonl#L638
[t2191]: ../../system-design/rollouts/theorems-rollout.jsonl#L2191
[t2193]: ../../system-design/rollouts/theorems-rollout.jsonl#L2193
[t2203]: ../../system-design/rollouts/theorems-rollout.jsonl#L2203
[t2330]: ../../system-design/rollouts/theorems-rollout.jsonl#L2330
[t3059]: ../../system-design/rollouts/theorems-rollout.jsonl#L3059
[t3083]: ../../system-design/rollouts/theorems-rollout.jsonl#L3083
[t3152]: ../../system-design/rollouts/theorems-rollout.jsonl#L3152
[t3175]: ../../system-design/rollouts/theorems-rollout.jsonl#L3175
[t3353]: ../../system-design/rollouts/theorems-rollout.jsonl#L3353
[t3488]: ../../system-design/rollouts/theorems-rollout.jsonl#L3488
[t3575]: ../../system-design/rollouts/theorems-rollout.jsonl#L3575
[t3617]: ../../system-design/rollouts/theorems-rollout.jsonl#L3617
[t4322]: ../../system-design/rollouts/theorems-rollout.jsonl#L4322
[t4550]: ../../system-design/rollouts/theorems-rollout.jsonl#L4550
[t4576]: ../../system-design/rollouts/theorems-rollout.jsonl#L4576
[t4593]: ../../system-design/rollouts/theorems-rollout.jsonl#L4593
[t4602]: ../../system-design/rollouts/theorems-rollout.jsonl#L4602
[t4909]: ../../system-design/rollouts/theorems-rollout.jsonl#L4909
[t4919]: ../../system-design/rollouts/theorems-rollout.jsonl#L4919
[t5591]: ../../system-design/rollouts/theorems-rollout.jsonl#L5591
[t5905]: ../../system-design/rollouts/theorems-rollout.jsonl#L5905
[t6086]: ../../system-design/rollouts/theorems-rollout.jsonl#L6086
[t6243]: ../../system-design/rollouts/theorems-rollout.jsonl#L6243
[t6372]: ../../system-design/rollouts/theorems-rollout.jsonl#L6372
[t6480]: ../../system-design/rollouts/theorems-rollout.jsonl#L6480
[t6542]: ../../system-design/rollouts/theorems-rollout.jsonl#L6542
[t6944]: ../../system-design/rollouts/theorems-rollout.jsonl#L6944
[t7038]: ../../system-design/rollouts/theorems-rollout.jsonl#L7038
[t7046]: ../../system-design/rollouts/theorems-rollout.jsonl#L7046
[t7079]: ../../system-design/rollouts/theorems-rollout.jsonl#L7079
[t7421]: ../../system-design/rollouts/theorems-rollout.jsonl#L7421
