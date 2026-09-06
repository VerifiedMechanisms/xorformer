# Formally Verified Autoresearch for Analyzing the Expressivity of Multi-Head Attention

## TL;DR

LLM agents collaborate to discover and formally verify theorems about the expressivity of multi-head attention by quantifying how many attention heads are required to represent Boolean functions.

## Keywords

Autonomous machine learning research; transformer expressivity; multi-head attention; attention-head complexity; Boolean functions; threshold degree; formal verification; Lean 4.

## Abstract

Multi-head attention is a central component of the transformer architecture, yet how its expressivity depends on the number of heads remains poorly understood. We study a one-layer, attention-only transformer and define the head complexity $H^\ast(f)$ of a Boolean function $f$ as the minimum number of attention heads required to represent it. Our main result exactly characterizes head complexity $H^\ast(f)$ for symmetric Boolean functions, showing that it equals the number of times $f$ changes value between consecutive Hamming-weight levels. Beyond the symmetric setting, we prove that threshold degree provides a lower bound on head complexity and give an explicit example showing that this lower bound is not always tight. These results were discovered and formalized by a frontier model through conjecture generation, theorem proving, and machine verification, while human researchers asked the high-level questions and reviewed the generated theorems. This work also lays the groundwork for a publicly available Lean codebase intended to support agent-assisted theorem proving and formal verification in mechanistic interpretability. More broadly, this work serves as a proof of concept for a broader research program that leverages the mathematical capabilities of frontier models, grounded by formal verification, to build towards a fundamental understanding of transformer architectures.
