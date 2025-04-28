# LeanLJ

LeanLJ stands for Lean Lennard-Jones. It is a project that brings mathematical accuracy and reliability to molecular simulations, and is the first steps toward formalizing molecular dynamics (MD) and Monte Carlo (MC) simulations. 
It is built using the Lean 4 programming language and theorem prover. LeanLJ aims to make scientific software provable by ensuring every 
calculation and simulation step is grounded in proven mathematics. Our vision is to help scientists and researchers run simulations 
they can fully trust, knowing that each part has been rigorously checked for correctness.

## Goals of LeanLJ
+ ***Mathematically Verified Simulations:*** LeanLJ’s eventual goal is on verifying every calculation involved in MD simulations, including foundational
equations like Newton's laws of motion and energy conservation. Unlike conventional simulations, which rely on humans to check correctness, we can formalize these
equations in Lean, ensuring each step adheres strictly to mathematical principles. This precision greatly reduces the risk of software errors, leading
to more reliable simulation results.

+ ***Provable Scientific Computing:*** LeanLJ provides a framework to prevent errors arising from coding bugs or oversight.
Inspired by the precise methods used in fields like chip manufacturing, LeanLJ’s system checks each step of the calculation for correctness, for
simulations that are as free from errors as possible. This is particularly valuable for complex molecular systems where accuracy is essential.

+ ***Supporting Education and Research:*** LeanLJ isn’t just a tool -- it’s also a resource for students and researchers learning about the importance of
verified computing. Through its open-source library, LeanLJ offers access to verified scientific theorems that anyone can use and learn from. This educational focus helps expand Lean’s impact, encouraging a culture of learning and collaboration among researchers and students alike.

+ ***Automation with AI:*** Looking to the future, LeanMD plans to incorporate AI tools, such as large language models (LLMs), to help automate some of the more complex proof steps. This addition could make it faster and easier to explore new scientific theories, validate findings, and possibly even generate new insights automatically. By integrating AI, LeanMD aims to keep up with the latest advancements, making proof generation and validation quicker and more efficient.

## Impact and Vision
LeanLJ sets a new standard in molecular simulations by ensuring that each calculation is backed by solid, error-free mathematics. In the future, LeanMD aims to improve the 
quality and reliability of scientific software, paving the way for discoveries grounded in accurate, proven calculations.

## Project Installation

### Prerequisite
  - Lean 4 (Lean version 4.16.0-rc2)
  
  - Mathlib Library (at commit e1a3d4c)

## Setup

1 - Install Lean Dependencies and Mathlib
 [HERE](https://lean-lang.org/lean4/doc/quickstart.html)

2 - Clone the repository
  ```bash
  git clone https://github.com/ATOMSLab/LeanLJ.git
  ```

## License
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](https://www.apache.org/licenses/LICENSE-2.0)

This project is licensed under the [Apache 2.0 License](https://www.apache.org/licenses/LICENSE-2.0).




