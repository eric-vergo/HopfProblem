/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5 (Claude Code)
-/
/-
The Hopf Problem blueprint — top-level document.

The subject arrives as a path dependency on the repository root, so `import Solution`
(through the chapter modules) puts all ~20,600 declarations of the `Mathoverflow1973`
namespace in the environment for the all-declarations registry, graph and declaration
pages.  `Challenge.lean` is NOT imported: it states the goal with `sorry`.

The byline strings below carry each contributor's ROLE, because `:::author` has nowhere
to put one and three bare names would read as joint authorship of all three layers
(mathematics / formalization / presentation), which is false in every direction.  They
must match the `:::author` display names in `Authors.lean` exactly.
-/

import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import VersoBlueprint.Commands.Bibliography
import VersoBlueprint.Commands.Formalization

import Contents.TeXPrelude
import Authors
import Bibliography
import Chapters.Introduction
import Chapters.Lattice
import Chapters.AnalyticFoundations
import Chapters.Orbifold
import Chapters.PeriodFamily
import Chapters.ToricFilling
import Chapters.LogTransforms
import Chapters.Threefold
import Chapters.HomologyTheory
import Chapters.TorusHomology
import Chapters.CuspFibre
import Chapters.FundamentalGroup
import Chapters.HomologyOfX
import Chapters.HurewiczLadder
import Chapters.HomotopyEquivalence
import Chapters.MorseTheory
import Chapters.Cancellation
import Chapters.MainTheorem

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true
-- Scale headroom for the top-level document over the subject's ~20,600 declarations.
-- The `{blueprint_graph}` flat-JSON payload retires the code-generator recursion, but
-- the ELABORATOR still recurses building the registry / graph model (the first command
-- to trigger it is `{blueprint_dashboard}` below), which far exceeds the default
-- 512-frame `maxRecDepth`.  This is ordinary elaborator headroom, not a band-aid.
-- Heartbeats are raised for the same reason: the featured-card render and the
-- `{blueprint_trust_model}` axiom audit normalize heavy analytic signatures well past
-- the default 200k-heartbeat cap.
set_option maxRecDepth 400000
set_option maxHeartbeats 40000000

#doc (Manual) "The Hopf Problem" =>

%%%
shortTitle := "Hopf"
authors := ["Boris Alexeev (formalization)", "Levent Alpöge (mathematics)", "Eric Vergo (presentation)"]
%%%

{blueprint_dashboard (featured := "thm:mathoverflow-1973, def:threefold-space, def:threefold-homotopy-equiv, thm:homeomorphic-six-sphere-of-homotopy-six-sphere")}

{include 0 Chapters.Introduction}

{include 0 Chapters.Lattice}

{include 0 Chapters.AnalyticFoundations}

{include 0 Chapters.Orbifold}

{include 0 Chapters.PeriodFamily}

{include 0 Chapters.ToricFilling}

{include 0 Chapters.LogTransforms}

{include 0 Chapters.Threefold}

{include 0 Chapters.HomologyTheory}

{include 0 Chapters.TorusHomology}

{include 0 Chapters.CuspFibre}

{include 0 Chapters.FundamentalGroup}

{include 0 Chapters.HomologyOfX}

{include 0 Chapters.HurewiczLadder}

{include 0 Chapters.HomotopyEquivalence}

{include 0 Chapters.MorseTheory}

{include 0 Chapters.Cancellation}

{include 0 Chapters.MainTheorem}


{blueprint_graph}

{blueprint_summary}

{blueprint_formalization "../formalization.yaml"}

{blueprint_trust_model}

{blueprint_bibliography}
