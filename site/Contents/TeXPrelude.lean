/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5 (Claude Code)
-/
import Verso
import VersoManual
import VersoBlueprint

open Informal

tex_prelude r#"
% KaTeX in the current harness is missing these shorthands.
% (\R and \Z are already builtin as \mathbb{R} / \mathbb{Z}, so do not redefine them.)
\newcommand{\C}{\mathbb{C}}
\newcommand{\PP}{\mathbb{P}}
"#
