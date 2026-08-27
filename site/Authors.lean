/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5 (Claude Code)
-/
/-
The Hopf Problem blueprint — author bylines / attribution metadata.

Three distinct roles, none of them interchangeable, and the bylines below are not a
claim of joint authorship:

  Mathematics:   Levent Alpöge — "A compact complex threefold fibred by tori over the
                 projective line, and the six-sphere" (https://alpo.ge/s6.pdf).
  Formalization: Boris Alexeev (https://github.com/plby/HopfProblem); the file header
                 of `Solution.lean` records that the majority of the Lean code was
                 written by Codex.
  Presentation:  this site — Eric Vergo, with Claude (Claude Code).

The `:::author` directive carries only name, link and (unused here) an image url, with
nowhere to put a role — and an undifferentiated three-name byline would read as joint
authorship of all three layers, which is false in every direction.  So the role rides in
the display name itself, and the byline in `Contents.lean` uses the same strings.  The
`image_url` field is deliberately never set: no author avatars (project convention),
name + link only.
-/

import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Blueprint Authors" =>

:::author "alexeev" (name := "Boris Alexeev (formalization)") (url := "https://github.com/plby")
:::

:::author "alpoge" (name := "Levent Alpöge (mathematics)") (url := "https://alpo.ge/")
:::

:::author "vergo" (name := "Eric Vergo (presentation)")
:::
