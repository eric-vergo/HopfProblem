/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5 (Claude Code)
-/
/-
The Hopf Problem blueprint — site generator entrypoint.
-/

import Std.Data.HashMap
import VersoManual
import VersoBlueprint.Macros
import VersoBlueprint.PreviewManifest
import VersoBlueprint.Main
import Contents

open Verso Doc
open Verso.Genre Manual

open Std (HashMap)

def htmlAssets : HtmlAssets where
  features := .all
  extraCss := {}
  extraJs := [tex_prelude_table_js%, Informal.Macros.blueprintMathJs]
  extraJsFiles := {}
  extraCssFiles := {}
  extraDataFiles := {}
  licenseInfo := {}

def htmlConfig : HtmlConfig where
  toHtmlAssets := htmlAssets
  htmlDepth := 1
  extraHead : Array Output.Html := #[]

def outputConfig : OutputConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately

def config : Config where
  toHtmlConfig := htmlConfig
  toOutputConfig := outputConfig

def renderConfig : RenderConfig where
  toConfig := config

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithFeatures
    (%doc Contents)
    args
    (extensionImpls := by exact extension_impls%)
    (config := renderConfig)
    (extraSteps := [])
