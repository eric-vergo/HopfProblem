/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5 (Claude Code)
-/
/-
The Hopf Problem blueprint — bibliography.

Only sources this site actually cites.  The two entries that carry the provenance of
the formalization (Alpöge's preprint and the Formal Conjectures statement) are the two
whose locators are recorded in `Solution.lean`'s own file header, so they can be
checked against the subject rather than taken on this site's word.
-/

import VersoManual.Bibliography
import VersoBlueprint.Cite

open Verso.Genre.Manual.Bibliography

@[bib "alpoge.s6"]
def alpoge.s6 : Citable := .inProceedings
    { title := inlines!"A compact complex threefold fibred by tori over the projective line, and the six-sphere"
    , authors := #[inlines!"Levent Alpöge"]
    , year := 2026
    , booktitle := inlines!"Preprint"
    , url := some "https://alpo.ge/s6.pdf"
    }

@[bib "alexeev.hopf"]
def alexeev.hopf : Citable := .inProceedings
    { title := inlines!"HopfProblem: a formalization of the resolution of the Hopf problem"
    , authors := #[inlines!"Boris Alexeev"]
    , year := 2026
    , booktitle := inlines!"GitHub repository"
    , url := some "https://github.com/plby/HopfProblem"
    }

@[bib "mathoverflow1973"]
def mathoverflow1973 : Citable := .inProceedings
    { title := inlines!"Does the 6-sphere admit the structure of a complex manifold? (MathOverflow question 1973)"
    , authors := #[inlines!"MathOverflow"]
    , year := 2009
    , booktitle := inlines!"MathOverflow"
    , url := some "https://mathoverflow.net/questions/1973/"
    }

@[bib "formal.conjectures"]
def formal.conjectures : Citable := .inProceedings
    { title := inlines!"Formal Conjectures — FormalConjectures/Mathoverflow/1973.lean"
    , authors := #[inlines!"The Formal Conjectures Authors"]
    , year := 2025
    , booktitle := inlines!"Google DeepMind"
    , url := some "https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Mathoverflow/1973.lean"
    }

@[bib "hopf48"]
def hopf48 : Citable := .inProceedings
    { title := inlines!"Zur Topologie der komplexen Mannigfaltigkeiten"
    , authors := #[inlines!"Heinz Hopf"]
    , year := 1948
    , booktitle := inlines!"Studies and Essays Presented to R. Courant on his 60th Birthday"
    }

@[bib "kodaira64"]
def kodaira64 : Citable := .inProceedings
    { title := inlines!"On the structure of compact complex analytic surfaces, I"
    , authors := #[inlines!"Kunihiko Kodaira"]
    , year := 1964
    , booktitle := inlines!"American Journal of Mathematics 86, 751–798"
    }

@[bib "mumford72"]
def mumford72 : Citable := .inProceedings
    { title := inlines!"An analytic construction of degenerating abelian varieties over complete rings"
    , authors := #[inlines!"David Mumford"]
    , year := 1972
    , booktitle := inlines!"Compositio Mathematica 24, 239–272"
    }

@[bib "smale61"]
def smale61 : Citable := .inProceedings
    { title := inlines!"Generalized Poincaré's conjecture in dimensions greater than four"
    , authors := #[inlines!"Stephen Smale"]
    , year := 1961
    , booktitle := inlines!"Annals of Mathematics 74, 391–406"
    }

@[bib "kervaire.milnor63"]
def kervaire.milnor63 : Citable := .inProceedings
    { title := inlines!"Groups of homotopy spheres: I"
    , authors := #[inlines!"Michel A. Kervaire", inlines!"John W. Milnor"]
    , year := 1963
    , booktitle := inlines!"Annals of Mathematics 77, 504–537"
    }

@[bib "milnor65"]
def milnor65 : Citable := .inProceedings
    { title := inlines!"Lectures on the h-cobordism theorem"
    , authors := #[inlines!"John W. Milnor"]
    , year := 1965
    , booktitle := inlines!"Princeton Mathematical Notes, Princeton University Press"
    }

@[bib "cdp98"]
def cdp98 : Citable := .inProceedings
    { title := inlines!"The algebraic dimension of compact complex threefolds with vanishing second Betti number"
    , authors := #[inlines!"Frédéric Campana", inlines!"Jean-Pierre Demailly", inlines!"Thomas Peternell"]
    , year := 1998
    , booktitle := inlines!"Compositio Mathematica 112, 77–91"
    }

@[bib "cdp20"]
def cdp20 : Citable := .inProceedings
    { title := inlines!"Erratum to: The algebraic dimension of compact complex threefolds with vanishing second Betti number"
    , authors := #[inlines!"Frédéric Campana", inlines!"Jean-Pierre Demailly", inlines!"Thomas Peternell"]
    , year := 2020
    , booktitle := inlines!"Compositio Mathematica 156"
    }

@[bib "hatcher02"]
def hatcher02 : Citable := .inProceedings
    { title := inlines!"Algebraic Topology"
    , authors := #[inlines!"Allen Hatcher"]
    , year := 2002
    , booktitle := inlines!"Cambridge University Press"
    }

@[bib "orlik72"]
def orlik72 : Citable := .inProceedings
    { title := inlines!"Seifert Manifolds"
    , authors := #[inlines!"Peter Orlik"]
    , year := 1972
    , booktitle := inlines!"Lecture Notes in Mathematics 291, Springer"
    }

@[bib "agr.ang18"]
def agr.ang18 : Citable := .inProceedings
    { title := inlines!"Complex structures on the six-dimensional sphere (survey collection)"
    , authors := #[inlines!"Ilka Agricola", inlines!"Aleksy Tralle", inlines!"et al."]
    , year := 2018
    , booktitle := inlines!"Differential Geometry and its Applications 57 (special issue)"
    }

@[bib "lebrun87"]
def lebrun87 : Citable := .inProceedings
    { title := inlines!"Orthogonal complex structures on S⁶"
    , authors := #[inlines!"Claude LeBrun"]
    , year := 1987
    , booktitle := inlines!"Proceedings of the American Mathematical Society 101, 136–138"
    }

@[bib "kudryashov.rmt"]
def kudryashov.rmt : Citable := .inProceedings
    { title := inlines!"Riemann mapping theorem (Mathlib pull request #33505)"
    , authors := #[inlines!"Yury Kudryashov"]
    , year := 2026
    , booktitle := inlines!"leanprover-community/mathlib4"
    , url := some "https://github.com/leanprover-community/mathlib4/pull/33505"
    }

@[bib "kumar.vankampen"]
def kumar.vankampen : Citable := .inProceedings
    { title := inlines!"Simply connected spheres and the van Kampen development (Mathlib pull request #28246)"
    , authors := #[inlines!"Sebastian Kumar"]
    , year := 2026
    , booktitle := inlines!"leanprover-community/mathlib4"
    , url := some "https://github.com/leanprover-community/mathlib4/pull/28246"
    }

