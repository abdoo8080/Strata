/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.DDMTransform.Parse

---------------------------------------------------------------------

namespace Strata

---------------------------------------------------------------------
---------------------------------------------------------------------

/- DDM support for parsing and pretty-printing Boole -/

-- Note: add support for multiple invariants, for loops down to, quantifier syntax, array assign syntax, structures and records, simple calls, `/` operator, summations, etc. are not supported yet

#dialect
dialect Boole;

import Boogie;

op for_statement (v : MonoBind, init : Expr,
  @[scope(v)] guard : bool, @[scope(v)] step : Expr,
  @[scope(v)] i : Option Invariant, @[scope(v)] body : Block) : Statement =>
  "for " "(" "var " v " := " init "; " guard "; " step ")" i body;

#end

---------------------------------------------------------------------

end Strata

def test : Strata.Program :=
#strata
program Boole;

procedure f () returns ()
{
  for (var i : int := 0; i < 10; i + 1)
  {
    i := i + 1;
  }
};

#end
