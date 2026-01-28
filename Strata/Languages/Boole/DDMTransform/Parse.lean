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

category Invariants;
op nilInvariants : Invariants => ;
op consInvariants(e : Expr, is : Invariants) : Invariants =>
  "invariant" e is;

category Step;
op step(e: Expr) : Step =>
  " by " e;

op for_statement (v : MonoBind, init : Expr,
  @[scope(v)] guard : bool, @[scope(v)] step : Expr,
  @[scope(v)] invs : Option Invariant, @[scope(v)] body : Block) : Statement =>
  "for " "(" v " := " init "; " guard "; " step ")" invs body;

op for_to_by_statement (v : MonoBind, init : Expr, limit : Expr,
  @[scope(v)] step : Option Step, @[scope(v)] invs : Invariants,
  @[scope(v)] body : Block) : Statement =>
  "for " v " := " init " to " limit step invs body;

op for_down_to_by_statement (v : MonoBind, init : Expr, limit : Expr,
  @[scope(v)] step : Option Step, @[scope(v)] invs : Invariants,
  @[scope(v)] body : Block) : Statement =>
  "for " v " := " init " downto " limit step invs body;

op while_statement (c : bool, invs : Invariants, body : Block) : Statement =>
  "while" c invs body;

#end

---------------------------------------------------------------------

end Strata

def test : Strata.Program :=
#strata
program Boole;

procedure f () returns ()
{
  for i : int := 0 to 10
    invariant 0 <= i
  {
    i := i + 1;
  }
};

procedure h_down_to () returns ()
{
  for k : int := 20 downto 0
      invariant k div 2 == 0
      invariant k >= 0
  {
      k := k - 2;
  }
};

procedure h_down_to_by () returns ()
{
  for k : int := 20 downto 0 by 2
      invariant k div 2 == 0
      invariant k >= 0
  {
      k := k - 2;
  }
};

procedure w () returns ()
{
  var j : int;
  j := 0;

  while j < 10
    invariant 0 <= j
    invariant j <= 10
    invariant j == 0 || j > 0
  {
    j := j + 1;
  }
};

#end
