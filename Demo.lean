import Strata.Languages.Boogie.ToVelvet

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 4
set_option auto.smt.solver.name "cvc5"

#strataVelvet
program Boogie;

procedure loopSimple (n: int) returns (r: int)
spec {
  requires (n >= 0);
}
{
  var sum : int := 0;
  var i : int := 0;
  while (i < n)
    invariant (i <= n && ((i * (i-1)) div 2 == sum));
  {
    sum := sum + i;
    i := i + 1;
  }
  r := sum;
};

#end

#check Boogie.loopSimple
#print Boogie.loopSimple

prove_correct Boogie.loopSimple by
  dsimp [Boogie.loopSimple]
  loom_solve
  grind
