QUnit.assert.testevl = function (a, b){
  this.same(L.dsj(L.evl(L.prs(a))), b, "evaluating " + a);
};