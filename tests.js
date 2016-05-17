QUnit.test('Interpreter', function (assert){
  assert.testevl("`1", "1");
  assert.testevl("`a", "a");
  assert.testevl("`(a b c)", "(a b c)");
  assert.testevl("`(a b ,(if t 5 4))", "(a b 5)");
  assert.testevl("`,(if t 5 4)", "5");
  assert.testevl("`(a b `(c ,d ,,(if t 5 4)))", "(a b `(c ,d 5))");
  assert.testevl("``,,(if t 5 4)", "`5");
  assert.testevl("``,(if t 5 4)", "`,(if t 5 4)");
  assert.testevl("``(a b ,(c d ,(if t 5 4)))", "`(a b ,(c d 5))");
  // ...
  
  assert.testevl("('(1 2 3) 0)", "1");
});
