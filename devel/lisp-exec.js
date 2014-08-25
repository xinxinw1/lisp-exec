/***** Lisp Interpreter Devel *****/

/* requires tools >= 3.0 */
/* requires lisp-parse */

(function (win, udef){
  ////// Import //////
  
  var err = $.err;
  
  ////// Processing functions //////
  
  function rembds(a){
    return $.slc(a, 1, $.len(a)-1);
  }
  
  ////// Dynamic Javascript Vars //////
  
  function dyn(a, x, f){
    push(x, a);
    var r = f();
    pop(a);
    return r;
  }
  
  ////// Display //////
  
  var disps = [];
  function disp(a){
    return dyn(disps, a, function (){
      return disp1(a);
    });
  }
  
  function disp1(a){
    var tp = type(a);
    switch (tp){
      case "nil": return "()";
      case "str": return "\"" + a[1] + "\"";
      case "jfn": return $.disp(a);
      case "jfn2": return "<jfn2 " + disp(a[1]) + " " + disp(a[2]) + ">";
      case "fn": return "<fn " + disp(a[1]) + " " + disp(a[2]) + ">";
      case "mac": return "<mac " + disp(cdr(a)) + ">";
      case "spec": return "<spec " + disp(cdr(a)) + ">";
      case "obj": return dispobj(a);
      case "arr": return disparr(a);
      case "list":
      case "pair": return displis(a);
      case "num":
      case "sym": return a;
    }
    err(disp1, "Cannot display a = $1 with type tp = $2", a, tp);
  }
  
  function dispobj(a){
    if (has(a, cdr(disps)))return "{...}";
    var r = [];
    for (var i in a){
      r.push(disp(i) + " " + disp(a[i]), r);
    }
    return "{" + r.join(" ") + "}";
  }
  
  function disparr(a){
    if (has(a, cdr(disps)))return "[...]";
    var s = "[";
    if (a[1].length > 0){
      s += disp(a[1][0]);
      for (var i = 1; i < a[1].length; i++){
        s += " " + disp(a[1][i]);
      }
    }
    s += "]";
    return s;
  }
  
  var dlists = [];
  function displis(a){
    if (has(a, cdr(disps)))return "(...)";
    switch (car(a)){
      case "qt": return "'" + disp(cadr(a));
      case "qq": return "`" + disp(cadr(a));
      case "uq": return "," + disp(cadr(a));
      case "uqs": return ",@" + disp(cadr(a));
      case "nfn": return "~" + disp(cadr(a));
    }
    return "(" + dyn(dlists, a, function (){
      return displis2(a);
    }) + ")";
  }
  
  // displis2( '(1 2 3 4 . 5) ) -> "1 2 3 4 . 5"
  function displis2(a){
    if (nilp(cdr(a)))return disp(car(a));
    if (atomp(cdr(a)))return disp(car(a)) + " . " + disp(cdr(a));
    if (has(a, cdr(dlists)))return disp(car(a)) + " . (...)";
    return disp(car(a)) + " " + displis2(cdr(a));
  }
  
  ////// Lisp functions //////
  
  //// Boolean converters ////
  
  function bool(a){
    return (a === false)?[]:"t";
  }
  
  function booler(fn){
    return function (){
      return bool($.apply(fn, arguments));
    };
  }
  
  //// Predicates ////
  
  function consp(a){
    return $.arrp(a) && !($.strp(a[0]) && a[0][0] == "&");
  }
  
  function listp(a){
    if (nilp(a))return true;
    return consp(a) && listp(cdr(a));
  }
  
  function pairp(a){
    return consp(a) && !consp(cdr(a));
  }
  
  function atomp(a){
    return !consp(a) || a.length == 0;
  }
  
  function nilp(a){
    return $.arrp(a) && a.length == 0;
  }
  
  function nump(a){
    return $.strp(a) && $.has(/^-?[0-9]+(\.[0-9]+)?$/, a);
  }
  
  function strp(a){
    return $.arrp(a) && a[0] === "&str";
  }
  
  function objp(a){
    return $.objp(a);
  }
  
  function arrp(a){
    return $.arrp(a) && a[0] === "&arr";
  }
  
  function rgxp(a){
    return $.rgxp(a);
  }
  
  function fnp(a){
    return $.fnp(a) || $.arrp(a) && $.inp(a[0], "&fn", "&jfn", "&jfn2");
  }
  
  function specp(a){
    return $.arrp(a) && $.inp(a[0], "&mac", "&spec");
  }
  
  function procp(a){
    return fnp(a) || specp(a);
  }
  
  function symp(a){
    return $.strp(a) && !nump(a);
  }
  
  //// Basic ////
  
  function car(a){
    return (a[0] !== udef)?a[0]:[];
  }
  
  function cdr(a){
    return (a[1] !== udef)?a[1]:[];
  }
  
  function cons(a, b){
    return [a, b];
  }
  
  //// car and cdr extensions ////
  
  function caar(a){
    return car(car(a));
  }
  
  function cadr(a){
    return car(cdr(a));
  }
  
  function cdar(a){
    return cdr(car(a));
  }
  
  function cddr(a){
    return cdr(cdr(a));
  }
  
  function makeCxr(a){
    a = rembds(a);
    return makeCxr2($.self, a, $.len(a)-1);
  }
  
  function makeCxr2(func, a, pos){
    if (pos == -1)return func;
    if (a[pos] == "a")return makeCxr2(makeCar(func), a, pos-1);
    if (a[pos] == "d")return makeCxr2(makeCdr(func), a, pos-1);
    err(makeCxr2, "a = $1 must only contain a's and d's", a);
  }
  
  function makeCar(func){
    return function (a){
      return car(func(a));
    };
  }
  
  function makeCdr(func){
    return function (a){
      return cdr(func(a));
    };
  }
  
  //// General ////
  
  /*function is(a){
    if (nilp(a) || nilp(cdr(a)))return true;
    return is1(car(a), cadr(a)) && isLisp(cdr(a));
  }*/
  
  function is(a, b){
    return a === b || nilp(a) && nilp(b);
  }
  
  function type(a){
    if ($.fnp(a))return "jfn";
    if ($.arrp(a)){
      if (a.length == 0)return "nil";
      if ($.strp(a[0]) && a[0][0] == "&"){
        if (a[0] === "&jfn")return "jfn2";
        return $.slc(a[0], 1);
      }
      if (!consp(cdr(a)))return "pair";
      return "list";
    }
    if ($.objp(a))return "obj";
    if (nump(a))return "num";
    if ($.strp(a))return "sym";
    err(type, "Unknown type of a = $1", a);
  }
  
  function doLisp(){
    return $.last(arguments);
  }
  
  /*function testfn(a){
    if (fnp(a))return a;
    return function (x){
      return is(x, a);
    };
  }*/
  
  function call(a){
    return apply(a, $.apply(list, $.slc(arguments, 1)));
  }
  
  uniq.n = 0;
  function uniq(){
    uniq.n++;
    return "gs" + uniq.n;
  }
  
  //// List ////
  
  function list(){
    var r = [];
    for (var i = $.len(a)-1; i >= 0; i--){
      r = cons(a, r);
    }
    return r;
  }
  
  function apd(a, b){
    if (nilp(a))return b;
    if (nilp(b))return a;
    if (atomp(a))err(apd, "a = $1 must be a cons", a);
    return cons(car(a), apd(cdr(a), b));
  }
  
  function pair(a, b){
    if (nilp(a))return [];
    if (atomp(a))return list(cons(a, b));
    if (car(a) == "o")return list(cons(cadr(a), nilp(b)?nth(2, a):b));
    return apd(pair(car(a), car(b)), pair(cdr(a), cdr(b)));
  }
  
  function has(x, a){
    if (nilp(a))return false;
    if (is(car(a), x))return true;
    return has(x, cdr(a));
  }
  
  function map(f, a){
    if (nilp(a))return [];
    return cons(f(car(a)), map(f, cdr(a)));
  }
  
  function nth(n, a){
    if (n == 0)return car(a);
    return nth(n-1, cdr(a));
  }
  
  function push(x, a){
    if (nilp(a)){
      a[1] = [];
      a[0] = x;
      return a;
    }
    a[1] = cons(a[0], a[1]);
    a[0] = x;
    return a;
  }
  
  function pop(a){
    var x = car(a);
    if (nilp(cdr(a))){
      a.pop();
      a.pop();
    } else {
      a[0] = cadr(a);
      a[1] = cddr(a);
    }
    return x;
  }
  
  /*function nrev(a, b){
    if (b === udef)b = [];
    if (nilp(a))return b;
    var next = a[1];
    a[1] = b;
    return nrev(next, a);
  }*/
  
  function tail(a, x){
    if (nilp(a))return list(x);
    return cons(car(a), tail(cdr(a), x));
  }
  
  // list -> array
  function arr(a, r){
    if (r === udef)r = [];
    if (nilp(a))return r;
    r.push(car(a));
    return arr(cdr(a), r);
  }
  
  //// Object ////
  
  // k = keys, v = vals
  function pairobj(k, v, o){
    return obj(pair(k, v), o);
  }
  
  function obj(a, o){
    if (o === udef)o = {};
    if (nilp(a))return o;
    o[caar(a)] = cdar(a);
    return obj(cdr(a), o);
  }
  
  //// Extendable ////
  
  /*var lens = {};
  var deflen = handler(setter(lens));
  
  function len(a){
    try {
      var fn = get(type(car(a)), lens);
    } catch (e){
      err(len, "car(a) = $1 is unlenable", car(a));
    }
    return apply(fn, a);
  }
  
  var poses = {};
  var defpos = handler(setter(poses));
  
  function pos(a){
    try {
      var fn = get(type(cadr(a)), poses);
    } catch (e){
      err(pos, "cadr(a) = $1 is unposable", cadr(a));
    }
    return apply(fn, a);
  }
  
  var sums = {};
  var defsum = handler(setter(sums));
  
  function sum(a){
    if (nilp(a))return "0";
    if (nilp(cdr(a)))return car(a);
    try {
      var fn = get(type(car(a)), sums);
    } catch (e){
      err(sum, "Cannot add to car(a) = $1", car(a));
    }
    return apply(fn, a);
  }
  
  var maps = {};
  var defmap = handler(setter(maps));
  
  function map(a){
    try {
      var fn = get(type(cadr(a)), maps);
    } catch (e){
      err(map, "Cannot map over cadr(a) = $1", cadr(a));
    }
    return apply(fn, a);
  }
  
  var revs = {};
  var defrev = handler(setter(revs));
  
  function rev(a){
    try {
      var fn = get(type(car(a)), revs);
    } catch (e){
      err(rev, "car(a) = $1 is unreversible", car(a));
    }
    return apply(fn, a);
  }
  
  var isos = {};
  var defiso = handler(setter(isos));
  
  function iso(a){
    if (is(car(a), cadr(a)))return "t";
    var ta = type(car(a));
    if (ta != type(cadr(a)))return [];
    try {
      var fn = get(ta, isos);
    } catch (e){
      return [];
    }
    return apply(fn, a);
  }*/
  
  ////// Lisp evaluator //////
  
  var envs = [];
  function evl(a, env){
    if (env === udef)env = globals;
    return dyn(envs, env, function (){
      return evl2(a, env);
    });
  }
  
  function cvars(){
    return car(envs);
  }
  
  function evl2(a, env){
    if (atomp(a)){
      if (symp(a))return get(a, env);
      return a;
    }
    var obj = evl(car(a), env);
    if (specp(obj)){
      switch (obj[0]){
        case "&mac": return evl(apply(obj[1], cdr(a)), env);
        case "&spec": return evlspec(obj[1], cdr(a), env);
      }
    }
    return apply(obj, evlis(cdr(a), env));
  }
  
  function evlspec(name, a, env){
    switch (name){
      case "qt": return car(a);
      case "qq": return evlqq(car(a), env);
      case "=": return set(car(a), evl(cadr(a), env), env);
      case "var": return add(car(a), evl(cadr(a), env), env);
      case "if": return evlif(a, env);
      case "fn": return fn(car(a), cons("do", cdr(a)), env);
      case "mc": return mc(car(a), cons("do", cdr(a)), env);
      case "evl": return evl(evl(car(a), env), env);
      case "while": return evlwhile(car(a), cdr(a), env);
      case "set?": return evlsetp(car(a), env);
      case "obj": return evlobj(a, env);
      case "arr": return evlarr(a, env);
    }
    err(evlspec, "Unknown special procedure named $1", name);
  }
  
  function evlis(a, env){
    if (nilp(a))return [];
    return cons(evl(car(a), env), evlis(cdr(a), env));
  }
  
  /*var applys = {};
  var defapply = handler(setter(applys));
  
  function apply(obj, args){
    var tp = type(obj);
    switch (tp){
      case "fn": return evl(obj[2], pairobj(obj[1], args, {0: obj[3]}));
      case "jfn": return $.apply(obj, arr(args));
      case "jfn2": return $.apply(obj[2], arr(map(cdr, pair(obj[1], args))));
    }
    try {
      var fn = get(tp, applys);
    } catch (e){
      err(apply, "Cannot apply args = $1 to obj = $2", args, obj);
    }
    return apply(fn, cons(obj, args));
  }*/
  
  function apply(a, x){
    var tp = type(a);
    switch (tp){
      case "fn": return evl(a[2], pairobj(a[1], x, {0: a[3]}));
      case "jfn": return $.apply(a, arr(x));
      case "jfn2": return $.apply(a[2], arr(map(cdr, pair(a[1], x))));
    }
    err(apply, "Cannot apply x = $1 to a = $2", x, a);
  }
  
  //// Special ////
  
  function evlqq(a, env, lvl){
    if (lvl === udef)lvl = 1;
    if (atomp(a))return a;
    switch (car(a)){
      case "uq":
        if (lvl == 1)return evl(cadr(a), env);
        return list(car(a), evlqq(cadr(a), env, lvl-1));
      case "qq":
        return list(car(a), evlqq(cadr(a), env, lvl+1));
    }
    var arr = evlqq2(car(a), env, lvl);
    return car(arr)(cdr(arr), evlqq(cdr(a), env, lvl));
  }
  
  function evlqq2(a, env, lvl){
    if (atomp(a))return cons(cons, a);
    switch (car(a)){
      case "uq":
        if (lvl == 1)return cons(cons, evl(cadr(a), env));
        var ret = evlqq2(cadr(a), env, lvl-1);
        if (car(ret) == cons)return cons(car(ret), list("uq", cdr(ret)));
        return ret;
      case "uqs":
        if (lvl == 1)return cons(apd, evl(cadr(a), env));
    }
    return cons(cons, evlqq(a, env, lvl));
  }
  
  function evlif(a, env){
    if (nilp(a))return [];
    if (nilp(cdr(a)))return evl(car(a), env);
    if (!nilp(evl(car(a), env)))return evl(cadr(a), env);
    return evlif(cddr(a), env);
  }
  
  function fn(args, expr, env){
    return ["&fn", args, expr, env];
  }
  
  function mc(args, expr, env){
    return ["&mac", fn(args, expr, env)];
  }
  
  function evlwhile(cond, body, env){
    while (!nilp(evl(cond, env))){
      evl(cons("do", body), env);
    }
    return [];
  }
  
  function evlsetp(a, env){
    if (env === udef){
      if (a == "nil" || /^c[ad]+r$/.test(a))return "t";
      return [];
    }
    if (env[a] === udef)return evlsetp(a, env[0]);
    return "t";
  }
  
  function evlobj(a, env, o){
    if (o === udef)o = {};
    if (nilp(a))return o;
    o[disp(car(a))] = evl(cadr(a), env);
    return evlobj(cddr(a), env, o);
  }
  
  function evlarr(a, env, r){
    if (r === udef)r = [];
    if (nilp(a))return r;
    r.push(evl(car(a), env));
    return evlarr(cdr(a), env, r);
  }
  
  ////// Variables //////
  
  function get(a, env){
    if (env === udef){
      if (a == "nil")return [];
      if (/^c[ad]+r$/.test(a))return makeCxr(a);
      err(get, "Unknown variable a = $1 in env = $2", a, env);
    }
    if (env[a] === udef)return get(a, env[0]);
    return env[a];
  }
  
  function add(a, x, env){
    return env[a] = x;
  }
  
  function set(a, x, env){
    if (symp(a))return setsym(a, x, env, env);
    if (consp(a))return setf(evl(car(a), env), evlis(cdr(a), env), x);
    err(set, "Can't set a = $1 to x = $2", a, x);
  }
  
  function setsym(a, x, topenv, env){
    if (env === udef)return add(a, val, topenv);
    if (env[a] === udef)return setsym(a, val, topenv, env[0]);
    return add(a, x, env);
  }
  
  function setf(f, args, x){
    err(setf, "Can't set form a = $1 to x = $2", a, x);
  }
  
  /*var setfs = {};
  var defsetf = handler(setter(setfs));
  
  function setf(f, args, val){
    try {
      var fn = get(f, setfs);
    } catch (e){
      err(setf, "Unsetable function $1", f);
    }
    return apply(fn, tail(args, val));
  }
  
  function setcar(lis, val){
    lis[0] = val;
  }
  
  function setnth(n, lis, val){
    setcar(nthcdr(n, lis), val);
  }
  
  function setarr(arr, n, val){
    arr[1][Number(n)] = val;
  }
  
  var sets = {};
  var defset = handler(setter(sets));
  
  function setapply(obj, args, val){
    try {
      var fn = get(type(obj), sets);
    } catch (e){
      err(set, "Cannot set the apply of $1 to $2", obj, args);
    }
    return apply(fn, tail(cons(obj, args), val));
  }*/
  
  //// Handler creators ////
  
  function getter(env){
    return function (a){
      return get(a, env);
    };
  }
  
  function setter(env){
    return function (a, x){
      return set(a, x, env);
    };
  }
  
  function handler(fn){
    return function (a, x){
      if ($.objp(a)){
        for (var i in a){
          fn(i, a[i]);
        }
      } else {
        return fn(a, x);
      }
    };
  }
  
  ////// Global environment //////
  
  //// Variables ////
  
  var globals = {};
  var glob = handler(setter(globals));
  //var global = getter(globals);
  
  glob("t", "t");
  
  //// Specials ////
  
  function spec(){
    var a = arguments;
    for (var i = 0; i < a.length; i++){
      glob(a[i], ["&spec", a[i]]);
    }
  }
  
  spec("qt", "qq", "=", "var", "if", "fn",
       "mc", "evl", "while", "set?", "obj");
  
  //// Functions ////
  
  var jfn = handler(function (a, x){
    if ($.fnp(x))return glob(a, x);
    return glob(a, ["&jfn", x[0], x[1]]);
  });
  
  jfn({
    car: car,
    cdr: cdr,
    cons: cons,
    
    caar: caar,
    cdar: cdar,
    cadr: cadr,
    cddr: cddr,
    
    is: booler(is),
    type: type,
    do: doLisp,
    uniq: uniq,
    
    apply: apply,
    
    setf: setf,
    defset: defset,
    
    "*out*": function (a){return [];}
  });
  
  //// Booleans ////
  
  var bools = handler(function (name, func){
    return jsfunc(name, booler(func));
  });
  
  bools({
    "cons?": consp,
    "list?": listp,
    "pair?": pairp,
    "atom?": atomp,
    "nil?": nilp,
    "num?": nump,
    "str?": strp,
    "obj?": objp,
    "arr?": arrp,
    "fn?": fnp,
    "spec?": specp,
    "proc?": procp,
    "sym?": symp
  });
  
  ////// Standard output callback //////
  
  function out(a){
    return call(get("*out*", cvars()), a);
  }
  
  function setout(fn){
    var fn2 = function (a){
      var ret = fn(a);
      return (ret === udef)?[]:ret;
    };
    return glob("*out*", fn2);
  }
  
  ////// Processor //////
  
  function exec(a){
    a = prs(a);
    a = evl(a);
    a = disp(a);
    return a;
  }
  
  ////// Object exposure //////
  
  win.Lisp = {
    prs: prs,
    dyn: dyn,
    disp: disp,
    process: process,
    
    bool: bool,
    booler: booler,
    
    consp: consp,
    listp: listp,
    pairp: pairp,
    atomp: atomp,
    nilp: nilp,
    nump: nump,
    strp: strp,
    objp: objp,
    arrp: arrp,
    fnp: fnp,
    specp: specp,
    procp: procp,
    symp: symp,
    
    car: car,
    cdr: cdr,
    cons: cons,
    
    caar: caar,
    cdar: cdar,
    cadr: cadr,
    cddr: cddr,
    
    is: is,
    type: type,
    testfn: testfn,
    call: call,
    uniq: uniq,
    
    list: list,
    apd: apd,
    pair: pair,
    some: some,
    map: map,
    nth: nth,
    push: push,
    pop: pop,
    nrev: nrev,
    tail: tail,
    arr: arr,
    
    pairobj: pairobj,
    obj: obj,
    
    deflen: deflen,
    len: len,
    defpos: defpos,
    pos: pos,
    defrev: defrev,
    rev: rev,
    defmap: defmap,
    map: map,
    defsum: defsum,
    sum: sum,
    defiso: defiso,
    iso: iso,
    
    evl: evl,
    cvars: cvars,
    defapply: defapply,
    apply: apply,
    
    get: get,
    add: add,
    set: set,
    
    getter: getter,
    setter: setter,
    handler: handler,
    
    glob: glob,
    global: global,
    jsfunc: jsfunc,
    bools: bools,
    
    file: file,
    
    out: out,
    setout: setout,
    
    err: err
  };
  
  ////// Testing //////
  
  
  
})(window);
