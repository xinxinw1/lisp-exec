/***** Lisp Interpreter Devel *****/

/* requires tools >= 3.0 */
/* require lisp-parse */
/* require lisp-disp */

(function (win, udef){
  ////// Import //////
  
  var type = Lisp.type;
  
  var lisp = Lisp.lisp;
  var atomp = Lisp.atomp;
  var nilp = Lisp.nilp;
  var nump = Lisp.nump;
  var strp = Lisp.strp;
  var objp = Lisp.objp;
  var arrp = Lisp.arrp;
  var rgxp = Lisp.rgxp;
  var fnp = Lisp.fnp;
  var specp = Lisp.specp;
  var procp = Lisp.procp;
  var symp = Lisp.symp;
  
  var car = Lisp.car;
  var cdr = Lisp.cdr;
  var cons = Lisp.cons;
  
  var caar = Lisp.caar;
  var cadr = Lisp.cadr;
  var cdar = Lisp.cdar;
  var cddr = Lisp.cddr;
  var mkcxr = Lisp.mkcxr;
  
  var is = Lisp.is;
  
  var disp = Lisp.disp;
  
  var list = Lisp.list;
  var apd = Lisp.apd;
  var pair = Lisp.pair;
  var nth = Lisp.nth;
  
  var booler = Lisp.booler;
  
  var prs = Lisp.prs;
  
  var err = Lisp.err;
  
  var doLisp = Lisp.do;
  
  ////// Processing functions //////
  
  function rembds(a){
    return $.slc(a, 1, $.len(a)-1);
  }
  
  ////// Lisp evaluator //////
  
  function evl(a, env){
    if (env === udef)env = globals;
    if (atomp(a)){
      if (symp(a))return get(a, env);
      return a;
    }
    var o = evl(car(a), env);
    if (specp(o)){
      switch (o[0]){
        case "&mac": return evl(apply(o[1], cdr(a)), env);
        case "&spec": return evlspec(o[1], cdr(a), env);
      }
    }
    return apply(o, evlis(cdr(a), env));
  }
  
  function evlspec(f, a, env){
    switch (f){
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
    err(evlspec, "Unknown special procedure f = $1", f);
  }
  
  function apply(a, x){
    var tp = type(a);
    switch (tp){
      case "fn": return evl(a[2], lis2obj(pair(a[1], x), {0: a[3]}));
      case "jfn": return $.apply(a, lis2arr(x));
      case "jfn2": return $.apply(a[2], lis2arr(map(cdr, pair(a[1], x))));
      case "str": return applystr(a, x);
      case "arr": return chkudef(a[1][car(x)]);
      case "obj": return applyobj(a, x);
      case "cons": return nth(car(x), a);
    }
    err(apply, "Can't apply a = $1 to x = $2", a, x);
  }
  
  function applystr(a, x){
    if (nilp(cdr(x))){
      var s = chkudef(a[1][car(x)]);
      return nilp(s)?[]:["&str", s];
    }
    return ["&str", $.slc(a[1], car(x), cadr(x))];
  }
  
  function applyobj(a, x){
    var k = car(x);
    if (symp(k) || nump(k))return chkudef(a[k]);
    if (strp(k))return chkudef(a[k[1]]);
    err(applyobj, "Invalid object property name car(x) = $1", k);
  }
  
  function chkudef(a){
    return (a === udef)?[]:a;
  }
  
  function evlis(a, env){
    if (nilp(a))return [];
    return cons(evl(car(a), env), evlis(cdr(a), env));
  }
  
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
    o[evlprop(car(a))] = evl(cadr(a), env);
    return evlobj(cddr(a), env, o);
  }
  
  function evlprop(a){
    if (symp(a) || nump(a))return a;
    if (strp(a))return a[1];
    err(evlprop, "Invalid object property name a = $1", a);
  }
  
  function evlarr(a, env){
    return ["&arr", lis2arr(evlis(a, env))];
  }
  
  function lis2arr(a, r){
    if (r === udef)r = [];
    if (nilp(a))return r;
    r.push(car(a));
    return lis2arr(cdr(a), r);
  }
  
  function lis2obj(a, o){
    if (o === udef)o = {};
    if (nilp(a))return o;
    o[evlprop(caar(a))] = cdar(a);
    return lis2obj(cdr(a), o);
  }
  
  ////// Execute //////
  
  function exec(a){
    return disp(evl(prs(a)));
  }
  
  ////// Variables //////
  
  function get(a, env){
    if (env === udef){
      if (a == "nil")return [];
      if (/^c[ad]+r$/.test(a))return mkcxr(a);
      err(get, "Unknown variable a = $1", a);
    }
    if (env[a] === udef)return get(a, env[0]);
    return env[a];
  }
  
  function add(a, x, env){
    return env[a] = x;
  }
  
  function set(a, x, env){
    if (symp(a))return setsym(a, x, env, env);
    if (lisp(a))return setlis(evl(car(a), env), evlis(cdr(a), env), x);
    err(set, "Can't set a = $1 to x = $2", a, x);
  }
  
  function setsym(a, x, topenv, env){
    if (env === udef)return add(a, x, topenv);
    if (env[a] === udef)return setsym(a, x, topenv, env[0]);
    return add(a, x, env);
  }
  
  function setlis(f, a, x){
    if (fnp(f)){
      if (f === car)return car(a)[0] = x;
      if (f === cdr)return car(a)[1] = x;
      if (f === nth)return setnth(car(a), cadr(a), x);
      err(setlis, "Can't set f = $1 of a = $2 to x = $3", f, a, x);
    }
    if (arrp(f))return f[1][car(a)] = x;
    if (objp(f))return f[car(a)] = x;
    if (lisp(f))return setnth(car(a), f, x);
    err(setlis, "Can't set list with f = $1 and a = $2 to x = $3", f, a, x);
  }
  
  function setnth(n, a, x){
    if (n == 0)return a[0] = x;
    return setnth(n-1, cdr(a), x);
  }
  
  ////// Global environment //////
  
  var globals = {};
  
  function glob(a, x){
    add(a, x, globals);
  }
  
  glob("t", "t");
  
  //// Handler ////
  
  function setter(f){
    return function (a, x){
      if ($.objp(a)){
        for (var i in a){
          f(i, a[i]);
        }
      } else f(a, x);
    };
  }
  
  //// Specials ////
  
  function spec(){
    var a = arguments;
    for (var i = 0; i < a.length; i++){
      glob(a[i], ["&spec", a[i]]);
    }
  }
  
  spec("qt", "qq", "=", "var", "if", "fn", "mc",
       "evl", "while", "set?", "obj", "arr");
  
  //// JS functions ////
  
  var jsfn = setter(function (a, x){
    if ($.fnp(x))glob(a, x);
    else glob(a, ["&jfn", x[0], x[1]]);
  });
  
  jsfn({
    car: car,
    cdr: cdr,
    cons: cons,
    
    caar: caar,
    cdar: cdar,
    cadr: cadr,
    cddr: cddr,
    
    type: type,
    
    list: list,
    is: booler(is),
    do: doLisp,
    
    apply: apply
  });
  
  //// Booleans ////
  
  function bool(a){
    for (var i in a){
      jsfn(i, booler(a[i]));
    }
  }
  
  bool({
    "lis?": lisp,
    "atom?": atomp,
    "nil?": nilp,
    "num?": nump,
    "str?": strp,
    "obj?": objp,
    "arr?": arrp,
    "rgx?": rgxp,
    "fn?": fnp,
    "spec?": specp,
    "proc?": procp,
    "sym?": symp
  });
  
  ////// Object exposure //////
  
  $.apd({
    evl: evl,
    exec: exec
  }, Lisp);
  
  ////// Testing //////
  
  
  
})(window);
