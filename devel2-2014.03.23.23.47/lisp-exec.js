/***** Lisp Interpreter Devel *****/

/* require tools >= 3.1 */
/* require lisp-tools */
/* require lisp-parse */ // evls(a) runs prs(a)

(function (win, udf){
  ////// Import //////
  
  var typ = L.typ;
  var tg = L.tg;
  var rp = L.rp;
  var s = L.s;
  
  var nilp = L.nilp;
  var lisp = L.lisp;
  var atmp = L.atmp;
  var nump = L.nump;
  var symp = L.symp;
  var objp = L.objp;
  var rgxp = L.rgxp;
  var udfp = L.udfp;
  var tgp = L.tgp;
  var strp = L.strp;
  var arrp = L.arrp;
  var fnp = L.fnp;
  var macp = L.macp;
  var spcp = L.spcp;
  var prcp = L.prcp;
  
  var is = L.is;
  
  var dyn = L.dyn;
  
  var dsp = L.dsp;
  var dsj = L.dsj;
  
  var ofn = L.ofn;
  
  var tarr = L.tarr;
  var tobj = L.tobj;
  var jarr = L.jarr;
  
  var has = L.has;
  
  var rst = L.rst;
  var mid = L.mid;
  
  var app = L.app;
  
  var beg = L.beg;
  
  var car = L.car;
  var cdr = L.cdr;
  var cons = L.cons;
  
  var caar = L.caar;
  var cadr = L.cadr;
  var cdar = L.cdar;
  var cddr = L.cddr;
  var cxr = L.cxr;
  
  var lis = L.lis;
  var nth = L.nth;
  
  var sub = L.sub;
  
  var scal = L.scal;
  
  var chku = L.chku;
  var chkb = L.chkb;
  var chrb = L.chrb;
  
  var prs = L.prs;
  
  var err = L.err;
  
  var dol = L.dol;
  var gs = L.gs;
  
  ////// Lisp evaluator //////
  
  var envs = [];
  function evl(a, env){
    if (udfp(env))env = glbs;
    return dyn(envs, env, function (){
      return evl2(a, env);
    });
  }
  
  function evl2(a, env){
    if (atmp(a)){
      if (symp(a))return get(a, env);
      return a;
    }
    var o = evl(car(a), env);
    if (spcp(o)){
      switch (typ(o)){
        case "mac": return evl(apl(rp(o), cdr(a)), env);
        case "spc": return espc(rp(o), cdr(a), env);
      }
    }
    return apl(o, elis(cdr(a), env));
  }
  
  function espc(f, a, env){
    switch (f){
      case "qt": return car(a);
      case "qq": return eqq(car(a), env);
      case "=": return set(car(a), evl(cadr(a), env), env);
      case "var": return put(car(a), evl(cadr(a), env), env);
      case "if": return eif(a, env);
      case "fn": return fn(car(a), cons("do", cdr(a)), env);
      case "nfn": return nfn(cons("do", a), env);
      case "mc": return mc(car(a), cons("do", cdr(a)), env);
      case "evl": return evl(evl(car(a), env), env);
      case "whi": return ewhi(car(a), cdr(a), env);
      case "set?": return esetp(evl(car(a), env), env);
      case "obj": return eobj(a, env);
    }
    err(espc, "Unknown spcial prcedure f = $1", f);
  }
  
  function apl(a, x){
    var tp = typ(a);
    switch (tp){
      case "fn": return afn(a, x);
      case "nfn": return anfn(a, x);
      case "jn": return $.apl(a, jarr(x));
      case "jn2": return ajn2(a, x);
      case "str": return astr(a, x);
      case "arr": return chku(rp(a)[car(x)]);
      case "obj": return aobj(a, x);
      case "lis": return nth(car(x), a);
    }
    err(apl, "Can't apl a = $1 to x = $2", a, x);
  }
  
  function par(a, b){
    if (nilp(a))return [];
    if (atmp(a))return lis(cons(a, b));
    if (is(car(a), "o"))return lis(cons(cadr(a), nilp(b)?nth("2", a):b));
    return app(par(car(a), car(b)), par(cdr(a), cdr(b)));
  }
  
  function afn(a, x){
    return evl(rp(a, "1"), tobj(par(rp(a, "0"), x), {0: rp(a, "2")}));
  }
  
  function anfn(a, x){
    return evl(rp(a, "0"), {0: rp(a, "1"), "-1": x});
  }
  
  function ajn2(a, x){
    return $.apl(rp(a, "1"), jarr(map(cdr, par(rp(a, "0"), x))));
  }
  
  function astr(a, x){
    if (nilp(cdr(x))){
      var str = chku(rp(a)[car(x)]);
      return nilp(s)?[]:s(str);
    }
    return s($.sli(rp(a), car(x), cadr(x)));
  }
  
  function aobj(a, x){
    var k = car(x);
    if (symp(k) || nump(k))return chku(a[k]);
    if (strp(k))return chku(a[rp(k)]);
    err(aobj, "Invalid object property name car(x) = $1", k);
  }
  
  function elis(a, env){
    if (nilp(a))return [];
    return cons(evl(car(a), env), elis(cdr(a), env));
  }
  
  var qgs = {};
  function eqq(a, env, lvl){
    if (udfp(lvl)){
      lvl = 1;
      qgs = {};
    }
    if (atmp(a))return a;
    switch (car(a)){
      case "uq":
        if (lvl == 1)return evl(cadr(a), env);
        return lis(car(a), eqq(cadr(a), env, lvl-1));
      case "qq":
        return lis(car(a), eqq(cadr(a), env, lvl+1));
      case "qgs":
        var t = cadr(a);
        if (!udfp(qgs[t]))return qgs[t];
        return qgs[t] = gs();
    }
    var r = eqq2(car(a), env, lvl);
    return r[0](r[1], eqq(cdr(a), env, lvl));
  }
  
  function eqq2(a, env, lvl){
    if (atmp(a))return cons(cons, a);
    switch (car(a)){
      case "uq":
        if (lvl == 1)return [cons, evl(cadr(a), env)];
        var ret = eqq2(cadr(a), env, lvl-1);
        if (car(ret) == cons)return [car(ret), lis("uq", cdr(ret))];
        return ret;
      case "uqs":
        if (lvl == 1)return [app, evl(cadr(a), env)];
    }
    return [cons, eqq(a, env, lvl)];
  }
  
  function eif(a, env){
    if (nilp(a))return [];
    if (nilp(cdr(a)))return evl(car(a), env);
    if (!nilp(evl(car(a), env)))return evl(cadr(a), env);
    return eif(cddr(a), env);
  }
  
  function fn(args, expr, env){
    return tg("fn", args, expr, env);
  }
  
  function nfn(expr, env){
    return tg("nfn", expr, env);
  }
  
  function mc(args, expr, env){
    return tg("mac", fn(args, expr, env));
  }
  
  function ewhi(cond, body, env){
    while (!nilp(evl(cond, env))){
      evl(cons("do", body), env);
    }
    return [];
  }
  
  function esetp(a, env){
    if (udfp(env)){
      if (is(a, "nil") || has(/^c[ad]+r$/, a))return "t";
      return [];
    }
    if (udfp(env[a]))return esetp(a, env[0]);
    return "t";
  }
  
  function eobj(a, env, o){
    if (udfp(o))o = {};
    if (nilp(a))return o;
    o[eprop(car(a))] = evl(cadr(a), env);
    return eobj(cddr(a), env, o);
  }
  
  function eprop(a){
    if (symp(a) || nump(a))return a;
    if (strp(a))return a[1];
    err(eprop, "Invalid object property name a = $1", a);
  }
  
  function cal(a){
    return apl(a, $.apl(lis, $.sli(arguments, 1)));
  }
  
  scal(cal);
  
  ////// Execute //////
  
  // eval string
  function evls(a){
    return dsj(evl(prs(a)));
  }
  
  ////// Variables //////
  
  function get(a, env){
    if (a === "%")return get(a + "1", env);
    if (a[0] === "%"){
      var args = geta(env);
      if (udfp(args))err(get, "Unknown variable a = $1", a);
      return nth(sub(rst(a), "1"), args);
    }
    if (env === udf){
      if (a === "nil")return [];
      if (has(/^c[ad]+r$/, a))return cxr(mid(a));
      err(get, "Unknown variable a = $1", a);
    }
    if (env[a] === udf)return get(a, env[0]);
    return env[a];
  }
  
  function geta(env){
    if (udfp(env))return udf;
    if (udfp(env[-1]))return geta(env[0]);
    return env[-1];
  }
  
  function put(a, x, env){
    return env[a] = x;
  }
  
  function set(a, x, env){
    if (symp(a))return ssym(a, x, env, env);
    if (lisp(a))return slis(evl(car(a), env), elis(cdr(a), env), x);
    err(set, "Can't set a = $1 to x = $2", a, x);
  }
  
  function ssym(a, x, topenv, env){
    if (udfp(env))return put(a, x, topenv);
    if (udfp(env[a]))return ssym(a, x, topenv, env[0]);
    return put(a, x, env);
  }
  
  function slis(f, a, x){
    if (fnp(f)){
      if (f === car)return car(a)[0] = x;
      if (f === cdr)return car(a)[1] = x;
      if (f === nth)return L.set(cadr(a), car(a), x);
      err(slis, "Can't set f = $1 of a = $2 to x = $3", f, a, x);
    }
    if (arrp(f))return rp(f)[car(a)] = x;
    if (objp(f))return f[car(a)] = x;
    if (lisp(f))return L.set(f, car(a), x);
    err(slis, "Can't set list with f = $1 and a = $2 to x = $3", f, a, x);
  }
  
  ////// Global environment //////
  
  var glbs = {};
  
  /*var glb = $.man2(a, b){
    put(a, b, glbs);
  }*/
  
  var glb = $.man2(function (a, b){
    put(a, b, glbs);
  });
  
  glb("t", "t");
  
  //// Specials ////
  
  var spc = $.man1(function (a){
    glb(a, tg("spc", a));
  });
  
  spc("qt", "qq", "=", "var", "if", "fn", "nfn", "mc",
      "evl", "whi", "set?", "obj", "arr");
  
  //// JS functions ////
  
  var jn = $.man2(function (a, b){
    if ($.fnp(b))glb(a, b);
    else glb(a, tg("jn2", b[0], b[1]));
  });
  
  jn({
    car: car,
    cdr: cdr,
    cons: cons,
    
    caar: caar,
    cdar: cdar,
    cadr: cadr,
    cddr: cddr,
    
    typ: typ,
    tg: tg,
    rp: rp,
    
    is: chrb(is),
    
    lis: lis,
    
    do: dol,
    gs: gs,
    
    apl: apl,
    
    "*out*": function (a){return [];}
  });
  
  ofn(function (a){
    return cal(get("*out*", car(envs)), a);
  });
  
  //// Booleans ////
  
  var bol = $.man2(function (a, b){
    jn(a, chrb(b));
  });
  
  bol({
    "lis?": lisp,
    "atm?": atmp,
    "nil?": nilp,
    "num?": nump,
    "obj?": objp,
    "rgx?": rgxp,
    "tg?": tgp,
    "str?": strp,
    "arr?": arrp,
    "fn?": fnp,
    "mac?": macp,
    "spc?": spcp,
    "prc?": prcp,
    "sym?": symp
  });
  
  ////// Object exposure //////
  
  $.att({
    envs: envs,
    evl: evl,
    apl: apl,
    cal: cal,
    evls: evls,
    
    glbs: glbs,
    glb: glb,
    jn: jn,
    bol: bol
  }, L);
  
  ////// Testing //////
  
  
  
})(window);
