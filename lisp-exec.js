/***** Lisp Interpreter Devel *****/

/* require tools >= 3.1 */
/* require lisp-tools */

(function (win, udf){
  ////// Import //////
  
  var typ = L.typ;
  var tag = L.tag;
  var rep = L.rep;
  var dat = L.dat;
  var mkdat = L.mkdat;
  
  var sy = L.sy;
  var nu = L.nu;
  var st = L.st;
  var jn = L.jn;
  var ob = L.ob;
  var ar = L.ar;
  
  var nilp = L.nilp;
  var lisp = L.lisp;
  var atmp = L.atmp;
  var consp = L.consp;
  var synp = L.synp;
  var symp = L.symp;
  var nump = L.nump;
  var objp = L.objp;
  var rgxp = L.rgxp;
  var udfp = L.udfp;
  var strp = L.strp;
  var arrp = L.arrp;
  var jnp = L.jnp;
  var fnp = L.fnp;
  var macp = L.macp;
  var smacp = L.smacp;
  var specp = L.specp;
  var prcp = L.prcp;
  
  var is = L.is;
  
  var sta = L.sta;
  
  var ofn = L.ofn;
  
  var tarr = L.tarr;
  var tobj = L.tobj;
  var jarr = L.jarr;
  var jnum = L.jnum;
  var prop = L.prop;
  
  var ref = L.ref;
  
  var map = L.map;
  var has = L.has;
  
  var rst = L.rst;
  var mid = L.mid;
  
  var app = L.app;
  
  var beg = L.beg;
  
  var car = L.car;
  var cdr = L.cdr;
  var cons = L.cons;
  var nil = L.nil;
  var scar = L.scar;
  var scdr = L.scdr;
  
  var caar = L.caar;
  var cadr = L.cadr;
  var cdar = L.cdar;
  var cddr = L.cddr;
  var cxr = L.cxr;
  
  var lis = L.lis;
  var nth = L.nth;
  
  var nrev = L.nrev;
  var revlis = L.revlis;
  var napp = L.napp;
  
  var sub = L.sub;
  
  var oput = L.oput;
  
  var sapl = L.sapl;
  
  var chku = L.chku;
  var chkb = L.chkb;
  var chrb = L.chrb;
  
  var psh = L.psh;
  var pop = L.pop;
  
  var err = L.err;
  
  var dol = L.dol;
  var gs = L.gs;
  
  ////// Lisp evaluator //////
  
  // moved here so envs = lis(glbs) doesn't make list(udf)
  var glbs = {};
  
  // envs always has glbs so that get(a) gets from glbs when 
  //   nothing is running
  var envs = lis(glbs);
  function evl(a, env){
    if (udfp(env))return evl1(a, car(envs));
    return sta(envs, env, function (){
      return evl1(a, env);
    });
  }
  
  function evl1(a, env){
    switch (typ(a)){
      case "sym":
        var x = get(dat(a), env);
        if (smacp(x))return evl1(apl(dat(x), nil()), env);
        return x;
      case "cons":
        var o = evl1(car(a), env);
        switch (typ(o)){
          case "mac": return evl1(apl(dat(o), cdr(a)), env);
          case "spec": return espc(dat(o), cdr(a), env);
        }
        return apl(o, elis(cdr(a), env));
    }
    return a;
  }
  
  function espc(f, a, env){
    switch (f){
      case "qt": return car(a);
      case "qq": return eqq(car(a), env);
      case "=": return eset(car(a), evl1(cadr(a), env), env);
      case "var": return evar(car(a), evl1(cadr(a), env), env);
      case "set?": return esetp(evl1(car(a), env), env);
      case "if": return eif(a, env);
      case "fn": return fn(car(a), cons(sy("do"), cdr(a)), env);
      case "mc": return mc(car(a), cons(sy("do"), cdr(a)), env);
      case "smc": return smc(cons(sy("do"), a), env);
      case "evl": return evl1(evl1(car(a), env), env);
      case "while": return ewhi(car(a), cdr(a), env);
      case "obj": return eobj(a, env);
      case "cat": return ecat(a, env);
      case "thr": return ethr(a, env);
      case "brk": return ebrk(a, env);
      case "cont": return econt(a, env);
      case "prot": return eprot(a, env);
    }
    err(espc, "Unknown spcial prcedure f = $1", f);
  }
  
  
  // input: a = a lisp fn, x = a lisp obj of args
  //          x doesn't have to be a list
  function apl(a, x){
    switch (typ(a)){
      case "fn": return afn(a, x);
      case "jn": return $.apl(dat(a), jarr(x));
      case "jn2": return ajn2(a, x);
      case "sym": 
      case "num": 
      case "str": 
      case "arr": 
      case "obj": 
      case "cons": return $.apl(ref, $.hea(jarr(x), a));
    }
    err(apl, "Can't apl a = $1 to x = $2", a, x);
  }
  
  sapl(apl);
  
  // input: a = a fn obj, x = a lisp obj of args
  function afn(a, x){
    var env = {0: rep(a, "env")};
    parenv(rep(a, "ag"), x, env);
    return evl(rep(a, "bd"), env);
  }
  
  // input: a = a jn2 obj, x = a lisp obj of args
  // in a jn2, .fn = a js fn, .ag = a lisp obj of syms
  function ajn2(a, x){
    return $.apl(rep(a, "fn"), parjn2(rep(a, "ag"), x));
  }
  
  // only called by afn
  // input: lisp objects a and b, env = a js obj to add resulting pairs to
  //          if b is nil, then a is set to nil,
  //          if b is udf, it is treated as unset
  // output: new pairs are added to env, env is returned
  function parenv(a, b, env){
    switch (typ(a)){
      case "cons": 
        if (is(car(a), sy("o"))){
          var r = udfp(b)?evl1(nth(nu("2"), a), env):b;
          oput(env, cadr(a), r);
        } else {
          parenv(car(a), udfp(b)?b:car(b), env);
          parenv(cdr(a), udfp(b)?b:cdr(b), env);
        }
        return env;
      case "sym":
        if (dat(a) === "nil")return env;
        // else do default
    }
    oput(env, a, udfp(b)?nil():b);
    return env;
  }
  
  // only called by ajn2
  // input: lisp objects a and b, r = a js arr to store results
  //          b should never be udf (no optional params, so udf isn't needed)
  //          whenever a new pair is created, only the value
  //            is pushed onto r
  //        note: no optional params, do it in js
  // output: values are added to r, r is returned
  function parjn2(a, b, r){
    if (udfp(r))r = []; // r should be a js arr
    switch (typ(a)){
      case "cons":
        parjn2(car(a), car(b), r);
        parjn2(cdr(a), cdr(b), r);
        return r;
      case "sym":
        if (dat(a) === "nil")return r;
        // else do default
    }
    r.push(b);
    return r;
  }
  
  // eval lisp list a for sending to apl as args
  function elis(a, env){
    var r = nil(); var x;
    while (consp(a)){
      // can't use nrevapp here because the spliced list might still
      //   be used
      x = car(a);
      if (is(car(x), sy("splice"))){
        r = revlis(evl1(cadr(x), env), r);
      } else {
        r = cons(evl1(x, env), r);
      }
      a = cdr(a);
    }
    return nrev(r);
  }
  
  /*function elis2(a, env){
    if (no(a))return [];
    if (is(caar(a), "splice"))return app(evl1(cadar(a), env), elis(cdr(a), env));
    return cons(evl1(car(a), env), elis(cdr(a), env));
  }
  
  function cadar(a){
    return car(cdr(car(a)));
  }*/
  
  var qgs = {};
  function eqq(a, env){
    if (env === udf)env = glbs;
    var prev = qgs;
    try {
      qgs = {};
      return eqq1(a, env, 1);
    } finally {
      qgs = prev;
    }
  }
  
  function eqq1(a, env, lvl){
    if (atmp(a))return a;
    switch (car(a)){
      case "uq":
        return euq(cadr(a), env, lvl-1).d;
      case "qq":
        return lis(car(a), eqq1(cadr(a), env, lvl+1));
      case "qgs":
        var t = cadr(a);
        if (!udfp(qgs[t]))return qgs[t];
        return qgs[t] = gs();
    }
    var r = eqq2(car(a), env, lvl);
    return r.f(r.d, eqq1(cdr(a), env, lvl));
  }
  
  function euq(a, env, lvl){
    if (lvl == 0)return {evp: true, d: evl1(a, env)};
    if (atmp(a))return {evp: false, d: lis("uq", a)};
    if (car(a) == "uq"){
      var r = euq(cadr(a), env, lvl-1);
      if (r.evp)return r;
      return {evp: false, d: lis("uq", r.d)};
    }
    return {evp: false, d: lis("uq", eqq1(a, env, lvl))};
  }
  
  function eqq2(a, env, lvl){
    if (atmp(a))return {f: cons, evp: false, d: a};
    switch (car(a)){
      case "uq":
        if (lvl == 1)return {f: cons, evp: true, d: evl1(cadr(a), env)};
        var r = eqq2(cadr(a), env, lvl-1);
        if (r.evp)return r;
        return {f: cons, evp: r.evp, d: lis("uq", r.d)};
      case "uqs":
        if (lvl == 1)return {f: app, evp: true, d: evl1(cadr(a), env)};
        return {f: cons, evp: false, d: eqq1(a, env, lvl-1)};
    }
    return {f: cons, evp: false, d: eqq1(a, env, lvl)};
  }
  
  // input: a = a lisp obj the var name, x = a lisp obj the value to be set to
  //        env = an env
  function evar(a, x, env){
    if (symp(a))return put(dat(a), x, env);
    err(evar, "a = $1 must be a symbol", a);
  }
  
  // for (= (nth 3 a) 3)
  // input: a = the lisp obj being set (ex. (nth 3 a) )
  //        x = the lisp obj a is being set to (ex. 3 )
  function eset(a, x, env){
    switch (typ(a)){
      case "sym":
        if (dat(a) === "nil")break;
        return set(dat(a), x, env);
      case "cons":
        var o = evl1(car(a), env);
        switch (typ(o)){
          case "mac": return eset(apl(dat(o), cdr(a)), x, env);
          case "spc": err(set, "Can't set a = $1 to x = $2", a, x);
        }
        return slis(o, elis(cdr(a), env), x);
    }
    err(eset, "Can't set a = $1 to x = $2", a, x);
  }
  
  // for (= (nth 0 '(1 2 3)) 5)
  //   or (= (#[1 2 3] 0) 5)
  // input: f = the car of the list being "set" (ex. the fn nth, or #[1 2 3] )
  //        a = the cdr of the list being "set"; the arguments to f; (ex. 0 )
  //        x = the lisp obj that the call is being set to (ex. 5 )
  function slis(f, a, x){
    switch (typ(f)){
      case "jn":
        if (dat(f) === car)return scar(car(a), x);
        if (dat(f) === cdr)return scdr(car(a), x);
        //if (f === nth)return L.set(cadr(a), car(a), x);
        break;
      case "arr": 
      case "obj": 
      case "cons": return L.set(f, car(a), x);
    }
    err(slis, "Can't set list with f = $1 and a = $2 to x = $3", f, a, x);
  }
  
  // input: a = a lisp obj the var name, env = an env
  function esetp(a, env){
    if (symp(a))return chkb(setp(dat(a), env));
    err(esetp, "a = $1 must be a symbol", a);
  }
  
  function eif(a, env){
    if (nilp(a))return nil();
    if (nilp(cdr(a)))return evl1(car(a), env);
    if (!nilp(evl1(car(a), env)))return evl1(cadr(a), env);
    return eif(cddr(a), env);
  }
  
  /*function eif2(a, env){
    while (true){
      if (nilp(a))return nil();
      if (nilp(cdr(a)))return evl1(car(a), env);
      if (!nilp(evl1(car(a), env)))return evl1(cadr(a), env);
      a = cddr(a);
    }
  }*/
  
  function fn(ag, bd, env){
    return {type: "fn", ag: ag, bd: bd, env: env};
  }
  
  function mc(ag, bd, env){
    return mkdat("mac", fn(ag, bd, env));
  }
  
  function smc(bd, env){
    return mkdat("smac", fn(nil(), bd, env));
  }
  
  function ewhi(cond, body, env){
    while (!nilp(evl1(cond, env))){
      try {
        evl1(cons(sy("do"), body), env);
      } catch (e){
        var t = typ(e);
        if (t === "break")break;
        if (t === "continue")continue;
        throw e;
      }
    }
    return nil();
  }
  
  function ebrk(a, env){
    throw {type: "break"};
  }
  
  function econt(a, env){
    throw {type: "continue"};
  }
  
  function eobj(a, env, o){
    if (udfp(o))o = {};
    if (nilp(a))return ob(o);
    o[prop(car(a))] = evl1(cadr(a), env);
    return eobj(cddr(a), env, o);
  }
  
  function ecat(a, env){
    var obj = evl1(car(a), env);
    try {
      return evl1(cons(sy("do"), cdr(a)), env);
    } catch (e){
      if (typ(e) === "throw" && is(rep(e, "obj"), obj)){
        return rep(e, "ret");
      }
      throw e;
    }
  }
  
  function ethr(a, env){
    throw {type: "throw", obj: evl1(car(a), env), ret: evl1(cadr(a), env)};
  }
  
  function eprot(a, env){
    try {
      return evl1(car(a), env);
    } finally {
      evl1(cons(sy("do"), cdr(a)), env);
    }
  }
  
  // see lisp-tools cal
  // input: a = a js str
  // calls the current fn called a in the stack
  function jcal(a){
    return apl(get(a), tlis(ar($.sli(arguments, 1))));
  }
  
  ////// Variables //////
  
  // env is a js obj where the own props of the obj is the current scope
  //   env[0] contains the scope above the current one
  //   and so on until env[0] === udf
  
  // input: a js str and an env obj
  //          if env === udf, then env = curr env (car(envs))
  function get(a, env){
    if (env === udf)env = car(envs);
    while (true){
      if (env === udf){
        if (a === "nil")return nil();
        if ($.has(/^c[ad]+r$/, a))return cxr($.mid(a));
        err(get, "Unknown variable a = $1", a);
      }
      if (env[a] !== udf)return env[a];
      env = env[0];
    }
  }
  
  // should not be called by outside code; use set instead
  // input: a = a js str, x = a lisp obj
  function put(a, x, env){
    return env[a] = x;
  }
  
  // for (= a 3)
  // input: a = a js str as the symbol being set
  //        x = the lisp obj as the item being set to
  function set(a, x, env){
    if (env === udf)env = car(envs);
    var topenv = env;
    while (true){
      if (env === udf)return put(a, x, topenv);
      if (env[a] !== udf)return put(a, x, env);
      env = env[0];
    }
  }
  
  /*function set(a, x, topenv, env){
    if (udfp(env))return put(a, x, topenv);
    if (udfp(env[a]))return set(a, x, topenv, env[0]);
    return put(a, x, env);
  }*/
  
  // input: a js str and an env obj
  // output: a js bool
  function setp(a, env){
    if (env === udf)env = car(envs);
    while (true){
      if (env === udf){
        return a === "nil" || $.has(/^c[ad]+r$/, a);
      }
      if (env[a] !== udf)return true;
      env = env[0];
    }
  }
  
  ////// Global environment //////
  
  // moved to top of file
  //var glbs = {};
  
  // input: a = a js str
  function glb(a){
    return get(a, glbs);
  }
  
  // input: a = a js str, b = a lisp obj
  var sglb = $.man2(function (a, b){
    return put(a, b, glbs);
  });
  
  sglb("t", sy("t"));
  sglb("$", ob($.cpyobj($)));
  
  //// Specials ////
  
  function sp(a){
    return mkdat("spec", a);
  }
  
  var spec = $.man1(function (a){
    return sglb(a, sp(a));
  });
  
  spec("qt", "qq", "=", "var", "if", "fn", "mc", "smc",
       "evl", "while", "set?", "obj", "cat", "thr",
       "brk", "cont", "prot");
  
  //// JS functions ////
  
  function jn2(ag, fn){
    return {type: "jn2", ag: prs(ag), fn: fn};
  }
  
  // set js function
  // input: a = a js str
  //        b = a js fn or a js arr
  //        if b is a js arr,
  //          b[0] = a str of lisp data as the args
  //          b[1] = a js fn
  var sjn = $.man2(function (a, b){
    if ($.fnp(b))return sglb(a, jn(b));
    return sglb(a, jn2(b[0], b[1]));
  });
  
  sjn({
    car: car,
    cdr: cdr,
    cons: cons,
    
    caar: caar,
    cdar: cdar,
    cadr: cadr,
    cddr: cddr,
    
    typ: typ,
    tag: tag,
    rep: rep,
    dat: dat,
    
    is: chrb(is),
    
    lis: lis,
    
    do: dol,
    gs: gs,
    
    apl: apl,
    
    "*out*": function (a){return nil();}
  });
  
  ofn(function (a){
    return cal(get("*out*"), a);
  });
  
  //// Booleans ////
  
  var bol = $.man2(function (a, b){
    sjn(a, chrb(b));
  });
  
  bol({
    "lis?": lisp,
    "atm?": atmp,
    "nil?": nilp,
    "cons?": consp,
    "syn?": synp,
    "sym?": symp,
    "num?": nump,
    "obj?": objp,
    "rgx?": rgxp,
    "str?": strp,
    "arr?": arrp,
    "fn?": fnp,
    "jn?": jnp,
    "mac?": macp,
    "spec?": specp,
    "prc?": prcp
  });
  
  ////// Object exposure //////
  
  $.att({
    envs: envs,
    evl: evl,
    evl1: evl1,
    // apl is already sapl'd
    
    jcal: jcal,
    
    xget: get,
    xput: put,
    xset: set,
    xsetp: setp,
    
    glbs: glbs,
    glb: glb,
    sglb: sglb,
    sjn: sjn,
    bol: bol
  }, L);
  
  ////// Testing //////
  
  
  
})(window);
