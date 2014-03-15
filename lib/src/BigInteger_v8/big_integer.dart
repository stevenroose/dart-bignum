part of bignum;

/*
 * Copyright (c) 2003-2005  Tom Wu
 * Copyright (c) 2012 Adam Singer (adam@solvr.io)
 * All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS-IS" AND WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS, IMPLIED OR OTHERWISE, INCLUDING WITHOUT LIMITATION, ANY
 * WARRANTY OF MERCHANTABILITY OR FITNESS FOR A PARTICULAR PURPOSE.
 *
 * IN NO EVENT SHALL TOM WU BE LIABLE FOR ANY SPECIAL, INCIDENTAL,
 * INDIRECT OR CONSEQUENTIAL DAMAGES OF ANY KIND, OR ANY DAMAGES WHATSOEVER
 * RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER OR NOT ADVISED OF
 * THE POSSIBILITY OF DAMAGE, AND ON ANY THEORY OF LIABILITY, ARISING OUT
 * OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 * In addition, the following condition applies:
 *
 * All redistributions must retain an intact copy of this copyright notice
 * and disclaimer.
 */

// TODO: reduction algorithms need to be implemented via an interface


/**
 * Modular reduction using "classic" algorithm on [BigInteger]
 */
class Classic {

  BigInteger m;

  Classic(this.m);
  convert(x) {
    if(x.sxxxxx < 0 || x.compareTo(this.m) >= 0) { return x.mod(this.m);
    } else { return x;
    }
  }
  revert(x) { return x; }
  reduce(x) { return x._divRemTo(this.m,null,x).r; }
  mulTo(x,y,r) { r = x._multiplyTo(y,r); return this.reduce(r); }
  sqrTo(x,r) { r = x._squareTo(r); return this.reduce(r); }
}

/**
 * Montgomery reduction on [BigInteger]
 */
class Montgomery {

  BigInteger m;

  var mp;
  var mpl;
  var mph;
  var um;
  var mt2;

  /**
   * Montgomery reduction
   */
  Montgomery(this.m) {
  this.mp = m._invDigit();
  this.mpl = this.mp&0x7fff;
  this.mph = this.mp>>15;
  this.um = (1<<(BigInteger.BI_DB-15))-1;
  this.mt2 = 2*m.txxxxx;
  }

  /**
   * xR mod m
   */
  BigInteger convert(BigInteger x) {
    var r = BigInteger._nbi();
    r = x.abs()._dlShiftTo(this.m.txxxxx,r);
    r = r._divRemTo(this.m,null,r).r;
    if(x.sxxxxx < 0 && r.compareTo(BigInteger.ZERO) > 0) r = this.m._subTo(r,r);
    return r;
  }

  /**
   * x/R mod m
   */
  BigInteger revert(BigInteger x) {
    var r = BigInteger._nbi();
    r = x.copy();
    return this.reduce(r);
  }

  /**
   * x = x/R mod m (HAC 14.32)
   */
  BigInteger reduce(x) {
    var x_array = x.arrayxxxxx;
    var x_t = x.txxxxx;
    while(x_t <= this.mt2) { // pad x so am has enough room later
      x_array[x_t++] = 0;
    }

    for(var i = 0; i < this.m.txxxxx; ++i) {
      // faster way of calculating u0 = x[i]*mp mod DV
      var j = x_array[i]&0x7fff;
      var u0 = (j*this.mpl+(((j*this.mph+(x_array[i]>>15)*this.mpl)&this.um)<<15))&BigInteger.BI_DM;
      // use am to combine the multiply-shift-add into one call
      j = i+this.m.txxxxx;
      x_array[j] += this.m.amxxxxx(0,u0,x,i,0,this.m.txxxxx,this.m.arrayxxxxx);
      // propagate carry
      while(x_array[j] >= BigInteger.BI_DV) {
        x_array[j] -= BigInteger.BI_DV;
        x_array[++j]++;
      }
    }
    x_t = BigInteger.clamp(x_t, x_array, x.sxxxxx);
    x.drShiftTo(this.m.txxxxx,x);//TODO <- here was I
    if(x.compareTo(this.m) >= 0) {
      x.subTo(this.m,x);
    }
  }

  /**
   * r = "x^2/R mod m"; x != r
   */
  sqrTo(x,r) {
    x.squareTo(r);
    this.reduce(r);
  }

  /**
   * r = "xy/R mod m"; x,y != r
   */
  mulTo(x,y,r) {
    x.multiplyTo(y,r);
    this.reduce(r);
  }
}

/**
 * Barrett modular reduction
 */
class Barrett {

  BigInteger m;
  BigInteger r2;
  BigInteger q3;
  var mu;

  /**
   * Barrett modular reduction
   */
  Barrett(this.m) {
    // setup Barrett
    this.r2 = BigInteger._nbi();
    this.q3 = BigInteger._nbi();
    BigInteger.ONE.dlShiftTo(2*m.txxxxx,this.r2);
    this.mu = this.r2.divide(m);

  }

  BigInteger convert(BigInteger x) {
    if(x.sxxxxx < 0 || x.txxxxx > 2*this.m.txxxxx)  {
      return x.mod(this.m);
    } else if(x.compareTo(this.m) < 0) {
      return x;
    } else {
      var r = BigInteger._nbi();
      x.copyTo(r);
      this.reduce(r);
      return r;
    }
  }

  revert(x) {
    return x;
  }

  /**
   * x = x mod m (HAC 14.42)
   */
  void reduce(BigInteger x) {
    x.drShiftTo(this.m.txxxxx - 1, this.r2);
    if(x.txxxxx > this.m.txxxxx+1) {
      x.txxxxx = this.m.txxxxx+1;
      x.clamp();
    }

    this.mu.multiplyUpperTo(this.r2, this.m.txxxxx + 1, this.q3);
    this.m.multiplyLowerTo(this.q3, this.m.txxxxx + 1, this.r2);
    while(x.compareTo(this.r2) < 0) {
      x.dAddOffset(1,this.m.txxxxx+1);
    }

    x.subTo(this.r2,x);

    while(x.compareTo(this.m) >= 0) {
      x.subTo(this.m,x);
    }
  }

  /**
   * r = x^2 mod m; x != r
   */
  sqrTo(x,r) { x.squareTo(r); this.reduce(r); }

  /**
   * r = x*y mod m; x,y != r
   */
  mulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }

}

class NullExp {
  NullExp();
  convert(x) { return x; }
  revert(x) { return x; }
  mulTo(x,y,r) { x.multiplyTo(y,r); }
  sqrTo(x,r) { x.squareTo(r); }
}


// typedef AmplitudeModulation
/**
 * This class wraps a Dart List and provides a JS-like behaviour.
 * i.e. Storing an out-of-bounds element grows the list automatically.
 */
class JSArray<T> {
  operator [](var index) {
    return data[index];
  }

  operator []=(var index, var value) {
    if (index > data.length - 1) {
      data.length = index + 1;
    }
    return data[index] = value;
  }

  List<T> data = new List<T>();
  
  @override
  String toString() => data.toString();
}

class _QuotRem {
  final BigInteger q;
  final BigInteger r;
  _QuotRem(this.q, this.r);
}

/**
 * Basic dart [BigInteger] class. Implementation works across
 * dart and dart2js.
 */
class BigInteger {
  /** Bits per digit */
  static int dbits;
  static int BI_DB;
  static int BI_DM;
  static int BI_DV;

  static int BI_FP;
  static int BI_FV;
  static int BI_F1;
  static int BI_F2;

  /** Create a new [BigInteger] */
  static BigInteger _nbi() => 
      new BigInteger._internal(_initArray, _am3, null, null);
  /** return [BigInteger] initialized to [i] */
  static BigInteger nbv(int i) {
    var r = _nbi();
    r.fromInt(i);
    return r;
  }

  static BigInteger get ZERO => nbv(0);
  static BigInteger get ONE => nbv(1);
  static BigInteger get TWO => nbv(2);
  static BigInteger get THREE => nbv(3);

  // Basic dart BN library - subset useful for RSA encryption.

  /** [List] of low primes */
  static final List<int> _lowprimes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509];
  static final int _lplim = (1 << 26) ~/ _lowprimes[_lowprimes.length-1];

  /** JavaScript engine analysis */
  // commented because unused
  //static final int canary = 0xdeadbeefcafe;
  //static final bool _j_lm = ((canary & 0xffffff) == 0xefcafe);
  
  static final BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
  static Map BI_RC;

  /**
   * Internal data structure of [BigInteger] implementation.
   */
  final JSArray<int> arrayxxxxx;
  static JSArray<int> get _initArray => new JSArray<int>();

  final Function amxxxxx;

  final int txxxxx;
  final int sxxxxx;

  /**
   * Constructor of [BigInteger]
   *
   * Constructor can be called in mutiple ways
   *
   * 1) Passing byte array [List]
   *    var x = new BigInteger([0x5]);
   *    x.toString() == "5";
   *
   * 2) Passing [int]
   *    int i = 5;
   *    var x = new BigInteger(i);
   *    x.toString() == "5";
   *
   * 3) Passing [num]
   *    num i = 5;
   *    var x = new BigInteger(i);
   *    x.toString() == "5";
   *
   * 4) Passing [double]
   *    double i = 5.0;
   *    var x = new BigInteger(i);
   *    x.toString() == "5";
   *
   * 5) Passing [String] with optional base [int]
   *    String s = "5";
   *    var x = new BigInteger(s);
   *    x.toString() == "5";
   *
   *    String s = "beef";
   *    var x = new BigInteger(s);
   *    x.toString() == "beef";
   */
  factory BigInteger([a,b,c]) { // TODO: create mutiple constructors, instead of constructing based on the dynamimc type
    if (a == null)
      throw new ArgumentError("The first argument must not be null.");
    if (a is int) {
      // this.fromNumber(a,b,c);
      // NOTE: the fromNumber implementation trys to exploit js numbers
      return new BigInteger.fromString(a.toString(), 10);
    } else if (a is num) {
      return new BigInteger.fromString(a.toInt().toString(), 10);
    } else if (b == null && a is! String) {
      return new BigInteger.fromString(a, 256);
    } else {
      return new BigInteger.fromString(a, b);
    }
  }
  
  const BigInteger._internal(this.arrayxxxxx, this.amxxxxx, this.txxxxx, this.sxxxxx);
  // shorter
  static BigInteger _newInst(array, am, t, s) => 
      new BigInteger._internal(array, am, t, s);

  factory BigInteger.fromBytes( int signum, List<int> magnitude ) {
    if( signum==0 ) throw new ArgumentError("Argument signum must not be zero");
    // Add a leading 0 if most significant bit set (otherwise, the magnitude
    // is interpreted as negative and this constructor fails)
    if( (magnitude[0] & 0x80) != 0 ) {
      magnitude = new List<int>(1+magnitude.length)
          ..[0] = 0
          ..setRange(1, 1+magnitude.length, magnitude);
    }
    var self = new BigInteger(magnitude);
    return (signum<0) ? -self : self;
  }
  
  static var _default_am = _am3;

  /**
   * Alternately, set max digit bits to 28 since some
   * browsers slow down when dealing with 32-bit numbers.
   */
  static _am3(i,x,w,j,c,n,array) {
    var this_array = array;
    var w_array    = w.arrayxxxxx;
    var xl = x.toInt() & 0x3fff, xh = x.toInt() >> 14;
    while(--n >= 0) {
      var l = this_array[i]&0x3fff;
      var h = this_array[i++]>>14;
      var m = xh*l+h*xl;
      l = xl*l+((m&0x3fff)<<14)+w_array[j]+c;
      c = (l>>28)+(m>>14)+xh*h;
      w_array[j++] = l&0xfffffff;
    }
    return c;
  }

  static _am4(i,x,w,j,c,n,array) {
    var this_array = array;
    var w_array    = w.arrayxxxxx;
    var xl = x.toInt()&0x1fff, xh = x.toInt()>>13;
    while(--n >= 0) {
      var l = this_array[i]&0x1fff;
      var h = this_array[i++]>>13;
      var m = xh*l+h*xl;
      l = xl*l+((m&0x1fff)<<13)+w_array[j]+c;
      c = (l>>26)+(m>>13)+xh*h;
      w_array[j++] = l&0x3ffffff;
    }
    return c;
  }
  
  static _setup(am) {
    // Setup all the global scope js code here
    _setupDigitConversions();
    //am3 works better on x64, while am3 is faster on 32-bit platforms.
    //_setupEngine(_am4, 26)
    _setupEngine(am, 28);
  }

  /**
   * am3/28 is best for SM, Rhino, but am4/26 is best for v8.
   * Kestrel (Opera 9.5) gets its best result with am4/26.
   * IE7 does 9% better with am3/28 than with am4/26.
   * Firefox (SM) gets 10% faster with am3/28 than with am4/26.
   */
  static _setupEngine(Function fn, int bits) {
    dbits = bits;

    BI_DB = dbits;
    BI_DM = ((1<<dbits)-1);
    BI_DV = (1<<dbits);

    BI_FP = 52;
    BI_FV = Mathx.pow(2,BI_FP);
    BI_F1 = BI_FP-dbits;
    BI_F2 = 2*dbits-BI_FP;
  }

  /** Digit conversions */
  static _setupDigitConversions() {
    // Digit conversions
    //BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
    BI_RC = new Map();
    int rr, vv;
    rr = "0".codeUnitAt(0);
    for(vv = 0; vv <= 9; ++vv) BI_RC[rr++] = vv;
    rr = "a".codeUnitAt(0);
    for(vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;
    rr = "A".codeUnitAt(0);
    for(vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;
  }

  static _int2char(n) {
    return BI_RM[n];
  }

  static _intAt(s,i) {
    var c = BI_RC[s.codeUnitAt(i)];
    return (c==null)?-1:c;
  }

  /** copy [this] to [r] */
  void copyTo(BigInteger r) {
    var this_array = this.arrayxxxxx;
    var r_array    = r.arrayxxxxx;

    for(var i = this.txxxxx-1; i >= 0; --i) r_array[i] = this_array[i];
    r.txxxxx = this.txxxxx;
    r.sxxxxx = this.sxxxxx;
  }
  
  BigInteger copy() {
    var this_array = this.arrayxxxxx;
    var n_array = _initArray;
    for(var i = this.txxxxx-1; i >= 0; --i) n_array[i] = this_array[i];
    return _newInst(n_array, this.amxxxxx, this.txxxxx, this.sxxxxx);
  }

  /** set from integer value [x], -[BI_DV] <= [x] < [BI_DV] */
  factory BigInteger.fromInt(int x) {
    var this_array = _initArray;
    var this_am = _default_am;
    _setup(this_am);
    var this_t = 1;
    var this_s = (x<0)?-1:0;
    if(x > 0)
      this_array[0] = x;
    else if(x < -1)
      this_array[0] = x+BI_DV;
    else
      this_t = 0;
    return _newInst(this_array, this_am, this_t, this_s);
  }

  /** set from string [s] and radix [b] */
  // it seems that s can also be a byte list (like Uint8List)
  factory BigInteger.fromString(s, int b) {
    var this_array = _initArray;
    var this_am = _default_am;
    _setup(this_am);
    var k;
    if(b == 16) { k = 4;
    } else if(b == 8) { k = 3;
    } else if(b == 256) { k = 8; // byte array
    } else if(b == 2) { k = 1;
    } else if(b == 32) { k = 5;
    } else if(b == 4) { k = 2;
    } else { return fromRadix(s,b); }
    var this_txxxxx = 0;
    var this_sxxxxx = 0;
    var i = s.length, mi = false, sh = 0;
    while(--i >= 0) {
      var x = (k==8) ? s[i] & 0xff : _intAt(s,i); // if k==8 its a byte array
      if(x < 0) {
        //if(s.charAt(i) == "-") mi = true;
        if(s[i] == "-") mi = true;
        continue;
      }
      mi = false;
      if(sh == 0) {
        this_array[this_txxxxx++] = x;
      } else if(sh+k > BI_DB) {
        this_array[this_txxxxx-1] |= (x&((1<<(BI_DB-sh))-1))<<sh;
        this_array[this_txxxxx++] = (x>>(BI_DB-sh));
      }
      else {
        this_array[this_txxxxx-1] |= x<<sh;
      }
      sh += k;
      if(sh >= BI_DB) sh -= BI_DB;
    }
    if(k == 8 && (s[0]&0x80) != 0) {
      this_sxxxxx = -1;
      if(sh > 0) this_array[this_txxxxx-1] |= ((1<<(BI_DB-sh))-1)<<sh;
    }
    this_txxxxx = clamp(this_txxxxx, this_array, this_sxxxxx);
    if(mi) BigInteger.ZERO.subTo(this,this);
  }

  /** return string representation in given radix [b] */
  String toString([int b]) { // NOTE: overriding toString like this is probably bad.
    var this_array = this.arrayxxxxx;
    if(this.sxxxxx < 0) {
      return "-${this.negate_op().toString(b)}"; //return "-"+this.negate().toString(b);
    }

    var k;
    if(b == 16) { k = 4;
    } else if(b == 8) { k = 3;
    } else if(b == 2) { k = 1;
    } else if(b == 32) { k = 5;
    } else if(b == 4) { k = 2;
    } else { return this.toRadix(b);
    }
    var km = (1<<k)-1, d, m = false, r = "", i = this.txxxxx;
    var p = BI_DB-(i*BI_DB)%k;
    if(i-- > 0) {
      if(p < BI_DB && (d = this_array[i]>>p) > 0) { m = true; r = _int2char(d); }
      while(i >= 0) {
        if(p < k) {
          d = (this_array[i]&((1<<p)-1))<<(k-p);
          d |= this_array[--i]>>(p+=BI_DB-k);
        }
        else {
          d = (this_array[i].toInt()>>(p-=k.toInt()).toInt())&km.toInt();
          if(p <= 0) { p += BI_DB; --i; }
        }
        if(d > 0) m = true;
        if(m) r = "${r}${_int2char(d)}"; //r += int2char(d); // NOTE: Might not be best use of string
      }
    }
    return m ? r : "0";
  }

  /** -this */
  BigInteger negate_op() {
    var r = _nbi();
    BigInteger.ZERO.subTo(this,r);
    return r;
  }

  /** |this| */
  BigInteger abs() {
    return (this.sxxxxx<0)?this.negate_op():this;
  }

  /** return + if [this] > [a], - if [this] < [a], 0 if equal **/
  int compareTo(a) {
    if( a is num ) {
      a = new BigInteger(a);
    }
    var this_array = this.arrayxxxxx;
    var a_array = a.arrayxxxxx;

    var r = this.sxxxxx-a.sxxxxx;
    if(r != 0) return r;
    var i = this.txxxxx;
    r = i-a.txxxxx;
    if(r != 0) return r;
    while(--i >= 0) if((r=this_array[i]-a_array[i]) != 0) return r;
    return 0;
  }

  /** returns bit length of the integer [x] */
  int nbits(x) {
    var r = 1, t;

    if (x is num) x = x.toInt();

    if((t=x>>16) != 0) { x = t; r += 16; }
    if((t=x>>8) != 0) { x = t; r += 8; }
    if((t=x>>4) != 0) { x = t; r += 4; }
    if((t=x>>2) != 0) { x = t; r += 2; }
    if((t=x>>1) != 0) { x = t; r += 1; }
    return r;
  }

  /** return the number of bits in [this] */
  int bitLength() {
    var this_array = this.arrayxxxxx;
    if(this.txxxxx <= 0) return 0;
    return BI_DB*(this.txxxxx-1)+nbits(this_array[this.txxxxx-1]^(this.sxxxxx&BI_DM));
  }
  
  static String _dump_state(a) {
    return "t=${a.txxxxx}, s=${a.sxxxxx}, array = ${a.arrayxxxxx}";
  }

  /** r = this << n*DB */
  void dlShiftTo(n,r) {
    var this_array = this.arrayxxxxx;
    var r_array = r.arrayxxxxx;
    var i;
    for(i = this.txxxxx-1; i >= 0; --i) r_array[i+n] = this_array[i];
    for(i = n-1; i >= 0; --i) r_array[i] = 0;
    r.txxxxx = this.txxxxx+n;
    r.sxxxxx = this.sxxxxx;
  }
  
  BigInteger _dlShiftTo(n,r) {
    var this_array = this.arrayxxxxx;
    var n_array = r.arrayxxxxx;
    var i;
    for(i = this.txxxxx-1; i >= 0; --i) n_array[i+n] = this_array[i];
    for(i = n-1; i >= 0; --i) n_array[i] = 0;
    return _newInst(n_array, this.amxxxxx, this.txxxxx + 1, this.sxxxxx);
  }

  /** r = this >> n*DB */
  void drShiftTo(n,r) {
    var this_array = this.arrayxxxxx;
    var r_array = r.arrayxxxxx;
    for(var i = n; i < this.txxxxx; ++i) r_array[i-n] = this_array[i];
    r.txxxxx = Mathx.max(this.txxxxx-n,0);
    r.sxxxxx = this.sxxxxx;
  }
  
  BigInteger _drShiftTo(n,r) {
    var this_array = this.arrayxxxxx;
    var n_array = r.arrayxxxxx;
    for(var i = n; i < this.txxxxx; ++i) n_array[i-n] = this_array[i];
    return _newInst(n_array, this.amxxxxx, Mathx.max(this.txxxxx-n,0), this.sxxxxx);
  }

  /** r = this << n */
  void lShiftTo(n,r) {
    var this_array = this.arrayxxxxx;
    var r_array = r.arrayxxxxx;
    var bs = n%BI_DB;
    var cbs = BI_DB-bs;
    var bm = (1<<cbs)-1;
    int ds = n~/BI_DB;
    var c = (this.sxxxxx<<bs)&BI_DM;
    var i;
    for(i = this.txxxxx-1; i >= 0; --i) {
      r_array[i+ds+1] = (this_array[i]>>cbs)|c;
      c = (this_array[i]&bm)<<bs;
    }
    for(i = ds-1; i >= 0; --i) r_array[i] = 0;
    r_array[ds] = c;
    r.txxxxx = this.txxxxx+ds+1;
    r.sxxxxx = this.sxxxxx;
    r.clamp();
  }
  
  BigInteger _lShiftTo(n,r) {
    var this_array = this.arrayxxxxx;
    var n_array = r.arrayxxxxx;
    var bs = n%BI_DB;
    var cbs = BI_DB-bs;
    var bm = (1<<cbs)-1;
    int ds = n~/BI_DB;
    var c = (this.sxxxxx<<bs)&BI_DM;
    var i;
    for(i = this.txxxxx-1; i >= 0; --i) {
      n_array[i+ds+1] = (this_array[i]>>cbs)|c;
      c = (this_array[i]&bm)<<bs;
    }
    for(i = ds-1; i >= 0; --i) n_array[i] = 0;
    n_array[ds] = c;
    var n_t = this.txxxxx+ds+1;
    var n_s = this.sxxxxx;
    n_t = clamp(n_t, n_array, n_s);
    return _newInst(n_array, this.amxxxxx, n_t, n_s);
  }


  /** r = this >> n */
  void rShiftTo(n,r) {
      var this_array = this.arrayxxxxx;
      var r_array = r.arrayxxxxx;
      r.sxxxxx = this.sxxxxx;
      var ds = n~/BI_DB;

      if(ds >= this.txxxxx) {
        r.txxxxx = 0;
        return;
      }
      var bs = n%BI_DB;
      var cbs = BI_DB-bs;
      var bm = (1<<bs)-1;
      r_array[0] = this_array[ds]>>bs;
      for(var i = ds+1; i < this.txxxxx; ++i) {
        r_array[i-ds-1] |= (this_array[i]&bm)<<cbs;
        r_array[i-ds] = this_array[i]>>bs;
      }
      if(bs > 0) r_array[this.txxxxx-ds-1] |= (this.sxxxxx&bm)<<cbs;
      r.txxxxx = this.txxxxx-ds;
      r.clamp();
  }

  BigInteger _rShiftTo(n,r) {
      var this_array = this.arrayxxxxx;
      var n_array = r.arrayxxxxx;;
      var n_s = this.sxxxxx;
      var ds = n~/BI_DB;

      if(ds >= this.txxxxx)
        return _newInst(n_array, this.amxxxxx, 0, n_s);
      var bs = n%BI_DB;
      var cbs = BI_DB-bs;
      var bm = (1<<bs)-1;
      n_array[0] = this_array[ds]>>bs;
      for(var i = ds+1; i < this.txxxxx; ++i) {
        n_array[i-ds-1] |= (this_array[i]&bm)<<cbs;
        n_array[i-ds] = this_array[i]>>bs;
      }
      if(bs > 0) n_array[this.txxxxx-ds-1] |= (this.sxxxxx&bm)<<cbs;
      var n_t = this.txxxxx-ds;
      n_t = clamp(n_t, n_array, n_s);
      return _newInst(n_array, this.amxxxxx, n_t, n_s);
  }


  /** clamp off excess high words, returns new t */
  static int clamp(n_t, n_array, n_s) {
    var c = n_s & BI_DM;
    while(n_t > 0 && n_array[n_t-1] == c) {
      --n_t;
    }
    return n_t;
  }

  /** r = this - a */
  void subTo(a,r) {
    var this_array = this.arrayxxxxx;
    var r_array = r.arrayxxxxx;
    var a_array = a.arrayxxxxx;
    int i = 0;
    int c = 0;
    int m = Mathx.min(a.txxxxx, this.txxxxx);

    while(i < m) {
      c += (this_array[i].toInt() - a_array[i].toInt()).toInt();
      r_array[i++] = c&BI_DM;
      c >>= BI_DB;
      // NOTE: this is to bypass a dart2js bug
      if (c == 4294967295) {
        c = -1;
      }
    }

    if(a.txxxxx < this.txxxxx) {
      c -= a.sxxxxx;
      while(i < this.txxxxx) {
        c += this_array[i];
        r_array[i++] = c&BI_DM;
        c >>= BI_DB;
        // NOTE: this is to bypass a dart2js bug
        if (c == 4294967295) {
          c = -1;
        }
      }
      c += this.sxxxxx;
    } else {
      c += this.sxxxxx;
      while(i < a.txxxxx) {
        c -= a_array[i];
        r_array[i++] = c&BI_DM;
        c >>= BI_DB;
        if (c == 4294967295) {
          c = -1;
        }
      }
      c -= a.sxxxxx;
    }

    r.sxxxxx = (c<0) ? -1 : 0;

    if(c < -1) {
      r_array[i++] = BI_DV+c;
    } else if(c > 0) {
      r_array[i++] = c;
    }

    r.txxxxx = i;
    r.clamp();
  }
  
  BigInteger _subTo(a,r) {
    var this_array = this.arrayxxxxx;
    var n_array = r.arrayxxxxx;
    var a_array = a.arrayxxxxx;
    int i = 0;
    int c = 0;
    int m = Mathx.min(a.txxxxx, this.txxxxx);

    while(i < m) {
      c += (this_array[i].toInt() - a_array[i].toInt()).toInt();
      n_array[i++] = c&BI_DM;
      c >>= BI_DB;
      // NOTE: this is to bypass a dart2js bug
      if (c == 4294967295) {
        c = -1;
      }
    }

    if(a.txxxxx < this.txxxxx) {
      c -= a.sxxxxx;
      while(i < this.txxxxx) {
        c += this_array[i];
        n_array[i++] = c&BI_DM;
        c >>= BI_DB;
        // NOTE: this is to bypass a dart2js bug
        if (c == 4294967295) {
          c = -1;
        }
      }
      c += this.sxxxxx;
    } else {
      c += this.sxxxxx;
      while(i < a.txxxxx) {
        c -= a_array[i];
        n_array[i++] = c&BI_DM;
        c >>= BI_DB;
        if (c == 4294967295) {
          c = -1;
        }
      }
      c -= a.sxxxxx;
    }

    var n_s = (c<0) ? -1 : 0;

    if(c < -1) {
      n_array[i++] = BI_DV+c;
    } else if(c > 0) {
      n_array[i++] = c;
    }
    
    var n_t = i;
    n_t = clamp(n_t, n_array, n_s);
    return _newInst(n_array, this.amxxxxx, n_t, n_s);
  }
  

  /**
   * r = this * a, r != this,a (HAC 14.12)
   * [this] should be the larger one if appropriate.
   */
  void multiplyTo(a,r) {
    var this_array = this.arrayxxxxx;
    var r_array = r.arrayxxxxx;
    BigInteger x = this.abs();
    BigInteger y = a.abs();
    var y_array = y.arrayxxxxx;
    var i = x.txxxxx;
    r.txxxxx = i+y.txxxxx;
    while(--i >= 0) r_array[i] = 0;
    for(i = 0; i < y.txxxxx; ++i) r_array[i+x.txxxxx] = x.amxxxxx(0,y_array[i],r,i,0,x.txxxxx,x.arrayxxxxx);
    r.sxxxxx = 0;
    r.clamp();

    if(this.sxxxxx != a.sxxxxx) {
      BigInteger.ZERO.subTo(r,r);
    }
  }
  
  BigInteger _multiplyTo(a,r) {
    var this_array = this.arrayxxxxx;
    var n_array = r.arrayxxxxx;
    BigInteger x = this.abs();
    BigInteger y = a.abs();
    var y_array = y.arrayxxxxx;
    var i = x.txxxxx;
    var n_t = i+y.txxxxx;
    while(--i >= 0) n_array[i] = 0;
    for(i = 0; i < y.txxxxx; ++i) n_array[i+x.txxxxx] = x.amxxxxx(0,y_array[i],r,i,0,x.txxxxx,x.arrayxxxxx);
    var n_s = 0;
    n_t = clamp(n_t, n_array, n_s);

    if(this.sxxxxx != a.sxxxxx) {
      return BigInteger.ZERO._subTo(r,r);
    }
    return _newInst(n_array, this.amxxxxx, n_t, n_s);
  }

  /** r = this^2, r != this (HAC 14.16) */
  void squareTo(r) {
    var x = this.abs();
    var x_array = x.arrayxxxxx;
    var r_array = r.arrayxxxxx;

    var i = r.txxxxx = 2*x.txxxxx;
    while(--i >= 0) r_array[i] = 0;
    for(i = 0; i < x.txxxxx-1; ++i) {
      var c = x.amxxxxx(i,x_array[i],r,2*i,0,1,x.arrayxxxxx);
      if((r_array[i+x.txxxxx]+=x.amxxxxx(i+1,2*x_array[i],r,2*i+1,c,x.txxxxx-i-1,x.arrayxxxxx)) >= BI_DV) {
        r_array[i+x.txxxxx] -= BI_DV;
        r_array[i+x.txxxxx+1] = 1;
      }
    }
    if(r.txxxxx > 0) r_array[r.txxxxx-1] += x.amxxxxx(i,x_array[i],r,2*i,0,1,x.arrayxxxxx);
    r.sxxxxx = 0;
    r.clamp();
  }
  
  BigInteger _squareTo(r) {
    var x = this.abs();
    var x_array = x.arrayxxxxx;
    var n_array = r.arrayxxxxx;
    
    var i = 2*x.txxxxx;
    var n_t = i;
    while(--i >= 0) n_array[i] = 0;
    for(i = 0; i < x.txxxxx-1; ++i) {
      var c = x.amxxxxx(i,x_array[i],r,2*i,0,1,x.arrayxxxxx);
      if((n_array[i+x.txxxxx]+=x.amxxxxx(i+1,2*x_array[i],r,2*i+1,c,x.txxxxx-i-1,x.arrayxxxxx)) >= BI_DV) {
        n_array[i+x.txxxxx] -= BI_DV;
        n_array[i+x.txxxxx+1] = 1;
      }
    }
    if(r.txxxxx > 0) n_array[r.txxxxx-1] += x.amxxxxx(i,x_array[i],r,2*i,0,1,x.arrayxxxxx);
    var n_s = 0;
    n_t = clamp(n_t, n_array, n_s);
    return _newInst(n_array, this.amxxxxx, n_t, n_s);
  }

  /**
   * divide this by m, quotient and remainder to q, r (HAC 14.20)
   * r != q, this != m.  q or r may be null.
   */
  void divRemTo(BigInteger m,q,BigInteger r) {
    var pm = m.abs();
    if(pm.txxxxx <= 0) return;
    var pt = this.abs();
    if(pt.txxxxx < pm.txxxxx) {
      if(q != null) q.fromInt(0);
      if(r != null) this.copyTo(r);
      return;
    }
    if(r == null) r = _nbi();
    var y = _nbi(), ts = this.sxxxxx, ms = m.sxxxxx;
    var pm_array = pm.arrayxxxxx;
    var nsh = BI_DB-nbits(pm_array[pm.txxxxx-1]);  // normalize modulus
    if(nsh > 0) { pm.lShiftTo(nsh,y); pt.lShiftTo(nsh,r); }
    else { pm.copyTo(y); pt.copyTo(r); }
    var ys = y.txxxxx;

    var y_array = y.arrayxxxxx;
    var y0 = y_array[ys-1];
    if(y0 == 0) return;
    var yt = y0*(1<<BI_F1)+((ys>1)?y_array[ys-2]>>BI_F2:0);
    var d1 = BI_FV/yt, d2 = (1<<BI_F1)/yt, e = 1<<BI_F2;
    var i = r.txxxxx,
        j = i-ys;
    BigInteger t = (q==null) ?_nbi() : q;

    y.dlShiftTo(j,t);

    var r_array = r.arrayxxxxx;
    if(r.compareTo(t) >= 0) {
      r_array[r.txxxxx++] = 1;
      r.subTo(t,r);
    }
    BigInteger.ONE.dlShiftTo(ys,t);
    t.subTo(y,y); // "negative" y so we can replace sub with am later
    while(y.txxxxx < ys) y_array[y.txxxxx++] = 0;
    while(--j >= 0) {
      // Estimate quotient digit
      var qd = (r_array[--i]==y0)?BI_DM:(r_array[i]*d1+(r_array[i-1]+e)*d2).floor();
      if((r_array[i]+=y.amxxxxx(0,qd,r,j,0,ys,y.arrayxxxxx)) < qd) {  // Try it out
        y.dlShiftTo(j,t);
        r.subTo(t,r);
        while(r_array[i] < --qd) r.subTo(t,r);
      }
    }
    if(q != null) {
      r.drShiftTo(ys,q);
      if(ts != ms) BigInteger.ZERO.subTo(q,q);
    }
    r.txxxxx = ys;
    r.clamp();
    if(nsh > 0) r.rShiftTo(nsh,r);  // Denormalize remainder
    if(ts < 0) BigInteger.ZERO.subTo(r,r);
  }
  
  // returns [q,r] with q = quotient and r = remainder
  _QuotRem _divRemTo(BigInteger m,q,BigInteger r) {
    var pm = m.abs();
    if(pm.txxxxx <= 0) 
      return new _QuotRem(q,r);
    var pt = this.abs();
    if(pt.txxxxx < pm.txxxxx) {
      if(q != null) {
        q = new BigInteger.fromInt(0);
        return new _QuotRem(q,r);
      }
      if(r != null)
        r = this.copy();
      return new _QuotRem(q,r);
    }
    if(r == null) r = _nbi();
    var y = _nbi(), ts = this.sxxxxx, ms = m.sxxxxx;
    var pm_array = pm.arrayxxxxx;
    var nsh = BI_DB-nbits(pm_array[pm.txxxxx-1]);  // normalize modulus
    if(nsh > 0) {
      y = pm._lShiftTo(nsh,y); 
      r = pt._lShiftTo(nsh,r); 
    } else { 
      y = pm.copy(); 
      r = pt.copy(); 
    }
    var ys = y.txxxxx;

    var y_array = y.arrayxxxxx;
    var y0 = y_array[ys-1];
    if(y0 == 0) {
      return new _QuotRem(q,r);
    }
    var yt = y0*(1<<BI_F1)+((ys>1)?y_array[ys-2]>>BI_F2:0);
    var d1 = BI_FV/yt, d2 = (1<<BI_F1)/yt, e = 1<<BI_F2;
    var i = r.txxxxx,
        j = i-ys;
    BigInteger t = (q==null) ? _nbi() : q;

    t = y._dlShiftTo(j,t);

    var r_array = r.arrayxxxxx;
    if(r.compareTo(t) >= 0) {
      var r_t = r.txxxxx;
      r_array[r_t++] = 1;
      var new_r = _newInst(r_array, r.amxxxxx, r_t, r.sxxxxx);
      r = new_r._subTo(t,new_r);
    }
    t = BigInteger.ONE._dlShiftTo(ys,t);
    y = t._subTo(y,y); // "negative" y so we can replace sub with am later
    var y_t = y.txxxxx;
    while(y_t < ys) y_array[y_t++] = 0;
    y = _newInst(y.arrayxxxxx, y.amxxxxx, y_t, y.sxxxxx);
    while(--j >= 0) {
      // Estimate quotient digit
      var qd = (r_array[--i]==y0)?BI_DM:(r_array[i]*d1+(r_array[i-1]+e)*d2).floor();
      if((r_array[i]+=y.amxxxxx(0,qd,r,j,0,ys,y.arrayxxxxx)) < qd) {  // Try it out
        t = y._dlShiftTo(j,t);
        r = r._subTo(t,r);
        while(r_array[i] < --qd) r = r._subTo(t,r);
      }
    }
    if(q != null) {
      q = r._drShiftTo(ys,q);
      if(ts != ms) q = BigInteger.ZERO._subTo(q,q);
    }
    var r_t = ys;
    r_t = clamp(r_t, r.arrayxxxxx, r.sxxxxx);
    if(nsh > 0) r = r._rShiftTo(nsh,r);  // Denormalize remainder
    if(ts < 0) r = BigInteger.ZERO._subTo(r,r);
    var new_q = _newInst(q.arrayxxxxx, q.amxxxxx, q.txxxxx, q.sxxxxx);
    var new_r = _newInst(r.arrayxxxxx, r.amxxxxx, r_t, r.sxxxxx);
    return new _QuotRem(new_q,new_r);
  }
  

  /** this mod a */
  mod(a) {
    var r = _nbi();
    this.abs().divRemTo(a,null,r);
    if(this.sxxxxx < 0 && r.compareTo(BigInteger.ZERO) > 0) a.subTo(r,r);
    return r;
  }
  
  BigInteger _mod(a) {
    var r = _nbi();
    r = this.abs()._divRemTo(a,null,r).r;
    if(this.sxxxxx < 0 && r.compareTo(BigInteger.ZERO) > 0) r = a._subTo(r,r);
    return r;
  }

  /**
   * return "-1/this % 2^DB"; useful for Mont. reduction
   * justification:
   *         xy == 1 (mod m)
   *         xy =  1+km
   *   xy(2-xy) = (1+km)(1-km)
   * x[y(2-xy)] = 1-k^2m^2
   * x[y(2-xy)] == 1 (mod m^2)
   * if y is 1/x mod m, then y(2-xy) is 1/x mod m^2
   * should reduce x and y(2-xy) by m^2 at each step to keep size bounded.
   * JS multiply "overflows" differently from C/C++, so care is needed here.
   */
  invDigit() {
    var this_array = this.arrayxxxxx;
    if(this.txxxxx < 1) return 0;
    var x = this_array[0];
    if((x&1) == 0) return 0;
    var y = x&3;    // y == 1/x mod 2^2
    y = (y*(2-(x&0xf)*y))&0xf;  // y == 1/x mod 2^4
    y = (y*(2-(x&0xff)*y))&0xff;  // y == 1/x mod 2^8
    y = (y*(2-(((x&0xffff)*y)&0xffff)))&0xffff; // y == 1/x mod 2^16
    // last step - calculate inverse mod DV directly;
    // assumes 16 < DB <= 32 and assumes ability to handle 48-bit ints
    y = (y*(2-x*y%BI_DV))%BI_DV;    // y == 1/x mod 2^dbits
    // we really want the negative inverse, and -DV < y < DV
    return (y>0)?BI_DV-y:-y;
  }
  
  int _invDigit() {
    var this_array = this.arrayxxxxx;
    if(this.txxxxx < 1) return 0;
    var x = this_array[0];
    if((x&1) == 0) return 0;
    var y = x&3;    // y == 1/x mod 2^2
    y = (y*(2-(x&0xf)*y))&0xf;  // y == 1/x mod 2^4
    y = (y*(2-(x&0xff)*y))&0xff;  // y == 1/x mod 2^8
    y = (y*(2-(((x&0xffff)*y)&0xffff)))&0xffff; // y == 1/x mod 2^16
    // last step - calculate inverse mod DV directly;
    // assumes 16 < DB <= 32 and assumes ability to handle 48-bit ints
    y = (y*(2-x*y%BI_DV))%BI_DV;    // y == 1/x mod 2^dbits
    // we really want the negative inverse, and -DV < y < DV
    return (y>0)?BI_DV-y:-y;
  }

  /** true iff [this] is even */
  isEven() {
    var this_array = this.arrayxxxxx;
    return ((this.txxxxx>0)?(this_array[0]&1):this.sxxxxx) == 0;
  }

  /** true iff [this] is odd */
  isOdd() => !isEven();

  /** this^e, e < 2^32, doing sqr and mul with "r" (HAC 14.79) */
  BigInteger exp(int e, z) { // TODO: z is one of the reduction algorithms, pass interface class
    if(e > 0xffffffff || e < 1) return BigInteger.ONE;
    BigInteger r = _nbi();
    BigInteger r2 = _nbi();

    BigInteger  g = z.convert(this);
    int i = nbits(e)-1;

    g.copyTo(r);
    while(--i >= 0) {
      z.sqrTo(r,r2);
      if((e&(1<<i)) > 0) { z.mulTo(r2,g,r);
      } else { var t = r; r = r2; r2 = t; }
    }

    return z.revert(r);
  }

  /**  this^e % m, 0 <= e < 2^32 */
  BigInteger modPowInt(int e, BigInteger m) {
    var z;
    if(e < 256 || m.isEven()) {
      z = new Classic(m);
    } else {
      z = new Montgomery(m);
    }

    return this.exp(e,z);
  }

  /** clone */
  clone() {
    var r = _nbi();
    this.copyTo(r);
    return r;
  }

  /** return value as integer */
  int intValue() {
    var this_array = this.arrayxxxxx;
    if(this.sxxxxx < 0) {
      if(this.txxxxx == 1) { return this_array[0]-BI_DV;
      } else if(this.txxxxx == 0) return -1;
    }
    else if(this.txxxxx == 1) { return this_array[0];
    } else if(this.txxxxx == 0) return 0;
    // assumes 16 < DB < 32
    return ((this_array[1]&((1<<(32-BI_DB))-1))<<BI_DB)|this_array[0];
  }

  /** return value as byte */
  byteValue() {
    var this_array = this.arrayxxxxx;
    return (this.txxxxx==0)?this.sxxxxx:(this_array[0]<<24)>>24;
  }

  /** return value as short (assumes DB>=16) */
  shortValue() {
    var this_array = this.arrayxxxxx;
    return (this.txxxxx==0)?this.sxxxxx:(this_array[0]<<16)>>16;
  }

  /** return x s.t. r^x < DV */
  int chunkSize(r) {
    return (Mathx.LN2*BI_DB/Mathx.log(r)).floor().toInt();
  }

  /** 0 if this == 0, 1 if this > 0 */
  int signum() {
    var this_array = this.arrayxxxxx;
    if(this.sxxxxx < 0) {
      return -1;
    } else if(this.txxxxx <= 0 || (this.txxxxx == 1 && this_array[0] <= 0)) {
      return 0;
    } else {
      return 1;
    }
  }

  /** convert to radix string , http://dartbug.com/461 num only supports up to radix 16 */
  String toRadix([int b=10]) {
    if(b == null) b = 10;
    if(this.signum() == 0 || b < 2 || b > 36) return "0";
    var cs = this.chunkSize(b);
    int a = Mathx.pow(b,cs);
    var d = nbv(a), y = _nbi(), z = _nbi(), r = "";
    this.divRemTo(d,y,z);
    while(y.signum() > 0) {
      r = "${(a+z.intValue()).toInt().toRadixString(b).substring(1)}${r}";
      y.divRemTo(d,y,z);
    }

    return "${z.intValue().toRadixString(b)}${r}";
  }


  /** convert from radix string */
  //TODO
  static BigInteger fromRadix(s,b) {
    this.fromInt(0);

    if(b == null) b = 10;

    var cs = this.chunkSize(b);
    num d = Mathx.pow(b,cs);
    bool mi = false;
    int j = 0,
        w = 0;

    for(var i = 0; i < s.length; ++i) {
      var x = _intAt(s,i);
      if(x < 0) {
        if (s is String) {
          if(s[0] == "-" && this.signum() == 0) {
            mi = true;
          }
        }
        continue;
      }
      w = b*w+x;
      if(++j >= cs) {
        this.dMultiply(d);
        this.dAddOffset(w,0);
        j = 0;
        w = 0;
      }
    }

    if(j > 0) {
      this.dMultiply(Mathx.pow(b,j));
      // w is zero there should not add offset
      if (w != 0) {
        this.dAddOffset(w,0);
      }
    }

    if(mi)  {
      BigInteger.ZERO.subTo(this,this);
    }
  }



// (protected) alternate constructor
//  fromNumber(a,b,c) {
//    //if("number" == typeof b) {
//    if (b is num || b is int || b is double) {
//      // new BigInteger(int,int,RNG)
//      if(a < 2) {
//        this.fromInt(1);
//      } else {
//        this.fromNumber(a,c, null);
//        if(!this.testBit(a-1))  // force MSB set
//          this.bitwiseTo(BigInteger.ONE.shiftLeft(a-1),op_or,this);
//        if(this.isEven()) this.dAddOffset(1,0); // force odd
//        while(!this.isProbablePrime(b)) {
//          this.dAddOffset(2,0);
//          if(this.bitLength() > a) this.subTo(BigInteger.ONE.shiftLeft(a-1),this);
//        }
//      }
//    }
//    else {
//      // new BigInteger(int,RNG)
//      var x = new Map();
//      StringBuffer sb = new StringBuffer();
//      //x[0] = 0;
//      var t = a & 7;
//      // x.length = (a>>3)+1; // TODO: do we really need to set the length for the Array when using something like map?
//      if(t > 0) {
//        x[0] = ((1<<t)-1);
//      } else {
//        x[0] = 0;
//      }
//
//      this.fromString(x,256);
//    }
//  }

  /**
   * convert to bigendian byte array [List]
   */
  List<int> toByteArray() {
    var this_array = this.arrayxxxxx;
    var i = this.txxxxx;
    JSArray<int> r = new JSArray<int>();
    r[0] = this.sxxxxx;
    var p = BI_DB-(i*BI_DB)%8, d, k = 0;
    if(i-- > 0) {
      if(p < BI_DB && (d = this_array[i]>>p) != (this.sxxxxx&BI_DM)>>p) {
        r[k++] = d|(this.sxxxxx<<(BI_DB-p));
      }
      while(i >= 0) {
        if(p < 8) {
          d = (this_array[i]&((1<<p)-1))<<(8-p);
          d |= this_array[--i]>>(p+=BI_DB-8);
        }
        else {
          d = (this_array[i]>>(p-=8))&0xff;
          if(p <= 0) { p += BI_DB; --i; }
        }
        if((d&0x80) != 0) d |= -256;
        if(k == 0 && (this.sxxxxx&0x80) != (d&0x80)) ++k;
        if(k > 0 || d != this.sxxxxx) r[k++] = d;
      }
    }
    return r.data;
  }

  bool equals(BigInteger a) {
    return this.compareTo(a)==0 ? true : false;
  }

  BigInteger min(BigInteger a) {
    return(this.compareTo(a)<0)?this:a;
  }

  BigInteger max(BigInteger a) {
    return(this.compareTo(a)>0)?this:a;
  }


  /** r = this op a (bitwise) */
  void bitwiseTo(BigInteger a, Function op, BigInteger r) {
    var this_array = this.arrayxxxxx;
    var a_array    = a.arrayxxxxx;
    var r_array    = r.arrayxxxxx;
    var i, f, m = Mathx.min(a.txxxxx,this.txxxxx);
    for(i = 0; i < m; ++i) r_array[i] = op(this_array[i],a_array[i]);
    if(a.txxxxx < this.txxxxx) {
      f = a.sxxxxx&BI_DM;
      for(i = m; i < this.txxxxx; ++i) r_array[i] = op(this_array[i],f);
      r.txxxxx = this.txxxxx;
    }
    else {
      f = this.sxxxxx&BI_DM;
      for(i = m; i < a.txxxxx; ++i) r_array[i] = op(f,a_array[i]);
      r.txxxxx = a.txxxxx;
    }
    r.sxxxxx = op(this.sxxxxx,a.sxxxxx);
    r.clamp();
  }


  /** this & a */
  op_and(x,y) { return x&y; }
  and(a) {
    var r = _nbi();
    this.bitwiseTo(a,op_and,r);
    return r;
  }

  /** this | a */
  op_or(x,y) {
    return x|y;
  }

  or(a) {
    var r = _nbi();
    this.bitwiseTo(a,op_or,r);
    return r;
  }

  /** this ^ a */
  op_xor(x,y) { return x^y; }
  xor(a) {
    var r = _nbi();
    this.bitwiseTo(a,op_xor,r);
    return r;
  }

  /** this & ~a */
  op_andnot(x,y) { return x&~y; }
  andNot(a) {
    var r = _nbi();
    this.bitwiseTo(a,op_andnot,r);
    return r;
  }

  /** ~this */
  not() {
    var this_array = this.arrayxxxxx;
    var r = _nbi();
    var r_array = r.arrayxxxxx;

    for(var i = 0; i < this.txxxxx; ++i) {
      r_array[i] = BI_DM & ~this_array[i];
    }

    r.txxxxx = this.txxxxx;
    r.sxxxxx = ~this.sxxxxx;
    return r;
  }


  /** this << n */
  shiftLeft(n) {
    var r = _nbi();
    if(n < 0) {
      this.rShiftTo(-n,r);
    } else {
      this.lShiftTo(n,r);
    }
    return r;
  }

  /** this >> n */
  shiftRight(n) {
    var r = _nbi();
    if(n < 0) {
      this.lShiftTo(-n,r);
    } else {
      this.rShiftTo(n,r);
    }
    return r;
  }

  /** return index of lowest 1-bit in x, x < 2^31 */
  lbit(x) {
    if(x == 0) return -1;
    var r = 0;
    if((x&0xffff) == 0) { x >>= 16; r += 16; }
    if((x&0xff) == 0) { x >>= 8; r += 8; }
    if((x&0xf) == 0) { x >>= 4; r += 4; }
    if((x&3) == 0) { x >>= 2; r += 2; }
    if((x&1) == 0) ++r;
    return r;
  }

  /** returns index of lowest 1-bit (or -1 if none) */
  getLowestSetBit() {
    var this_array = this.arrayxxxxx;
    for(var i = 0; i < this.txxxxx; ++i)
      if(this_array[i] != 0) return i*BI_DB+lbit(this_array[i]);
    if(this.sxxxxx < 0) return this.txxxxx*BI_DB;
    return -1;
  }

  int get lowestSetBit => getLowestSetBit();

  /** return number of 1 bits in x */
  cbit(x) {
    var r = 0;
    while(x != 0) { x &= x-1; ++r; }
    return r;
  }

  /** return number of set bits */
  bitCount() {
    var this_array = this.arrayxxxxx;
    var r = 0, x = this.sxxxxx&BI_DM;
    for(var i = 0; i < this.txxxxx; ++i) r += cbit(this_array[i]^x);
    return r;
  }

  /** true iff nth bit is set */
  testBit(n) {
    var this_array = this.arrayxxxxx;
    int j = n~/BI_DB;
    if(j >= this.txxxxx) return(this.sxxxxx!=0);
    return((this_array[j]&(1<<(n%BI_DB)))!=0);
  }

  /** this op (1<<n) */
  changeBit(n,op) {
    var r = BigInteger.ONE.shiftLeft(n);
    this.bitwiseTo(r,op,r);
    return r;
  }

  /** this | (1<<n) */
  setBit(n) { return this.changeBit(n,op_or); }

  /** this & ~(1<<n) */
  clearBit(n) { return this.changeBit(n,op_andnot); }

  /** this ^ (1<<n) */
  flipBit(n) { return this.changeBit(n,op_xor); }

  /** r = this + a */
  addTo(a,r) {
    var this_array = this.arrayxxxxx;
    var a_array = a.arrayxxxxx;
    var r_array = r.arrayxxxxx;
    var i = 0, c = 0, m = Mathx.min(a.txxxxx,this.txxxxx);
    while(i < m) {
      c += this_array[i]+a_array[i];
      r_array[i++] = c&BI_DM;
      c >>= BI_DB;
    }
    if(a.txxxxx < this.txxxxx) {
      c += a.sxxxxx;
      while(i < this.txxxxx) {
        c += this_array[i];
        r_array[i++] = c&BI_DM;
        c >>= BI_DB;
      }
      c += this.sxxxxx;
    }
    else {
      c += this.sxxxxx;
      while(i < a.txxxxx) {
        c += a_array[i];
        r_array[i++] = c&BI_DM;
        c >>= BI_DB;
      }
      c += a.sxxxxx;
    }
    r.sxxxxx = (c<0)?-1:0;
    if(c > 0) { r_array[i++] = c;
    } else if(c < -1) r_array[i++] = BI_DV+c;
    r.txxxxx = i;
    r.clamp();
  }

  /** this + a */
  BigInteger add(a) {
    var r = _nbi();
    this.addTo(a,r);
    return r;
  }

  /** this - a */
  BigInteger subtract(a) {
    var r = _nbi();
    this.subTo(a,r);
    return r;
  }

  /** this * a */
  BigInteger multiply(a) {
    var r = _nbi();
    this.multiplyTo(a,r);
    return r;
  }

  /** this / a */
  BigInteger divide(a) {
    var r = _nbi();
    this.divRemTo(a,r,null);
    return r;
  }

  /** this % a */
  BigInteger remainder(BigInteger a) {
    BigInteger r = _nbi();
    this.divRemTo(a,null,r);
    return (r.signum()>=0) ? r : (r+a);
  }

  /** [this/a, this%a] returns Map<BigInteger>
   * [0] = this/a
   * [1] = this%a
   */
  Map<int, BigInteger> divideAndRemainder(a) {
    var q = _nbi(), r = _nbi();
    this.divRemTo(a,q,r);
    //return new Array(q,r);
    Map ret_m = new Map();
    ret_m[0] = q;
    ret_m[1] = r;
    return ret_m;
  }

  /** this *= n, this >= 0, 1 < n < [BI_DV] */
  dMultiply(n) {
    var this_array = this.arrayxxxxx;
    this_array[this.txxxxx] = this.amxxxxx(0,n-1,this,0,0,this.txxxxx,this.arrayxxxxx);
    ++this.txxxxx;
    this.clamp();
  }

  /** this += n << w words, this >= 0 */
  dAddOffset(n,w) {
    var this_array = this.arrayxxxxx;
    while(this.txxxxx <= w) this_array[this.txxxxx++] = 0;
    this_array[w] += n;
    while(this_array[w] >= BI_DV) {
      this_array[w] -= BI_DV;
      if(++w >= this.txxxxx) this_array[this.txxxxx++] = 0;
      ++this_array[w];
    }
  }

  /** this^e */
  BigInteger pow(int e) {
    return this.exp(e,new NullExp());
  }


  /**
   * r = lower n words of "this * a", a.t <= n
   * "this" should be the larger one if appropriate.
   */
  multiplyLowerTo(a,n,r) {
    var r_array = r.arrayxxxxx;
    var a_array = a.arrayxxxxx;
    var i = Mathx.min(this.txxxxx+a.txxxxx,n);
    r.sxxxxx = 0; // assumes a,this >= 0
    r.txxxxx = i;
    while(i > 0) r_array[--i] = 0;
    var j;
    for(j = r.txxxxx-this.txxxxx; i < j; ++i) r_array[i+this.txxxxx] = this.amxxxxx(0,a_array[i],r,i,0,this.txxxxx,this.arrayxxxxx);
    for(j = Mathx.min(a.txxxxx,n); i < j; ++i) this.amxxxxx(0,a_array[i],r,i,0,n-i,this.arrayxxxxx);
    r.clamp();
  }

  /**
   * r = "this * a" without lower n words, n > 0
   * "this" should be the larger one if appropriate.
   */
  multiplyUpperTo(a,n,r) {
    var r_array = r.arrayxxxxx;
    var a_array = a.arrayxxxxx;
    --n;
    var i = r.txxxxx = this.txxxxx+a.txxxxx-n;
    r.sxxxxx = 0; // assumes a,this >= 0
    while(--i >= 0) r_array[i] = 0;
    for(i = Mathx.max(n-this.txxxxx,0); i < a.txxxxx; ++i) {
      r_array[this.txxxxx+i-n] = this.amxxxxx(n-i,a_array[i],r,0,0,this.txxxxx+i-n,this.arrayxxxxx);
    }
    r.clamp();
    r.drShiftTo(1,r);
  }


  /** this^e % m (HAC 14.85) */
  modPow(BigInteger e, BigInteger m) {
    // TODO: need to create interface for the reduction algorithms
    var e_array = e.arrayxxxxx;
    var i = e.bitLength(), k, r = nbv(1), z;
    if(i <= 0) { return r;
    } else if(i < 18) { k = 1;
    } else if(i < 48) { k = 3;
    } else if(i < 144) { k = 4;
    } else if(i < 768) { k = 5;
    } else { k = 6;
    }
    if(i < 8) {
      z = new Classic(m);
    } else if(m.isEven()) {
      z = new Barrett(m);
    } else {
      z = new Montgomery(m);
    }


    // precomputation
    var g = new Map(), n = 3, k1 = k-1, km = (1<<k)-1;
    g[1] = z.convert(this);
    if(k > 1) {
      var g2 = _nbi();
      z.sqrTo(g[1],g2);
      while(n <= km) {
        g[n] = _nbi();
        z.mulTo(g2,g[n-2],g[n]);
        n += 2;
      }
    }

    var j = e.txxxxx-1, w, is1 = true, r2 = _nbi(), t;
    i = nbits(e_array[j])-1;
    while(j >= 0) {
      if(i >= k1) { w = (e_array[j]>>(i-k1))&km;
      } else {
        w = (e_array[j]&((1<<(i+1))-1))<<(k1-i);
        if(j > 0) w |= e_array[j-1]>>(BI_DB+i-k1);
      }

      n = k;
      while((w&1) == 0) { w >>= 1; --n; }
      if((i -= n) < 0) { i += BI_DB; --j; }
      if(is1) { // ret == 1, don't bother squaring or multiplying it
        g[w].copyTo(r);
        is1 = false;
      }
      else {
        while(n > 1) { z.sqrTo(r,r2); z.sqrTo(r2,r); n -= 2; }
        if(n > 0) z.sqrTo(r,r2); else { t = r; r = r2; r2 = t; }
        z.mulTo(r2,g[w],r);
      }

      while(j >= 0 && (e_array[j]&(1<<i)) == 0) {
        z.sqrTo(r,r2); t = r; r = r2; r2 = t;
        if(--i < 0) { i = BI_DB-1; --j; }
      }
    }
    return z.revert(r);
  }

  /** gcd(this,a) (HAC 14.54) */
  gcd(a) {
    var x = (this.sxxxxx<0)?this.negate_op():this.clone();
    var y = (a.sxxxxx<0)?a.negate_op():a.clone();
    if(x.compareTo(y) < 0) { var t = x; x = y; y = t; }
    var i = x.getLowestSetBit(), g = y.getLowestSetBit();
    if(g < 0) return x;
    if(i < g) g = i;
    if(g > 0) {
      x.rShiftTo(g,x);
      y.rShiftTo(g,y);
    }
    while(x.signum() > 0) {
      if((i = x.getLowestSetBit()) > 0) x.rShiftTo(i,x);
      if((i = y.getLowestSetBit()) > 0) y.rShiftTo(i,y);
      if(x.compareTo(y) >= 0) {
        x.subTo(y,x);
        x.rShiftTo(1,x);
      }
      else {
        y.subTo(x,y);
        y.rShiftTo(1,y);
      }
    }
    if(g > 0) y.lShiftTo(g,y);
    return y;
  }

  /** this % n, n < 2^26 */
  int modInt(int n) {
    var this_array = this.arrayxxxxx;
    if(n <= 0) return 0;
    var d = BI_DV%n, r = (this.sxxxxx<0)?n-1:0;
    if(this.txxxxx > 0) {
      if(d == 0) { r = this_array[0]%n;
      } else { for(var i = this.txxxxx-1; i >= 0; --i) r = (d*r+this_array[i])%n;
    }
      }
    return r;
  }

  /** 1/this % m (HAC 14.61) */
  BigInteger modInverse(BigInteger m) {
    var ac = m.isEven();
    if((this.isEven() && ac) || m.signum() == 0) return BigInteger.ZERO;
    var u = m.clone(), v = this.clone();
    if( v.signum()<0 ) v = -v;
    var a = nbv(1), b = nbv(0), c = nbv(0), d = nbv(1);
    while(u.signum() != 0) {
      while(u.isEven()) {
        u.rShiftTo(1,u);
        if(ac) {
          if(!a.isEven() || !b.isEven()) { a.addTo(this,a); b.subTo(m,b); }
          a.rShiftTo(1,a);
        }
        else if(!b.isEven()) b.subTo(m,b);
        b.rShiftTo(1,b);
      }
      while(v.isEven()) {
        v.rShiftTo(1,v);
        if(ac) {
          if(!c.isEven() || !d.isEven()) { c.addTo(this,c); d.subTo(m,d); }
          c.rShiftTo(1,c);
        }
        else if(!d.isEven()) d.subTo(m,d);
        d.rShiftTo(1,d);
      }
      if(u.compareTo(v) >= 0) {
        u.subTo(v,u);
        if(ac) a.subTo(c,a);
        b.subTo(d,b);
      }
      else {
        v.subTo(u,v);
        if(ac) c.subTo(a,c);
        d.subTo(b,d);
      }
    }
    if(v.compareTo(BigInteger.ONE) != 0) return BigInteger.ZERO;
    if(d.compareTo(m) >= 0) return _adjust(d.subtract(m),m);
    if(d.signum() < 0) d.addTo(m,d); else return _adjust(d,m);
    if(d.signum() < 0) return _adjust(d.add(m),m); else return _adjust(d,m);
  }

  // TODO: optimize this
  _adjust(val,m) => ( signum()<0 ) ? (m-val) : val;

  /** test primality with certainty >= 1-.5^t */
  bool isProbablePrime(int t) {
    var i, x = this.abs();
    var x_array = x.arrayxxxxx;
    if(x.txxxxx == 1 && x_array[0] <= _lowprimes[_lowprimes.length-1]) {
      for(i = 0; i < _lowprimes.length; ++i)
        if(x_array[0] == _lowprimes[i]) return true;
      return false;
    }
    if(x.isEven()) return false;
    i = 1;
    while(i < _lowprimes.length) {
      var m = _lowprimes[i], j = i+1;
      while(j < _lowprimes.length && m < _lplim) m *= _lowprimes[j++];
      m = x.modInt(m);
      while(i < j) if(m%_lowprimes[i++] == 0) return false;
    }
    return x.millerRabin(t);
  }

  /** true if probably prime (HAC 4.24, Miller-Rabin) */
  bool millerRabin(t) {
    var n1 = this.subtract(BigInteger.ONE);
    var k = n1.getLowestSetBit();
    if(k <= 0) return false;
    var r = n1.shiftRight(k);
    t = (t+1)>>1;
    if(t > _lowprimes.length) t = _lowprimes.length;
    var a = _nbi();
    for(var i = 0; i < t; ++i) {
      a.fromInt(_lowprimes[i]);
      var y = a.modPow(r,this);
      if(y.compareTo(BigInteger.ONE) != 0 && y.compareTo(n1) != 0) {
        var j = 1;
        while(j++ < k && y.compareTo(n1) != 0) {
          y = y.modPowInt(2,this);
          if(y.compareTo(BigInteger.ONE) == 0) return false;
        }
        if(y.compareTo(n1) != 0) return false;
      }
    }
    return true;
  }


  // Arithmetic operations.
  BigInteger operator +(BigInteger other) => add(other);
  BigInteger operator -(BigInteger other) => subtract(other);
  BigInteger operator *(BigInteger other) => multiply(other);
  BigInteger operator %(BigInteger other) => remainder(other);
  BigInteger operator /(BigInteger other) => divide(other);

  // Truncating division.
  BigInteger operator ~/(BigInteger other) => divide(other);

  // The unary '-' operator.
  BigInteger operator -() => this.negate_op();

  // NOTE: This is implemented above.
  //BigInteger remainder(BigInteger other) { throw "Not Implemented"; }

  // Relational operations.
  bool operator <(BigInteger other) => compareTo(other) < 0 ? true : false;
  bool operator <=(BigInteger other) => compareTo(other) <= 0 ? true : false;
  bool operator >(BigInteger other) => compareTo(other) > 0 ? true : false;
  bool operator >=(BigInteger other) => compareTo(other) >= 0 ? true : false;
  bool operator ==(other) => compareTo(other) == 0 ? true : false;

  // Bit-operations.
  BigInteger operator &(BigInteger other) => and(other);
  BigInteger operator |(BigInteger other) => or(other);
  BigInteger operator ^(BigInteger other) => xor(other);
  BigInteger operator ~() => not();
  BigInteger operator <<(int shiftAmount) => shiftLeft(shiftAmount);
  BigInteger operator >>(int shiftAmount) => shiftRight(shiftAmount);

}
