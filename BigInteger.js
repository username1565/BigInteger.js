//Make compatible with scripts, where BigInteger included and calling as BigInteger, not bigInt
//Just add BigInteger name for variable
var bigInt = BigInteger = (function (undefined) {
    "use strict";

    var BASE = 1e7,
        LOG_BASE = 7,
        MAX_INT = Number.MAX_SAFE_INTEGER, //= 9007199254740991
        MAX_INT_ARR = smallToArray(MAX_INT),
        DEFAULT_ALPHABET = "0123456789abcdefghijklmnopqrstuvwxyz"
	;

    function Integer(v, radix, alphabet, caseSensitive) {
        if (typeof v === "undefined") return Integer[0];
        if (typeof radix !== "undefined") return +radix === 10 && !alphabet ? parseValue(v) : v.parseBase(radix, alphabet, caseSensitive, v);
        return parseValue(v);
    }

    function BigInteger(value, sign) {
        this.value = value;
        this.sign = sign;
        this.isSmall = false;
    }
    BigInteger.prototype = Object.create(Integer.prototype);

    function SmallInteger(value) {
        this.value = value;
        this.sign = value < 0;
        this.isSmall = true;
    }
    SmallInteger.prototype = Object.create(Integer.prototype);

    function isPrecise(n) {
        return -MAX_INT < n && n < MAX_INT;
    }

    function smallToArray(n) { // For performance reasons doesn't reference BASE, need to change this function if BASE changes
        if (n < 1e7)
            return [n];
        if (n < 1e14)
            return [n % 1e7, Math.floor(n / 1e7)];
        return [n % 1e7, Math.floor(n / 1e7) % 1e7, Math.floor(n / 1e14)];
    }

    function arrayToSmall(arr) { // If BASE changes this function may need to change
        trim(arr);
        var length = arr.length;
        if (length < 4 && compareAbs(arr, MAX_INT_ARR) < 0) {
            switch (length) {
                case 0: return 0;
                case 1: return arr[0];
                case 2: return arr[0] + arr[1] * BASE;
                default: return arr[0] + (arr[1] + arr[2] * BASE) * BASE;
            }
        }
        return arr;
    }

    function trim(v) {
        var i = v.length;
        while (v[--i] === 0);
        v.length = i + 1;
    }

    function createArray(length) { // function shamelessly stolen from Yaffle's library https://github.com/Yaffle/BigInteger
        var x = new Array(length);
        var i = -1;
        while (++i < length) {
            x[i] = 0;
        }
        return x;
    }

    function truncate(n) {
        if (n > 0) return Math.floor(n);
        return Math.ceil(n);
    }

    function add(a, b) { // assumes a and b are arrays with a.length >= b.length
        var l_a = a.length,
            l_b = b.length,
            r = new Array(l_a),
            carry = 0,
            base = BASE,
            sum, i;
        for (i = 0; i < l_b; i++) {
            sum = a[i] + b[i] + carry;
            carry = sum >= base ? 1 : 0;
            r[i] = sum - carry * base;
        }
        while (i < l_a) {
            sum = a[i] + carry;
            carry = sum === base ? 1 : 0;
            r[i++] = sum - carry * base;
        }
        if (carry > 0) r.push(carry);
        return r;
    }

    function addAny(a, b) {
        if (a.length >= b.length) return add(a, b);
        return add(b, a);
    }

    function addSmall(a, carry) { // assumes a is array, carry is number with 0 <= carry < MAX_INT
        var l = a.length,
            r = new Array(l),
            base = BASE,
            sum, i;
        for (i = 0; i < l; i++) {
            sum = a[i] - base + carry;
            carry = Math.floor(sum / base);
            r[i] = sum - carry * base;
            carry += 1;
        }
        while (carry > 0) {
            r[i++] = carry % base;
            carry = Math.floor(carry / base);
        }
        return r;
    }

    BigInteger.prototype.add = function (v) {
        var n = parseValue(v);
        if (this.sign !== n.sign) {
            return this.subtract(n.negate());
        }
        var a = this.value, b = n.value;
        if (n.isSmall) {
            return new BigInteger(addSmall(a, Math.abs(b)), this.sign);
        }
        return new BigInteger(addAny(a, b), this.sign);
    };
    BigInteger.prototype.plus = BigInteger.prototype.add;

    SmallInteger.prototype.add = function (v) {
        var n = parseValue(v);
        var a = this.value;
        if (a < 0 !== n.sign) {
            return this.subtract(n.negate());
        }
        var b = n.value;
        if (n.isSmall) {
            if (isPrecise(a + b)) return new SmallInteger(a + b);
            b = smallToArray(Math.abs(b));
        }
        return new BigInteger(addSmall(b, Math.abs(a)), a < 0);
    };
    SmallInteger.prototype.plus = SmallInteger.prototype.add;

    function subtract(a, b) { // assumes a and b are arrays with a >= b
        var a_l = a.length,
            b_l = b.length,
            r = new Array(a_l),
            borrow = 0,
            base = BASE,
            i, difference;
        for (i = 0; i < b_l; i++) {
            difference = a[i] - borrow - b[i];
            if (difference < 0) {
                difference += base;
                borrow = 1;
            } else borrow = 0;
            r[i] = difference;
        }
        for (i = b_l; i < a_l; i++) {
            difference = a[i] - borrow;
            if (difference < 0) difference += base;
            else {
                r[i++] = difference;
                break;
            }
            r[i] = difference;
        }
        for (; i < a_l; i++) {
            r[i] = a[i];
        }
        trim(r);
        return r;
    }

    function subtractAny(a, b, sign) {
        var value;
        if (compareAbs(a, b) >= 0) {
            value = subtract(a, b);
        } else {
            value = subtract(b, a);
            sign = !sign;
        }
        value = arrayToSmall(value);
        if (typeof value === "number") {
            if (sign) value = -value;
            return new SmallInteger(value);
        }
        return new BigInteger(value, sign);
    }

    function subtractSmall(a, b, sign) { // assumes a is array, b is number with 0 <= b < MAX_INT
        var l = a.length,
            r = new Array(l),
            carry = -b,
            base = BASE,
            i, difference;
        for (i = 0; i < l; i++) {
            difference = a[i] + carry;
            carry = Math.floor(difference / base);
            difference %= base;
            r[i] = difference < 0 ? difference + base : difference;
        }
        r = arrayToSmall(r);
        if (typeof r === "number") {
            if (sign) r = -r;
            return new SmallInteger(r);
        } return new BigInteger(r, sign);
    }

    BigInteger.prototype.subtract = function (v) {
        var n = parseValue(v);
        if (this.sign !== n.sign) {
            return this.add(n.negate());
        }
        var a = this.value, b = n.value;
        if (n.isSmall)
            return subtractSmall(a, Math.abs(b), this.sign);
        return subtractAny(a, b, this.sign);
    };
    BigInteger.prototype.minus = BigInteger.prototype.subtract;

    SmallInteger.prototype.subtract = function (v) {
        var n = parseValue(v);
        var a = this.value;
        if (a < 0 !== n.sign) {
            return this.add(n.negate());
        }
        var b = n.value;
        if (n.isSmall) {
            return new SmallInteger(a - b);
        }
        return subtractSmall(b, Math.abs(a), a >= 0);
    };
    SmallInteger.prototype.minus = SmallInteger.prototype.subtract;

    BigInteger.prototype.negate = function () {
        return new BigInteger(this.value, !this.sign);
    };
    SmallInteger.prototype.negate = function () {
        var sign = this.sign;
        var small = new SmallInteger(-this.value);
        small.sign = !sign;
        return small;
    };

    BigInteger.prototype.abs = function () {
        return new BigInteger(this.value, false);
    };
    SmallInteger.prototype.abs = function () {
        return new SmallInteger(Math.abs(this.value));
    };

    function multiplyLong(a, b) {
        var a_l = a.length,
            b_l = b.length,
            l = a_l + b_l,
            r = createArray(l),
            base = BASE,
            product, carry, i, a_i, b_j;
        for (i = 0; i < a_l; ++i) {
            a_i = a[i];
            for (var j = 0; j < b_l; ++j) {
                b_j = b[j];
                product = a_i * b_j + r[i + j];
                carry = Math.floor(product / base);
                r[i + j] = product - carry * base;
                r[i + j + 1] += carry;
            }
        }
        trim(r);
        return r;
    }

    function multiplySmall(a, b) { // assumes a is array, b is number with |b| < BASE
        var l = a.length,
            r = new Array(l),
            base = BASE,
            carry = 0,
            product, i;
        for (i = 0; i < l; i++) {
            product = a[i] * b + carry;
            carry = Math.floor(product / base);
            r[i] = product - carry * base;
        }
        while (carry > 0) {
            r[i++] = carry % base;
            carry = Math.floor(carry / base);
        }
        return r;
    }

    function shiftLeft(x, n) {
        var r = [];
        while (n-- > 0) r.push(0);
        return r.concat(x);
    }

    function multiplyKaratsuba(x, y) {
        var n = Math.max(x.length, y.length);

        if (n <= 30) return multiplyLong(x, y);
        n = Math.ceil(n / 2);

        var b = x.slice(n),
            a = x.slice(0, n),
            d = y.slice(n),
            c = y.slice(0, n);

        var ac = multiplyKaratsuba(a, c),
            bd = multiplyKaratsuba(b, d),
            abcd = multiplyKaratsuba(addAny(a, b), addAny(c, d));

        var product = addAny(addAny(ac, shiftLeft(subtract(subtract(abcd, ac), bd), n)), shiftLeft(bd, 2 * n));
        trim(product);
        return product;
    }

    // The following function is derived from a surface fit of a graph plotting the performance difference
    // between long multiplication and karatsuba multiplication versus the lengths of the two arrays.
    function useKaratsuba(l1, l2) {
        return -0.012 * l1 - 0.012 * l2 + 0.000015 * l1 * l2 > 0;
    }

    BigInteger.prototype.multiply = function (v) {
        var n = parseValue(v),
            a = this.value, b = n.value,
            sign = this.sign !== n.sign,
            abs;
        if (n.isSmall) {
            if (b === 0) return Integer[0];
            if (b === 1) return this;
            if (b === -1) return this.negate();
            abs = Math.abs(b);
            if (abs < BASE) {
                return new BigInteger(multiplySmall(a, abs), sign);
            }
            b = smallToArray(abs);
        }
        if (useKaratsuba(a.length, b.length)) // Karatsuba is only faster for certain array sizes
            return new BigInteger(multiplyKaratsuba(a, b), sign);
        return new BigInteger(multiplyLong(a, b), sign);
    };

    BigInteger.prototype.times = BigInteger.prototype.multiply;

    function multiplySmallAndArray(a, b, sign) { // a >= 0
        if (a < BASE) {
            return new BigInteger(multiplySmall(b, a), sign);
        }
        return new BigInteger(multiplyLong(b, smallToArray(a)), sign);
    }
    SmallInteger.prototype._multiplyBySmall = function (a) {
        if (isPrecise(a.value * this.value)) {
            return new SmallInteger(a.value * this.value);
        }
        return multiplySmallAndArray(Math.abs(a.value), smallToArray(Math.abs(this.value)), this.sign !== a.sign);
    };
    BigInteger.prototype._multiplyBySmall = function (a) {
        if (a.value === 0) return Integer[0];
        if (a.value === 1) return this;
        if (a.value === -1) return this.negate();
        return multiplySmallAndArray(Math.abs(a.value), this.value, this.sign !== a.sign);
    };
    SmallInteger.prototype.multiply = function (v) {
        return parseValue(v)._multiplyBySmall(this);
    };
    SmallInteger.prototype.times = SmallInteger.prototype.multiply;

    function square(a) {
        var l = a.length,
            r = createArray(l + l),
            base = BASE,
            product, carry, i, a_i, a_j;
        for (i = 0; i < l; i++) {
            a_i = a[i];
            carry = 0 - a_i * a_i;
            for (var j = i; j < l; j++) {
                a_j = a[j];
                product = 2 * (a_i * a_j) + r[i + j] + carry;
                carry = Math.floor(product / base);
                r[i + j] = product - carry * base;
            }
            r[i + l] = carry;
        }
        trim(r);
        return r;
    }

    BigInteger.prototype.square = function () {
        return new BigInteger(square(this.value), false);
    };

    SmallInteger.prototype.square = function () {
        var value = this.value * this.value;
        if (isPrecise(value)) return new SmallInteger(value);
        return new BigInteger(square(smallToArray(Math.abs(this.value))), false);
    };

    function divMod1(a, b) { // Left over from previous version. Performs faster than divMod2 on smaller input sizes.
        var a_l = a.length,
            b_l = b.length,
            base = BASE,
            result = createArray(b.length),
            divisorMostSignificantDigit = b[b_l - 1],
            // normalization
            lambda = Math.ceil(base / (2 * divisorMostSignificantDigit)),
            remainder = multiplySmall(a, lambda),
            divisor = multiplySmall(b, lambda),
            quotientDigit, shift, carry, borrow, i, l, q;
        if (remainder.length <= a_l) remainder.push(0);
        divisor.push(0);
        divisorMostSignificantDigit = divisor[b_l - 1];
        for (shift = a_l - b_l; shift >= 0; shift--) {
            quotientDigit = base - 1;
            if (remainder[shift + b_l] !== divisorMostSignificantDigit) {
                quotientDigit = Math.floor((remainder[shift + b_l] * base + remainder[shift + b_l - 1]) / divisorMostSignificantDigit);
            }
            // quotientDigit <= base - 1
            carry = 0;
            borrow = 0;
            l = divisor.length;
            for (i = 0; i < l; i++) {
                carry += quotientDigit * divisor[i];
                q = Math.floor(carry / base);
                borrow += remainder[shift + i] - (carry - q * base);
                carry = q;
                if (borrow < 0) {
                    remainder[shift + i] = borrow + base;
                    borrow = -1;
                } else {
                    remainder[shift + i] = borrow;
                    borrow = 0;
                }
            }
            while (borrow !== 0) {
                quotientDigit -= 1;
                carry = 0;
                for (i = 0; i < l; i++) {
                    carry += remainder[shift + i] - base + divisor[i];
                    if (carry < 0) {
                        remainder[shift + i] = carry + base;
                        carry = 0;
                    } else {
                        remainder[shift + i] = carry;
                        carry = 1;
                    }
                }
                borrow += carry;
            }
            result[shift] = quotientDigit;
        }
        // denormalization
        remainder = divModSmall(remainder, lambda)[0];
        return [arrayToSmall(result), arrayToSmall(remainder)];
    }

    function divMod2(a, b) { // Implementation idea shamelessly stolen from Silent Matt's library http://silentmatt.com/biginteger/
        // Performs faster than divMod1 on larger input sizes.
        var a_l = a.length,
            b_l = b.length,
            result = [],
            part = [],
            base = BASE,
            guess, xlen, highx, highy, check;
        while (a_l) {
            part.unshift(a[--a_l]);
            trim(part);
            if (compareAbs(part, b) < 0) {
                result.push(0);
                continue;
            }
            xlen = part.length;
            highx = part[xlen - 1] * base + part[xlen - 2];
            highy = b[b_l - 1] * base + b[b_l - 2];
            if (xlen > b_l) {
                highx = (highx + 1) * base;
            }
            guess = Math.ceil(highx / highy);
            do {
                check = multiplySmall(b, guess);
                if (compareAbs(check, part) <= 0) break;
                guess--;
            } while (guess);
            result.push(guess);
            part = subtract(part, check);
        }
        result.reverse();
        return [arrayToSmall(result), arrayToSmall(part)];
    }

    function divModSmall(value, lambda) {
        var length = value.length,
            quotient = createArray(length),
            base = BASE,
            i, q, remainder, divisor;
        remainder = 0;
        for (i = length - 1; i >= 0; --i) {
            divisor = remainder * base + value[i];
            q = truncate(divisor / lambda);
            remainder = divisor - q * lambda;
            quotient[i] = q | 0;
        }
        return [quotient, remainder | 0];
    }

    function divModAny(self, v) {
        var value, n = parseValue(v);
        var a = self.value, b = n.value;
        var quotient;
        if (b === 0) throw new Error("Cannot divide by zero");
        if (self.isSmall) {
            if (n.isSmall) {
                return [new SmallInteger(truncate(a / b)), new SmallInteger(a % b)];
            }
            return [Integer[0], self];
        }
        if (n.isSmall) {
            if (b === 1) return [self, Integer[0]];
            if (b == -1) return [self.negate(), Integer[0]];
            var abs = Math.abs(b);
            if (abs < BASE) {
                value = divModSmall(a, abs);
                quotient = arrayToSmall(value[0]);
                var remainder = value[1];
                if (self.sign) remainder = -remainder;
                if (typeof quotient === "number") {
                    if (self.sign !== n.sign) quotient = -quotient;
                    return [new SmallInteger(quotient), new SmallInteger(remainder)];
                }
                return [new BigInteger(quotient, self.sign !== n.sign), new SmallInteger(remainder)];
            }
            b = smallToArray(abs);
        }
        var comparison = compareAbs(a, b);
        if (comparison === -1) return [Integer[0], self];
        if (comparison === 0) return [Integer[self.sign === n.sign ? 1 : -1], Integer[0]];

        // divMod1 is faster on smaller input sizes
        if (a.length + b.length <= 200)
            value = divMod1(a, b);
        else value = divMod2(a, b);

        quotient = value[0];
        var qSign = self.sign !== n.sign,
            mod = value[1],
            mSign = self.sign;
        if (typeof quotient === "number") {
            if (qSign) quotient = -quotient;
            quotient = new SmallInteger(quotient);
        } else quotient = new BigInteger(quotient, qSign);
        if (typeof mod === "number") {
            if (mSign) mod = -mod;
            mod = new SmallInteger(mod);
        } else mod = new BigInteger(mod, mSign);
        return [quotient, mod];
    }

    BigInteger.prototype.divmod = function (v) {
        var result = divModAny(this, v);
        return {
            quotient: result[0],
            remainder: result[1]
        };
    };
    SmallInteger.prototype.divmod = BigInteger.prototype.divmod;

    BigInteger.prototype.divide = function (v) {
        return divModAny(this, v)[0];
    };
    SmallInteger.prototype.over = SmallInteger.prototype.divide = BigInteger.prototype.over = BigInteger.prototype.divide;

    BigInteger.prototype.mod = function (v) {
        return divModAny(this, v)[1];
    };
    SmallInteger.prototype.remainder = SmallInteger.prototype.mod = BigInteger.prototype.remainder = BigInteger.prototype.mod;

    BigInteger.prototype.pow = function (v) {
        var n = parseValue(v),
            a = this.value,
            b = n.value,
            value, x, y;
        if (b === 0) return Integer[1];
        if (a === 0) return Integer[0];
        if (a === 1) return Integer[1];
        if (a === -1) return n.isEven() ? Integer[1] : Integer[-1];
        if (n.sign) {
            return Integer[0];
        }
        if (!n.isSmall) throw new Error("The exponent " + n.toString() + " is too large.");
        if (this.isSmall) {
            if (isPrecise(value = Math.pow(a, b)))
                return new SmallInteger(truncate(value));
        }
        x = this;
        y = Integer[1];
        while (true) {
            if (b & 1 === 1) {
                y = y.times(x);
                --b;
            }
            if (b === 0) break;
            b /= 2;
            x = x.square();
        }
        return y;
    };
    SmallInteger.prototype.pow = BigInteger.prototype.pow;

    BigInteger.prototype.modPow = function (exp, mod) {
        exp = parseValue(exp);
        mod = parseValue(mod);
        if (mod.isZero()) throw new Error("Cannot take modPow with modulus 0");
        var r = Integer[1],
            base = this.mod(mod);
        if (exp.isNegative()) {
            exp = exp.multiply(Integer[-1]);
            base = base.modInv(mod);
        }
        while (exp.isPositive()) {
            if (base.isZero()) return Integer[0];
            if (exp.isOdd()) r = r.multiply(base).mod(mod);
            exp = exp.divide(2);
            base = base.square().mod(mod);	//maybe, this can be a faster, using Montgomery Algorithm.
        }
        return r;
    };
    SmallInteger.prototype.modPow = BigInteger.prototype.modPow;

    function compareAbs(a, b) {
        if (a.length !== b.length) {
            return a.length > b.length ? 1 : -1;
        }
        for (var i = a.length - 1; i >= 0; i--) {
            if (a[i] !== b[i]) return a[i] > b[i] ? 1 : -1;
        }
        return 0;
    }

    BigInteger.prototype.compareAbs = function (v) {
        var n = parseValue(v),
            a = this.value,
            b = n.value;
        if (n.isSmall) return 1;
        return compareAbs(a, b);
    };
    SmallInteger.prototype.compareAbs = function (v) {
        var n = parseValue(v),
            a = Math.abs(this.value),
            b = n.value;
        if (n.isSmall) {
            b = Math.abs(b);
            return a === b ? 0 : a > b ? 1 : -1;
        }
        return -1;
    };

    BigInteger.prototype.compare = function (v) {
        // See discussion about comparison with Infinity:
        // https://github.com/peterolson/BigInteger.js/issues/61
        if (v === Infinity) {
            return -1;
        }
        if (v === -Infinity) {
            return 1;
        }

        var n = parseValue(v),
            a = this.value,
            b = n.value;
        if (this.sign !== n.sign) {
            return n.sign ? 1 : -1;
        }
        if (n.isSmall) {
            return this.sign ? -1 : 1;
        }
        return compareAbs(a, b) * (this.sign ? -1 : 1);
    };
    BigInteger.prototype.compareTo = BigInteger.prototype.compare;

    SmallInteger.prototype.compare = function (v) {
        if (v === Infinity) {
            return -1;
        }
        if (v === -Infinity) {
            return 1;
        }

        var n = parseValue(v),
            a = this.value,
            b = n.value;
        if (n.isSmall) {
            return a == b ? 0 : a > b ? 1 : -1;
        }
        if (a < 0 !== n.sign) {
            return a < 0 ? -1 : 1;
        }
        return a < 0 ? 1 : -1;
    };
    SmallInteger.prototype.compareTo = SmallInteger.prototype.compare;

    BigInteger.prototype.equals = function (v) {
        return this.compare(v) === 0;
    };
    SmallInteger.prototype.eq = SmallInteger.prototype.equals = BigInteger.prototype.eq = BigInteger.prototype.equals;

    BigInteger.prototype.notEquals = function (v) {
        return this.compare(v) !== 0;
    };
    SmallInteger.prototype.neq = SmallInteger.prototype.notEquals = BigInteger.prototype.neq = BigInteger.prototype.notEquals;

    BigInteger.prototype.greater = function (v) {
        return this.compare(v) > 0;
    };
    SmallInteger.prototype.gt = SmallInteger.prototype.greater = BigInteger.prototype.gt = BigInteger.prototype.greater;

    BigInteger.prototype.lesser = function (v) {
        return this.compare(v) < 0;
    };
    SmallInteger.prototype.lt = SmallInteger.prototype.lesser = BigInteger.prototype.lt = BigInteger.prototype.lesser;

    BigInteger.prototype.greaterOrEquals = function (v) {
        return this.compare(v) >= 0;
    };
    SmallInteger.prototype.geq = SmallInteger.prototype.greaterOrEquals = BigInteger.prototype.geq = BigInteger.prototype.greaterOrEquals;

    BigInteger.prototype.lesserOrEquals = function (v) {
        return this.compare(v) <= 0;
    };
    SmallInteger.prototype.leq = SmallInteger.prototype.lesserOrEquals = BigInteger.prototype.leq = BigInteger.prototype.lesserOrEquals;

    BigInteger.prototype.isEven = function () {
        return (this.value[0] & 1) === 0;
    };
    SmallInteger.prototype.isEven = function () {
        return (this.value & 1) === 0;
    };

    BigInteger.prototype.isOdd = function () {
        return (this.value[0] & 1) === 1;
    };
    SmallInteger.prototype.isOdd = function () {
        return (this.value & 1) === 1;
    };

    BigInteger.prototype.isPositive = function () {
        return !this.sign;
    };
    SmallInteger.prototype.isPositive = function () {
        return this.value > 0;
    };

    BigInteger.prototype.isNegative = function () {
        return this.sign;
    };
    SmallInteger.prototype.isNegative = function () {
        return this.value < 0;
    };

    BigInteger.prototype.isUnit = function () {
        return false;
    };
    SmallInteger.prototype.isUnit = function () {
        return Math.abs(this.value) === 1; //-1 or 1
    };
	
	BigInteger.prototype.isOne = function(){
		return false;
	}
    SmallInteger.prototype.isOne = function () {
        return this.value === 1;
    };

    BigInteger.prototype.isZero = function () {
        return false;
    };
    SmallInteger.prototype.isZero = function () {
        return this.value === 0;
    };

    BigInteger.prototype.isDivisibleBy = function (v) {
        var n = parseValue(v);
        if (n.isZero()) return false;
        if (n.isUnit()) return true;
        if (n.compareAbs(2) === 0) return this.isEven();
        return this.mod(n).isZero();
    };
    SmallInteger.prototype.isDivisibleBy = BigInteger.prototype.isDivisibleBy;

    function isBasicPrime(v) {
        var n = v.abs();
        if (n.eq(0) || n.eq(1)){return false;}
        if (n.eq(2) || n.eq(3) || n.eq(5)){return true;}
        if (n.isEven() || n.isDivisibleBy(3) || n.isDivisibleBy(5)){return false;}
        if (n.lesser(49)){return true;}
        // else
		// we don't know if it's prime: let the other functions figure it out
		// and return 'undefined'
    }
	//	Usage:
	//	console.log(BigInteger.isBasicPrime(new bigInt('47'))); //Usage

    BigInteger.prototype.isPrime = function () {
        var isPrime = isBasicPrime(this);
        if (isPrime !== undefined) return isPrime;
        var n = this.abs(),
            nPrev = n.prev();
        var a = [2, 3, 5, 7, 11, 13, 17, 19],
            b = nPrev,
            d, t, i, x;
        while (b.isEven()) b = b.divide(2);
        for (i = 0; i < a.length; i++) {
            x = bigInt(a[i]).modPow(b, n);
            if (x.eq(Integer[1]) || x.eq(nPrev)) continue;
            for (t = true, d = b; t && d.lesser(nPrev); d = d.multiply(2)) {
                x = x.square().mod(n);
                if (x.eq(nPrev)) t = false;
            }
            if (t) return false;
        }
        return true;
    };
    SmallInteger.prototype.isPrime = BigInteger.prototype.isPrime;
	//	console.log(new BigInteger('47').isPrime()); //Usage

    BigInteger.prototype.isProbablePrime = function (iterations, rng) {
        var isPrime = isBasicPrime(this);
        if (isPrime !== undefined) return isPrime;
        var n = this.abs();
        var t = iterations === undefined ? 5 : iterations;
        // use the Fermat primality test
        for (var i = 0; i < t; i++) {
            var a = bigInt.randBetween(2, n.minus(2), rng);
            if (!a.modPow(n.prev(), n).isUnit()) return false; // definitely composite
        }
        return true; // large chance of being prime
    };
    SmallInteger.prototype.isProbablePrime = BigInteger.prototype.isProbablePrime;
	//	console.log(new BigInteger('47').isPrime()); //Usage

    //Miller-Rabin algorithm implementation for check primality for number
    function Miller_Rabin_prime_check(a, s, d, n){
        var x = a.modPow(d, n);
        //x = pow(a, d, n);
        if(x.eq(1)){return true;}
		var nprev = n.prev();
        for(var step=1;step<=(s-1);step++){
            if(x.eq(nprev)){return true;}
            x = x.modPow(Integer[2], n);
        }
        return (x.eq(nprev));
    }

	var roundsMR = undefined;	//rounds of MillerRabin - global value
	
	var getSetMRrounds = function(setMRrounds){
		var defMRrounds = (setMRrounds || 20);	//set default - setMRrounds rounds or 20, if undefined.
		return (
					( (typeof roundsMR === 'undefined') || (typeof setMRrounds !== 'undefined') )
						? ( roundsMR = defMRrounds, defMRrounds )		    //set defMRrounds rounds globally, and return 20 for k.
						: roundsMR
				)
		;
	}
	//Usage:
	//	BigInteger.getSetMRrounds()		//get current number of rounds or set default, if undefined, and return it.
	//	BigInteger.getSetMRrounds(10)	//set specified number of rounds, save it globally, and return it.

    BigInteger.prototype.MillerRabin = function (
		k	//rounds of MillerRabin
	,	rng //seeded rng
	)
	{
        var isPrime = isBasicPrime(this);
        if (isPrime !== undefined) return isPrime;

        // use the Miller-Rabin primality test
        var a, s, d;
        var n = this.abs();
        var k =	k || getSetMRrounds();			//use k rounds or global value, or set it in k and globally, if undefined.
        if(n.eq(2)){
            return true;
        }
        if(n!==false & n.eq(1)){
            return false;
        }
        s = 0;
        d = n.prev();

        while(d.mod(2).eq(0)){
            d = d.divmod(2)['quotient'];
            s++;
        }

        for(var round=0; round<k; round++){
            a = bigInt.randBetween(2, n.prev(), rng);
            if(!Miller_Rabin_prime_check(a, s, d, n)){return false;}
        }
        return true;
    };
    SmallInteger.prototype.MillerRabin = BigInteger.prototype.MillerRabin;
	//	console.log(new BigInteger('47').MillerRabin()); //Usage

	//PeterOlson's Miller-Rabin
    function millerRabinTest(n, a) {
        var nPrev = n.prev(),
            b = nPrev,
            r = 0,
            d, t, i, x;
        while (b.isEven()) b = b.divide(2), r++;
        next: for (i = 0; i < a.length; i++) {
            if (n.lesser(a[i])) continue;
            x = bigInt(a[i]).modPow(b, n);
            if (x.isUnit() || x.eq(nPrev)) continue;
            for (d = r - 1; d != 0; d--) {
                x = x.square().mod(n);
                if (x.isUnit()) return false;
                if (x.eq(nPrev)) continue next;
            }
            return false;
        }
        return true;
    }
	//MillerRabin full primality check, for logN steps.
    // Set "strict" to true to force GRH-supported lower bound of 2*log(N)^2
    BigInteger.prototype.isPrimeMR = function (strict) {
        var isPrime = isBasicPrime(this);
        if (isPrime !== undefined) return isPrime;
        var n = this.abs();
        var bits = n.bitLength();
        if (bits <= 64)
            return millerRabinTest(n, [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]);
        var logN = Math.log(2) * bits.toJSNumber();
        var t = Math.ceil((strict === true) ? (2 * Math.pow(logN, 2)) : logN);
        for (var a = [], i = 0; i < t; i++) {
            a.push(bigInt(i + 2));
        }
        return millerRabinTest(n, a);
    };
    SmallInteger.prototype.isPrimeMR = BigInteger.prototype.isPrimeMR;
	//	console.log(new BigInteger('47').isPrime()); //Usage
	
	//MillrRabin probablistic primality check: errors = 1/(N^k), where N - is number value, k - number of iterations.
    BigInteger.prototype.isProbablePrimeMR = function (iterations, rng) {
        var isPrime = isBasicPrime(this);
        if (isPrime !== undefined) return isPrime;
        var n = this.abs();
        var t = iterations === undefined ? 5 : iterations;
        for (var a = [], i = 0; i < t; i++) {
            a.push(bigInt.randBetween(2, n.minus(2), rng)); //maybe need to make this odd, or moreover - primes, because primes in array are odd.
        }
        return millerRabinTest(n, a);
    };
    SmallInteger.prototype.isProbablePrimeMR = BigInteger.prototype.isProbablePrimeMR;
	//	console.log(new BigInteger('47').isPrime()); //Usage
	
    BigInteger.prototype.modInv = function (n) {
        var t = bigInt.zero, newT = bigInt.one, r = parseValue(n), newR = this.abs(), q, lastT, lastR;
        while (!newR.eq(0)) {
            q = r.divide(newR);
            lastT = t;
            lastR = r;
            t = newT;
            r = newR;
            newT = lastT.subtract(q.multiply(newT));
            newR = lastR.subtract(q.multiply(newR));
        }
        if (!r.eq(1)) throw new Error(this.toString() + " and " + n.toString() + " are not co-prime");
        if (t.compare(0) === -1) {
            t = t.add(n);
        }
        if (this.isNegative()) {
            return t.negate();
        }
        return t;
    };
    SmallInteger.prototype.modInv = BigInteger.prototype.modInv;

    BigInteger.prototype.next = function (number) {
		if(number === false || number === 0){return this;}
		number = number || 1;
        var value = this.value;
        if (this.sign) {
            return subtractSmall(value, number, this.sign);
        }
        return new BigInteger(addSmall(value, number), this.sign);
    };
    SmallInteger.prototype.next = function (number) {
		if(number === false || number === 0){return this;}
		number = number || 1;
        var value = this.value;
        if (value + number < MAX_INT) return new SmallInteger(value + number);
        return new BigInteger(MAX_INT_ARR, false);
    };

    BigInteger.prototype.prev = function (number) {
		if(number === false || number === 0){return this;}
		number = number || 1;
        var value = this.value;
        if (this.sign) {
            return new BigInteger(addSmall(value, number), true);
        }
        return subtractSmall(value, number, this.sign);
    };
    SmallInteger.prototype.prev = function (number) {
		if(number === false || number === 0){return this;}
		number = number || 1;
        var value = this.value;
        if (value - number > -MAX_INT) return new SmallInteger(value - number);
        return new BigInteger(MAX_INT_ARR, true);
    };

    var powersOfTwo = [1];
    while (2 * powersOfTwo[powersOfTwo.length - 1] <= BASE) powersOfTwo.push(2 * powersOfTwo[powersOfTwo.length - 1]);
    var powers2Length = powersOfTwo.length, highestPower2 = powersOfTwo[powers2Length - 1];

    function shift_isSmall(n) {
        return ((typeof n === "number" || typeof n === "string") && +Math.abs(n) <= BASE) ||
            (n instanceof BigInteger && n.value.length <= 1);
    }

    BigInteger.prototype.shiftLeft = function (n) {
        if (!shift_isSmall(n)) {
            throw new Error(String(n) + " is too large for shifting.");
        }
        n = +n;
        if (n < 0) return this.shiftRight(-n);
        var result = this;
        if (result.isZero()) return result;
        while (n >= powers2Length) {
            result = result.multiply(highestPower2);
            n -= powers2Length - 1;
        }
        return result.multiply(powersOfTwo[n]);
    };
    SmallInteger.prototype.shiftLeft = BigInteger.prototype.shiftLeft;

    BigInteger.prototype.shiftRight = function (n) {
        var remQuo;
        if (!shift_isSmall(n)) {
            throw new Error(String(n) + " is too large for shifting.");
        }
        n = +n;
        if (n < 0) return this.shiftLeft(-n);
        var result = this;
        while (n >= powers2Length) {
            if (result.isZero() || (result.isNegative() && result.isUnit())) return result;
            remQuo = divModAny(result, highestPower2);
            result = remQuo[1].isNegative() ? remQuo[0].prev() : remQuo[0];
            n -= powers2Length - 1;
        }
        remQuo = divModAny(result, powersOfTwo[n]);
        return remQuo[1].isNegative() ? remQuo[0].prev() : remQuo[0];
    };
    SmallInteger.prototype.shiftRight = BigInteger.prototype.shiftRight;

	function PrimeNear(	//return "next" or "prev" prime, near "bi", and check it with "rounds" of MillerRabin.
		bi				//BigInteger number
	,	MRrounds		//rounds of MillerRabin
	,	Next			//Next=true or Next=false (default) for previous prime.
	)
	{
		MRrounds = MRrounds || getSetMRrounds();	//default MillerRabin rounds
		if(bi.isEven()){bi = bi.add( Integer[ ( (Next) ? -1 : 1 ) ] );}		//if even - make odd, else take this odd.
		var isprime = false;							//false on start, even if bi is prime
		while( isprime == false ){							//while false - bi not a prime
            bi = bi.add(Integer[((Next) ? 2 : -2)]);		//prime is odd, so +2 or -2
		    isprime = bi.MillerRabin(MRrounds);				//is "bi" prime?
		}
		return bi; 										//return prev or next prime.
	}

    BigInteger.prototype.nextprime = function (MRrounds) {	// next prime
		MRrounds = MRrounds || getSetMRrounds();			// default MillerRabin rounds
        return PrimeNear(this, MRrounds, true);				// true - next
    };
    SmallInteger.prototype.nextprime = BigInteger.prototype.nextprime;

    BigInteger.prototype.prevprime = function (MRrounds) { 	// previous prime
		MRrounds = MRrounds || getSetMRrounds();			// default MillerRabin rounds
        return PrimeNear(this, MRrounds, false);			// false - prev
    };
    SmallInteger.prototype.prevprime = BigInteger.prototype.prevprime;

    BigInteger.prototype.shiftRight_to_positive = function (n, bitlength) { //equivalent <<<
        var bitlength = (typeof bitlength === 'undefined') ? 32 : bitlength; //if undefined - false, else use this bitlength
        if(this.isNegative() && (bitlength!==false)){
            var ones = bigInt(1).shiftLeft(bitlength).subtract(bigInt(1));
            return ones.add(this).shiftRight(n);
        }else return this.shiftRight(n);
    }
    SmallInteger.prototype.shiftRight_to_positive = BigInteger.prototype.shiftRight_to_positive;
    
    //find whole square root from biggest square.
    BigInteger.prototype.sqrt = function(round) { //return array [√n, difference]
        //round parameter
        //can be a strings:
        //1. 'floor', undefined, or another other value - by default...
        //2. 'ceil' - up rounding
        //3. 'round' - rounding to nearest integer.
        
        var n = this;
        if(n.isNegative()){var err = "Cann't calculate square root from negative number";console.log(err); return false;}
        if(n.isZero()){var err = "Cann't calculate square root from zero, because need to divide by 0!"; return false;}
            //x = √a;        -------->    x^2 = a; x = a/x = x^2/x;
            //x = √0 !== 0; because:     x^2 = 0; x = 0/x = 0/√0.
            //And If √0 = 0; x = 0/0.     And here is null as devisor.
            //Also, 0×x = 0; x = 0/0;     And x can be any one number (Or one great field set of many matrixes, like Universe?)

        var a = bigInt(1);
        var b = n.shiftRight(5).add(bigInt(8));
        var mid;

        while (b.compareTo(a) >= 0) {
            mid = a.add(b).shiftRight(1);
            if (mid.multiply(mid).compareTo(n) > 0) {
                b = mid.subtract(bigInt(1));
            } else {
                a = mid.add(bigInt(1));
            }
        }

        var sqrt;                             //define √n
        if(typeof round !== 'undefined'){    //something round method was been defined
            //What is this?
            if(round==='ceil'){//if 'ceil'
                if(a.subtract(bigInt('1')).pow(bigInt('2')).eq(n)){//if (a-1)^2 === n
                    sqrt = a.subtract(bigInt('1')); //√n = (a-1)
                }
                else{sqrt = a;} //else leave √n as a without decrement.
            }
            else if(round === 'round'){ //nearest whole integer
                //realization round for square root in BigInt (need again calculate root):
                //    1. sqrt = √n;     //default floor
                //    2. 100*n = 100n; //multiply n
                //    3. //10√n = √n * √100 = √(100n) //get 10√n
                //    if((10√n % 10) >= 5){sqrt++;} //round to nearest integer
                
                var n100 = n.multiply(bigInt('100'));
                var sqrt100n_is_10sqrt_n = n100.sqrt();
                if(sqrt100n_is_10sqrt_n[0].mod(bigInt('10')).geq(bigInt('5'))){//if ((√(100n) % 10) >= 5)
                    sqrt = a; ////increment square root from n, just leave incremented.
                }
                else{//if lesser than 5
                    sqrt = a.subtract(bigInt(1)); //floor this, decrement a.
                }
            }
            else{
                sqrt = a.subtract(bigInt(1)); //floor √n by default
            }
        }else{
            sqrt = a.subtract(bigInt(1)); //floor √n by default, decrement a.
        }

        return [sqrt, n.subtract(sqrt.multiply(sqrt))];
        //return array [√n, difference].
        //difference = n - rounded(√n)^2
        //In this case n = sqrt^2 + difference and sqrt^2 is the biggest square, lower n,
        //if floor rounding for root was been by default.        
    }
    SmallInteger.prototype.sqrt = BigInteger.prototype.sqrt;

	// floor(A**(1/n)), ceil and round available too.
	//call this by A.nthRoot(n); where A is bigInt.
	BigInteger.prototype.nthRoot = function (n, rounding) { // bugs - ? (test this!)
		//"rounding" parameter
		//can be a strings:
		//1. 'floor', undefined, or another other value - by default...
		//2. 'ceil' - up rounding
		//3. 'round' - rounding to nearest integer.

		var A = this;
		//Code from here: https://github.com/peterolson/BigInteger.js/issues/146
		//I already have integer logarithm function here

		// https://stackoverflow.com/questions/15978781/how-to-find-integer-nth-roots
		var nthRoot = function (A, n, e) {
			if (e.compareTo(n) < 0) {
				return bigInt(1);
			}
			var q = e.divide(n).divide(bigInt(2));
			var t = bigInt(2).pow(q);
			var x0 = q.compareTo(bigInt(0)) === 0 ? bigInt(4) : t.add(bigInt(1)).multiply(nthRoot(A.divide(t.pow(n)), n, e.subtract(q.multiply(n))));
			var x = x0;
			var xp = x.add(bigInt(1));
			while (x.compareTo(xp) < 0) {
				xp = x;
				var t = A.divide(x.pow(n.subtract(bigInt(1))));
				x = x.multiply(n.subtract(bigInt(1))).add(t).divide(n);
			}
			return xp;
		};
		A = bigInt(A);
		n = bigInt(n);
		if (A.compareTo(bigInt(0)) < 0 || n.compareTo(bigInt(0)) <= 0) {
			throw new RangeError();
		}
		if (A.compareTo(bigInt(0)) === 0) {
			return bigInt(0);
		}
		var e = bigInt(A.integerLogarithm(bigInt(2)).e);
		var x = nthRoot(A, n, e);

		if(typeof rounding !== 'undefined'){
			if(rounding === 'ceil'){
				return x.next();
			}
			else if(rounding === 'round'){
				//10 n√x = n√(10^n)x;
				//(n√(10^n)x % 10 >= 5) ? n_root++ : n_root;
				var n10 = bigInt('10').pow(n);
				var An10 = A.multiply(n10);
				var n_root_An10 = An10.nthRoot(n);
				var last_digit = n_root_An10.mod(bigInt('10'));
				if(last_digit.geq(bigInt('5'))){return x.next()}
				//else return default floor.
			}
			//else return default floor
		}//else return default floor
  
		return x;
		//if x not a whole root, and A not a x.pow(m), you can calculate difference yourself.
	}
    SmallInteger.prototype.nthRoot = BigInteger.prototype.nthRoot; //add this to make function callable.

    function bitwise(x, y, fn) {
        y = parseValue(y);
        var xSign = x.isNegative(), ySign = y.isNegative();
        var xRem = xSign ? x.not() : x,
            yRem = ySign ? y.not() : y;
        var xDigit = 0, yDigit = 0;
        var xDivMod = null, yDivMod = null;
        var result = [];
        while (!xRem.isZero() || !yRem.isZero()) {
            xDivMod = divModAny(xRem, highestPower2);
            xDigit = xDivMod[1].toJSNumber();
            if (xSign) {
                xDigit = highestPower2 - 1 - xDigit; // two's complement for negative numbers
            }

            yDivMod = divModAny(yRem, highestPower2);
            yDigit = yDivMod[1].toJSNumber();
            if (ySign) {
                yDigit = highestPower2 - 1 - yDigit; // two's complement for negative numbers
            }

            xRem = xDivMod[0];
            yRem = yDivMod[0];
            result.push(fn(xDigit, yDigit));
        }
        var sum = fn(xSign ? 1 : 0, ySign ? 1 : 0) !== 0 ? bigInt(-1) : bigInt(0);
        for (var i = result.length - 1; i >= 0; i -= 1) {
            sum = sum.multiply(highestPower2).add(bigInt(result[i]));
        }
        return sum;
    }

    BigInteger.prototype.not = function (bits) {//bits default - undefined
        var bits = (typeof bits === 'undefined') ? false : bits; //if undefined - false, else use this bits
        var negated = this.negate().prev();
        if(bits===false){//if false - return negated
            return negated;    //return (0-N)-1
        }else{
            //if bits was been specified
            if(this.isNegative()){
                return negated = this.abs().subtract(bigInt(1));  //-1 -(-n) = |n| - 1 
            }
            else{
                //2^bits-1 (bits number of one bits)
                var ones = bigInt(1).shiftLeft(bits).subtract(bigInt(1));
                return negated = ones.subtract(this.divmod(bigInt(1).shiftLeft(bits))['remainder']);
            }
        }
    };
    SmallInteger.prototype.not = BigInteger.prototype.not;

    BigInteger.prototype.and = function (n) {
        return bitwise(this, n, function (a, b) { return a & b; });
    };
    SmallInteger.prototype.and = BigInteger.prototype.and;

    BigInteger.prototype.or = function (n) {
        return bitwise(this, n, function (a, b) { return a | b; });
    };
    SmallInteger.prototype.or = BigInteger.prototype.or;

    BigInteger.prototype.xor = function (n) {
        return bitwise(this, n, function (a, b) { return a ^ b; });
    };
    SmallInteger.prototype.xor = BigInteger.prototype.xor;

    var LOBMASK_I = 1 << 30, LOBMASK_BI = (BASE & -BASE) * (BASE & -BASE) | LOBMASK_I;
    function roughLOB(n) { // get lowestOneBit (rough)
        // SmallInteger: return Min(lowestOneBit(n), 1 << 30)
        // BigInteger: return Min(lowestOneBit(n), 1 << 14) [BASE=1e7]
        var v = n.value,
            x = (typeof v === "number")
				?	v | LOBMASK_I
				:	(typeof v === "bigint")
					?	v | BigInt(LOBMASK_I)
					:	v[0] + v[1] * BASE | LOBMASK_BI
			;
        return x & -x;
    }

    BigInteger.prototype.integerLogarithm = function(base) {
        base = bigInt(base);
        if (base.compareTo(this) <= 0) {
            var tmp = this.integerLogarithm(base.square(base));
            var p = tmp.p;
            var e = tmp.e;
            var t = p.multiply(base);
            return t.compareTo(this) <= 0 ? { p: t, e: e * 2 + 1 } : { p: p, e: e * 2 };
        }
        return { p: bigInt(1), e: 0 };
    }
	SmallInteger.prototype.integerLogarithm = BigInteger.prototype.integerLogarithm;

    BigInteger.prototype.bitLength = function () {
        var n = this;
        if (n.compareTo(bigInt(0)) < 0) {
            n = n.negate().subtract(bigInt(1));
        }
        if (n.compareTo(bigInt(0)) === 0) {
            return bigInt(0);
        }
        return bigInt(n.integerLogarithm(bigInt(2)).e).add(bigInt(1));
    }
    SmallInteger.prototype.bitLength = BigInteger.prototype.bitLength;

    function max(a, b) {
        a = parseValue(a);
        b = parseValue(b);
        return a.greater(b) ? a : b;
    }
    function min(a, b) {
        a = parseValue(a);
        b = parseValue(b);
        return a.lesser(b) ? a : b;
    }
    function gcd(a, b) {
        a = parseValue(a).abs();
        b = parseValue(b).abs();
        if (a.eq(b)) return a;
        if (a.isZero()) return b;
        if (b.isZero()) return a;
        var c = Integer[1], d, t;
        while (a.isEven() && b.isEven()) {
            d = min(roughLOB(a), roughLOB(b));
            a = a.divide(d);
            b = b.divide(d);
            c = c.multiply(d);
        }
        while (a.isEven()) {
            a = a.divide(roughLOB(a));
        }
        do {
            while (b.isEven()) {
                b = b.divide(roughLOB(b));
            }
            if (a.greater(b)) {
                t = b; b = a; a = t;
            }
            b = b.subtract(a);
        } while (!b.isZero());
        return c.isUnit() ? a : a.multiply(c);
    }
    function lcm(a, b) {
        a = parseValue(a).abs();
        b = parseValue(b).abs();
        return a.divide(gcd(a, b)).multiply(b);
    }
    function randBetween(a, b, rng) {
		rng = rng || Math.random;
        a = parseValue(a);
        b = parseValue(b);
        var low = min(a, b), high = max(a, b);
        var range = high.subtract(low).add(1);
        if (range.isSmall) return low.add(Math.floor(rng() * range));

        var digits = toBase(BASE, range).value;
        var result = [], restricted = true;
        for (var i = 0; i < digits.length; i++) {
            var top = restricted ? digits[i] : BASE;
            var digit = truncate(rng() * top);
            result.push(digit);
            if (digit < top) restricted = false;
        }
        return low.add(Integer.fromArray(result, BASE, false));
    }

    function get_random_k_bits(
		k	//number of bits
	,	f1	//first bit is 1 or rand (true/false)
	,	rng //seeded rng
	){
		rng = rng || Math.random;
		f1 = ( ( ( typeof f1 === 'undefined') || (f1 === true)) ? true : false ); //default true, and 1-st bit is 1
        var bitstring = '';
        var randbit = ''
        for(i=0;i<k;i++){
            randbit = (Math.floor((rng() * 2))).toString();
            bitstring += ( (i==0 && k!=1 && f1) ? '1' : randbit);
        }
		var randBigInt = bitstring.parseBase(2);
	//	console.log('randBigInt', randBigInt.toString(2));
        return randBigInt;
    }

	//	Encoding/decoding bigIntegers <-> Strings
	var alphabet_36;			//to cache generated alphabet for base up to 36
	var alphabet_32768;			//to cache generated alphabet for base up to 32768
	var alphabet_54617;			//to cache generated alphabet for base up to 54617
	
	var CurrentAlphabet;		//to cache generated alphabet for current base to encoding-decoding BigIntegers.
	
	var custom_minus = "-"; //"-" (45) by default, but can be changed for '—' (8212), for example, using command: BigInteger.custom_minus = char;

	function GenerateBaseAlphabet(	//return specified alphabet, for base, or generate alphabet for base, and return it.
			base					//specify the base for this alphabet.
		,	useAlphabet				//(optional)	specify the alphabet, for base, if this is already defined.
		,	returnSet				//(optional)	set true, to get unique chars, from arbitrary string useAlphabet
	){
		//if alphabet defined, and corresponding the base - return this
		//else - generate this for base 36, 32768, and up to 54621, cache it, and return alphabet for the current base, as substring of this...
		base = base || 10;			//by default, base is 10, or use defined base.
		base = (base instanceof bigInt) ? base.toJSNumber() : base;	//bigint to number, if bigint
		base = (base < 0 && base !== -1) ? Math.abs(base) : base;	//negative base to positive, exclude -1 base
		if(returnSet === true){										//if need to return unique chars
			return Array.from(new Set(useAlphabet)).join('');			//return string with unique chars.
		}
		else if(														//if
				typeof useAlphabet === 'string'							//and useAlphabet is defined string
			&&	useAlphabet.length >= base								//and if base lesser of equal of alphabet.length
			//&&	new Set(useAlphabet).size === useAlphabet.length	//and if all characters are unique
		){
			CurrentAlphabet = useAlphabet;									//do nothing, and leave specified alphabet to return it.
		}
		else{														//else - generate alphabet, and return it.
			if(															//if
					typeof CurrentAlphabet !== 'undefined'					//alphabets are already defined
				&&	CurrentAlphabet.length >= base							//for this base
			){
				if([-1, 0, 1].indexOf(base) !== -1){			//use different alphabets for different base
					CurrentAlphabet = '';
				}else if(base<=36){
					CurrentAlphabet = alphabet_36;
				}
				else if(base<=32768){
					CurrentAlphabet = alphabet_32768;
				}
				else if(base<=54617){
					CurrentAlphabet = alphabet_54617;
				}
				return CurrentAlphabet.substring(0, base);		//and return as substring up to base.
			}

			//else, generate alphabet, and return it.
			var s = '';
			if(															//if
					base === 0												//base 0
				||	base === 1												//or base 1
				||	base === -1												//or base -1
			){
				s = '';														//empty alphabet for base 0, 1, -1
			}
			else if(
						( ( 2 <= base ) && ( base <= 36 ) )					//if base from 2 up to 36
					||	( base > 54617 )									//or if base is higher than 54617 (to make compatible with high base...)
			){							//if base from 2 up to 36
				if(typeof alphabet_36 === 'undefined'){
					for(var i = 0; i<36; i++){
						s += i.toString(36);								//generate alphabet_36, if undefined
					}
					//"0123456789abcdefghijklmnopqrstuvwxyz";
					alphabet_36 = s;										//cache alphabet for maxbase 36
				}
				s = alphabet_36.substring(0, base);							//or/and use substring for base, to return it
			}
			else if(36 < base && base <= 32768){						//if base from 37 up to 32768 - use alphabet_32768, with 32768 printable characters.
				if(		typeof alphabet_32768 === 'undefined'				//if undefined - generate alphabet for maximal base
					||	alphabet_32768.length !== 32768
				){
					//	Generate an "alphabet_32768" to encode and decode, the numbers <-> strings, with base up to 32768
					//	All characters in this string, are printable, and copyable. 
					for(var i=0; i<32768; ++i){
						//	Will be used BigInteger."custom_minus" = char; to mark encoded negative numbers. You can set it yourself, or "-" (45), by default.
						if			(	i>=0		&&	i<25		){	s	+=	String.fromCharCode	(	i	+13144	);	}	//[	13144	-	13168	]
						else if		(	i>=25		&&	i<51		){	s	+=	String.fromCharCode	(	i	+40		);	}	//[	65		-	90		]
						else if		(	i>=51		&&	i<77		){	s	+=	String.fromCharCode	(	i	+46		);	}	//[	97		-	122		]
						else if		(	i>=77		&&	i<86		){	s	+=	String.fromCharCode	(	i	-28		);	}	//[	49		-	57		]
						else if		(	i>=86		&&	i<87		){	s	+=	String.fromCharCode	(	i	-38		);	}	//[	48					]
						else if		(	i>=87		&&	i<226		){	s	+=	String.fromCharCode	(	i	+9225	);	}	//[	9312	-	9450	]
						else if		(	i>=226		&&	i<244		){	s	+=	String.fromCharCode	(	i	+19778	);	}	//[	20004	-	20021	]
						else if		(	i>=244		&&	i<300		){	s	+=	String.fromCharCode	(	i	+19779	);	}	//[	20023	-	20078	]
						else if		(	i>=300		&&	i<400		){	s	+=	String.fromCharCode	(	i	+19804	);	}	//[	20104	-	20203	]
						else if		(	i>=400		&&	i<21065		){	s	+=	String.fromCharCode	(	i	+19805	);	}	//[	20205	-	40869	]
						else if		(	i>=21065	&&	i<32237		){	s	+=	String.fromCharCode	(	i	+22967	);	}	//[	44032	-	55203	]
						else if		(	i>=32237	&&	i<32539		){	s	+=	String.fromCharCode	(	i	+31507	);	}	//[	63744	-	64045	]
						else if		(	i>=32539	&&	i<32575		){	s	+=	String.fromCharCode	(	i	-19707	);	}	//[	12832	-	12867	]
						else if		(	i>=32575	&&	i<32603		){	s	+=	String.fromCharCode	(	i	-19774	);	}	//[	12801	-	12828	]
						else if		(	i>=32603	&&	i<32631		){	s	+=	String.fromCharCode	(	i	-19707	);	}	//[	12896	-	12923	]
						else if		(	i>=32631	&&	i<32681		){	s	+=	String.fromCharCode	(	i	-19704	);	}	//[	12927	-	12976	]
						else if		(	i>=32681	&&	i<32693		){	s	+=	String.fromCharCode	(	i	-19689	);	}	//[	12992	-	13003	]
						else if		(	i>=32693	&&	i<32740		){	s	+=	String.fromCharCode	(	i	-19685	);	}	//[	13008	-	13054	]
						else if		(	i>=32740	&&	i<32745		){	s	+=	String.fromCharCode	(	i	-19684	);	}	//[	13056	-	13060	]
						else if		(	i>=32745	&&	i<32767		){	s	+=	String.fromCharCode	(	i	-0x317a	);	}	//[	20079	-	20100	]
						else if		(	i<32768						){	s	+=	String.fromCharCode	(	i	-12563	);	}	//[	20204				]
					}
					s = s.replace(new RegExp(custom_minus, "g"), '');				//remove "custom_minus" char
					alphabet_32768 = s;												//cache an alphabet for max base 32768
				}
				s = alphabet_32768.substring(0, base);							//or/and use substring for base, to return it
			}else if(32768 < base && base<=54617){							//if base up to 54617
				if(
						typeof alphabet_54617 === 'undefined'
					||	alphabet_54617.length !== 54617
				){																//if undefined - generate alphabet for maximal base
					var re = /[\"\\ \xA0\0-\x1F\x7F-\x9F\xAD\u0378\u0379\u037F-\u0383\u038B\u038D\u03A2\u0528-\u0530\u0557\u0558\u0560\u0588\u058B-\u058E\u0590\u05C8-\u05CF\u05EB-\u05EF\u05F5-\u0605\u061C\u061D\u06DD\u070E\u070F\u074B\u074C\u07B2-\u07BF\u07FB-\u07FF\u082E\u082F\u083F\u085C\u085D\u085F-\u089F\u08A1\u08AD-\u08E3\u08FF\u0978\u0980\u0984\u098D\u098E\u0991\u0992\u09A9\u09B1\u09B3-\u09B5\u09BA\u09BB\u09C5\u09C6\u09C9\u09CA\u09CF-\u09D6\u09D8-\u09DB\u09DE\u09E4\u09E5\u09FC-\u0A00\u0A04\u0A0B-\u0A0E\u0A11\u0A12\u0A29\u0A31\u0A34\u0A37\u0A3A\u0A3B\u0A3D\u0A43-\u0A46\u0A49\u0A4A\u0A4E-\u0A50\u0A52-\u0A58\u0A5D\u0A5F-\u0A65\u0A76-\u0A80\u0A84\u0A8E\u0A92\u0AA9\u0AB1\u0AB4\u0ABA\u0ABB\u0AC6\u0ACA\u0ACE\u0ACF\u0AD1-\u0ADF\u0AE4\u0AE5\u0AF2-\u0B00\u0B04\u0B0D\u0B0E\u0B11\u0B12\u0B29\u0B31\u0B34\u0B3A\u0B3B\u0B45\u0B46\u0B49\u0B4A\u0B4E-\u0B55\u0B58-\u0B5B\u0B5E\u0B64\u0B65\u0B78-\u0B81\u0B84\u0B8B-\u0B8D\u0B91\u0B96-\u0B98\u0B9B\u0B9D\u0BA0-\u0BA2\u0BA5-\u0BA7\u0BAB-\u0BAD\u0BBA-\u0BBD\u0BC3-\u0BC5\u0BC9\u0BCE\u0BCF\u0BD1-\u0BD6\u0BD8-\u0BE5\u0BFB-\u0C00\u0C04\u0C0D\u0C11\u0C29\u0C34\u0C3A-\u0C3C\u0C45\u0C49\u0C4E-\u0C54\u0C57\u0C5A-\u0C5F\u0C64\u0C65\u0C70-\u0C77\u0C80\u0C81\u0C84\u0C8D\u0C91\u0CA9\u0CB4\u0CBA\u0CBB\u0CC5\u0CC9\u0CCE-\u0CD4\u0CD7-\u0CDD\u0CDF\u0CE4\u0CE5\u0CF0\u0CF3-\u0D01\u0D04\u0D0D\u0D11\u0D3B\u0D3C\u0D45\u0D49\u0D4F-\u0D56\u0D58-\u0D5F\u0D64\u0D65\u0D76-\u0D78\u0D80\u0D81\u0D84\u0D97-\u0D99\u0DB2\u0DBC\u0DBE\u0DBF\u0DC7-\u0DC9\u0DCB-\u0DCE\u0DD5\u0DD7\u0DE0-\u0DF1\u0DF5-\u0E00\u0E3B-\u0E3E\u0E5C-\u0E80\u0E83\u0E85\u0E86\u0E89\u0E8B\u0E8C\u0E8E-\u0E93\u0E98\u0EA0\u0EA4\u0EA6\u0EA8\u0EA9\u0EAC\u0EBA\u0EBE\u0EBF\u0EC5\u0EC7\u0ECE\u0ECF\u0EDA\u0EDB\u0EE0-\u0EFF\u0F48\u0F6D-\u0F70\u0F98\u0FBD\u0FCD\u0FDB-\u0FFF\u10C6\u10C8-\u10CC\u10CE\u10CF\u1249\u124E\u124F\u1257\u1259\u125E\u125F\u1289\u128E\u128F\u12B1\u12B6\u12B7\u12BF\u12C1\u12C6\u12C7\u12D7\u1311\u1316\u1317\u135B\u135C\u137D-\u137F\u139A-\u139F\u13F5-\u13FF\u169D-\u169F\u16F1-\u16FF\u170D\u1715-\u171F\u1737-\u173F\u1754-\u175F\u176D\u1771\u1774-\u177F\u17DE\u17DF\u17EA-\u17EF\u17FA-\u17FF\u180F\u181A-\u181F\u1878-\u187F\u18AB-\u18AF\u18F6-\u18FF\u191D-\u191F\u192C-\u192F\u193C-\u193F\u1941-\u1943\u196E\u196F\u1975-\u197F\u19AC-\u19AF\u19CA-\u19CF\u19DB-\u19DD\u1A1C\u1A1D\u1A5F\u1A7D\u1A7E\u1A8A-\u1A8F\u1A9A-\u1A9F\u1AAE-\u1AFF\u1B4C-\u1B4F\u1B7D-\u1B7F\u1BF4-\u1BFB\u1C38-\u1C3A\u1C4A-\u1C4C\u1C80-\u1CBF\u1CC8-\u1CCF\u1CF7-\u1CFF\u1DE7-\u1DFB\u1F16\u1F17\u1F1E\u1F1F\u1F46\u1F47\u1F4E\u1F4F\u1F58\u1F5A\u1F5C\u1F5E\u1F7E\u1F7F\u1FB5\u1FC5\u1FD4\u1FD5\u1FDC\u1FF0\u1FF1\u1FF5\u1FFF\u200B-\u200F\u202A-\u202E\u2060-\u206F\u2072\u2073\u208F\u209D-\u209F\u20BB-\u20CF\u20F1-\u20FF\u218A-\u218F\u23F4-\u23FF\u2427-\u243F\u244B-\u245F\u2700\u2B4D-\u2B4F\u2B5A-\u2BFF\u2C2F\u2C5F\u2CF4-\u2CF8\u2D26\u2D28-\u2D2C\u2D2E\u2D2F\u2D68-\u2D6E\u2D71-\u2D7E\u2D97-\u2D9F\u2DA7\u2DAF\u2DB7\u2DBF\u2DC7\u2DCF\u2DD7\u2DDF\u2E3C-\u2E7F\u2E9A\u2EF4-\u2EFF\u2FD6-\u2FEF\u2FFC-\u2FFF\u3040\u3097\u3098\u3100-\u3104\u312E-\u3130\u318F\u31BB-\u31BF\u31E4-\u31EF\u321F\u32FF\u4DB6-\u4DBF\u9FCD-\u9FFF\uA48D-\uA48F\uA4C7-\uA4CF\uA62C-\uA63F\uA698-\uA69E\uA6F8-\uA6FF\uA78F\uA794-\uA79F\uA7AB-\uA7F7\uA82C-\uA82F\uA83A-\uA83F\uA878-\uA87F\uA8C5-\uA8CD\uA8DA-\uA8DF\uA8FC-\uA8FF\uA954-\uA95E\uA97D-\uA97F\uA9CE\uA9DA-\uA9DD\uA9E0-\uA9FF\uAA37-\uAA3F\uAA4E\uAA4F\uAA5A\uAA5B\uAA7C-\uAA7F\uAAC3-\uAADA\uAAF7-\uAB00\uAB07\uAB08\uAB0F\uAB10\uAB17-\uAB1F\uAB27\uAB2F-\uABBF\uABEE\uABEF\uABFA-\uABFF\uD7A4-\uD7AF\uD7C7-\uD7CA\uD7FC-\uF8FF\uFA6E\uFA6F\uFADA-\uFAFF\uFB07-\uFB12\uFB18-\uFB1C\uFB37\uFB3D\uFB3F\uFB42\uFB45\uFBC2-\uFBD2\uFD40-\uFD4F\uFD90\uFD91\uFDC8-\uFDEF\uFDFE\uFDFF\uFE1A-\uFE1F\uFE27-\uFE2F\uFE53\uFE67\uFE6C-\uFE6F\uFE75\uFEFD-\uFF00\uFFBF-\uFFC1\uFFC8\uFFC9\uFFD0\uFFD1\uFFD8\uFFD9\uFFDD-\uFFDF\uFFE7\uFFEF-\uFFFB\uFFFE\uFFFF\uFFFD]/g; //non-printable chars, which can not be displayed or copied.
					for(var i=0; i<65536; i++){s += String.fromCharCode(i);} s = s.replace(re, ""); //s.length = 54621 printable and copyable characters with codes in range 0000-ffff
					s = s	.replace(new RegExp( ( '[' +'\''+'\"'+'\\'+( custom_minus + "<" + ">") + ']' ) , "g" ), '' );
					//exclude "custom_minus", reserver for negative numbers, and "<", and ">" - reserved for higher base, and "'" with '"' (need to add backslash there.)
					//console.log('s.length', s.length);	//s.length = 54617
					alphabet_54617 = s;												//cache alphabet for max base 54617
				}
				s = alphabet_54617.substring(0, base);							//or/and use substring for base, to return it
			}
			CurrentAlphabet = s;											//cache CurrentAlphabet for this base
		}
		return CurrentAlphabet;											//and return the CurrentAlphabet.
	}

	var parseBaseToArray = function(base, alphabet, caseSensitive, text){ //decode string with base, by alphabet, to Object with array with digits up to base.
		base = base || 10;
		text = text || this; //"this" can be String or undefined - then "text". Use "text", or "this".

//		alphabet = alphabet || DEFAULT_ALPHABET;
		alphabet = GenerateBaseAlphabet(base, alphabet); //generate alphabet or use defined

		//start generate array with digits up to base
        text = String(text);
        if (
				caseSensitive !== undefined										//if defined, because (!undefined === true)
				&& !caseSensitive												//and if not sencetive for the case
				&&	(new Set(alphabet.toLowerCase()).size === alphabet.length)	//and if all lower-cased characters are unique
		){	text = text.toLowerCase(); alphabet = alphabet.toLowerCase(); } 	//to LowerCase the text, and alphabet

        var i;
        var absBase = Math.abs(base);


		//if(!(new RegExp("^["+"-"+"<"+">"+alphabet+"]+$")).test(text)){	//test allowed chars in text, and if fail - show invalid char:
	//This sometimes show Error: "RegExp too big", for large alphabets. Disable this.
			for (i = 0; i < text.length; i++) {		//for each char
				var c = text[i];					//in text
				if (	c === custom_minus			//if minus
					||	c === "<"					//or if "<"
					||	c === ">"					//or if ">"
				){continue;}							//skip this
				var index = alphabet.indexOf(c);								//get index
				if (index !== -1) {												//and if char found
					if (index >= absBase) {											//and if char have large index
						if (c === "0" && absBase === 0) continue;						//do nothing, for base 0
						if (c === "1" && absBase === 1) continue;						//do nothing, for base 1 and -1
						throw new Error("\""+c+"\"" + " with charcode " +c.charCodeAt(0)+
						" is not a valid digit in base " + base + "."); 				//or show invalid char
					}
				}else{															//else if char not found in alphabet
					if (c === "0" && absBase === 0) continue;							//do nothing, for base 0
					if ((c === "1" || c === "0") && absBase === 1) continue;			//do nothing, for base 1 and -1
					throw new Error("\""+c+"\"" + " with charcode " +c.charCodeAt(0)+
					" is not found in alphabet: "+alphabet+" for base "+base); 									//show invalid char
				}
			}
		//}
        base = parseValue(base); //value of base

		//start generate array with digits...
        var digits = [];
        var isNegative = (text[0] === custom_minus);
        for (i = ( isNegative ?1 :0 ); i < text.length; i++) {
            var c = text[i];
			if (c === "<") {
                var start = i;
                do { i++; } while (text[i] !== ">");
					digits.push(text.slice(start + 1, i));
            }else{
				var index = alphabet.indexOf(c);
				if (index !== -1){digits.push(index.toString());}
				else if(c === '1' || c === '0'){digits.push(c)}
				else throw new Error(c + " is not a valid character");
			}
        }
		//end generate array with digits up to base
		return { value: digits, isNegative: isNegative }; //return Object
	}
	Integer.parseBaseToArray = String.prototype.parseBaseToArray = parseBaseToArray; //Method for String, or for BigInteger
	//Usage:
	//console.log(BigInteger.parseBaseToArray(36, undefined, undefined, 'base36textstring'));	// as BigInteger-function with undefined for undefined values, and "srring" in 4-th param
	//console.log('base36textstring'.parseBaseToArray(36));										// as from "string", with base (+ optional params);
	
    var parseBase = function (base, alphabet, caseSensitive, text) { //decode text string into array with digits up to base -> and to BigInteger it.
		text = text || this; //use text, or this if "text" is undefined.
		var objArrDigits = text.parseBaseToArray(base, alphabet, caseSensitive, text);
        return parseBaseFromArray(base, objArrDigits); //and decode array with digits up to base - into bigInteger.
    };
	Integer.parseBase = String.prototype.parseBase = parseBase; //Method for String or for BigInteger
	//Usage:
	//console.log(BigInteger.parseBase(36, undefined, undefined, 'base36textstring'));		// as BigInteger-function with undefined for undefined values, and "srring" in 4-th param
	//console.log('base36textstring'.parseBase(36));										// as from "string", with base (+ optional params);

    var parseBaseFromArray = function(base, digitsOrNegative) { //Object or array -> to BigInteger, with base.
		//Last parameter is optional - object or isNegative (if this is an Array with digits up to base).
		var digits, isNegative;
		if(typeof digitsOrNegative === 'boolean'){isNegative = digitsOrNegative; digits = this;} //if second is true/false when "this" is an Array
		else{
			digits = digitsOrNegative || this; //use optional "object" with isNegative, or "this"
		}
		if(((digits instanceof Object) && !(digits instanceof Array))){	//if digits not an Array, but Object
			isNegative = digits.isNegative;	//extract this value
			digits = digits.value;			//and replace object to array from this
		}
		//parse BigInteger, from array.
        var val = Integer[0], pow = Integer[1], i;
        for (i = digits.length - 1; i >= 0; i--) {
            val = val.add(bigInt(digits[i]).times(pow));
            pow = pow.times(base);
        }
        return isNegative ? val.negate() : val; //and return bigInt +-
    }
	Integer.parseBaseFromArray = Object.prototype.parseBaseFromArray = Array.prototype.parseBaseFromArray = parseBaseFromArray; //array or object, or bigInt-method.
	//Usage:
	//console.log(BigInteger.parseBaseFromArray(36, JSON.parse('{"value": [1,2,3,4], "isNegative": true}')));		// as BigInteger-function, with base and object
	//console.log(Object.parseBaseFromArray(36, JSON.parse('{"value": [1,2,3,4], "isNegative": true}')));			// as Object-function, with base and object
	//console.log(Array.parseBaseFromArray(36, JSON.parse('{"value": [1,2,3,4], "isNegative": true}')));			// as Array-function, with base and object
	//console.log((JSON.parse('{"value": [1,2,3,4], "isNegative": true}')).parseBaseFromArray(36));					// as method of object, with base
	//console.log(([1,2,3,4]).parseBaseFromArray(36, true));														// as method for array with digits up to base, with base, and negative flag.

    function stringify(digit, alphabet) { //one digit to one char
		alphabet = alphabet || DEFAULT_ALPHABET;
		//return one digit from one char in alphabet, or string "<base>", if base is higher than alphabet.length	
        return ( (digit < alphabet.length) ? alphabet[digit] : ( "<" + digit + ">" ) );
    }

    var toBase = function (base, n) { //convert bigInt "n" to array with digits, up to base.
		n = bigInt(n || this);
        base = bigInt(base || 10);
        if (base.isZero()) {
            if (n.isZero()) return { value: ['0'], isNegative: false };
            else{
                console.log("Cannot convert nonzero numbers to base 0. Number: "+n.toString()+". 0 returned.");
                return {value: [0], isNegative: false}
            }
        }
        if (base.eq(-1)) {
            if(n.abs().geq(bigInt('100000'))){
                console.log(" For base -1, repeats of [1,0] have to many times (for value bigInt over 100000).\n",
                "You can see 'Uncaught RangeError: Maximum call stack size exceeded, for higher value of bigInt'\n",
                "So just zero was ben returned for bigInt "+n.toString());
                return {value: [0], isNegative: false};
            }
            if (n.isZero()) return { value: ['0'], isNegative: false };
            if (n.isNegative())
                return {
                    value: [].concat.apply([], Array.apply(null, Array(-n.toJSNumber()))
                        .map(Array.prototype.valueOf, ['1', '0'])
                    ),
                    isNegative: false
                };

            var arr = Array.apply(null, Array(n.toJSNumber() - 1))
                .map(Array.prototype.valueOf, ['0', '1']);
            arr.unshift(['1']);
            return {
                value: [].concat.apply([], arr),
                isNegative: false
            };
        }

        var neg = false;
        if (n.isNegative() && base.isPositive()) {
            neg = true;
            n = n.abs();
        }
        if (base.eq(1)) {
            if(n.abs().geq(bigInt('100000'))){
                console.log(" For base 1, repeats of [1] have to many times (for value bigInt over 100000).\n",
                "You can see 'Uncaught RangeError: Maximum call stack size exceeded, for higher value of bigInt'\n",
                "So just zero was ben returned for bigInt "+n.toString());
                return {value: [0], isNegative: false};
            }
            if (n.isZero()) return { value: ['0'], isNegative: false };

            return {
                value: Array.apply(null, Array(n.toJSNumber()))
                    .map(Number.prototype.toString, 1),
                isNegative: neg
            };
        }
        var out = [];
        var left = n, divmod;
        while (left.isNegative() || left.compareAbs(base) >= 0) {
            divmod = left.divmod(base);
            left = divmod.quotient;
            var digit = divmod.remainder;
            if (digit.isNegative()) {
                digit = base.minus(digit).abs();
                left = left.next();
            }
            out.push(digit.toString());
        }
        out.push(left.toString());
        return { value: out.reverse(), isNegative: neg };
    }
    Integer.toArray = BigInteger.prototype.toArray = SmallInteger.prototype.toArray = Number.prototype.toArray = toBase; //bigInt-method, or (bigInt/SmallInt).toArray(radix)
	//Usage:
	//console.log(BigInteger.toArray(36, new BigInteger('100500')));	// as BigInteger-function, with base and bigint
	//console.log(BigInteger.toArray(36, 100500));						// as BigInteger-function, with base and int
	//console.log((bigInt('100500')).toArray(36));						// as function for bigint, with base
	//console.log((100500).toArray(36));								// as Number-function, with base
	//console.log(JSON.stringify((100500).toArray(36)));				// object with array -> toJSON-string

    var toBaseString = function (base, alphabet, n) {					//BigInteger -> to chars, or object with array with digits up to base -> to chars
		n = bigInt(n || this);													//if optional parameter n is not specified, use this.
        var obj = 	(													//BigInteger -> to object, with Array with digits bi.toArray(base);
					((n instanceof Object) && !(n instanceof bigInt))	//if n is already an object with array with digits up to base, and not a bigInt
						? n												//use it
						: toBase(base, n)								//or get object with array with digits up to base, from bigInt n
				)
		;
		alphabet = GenerateBaseAlphabet(base, alphabet);											//select generate alphabet for base, or use defined alphabet;
		for(var i = 0, s = ''; i<obj.value.length; i++){s += stringify(obj.value[i], alphabet);}	//arr digits -> to string with chars from alphabet or <base>
		return ( ( (obj.isNegative === true) ? custom_minus : "" ) + s );							//and return it with/out "-".
    }
	//BigInt or Object with array with digits up to base -> to string with chars.
	Integer.toBaseString = BigInteger.prototype.toBaseString = SmallInteger.prototype.toBaseString = Object.prototype.toBaseString = Number.prototype.toBaseString = toBaseString;
	//Usage:
	//console.log(BigInteger.toBaseString(36, undefined, 100500));				// as BigInteger-function, with base, undefined alphabet, and number.
	//console.log(Object.toBaseString(36, undefined, bigInt('100500')));		// as Object-function, with base, undefined alphabet, and bigint
	//console.log((new bigInt('100500')).toBaseString(36));						// as bigInt-function, with base
	//console.log(JSON.parse('{"value":["2","5","19","24"],"isNegative":false}').toBaseString(36, "0123456789abcdefghijklmnopqrstuvwxyz"));	// as object-function, with base alphabet (if defined)

    var toString = function (radix, alphabet, n) {		//"BigInteger" -> to string with chars from "alphabet" for "base"
		n = bigInt(n || this);	//use optional "n" or this;
		if (radix === undefined) radix = 10;
        if (radix !== 10) return toBaseString(radix, alphabet, n);
		if(typeof n.value === 'number') return String(n.value); //one value in arr for SmallInteger.
        var v = n.value, l = v.length, str = String(v[--l]), zeros = "0000000", digit;
        while (--l >= 0) {
            digit = String(v[l]);
            str += zeros.slice(digit.length) + digit;
        }
        var sign = n.sign ? custom_minus : "";
        return sign + str;
    };
	Integer.toString = BigInteger.prototype.toString = SmallInteger.prototype.toString = Number.prototype.EncodeIt = toString;
	//Usage:
	//console.log(BigInteger.toString(36, undefined, 100500));		// as BigInteger-Function with Base, undefined alphabet, and number
	//console.log(BigInteger.toString(36, undefined, '100500'));	// as BigInteger-Function with Base, undefined alphabet, and string-number
	//console.log((new bigInt('100500')).toString(16));				// as bigint-Function with Base
	//console.log((new bigInt('100500')).toString(3, "abc"));		// as bigint-Function with Base, and some specified alphabet
	//console.log((100500).EncodeIt(3, "abc"));					// as Number-Function with Base, and some specified alphabet

    Integer.toNativeBigInt = BigInteger.prototype.toNativeBigInt = SmallInteger.prototype.toNativeBigInt = Number.prototype.toNativeBigInt
	Integer.toNative = BigInteger.prototype.toNative = SmallInteger.prototype.toNative = Number.prototype.toNative
	Integer.TOn = BigInteger.prototype.TOn = SmallInteger.prototype.TOn = Number.prototype.TOn
	= function (val) { return eval(bigInt(val||this).toString()+'n'); }	//to native bigint in form 123n
	//Usage:
	//console.log((new BigInteger('100500')).TOn()); 	//BigInteger to native-bigint;
	//console.log((100500).TOn()); 						//Number to native-bigint;
	//console.log(BigInteger.TOn('100500')); 			//String to native-bigint;

	BigInteger.prototype.toJSON = SmallInteger.prototype.toJSON = function(base){
		 //Use this as JSON.stringify(bigInt), or JSON.stringify(object with bigints): {"key1": bigInt1, "key2", bigInt2}
		return this.toString((typeof base === 'number') ? base : undefined); //base as number or default '10' and not a key;
	}
	//Usage:
	//console.log(JSON.stringify(RSABigInteger.RSA_key));		//Object with bigInts
	//console.log(JSON.stringify(new BigInteger('100500')));	//bigInt to JSON, using JSON.stringify
	//console.log((new BigInteger('100500')).toJSON());			//bigint.toJSON() as string with default base
	//console.log((new BigInteger('100500')).toJSON(100));		//bigint.toJSON() as string with base 100

	String.prototype.fromJSON = Object.prototype.fromJSON = function(){var x = JSON.parse(this); console.log('x', x);}

    BigInteger.prototype.valueOf = function () {
        return parseInt(this.toString(), 10);
    };
    BigInteger.prototype.toJSNumber = BigInteger.prototype.valueOf;

    SmallInteger.prototype.valueOf = function () {
        return this.value;
    };
    SmallInteger.prototype.toJSNumber = SmallInteger.prototype.valueOf;

    function parseStringValue(v) {
        if (isPrecise(+v)) {
            var x = +v;
            if (x === truncate(x))
                return new SmallInteger(x);
            throw new Error("Invalid integer: " + v);
        }
        var sign = v[0] === custom_minus;
        if (sign) v = v.slice(1);
        var split = v.split(/e/i);
        if (split.length > 2) throw new Error("Invalid integer: " + split.join("e"));
        if (split.length === 2) {
            var exp = split[1];
            if (exp[0] === "+") exp = exp.slice(1);
            exp = +exp;
            if (exp !== truncate(exp) || !isPrecise(exp)) throw new Error("Invalid integer: " + exp + " is not a valid exponent.");
            var text = split[0];
            var decimalPlace = text.indexOf(".");
            if (decimalPlace >= 0) {
                exp -= text.length - decimalPlace - 1;
                text = text.slice(0, decimalPlace) + text.slice(decimalPlace + 1);
            }
            if (exp < 0) throw new Error("Cannot include negative exponent part for integers");
            text += (new Array(exp + 1)).join("0");
            v = text;
        }
        var isValid = /^([0-9][0-9]*)$/.test(v);
        if (!isValid) throw new Error("Invalid integer: " + v);
        var r = [], max = v.length, l = LOG_BASE, min = max - l;
        while (max > 0) {
            r.push(+v.slice(min, max));
            min -= l;
            if (min < 0) min = 0;
            max -= l;
        }
        trim(r);
        return new BigInteger(r, sign);
    }

    function parseNumberValue(v) {
        if (isPrecise(v)) {
            if (v !== truncate(v)) throw new Error(v + " is not an integer.");
            return new SmallInteger(v);
        }
        return parseStringValue(v.toString());
    }

    function parseValue(v) {
        if (typeof v === "number") {
            return parseNumberValue(v);
        }
        if (typeof v === "string") {
            return parseStringValue(v);
        }
		if(typeof v === 'bigint'){	//if bigint, in form 123n
            return parseStringValue(v.toString()); //bigint.toString() -> and parse this string.
		}
        return v;
    }

    // Pre-define numbers in range [-999,999]
    for (var i = 0; i < 1000; i++) {
        Integer[i] = parseValue(i);
        if (i > 0) Integer[-i] = parseValue(-i);
    }
    // Backwards compatibility
    Integer.one								=	Integer[1];
    Integer.two								=	Integer[2];
    Integer.zero	=	Integer.null		=	Integer[0];
    Integer.minusOne						=	Integer[-1];
    Integer.max								=	max;
    Integer.min								=	min;
    Integer.gcd								=	gcd;
    Integer.lcm								=	lcm;
    Integer.isInstance						=	function (x) { return x instanceof BigInteger || x instanceof SmallInteger; };
    Integer.randBetween						=	randBetween;								//randBetween(a, b, rng)
    Integer.randbits						=	get_random_k_bits;
    Integer.getSetMRrounds					=	getSetMRrounds;								//getSetMRrounds() or getSetMRrounds(rounds) - get or set the value of rounds MillerRabin, to check primality for prime numbers.
    Integer.isBasicPrime 					=	isBasicPrime;
    Integer.alphabet 						=									 //Access to alphabet ans show it, or set it, or generate it by base: BigInteger.alphabet(base)
		function(baseOrAlphabet){
			if(typeof baseOrAlphabet === 'undefined'){
				return CurrentAlphabet;
			} else if(typeof baseOrAlphabet === 'string'){
				CurrentAlphabet = Array.from(new Set(baseOrAlphabet)).join('');
				return CurrentAlphabet;
			}
			else if(
					typeof baseOrAlphabet === 'number'
				||	baseOrAlphabet instanceof bigInt
			) {
				return GenerateBaseAlphabet(baseOrAlphabet);
			}
		}
	;

    Integer.custom_minus					=	custom_minus;	//cusomize char "-" for encoding-decoding the negative numbers.
    Integer.GenerateBaseAlphabet			=	GenerateBaseAlphabet;	//GenerateBaseAlphabet(base, useAlphabet, returnSet) - Generate and return alphabet for base. Alphabet is optional param, to check and return it, without generate.

    Integer.fromArray = function (digits, base, isNegative){ //digits, can be also an object from "toBase(n, base)" or "big.toArray(radix)"
		if((digits instanceof Object) && !(digits instanceof Array)){ //if digits is object and not an array (because, Array is an Object too)
			isNegative	=	digits.isNegative;	//set this value from object
			digits		=	digits.value;		//and replace object on an array from object
		}
		return (digits.map(parseValue)).parseBaseFromArray(parseValue(base || 10), isNegative); //decode array with base into +-bigint, and return it.
    };

    return Integer;
})();

// Node.js check
if (typeof module !== "undefined" && module.hasOwnProperty("exports")) {
    module.exports = bigInt;
}

//amd check
if (typeof define === "function" && define.amd) {
    define( function () {
        return bigInt;
    });
}
