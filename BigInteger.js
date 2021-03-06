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

    var isBasicPrime = function(v) { //v is optional bigint, when "this" is not bigint.
        var n = (bigInt(v || this)).abs();
        if (n.eq(0) || n.eq(1)){return false;}
        if (n.eq(2) || n.eq(3) || n.eq(5)){return true;}
        if (n.isEven() || n.isDivisibleBy(3) || n.isDivisibleBy(5)){return false;}
        if (n.lesser(49)){return true;}
        // else
		// we don't know if it's prime: let the other functions figure it out
		// and return 'undefined'
    }
	Integer.isBasicPrime = SmallInteger.prototype.isBasicPrime = BigInteger.prototype.isBasicPrime = Number.prototype.isBasicPrime = isBasicPrime;
	//	Usage:
	//	console.log(BigInteger.isBasicPrime(new bigInt('47')));		// as BigInteger-function, with bigInt
	//	console.log(BigInteger.isBasicPrime(47));					// as BigInteger-function, with number
	//	console.log((new bigInt(47)).isBasicPrime());				// as function for BigInteger or SmallInteger
	//	console.log((47).isBasicPrime());							// as function for Number

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
    var isPrime = function (strict, n) { //n is optional bigint or number, when "this" is not bigint.
		n = bigInt(n || this);
        var isPrime = isBasicPrime(n);
        if (isPrime !== undefined) return isPrime;
        var n = n.abs();
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
    Integer.isPrime = SmallInteger.prototype.isPrime = BigInteger.prototype.isPrime = Number.prototype.isPrime = isPrime;
	//	Usage:
	//	console.log(BigInteger.isPrime(false, '47'));	// as BigInteger-function with string-number
	//	console.log((bigInt(47)).isPrime(true));		// for bigInt, with strict only
	//	console.log(new BigInteger('47').isPrime());	// for new BigInteger
	//	console.log((47).isPrime(true));				// as Number-function
	
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

	//MillerRabin probablistic primality check: errors = 1/(N^k), where N - is number value, k - number of iterations.
    var MillerRabin = function (k, rng, n) { //n is optional bigint or number, when "this" is not bigint.
		n = bigInt(n || this);
        var isPrime = isBasicPrime(n);
        if (isPrime !== undefined) return isPrime;
        var n = n.abs();
        var t = k || getSetMRrounds();
        for (var a = [], i = 0; i < t; i++) {
            a.push(bigInt.randBetween(2, n.minus(2), rng)); //maybe need to make this odd, or moreover - primes, because primes in array are odd.
        }
        return millerRabinTest(n, a);
    };
    Integer.isProbablePrime	=	Number.prototype.isProbablePrime	= SmallInteger.prototype.isProbablePrime	=	BigInteger.prototype.isProbablePrime = 
    Integer.MillerRabin		=	Number.prototype.MillerRabin		= SmallInteger.prototype.MillerRabin		=	BigInteger.prototype.MillerRabin = 
	MillerRabin;
	//	Usage:
	//	console.log(BigInteger.isProbablePrime(5, undefined, '47'));	// as BigInteger-function isProbablePrime
	//	console.log((47).isProbablePrime(10));							// as Number-function isProbablePrime
	//	console.log((new BigInteger('47')).isProbablePrime(20));		// as function for new BigInteger
	//	console.log(BigInteger.MillerRabin(5, Math.random, '47'));		// as BigInteger-function MillerRabin
	//	console.log((47).MillerRabin(10));								// as Number-function MillerRabin
	//	console.log((bigInt('47')).MillerRabin(10));					// as function for new bigInt
	
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

    BigInteger.prototype.checkCoPrime = function (another) {
		var g = gcd(this, another);										//test gcd
		return ( (g.bitLength().value === 1) && (g.value == 1) )		//if 1, optionally, g.bitLength == 1		- true
    }
    SmallInteger.prototype.checkCoPrime = BigInteger.prototype.checkCoPrime;
	//	Usage:
	//	new BigInteger('100500').checkCoPrime(new BigInteger('121')) // true
	//	(new BigInteger('100500')).checkCoPrime(new BigInteger('119')) // true
	
    BigInteger.prototype.genCoPrime = function (
			bits			//number of bits to generate co-prime, or strings ('prev', 'previous') or 'next' - to get previous or next co-prime from number 
		,	number			//string or bigInteger with start number, from which need to generate co-prime.
							//This is optional parameter, and if not specified, first must be a number of bits, not a string.
		,	cur2			//check current number too, or not? default - false, and do not return the number if number is co-prime with "this".
	)
	{
		cur2 = ( ( ( typeof cur2 === 'undefined' ) || (cur2 == false) ) ? false : true );	//return current number if co-prime with "this"? 
		if(typeof number !== 'undefined'){
			if(['previous', 'prev'].indexOf(bits) !== -1){
				bits = 'previous';
			}else{
				bits = 'next';
			}
		}else{
			bits = bits || 256;
		}
		var RandCoPrimeResult = (typeof number !== 'undefined')				//when number is defined
									? bigInt().from(number)					//use this number, as start value
									: get_random_k_bits(bits)				//or generate random number, with specified bitlength, or default.
		;
		while((!cur2) ? (cur2=true, true) : !this.checkCoPrime(RandCoPrimeResult)){		//while it not co-prime with this
			RandCoPrimeResult =	RandCoPrimeResult.next( ((bits === 'next')? 1 : -1 ) ); //when number is defined, then bits can be a strings, use 'next' or 'prev' number.
		}
		return RandCoPrimeResult;
    }
    SmallInteger.prototype.genCoPrime = BigInteger.prototype.genCoPrime;
	//	Usage:
	//	(new BigInteger('100500')).genCoPrime('prev', new BigInteger('121'), true).toString()	//"121"
	//	new BigInteger('100500').genCoPrime('prev', new BigInteger('121'), false).toString()	//"119"

	var from = BigInteger.prototype.from = function(number)		//fast way to return bigInteger as is, or from decimal string, or from hexadecimal string.
	{
		var bigNumber = undefined;
		var number = number || this;

		if(
				(number instanceof bigInt)
			||	(typeof number === 'undefined')
			||	(typeof number === 'number')
			||	(typeof number === 'bigint')	//or if bigint in form 123n
			||	(
						(typeof number === 'string')
					&&	(			/^[+-\d]+$/				.test(number) === true		)
				)
		)
		{
			return new bigInt(number);
		}
		else if(
				(typeof number === 'string')
			&&	(	/^[0-9a-fA-F]+$/	.test(number) === true		)
		)
		{
				bigNumber = new bigInt(number, 16);
		}

		return new bigInt(bigNumber);
	}
    SmallInteger.prototype.from = BigInteger.prototype.from;
	//	Usage:
	//		new bigInt().from(new BigInteger('100500'));
	//		new bigInt().from('HexOrDecString')
	//or	new bigInt('HexOrDecString').from()

	BigInteger.prototype.isSafePrime = function (MRrounds)	//is the prime, value of (p-1)/2, where p = this? (true/false)
	{
		MRrounds = MRrounds || getSetMRrounds();	//default MillerRabin rounds
		return (
						this.MillerRabin(MRrounds)
					&&	(
							(
								this
								.subtract(
									bigInt('1')
								)
							)
							.divide(
								bigInt('2')
							)
						)
						.MillerRabin(MRrounds)
		);
	}
	SmallInteger.prototype.isSafePrime = BigInteger.prototype.isSafePrime;
	//	Usage:
	//	new BigInteger(83).isSafePrime();	//true

	//Generate and return the Safe Prime p, for which (p-1)/2 is a prime too.
	function generateSafePrime(
		x,				//string or BigInteger - safe-prime, or start-number from which need to generate a safe-prime,
						//or number - bitlength to generate random safePrime with specified bitlength, if "x" not a string or BigInteger
		mode			//'previous', or 'next', or 'doubled-previous', or 'doubled_next';
	,	MRrounds
	){		
		/*
			Proof of the validity of the representation a Safe-Prime number, in form: p = 12*k - 1:

			Let q = 12*x+r; where x - natural number, r = q%12 - remainder by modulo x, and number with value from 0 up to (x-1) (0,1,2,3,4,5,6,7,8,9,10,11).
			In this form can be represented each natural number.

			Now, let us prove that the representation of any Safe-Prime (which are not excepted), in form q = 12*x+11 is valid:
			
			1.	When r is even, y - natural number, r = 2*y; q = 12*x + r = 12*x + 2y; q = 2*(6x+y) - so q have divisor 2, and this is even number, not an odd prime number.
				So, y = 0,1,2,3,4,5, and even values of r = 0,2,4,6,8,10 - are excluded.
			
			2. Now, exclude an odd values of r:
				When r = 1; q = 12*x + 1; (q-1)/2 = 12*x/2 = 6*x = 2*3x - have divisor 2, and this is even number, not an odd Sophie-Germen prime number.
				When r = 3; q = 12*x + 3; q = 3*(4x+1) - have divisor 3, and this is not a prime, because this have no divisors besides 1 and itself.
				When r = 5; q = 12*x + 5; (q-1)/2 = (12*x+4)/2 = 2*(6x+2)/2 = (6x+2) = 2*(3x+1) - have divisor 2, and this is even number, not an odd Sophie-Germen prime number.
					Exception: x = 0; q = 12*0 + 5 = 5; (q-1)/2 = (5-1)/2 = 4/2 = 2, is even, but this is a Sophie-Germen prime-number, and this have divisor 1 and itself.
				When r = 7; q = 12*x + 7; (q-1)/2 = (12*x+6)/2 = 2*(6x+3)/2 = (6x+3) = 3*(2x+1) - have divisor 3, and this is not a prime, because this have no divisors besides 1 and itself.
					Exception: x = 0; q = 12*0 + 7 = 7; (q-1)/2 = (7-1)/2 = 6/2 = 3, have divisor 3, but this is a Sophie-Germen prime-number, and this have divisor 1 and itself.
				When r = 9; q = 12*x + 9; (q-1)/2 = (12*x+8)/2 = 2*(6*x+4)/2 = (6x+4) = 2*(3x+2) - have divisor 2, and this is even number, not an odd Sophie-Germen prime number.

			After this all, from all possible values of r = q%12, from the numbers 0,1,2,3,4,5,6,7,8,9,10,11,
			was been excluded (two exceptions) the values r = 0,2,4,6,8,10,1,3,5,7,9 (sorted: 0,1,2,3,4,5,6,7,8,9,10), and only one option remains - value 11.
			Consequently, r = 11, and any Safe-Prime nubmer (except for 5, 7), can be represented in form q = 12*x + 11;
			Now, let, k = (x+1); q = 12*(x+1) - 1 = 12k - 1; Consequently, q = 12k - 1.
			
			Original statement is proven.
		*/
		
		MRrounds = MRrounds || getSetMRrounds();	//default MillerRabin rounds
		
		if((typeof x !== 'number') && bigInt().from(x).isSafePrime()){return bigInt().from(x);} //if x not number but string or bigint, and if this already safe prime - return it
		
		//	Or start generate the Safe-Prime:
		//by "bitlength" - prime with specified bitlength in number "x", or by specified BigInteger "x" - the start number, with "mode" - 'previos'(default), 'next',
		//(also, 'doubled[_- +.]previous', 'doubled[_- +.]next' - means generate previous or next Sofi-Germen prime, and return doubled safePrime 2p+1).
		
		//	sp - Safe Prime, sgp - Sofi-Germen's prime, corresponding for sp.
		//sgp = (sp-1)/2 - must be a prime, when sp is Safe Prime. 			| * 2
		//2*sgp = sp-1														| + 1
		//2*sgp + 1 = sp													|revert this
		//sp = 2sgp + 1; 													|if sgp, is a prime -> return sp.
		
		mode = mode || 'previous';

	//	console.log(
	//		'Generating "safe prime" number, as '												+
	//		mode																				+
	//		' prime from x '																	+
	//		( ( mode.indexOf('doubled') !== -1 ) ? ', means as next 2x' : '' )					+
	//		((typeof x === 'number')?'from random '+x+' bits BigInteger': x.toString())			+
	//		', for which (p-1)/2 is prime number too... '
	//	);
				
		var p, prime = (typeof x === 'number') ? bigInt.randbits(x) : bigInt().from(x);	//just got rand bits or nubmer.
		prime = (
					(prime.MillerRabin(MRrounds))												//if already prime
						? prime															//use it
						: prime.prevprime()
				)
		;
		if(prime.isSafePrime()){return prime;}
		prime = (																		//find next or previous prime, (12k - 1)
							(mode.indexOf('previous')!==-1)
								? (prime.subtract(prime.mod(bigInt('12'))).add(bigInt('12')).prev())	//	((p - (p%12) + 12) - 1) 	->	next number (12k - 1)
								: (prime.subtract(prime.mod(bigInt('12'))).prev())						//	(p - (p%12) - 1) 		-> 	previous number (12k - 1)
				)
		;
		if(prime.isSafePrime()){return prime;}
		do{
		//	console.log('p', p, 'prime', prime.toString());
			prime = ( (mode.indexOf('previous')!==-1) ? prime.subtract(bigInt('12')) : prime.add(bigInt('12')) );	//next or previous nubmer (12k-1)
			//find next prime p, by rolling, using MillerRabin() primality check
			p = (
					( mode.indexOf('doubled') !== -1 )
						? (prime.multiply(bigInt('2'))).next()					//make p*2+1
						: (prime.prev()).divide(bigInt('2'))					//or (p-1)/2
				)
			;
		//	console.log('p.toString()', p.toString());
		}while(
				!prime.isNegative()
			&&	(
					!prime.MillerRabin(MRrounds)
				||	!p.MillerRabin(MRrounds)										//check (p*2)+1 primality of
			)
		)
		p = ( ( mode.indexOf( 'doubled' ) !== -1 ) ? p : prime );	//return safe prime, if next or previous was been Sofi-Germen prime, and need to return doubled Safe-prime.

	//	console.log('Done! p = ', p.toString());
		return p;													//maybe this fuction return a safe prime
	}
	//Usage:
	//	BigInteger.GenSafePrime(10).toString(2).length						//10 bits, when number on input
	//	BigInteger.GenSafePrime('10').toString()							//7 - when string
	//	BigInteger.GenSafePrime(new BigInteger('10')).toString()			//7 - when bigInteger

	function isStrongPrime(p, s, r, t, MRrounds)
	{
		MRrounds = MRrounds || getSetMRrounds();	//default MillerRabin rounds
		p	=	bigInt().from(p);	//bigInt from string if string, or bigInt from bigInt
		s	=	bigInt().from(s);
		r	=	bigInt().from(r);
		t	=	bigInt().from(t);
		return (										//true when
					(
							p.MillerRabin(MRrounds)		//p - is prime
						&&	s.MillerRabin(MRrounds)		//s - is prime
						&&	r.MillerRabin(MRrounds)		//r - is prime
						&&	t.MillerRabin(MRrounds)		//t - is prime
					)
					&&									//and
					(//criteries for a Strong prime:
							p.next().mod(s).eq(0)		//(p+1) have divisor s
						&&	p.prev().mod(r).eq(0)		//(p-1) have divisor r
						&&	r.prev().mod(t).eq(0)		//(r-1) have divisor t
					)
				)	//		when this all is true - return true, else - false.
		;
	}

	function genStrongPrime(	//Gordon's Algorithm, to generate Strong Prime (cryptography).
			bits
		,	maxIter
		,	strings
		,	MRrounds
	)
	{
		bits		=	bits || 20;
		MRrounds = MRrounds || getSetMRrounds();	//default MillerRabin rounds
		var s = get_random_k_bits(bits).prevprime();
		var t = get_random_k_bits(bits).prevprime();
		var r = Integer.one.next(3); //start - 4, first not prime.
		for(
			var l = Integer.one;							//from l = 1
			(												//while
					l.leq(t.bitLength())				//l<=t.bitlength()
				&&	!r.MillerRabin(MRrounds)						//and r not a prime
			);
			l = l.next()									//compute r, and increment l while contition is true
		){
			r = Integer.one.add(l.multiply(t));		// r = 1+l*t
		}
		var p0 = 	(								//p0 = ( (2*(s^(r-2) mod r)*s) - 1 )
						(
							(Integer.one.next())
							.multiply(
								s.modPow(r.subtract(Integer.one.next()), r)
							)
							.multiply(s)
						)
						.subtract(
							Integer.one
						)
					)
		;
	
		var p = Integer.one.next(3); 				//start - 4, first not a prime.
		var limit = maxIter || 1000;				//up to limit iterations in cycle, (1000 by default, if undefined).
		for(
			var j = Integer.one;					//from start j = 1
			(										//while
					!isStrongPrime(p, s, r, t)			//or p is not a strong-prime
				&&	(limit > 0)							//or number of iterations is reached
			);
			j = j.next()							//compute p, and then increment j, and continue
		){
			p = p0.add((((Integer.one.next()).multiply(j)).multiply(r)).multiply(s));		//p = p0 + 2*j*r*s
			limit--; //decrease limit-value
		}

		//	Proof, that prime p, generated with Gordon's algorithm, is a strong-prime:
		//		1. 	s^(r-1) === 1 (mod r) ; -> this is a corollary of Fermat's theorem.
		//			Consequently, p0 = 1 (mod r); p0 = -1 (mod s);
		//		2. After all:
		//			p-1 = p0 + 2jrs - 1 = 0 (mod r);	and (p-1) have divisor r
		//			p+1 = p0 + 2jrs + 1 = 0 (mod s);	and (p+1) have divisor s
		//			r-1 = 2it = 0 (mod t);				and (r-1) have divisor t
		
		var strings = (((typeof strings !== 'undefined') && (strings !== false)) ? true : false);		
		var object =	{
							//return as strings or as BigIntegers.
							'p': ((strings)?p.toString():p),
							'r': ((strings)?r.toString():r),
							's': ((strings)?s.toString():s),
							't': ((strings)?t.toString():t)
						}
		;
		return (
					(isStrongPrime(p, s, r, t))						//if p is a strong prime
						? object									//return object with results
						: genStrongPrime(bits, undefined, strings)	//else one more try, with default limit.
				)
		;
	}//test: var SP = BigInteger.genStrongPrime(20); BigInteger.isStrongPrime(SP.p, SP.s, SP.r, SP.t); //true
	
	var Factorize =
	BigInteger.prototype.Factorize =
	SmallInteger.prototype.Factorize =
	function FactorizePollardRhoBrent(
		NumberToFactorize
	,	MRrounds
	) {
		//	input - bigInteger,
		//	output - array with prime factors...

		NumberToFactorize = this || bigInt().from(NumberToFactorize);
		MRrounds = MRrounds || getSetMRrounds();	//default MillerRabin rounds

		function PollardRho(n_){ //return divisor from n_
			if (
					['0', '1', '2'].indexOf(n_.toString()) !== -1		//if 0, 1 or 2
				||	n_.MillerRabin()									//or prime
			){ 
				return n_;												//return n, as divisor.
			}
  
			//# even number means one of the divisors is 2  
			else if (n_.mod(2).eq(0)){									//if even
				return bigInt(2);										//divisor is 2
			}
			function f(_x){return ( ( ( ( _x.modPow(2, n_) ).add(c_) ).add(n_) ).mod(n_) ); }	//modPow is faster, than square and mod: f(x) = ( ( (x^2 mod n) + c + n ) mod n );
			var x_, y_, d_ = n_, c_ = n_;							//define this variables, on start;
			while(d_.eq(n_)){											//while failure - repeat again
				x_ = bigInt(1);											//test x = 1;
				y_ = x_;												//y_ = x_

				d_ = bigInt(1);											//start d_ = 1
				//# until the prime factor isn't obtained. 
				//# If n_ is prime, return n_
				while (d_.eq(1)){										//while d_ != 1
					x_ = f(x_);												//# Tortoise Move: x_(i+1) = f(x_(i));
					y_ = f(f(y_));											//# Hare Move: y_(i+1) = f(f(y_(i)));
					d_ = gcd((x_.subtract(y_).abs()), n_);					//# check gcd of |x_-y_| and n_  
				}
				if(d_.neq(n_)){											//if d_ !== n_
					return d_;												//return divisor
				}else{													//else
					c_ = c_.next();											//increment c_ after each failure, and continue with this c_.
				}
			}
		}

		var factors = [];							//define array with prime factors
		var currentNumber = NumberToFactorize;		//save current number
		var divisor, primeIs;						//define variables for divisor and primeIs
		do{											//and begin to
			divisor = PollardRho(currentNumber);	//get divisor. It can be a component (2*2*2 = 8, for example. Or 2*3*5 = 30)
			if(divisor.eq(0) || divisor.eq(1)){							//if this 0 or 1
				break;														//break from cycle
			}
			while(!(primeIs = divisor.MillerRabin(MRrounds), primeIs)){	//while divisor not a prime (save result into variable primeIs)
				divisor = PollardRho(divisor);								//try to factorize divisor
			}
			if(primeIs){												//if divisor is a prime (use saved variable, to do not check primality again)
				factors.push(divisor.toString());							//push this divisor as string
				currentNumber = currentNumber.divide(divisor);				//and divide current number on this
			}
		}while(currentNumber.neq(1))									//and try again, with the quotient, up to the end
		return factors;													//After all, return array with consecutive prime-factors.
	}

	/*
	//test:
	var start = new bigInt(1);
	for(var iter=start; iter<start.add(bigInt(100000)); iter = iter.next()){
		var num = iter;
	//	var num_factors = FactorizePollardRhoBrent(num);
		var num_factors = num.Factorize();
	//	console.log(num_factors);
		//now multiply factors
		var testNum = bigInt(1);	//1
		for(var factor = 0; factor<num_factors.length; factor++){
	//		console.log(num_factors[factor]);
			testNum = testNum.multiply(bigInt().from(num_factors[factor]));	//*each factor
		}
		if(testNum.neq(num)){	//if test not num
			console.log('(', num.toString() ,' === ', testNum.toString(), ')', (testNum.eq(num))); //show this
		}else if(iter.mod(bigInt(1000)).eq(0)){
			console.log('(', num.toString() ,' === ', testNum.toString(), ')', (testNum.eq(num))); //show this
		}
	}

	var rand = bigInt(Math.random().toString(10).slice(3));	//gen random bigInt
	var rand_factors = rand.Factorize();			//factorize this
	console.log('rand', rand, 'rand_factors: '+rand_factors);	//show rand and factors of this rand.

	//test working...
	*/

	// 		A simple method to evaluate Euler Totient Function, using BigInteger.
	//	Warning, n can be not a prime here.
	function EulerPhi(
		n
	,	MRrounds
	,	Exp			//Exp-velue, for: number = n^Exp; n - prime; phi(n^Exp) = n^Exp - n^(Exp-1)
	) {
//		console.log('Wait for evaluating Euler\'s totient function for ', n.toString(), '...');
		var exp = (typeof Exp !== 'undefined');		//if exponent defined, that means n = n^exp;
		MRrounds = MRrounds || getSetMRrounds();	//default MillerRabin rounds

		if(
				exp							//if exponent defined
			&&	n.MillerRabin(MRrounds)		//and if n = p^Exp, where p = n - prime
		){
			n = bigInt.from(n);				//n -> to BigInteger (this can be a number or string)
			var p = n;						//p = n;
			n = bigInt.from(Exp);			//n = Exp -> to BigInteger (this can be a number or string)
			var phi_p_n = (p.pow(n)).subtract(p.pow(n.prev()));			//phi(p^n) = p^n - p^(n-1)
			return phi_p_n;					//return phi(p^n) for nubmer n^Exp, where n is a prime.
			//number = p^n; 		phi(1*p^n) = phi(1) * phi(p^n) = 1*phi(p^n)
			//number = 2*p^n;		phi(2*p^n) = phi(2) * phi(p^n) = 1*phi(p^n) too.
			//So, number = n^Exp or number = 2*n^Exp; and phi(number) = phi_p_n;
		}
		else if(n.isOdd())		//if n is odd
		{
			if(n.MillerRabin(MRrounds)){		//and prime
				return n.subtract(bigInt('1')); //phi(n) = phi(1*n) = phi(1) * phi(n) = 1*(n-1) = (n-1), if n is prime. All numbers before n is co-prime with n.
			}
		}else if(n.isEven()){	//if n is Even
			var n2 = n.divide(Integer[2]);			//(n/2)
			if(n2.MillerRabin(MRrounds)){		//and if n/2 is a prime
				return n2.subtract(bigInt('1')); //phi(2n) = phi(2) * phi(n) = 1*(n-1) = (n-1), if n is prime. All numbers before n is co-prime with n.
			}
		}

		//else if n not a prime
		var n_factors = n.Factorize();				//factorize n to array with prime factors;
		//console.log('n_factors', n_factors);
		//
		//											//now, compute euler phi:
		//	phi(ab) = phi(a) * phi(b);															//ab
		//	phi(p^a) = p^a - p^(a-1);															//p^a
		//	phi(p^1) = p^1 - p^(1-1) = p - p^0 = p-1;											//p is prime;
		//	
		//	n = p1^a * p2^b * p3^c * ... * pN^n;												//canonical note of n, using factors.
		//	phi(n) =	phi(p1^a) * phi(p2^b) * phi(p3^c) * ... * phi(pN^n) =
		//				(p1^a - p1^(a-1)) * (p2^b - p2^(b-1)) * ... * (pN^n - pN^(n-1))		;	//phi_n from canonical n-factors
		var result = bigInt(1);
		//var factors = n.Factorize();		//factors
		var factor = bigInt(1);
		var curFactor;
		var exp = bigInt(0);
		for(var ifact = 0; ifact<n_factors.length+1; ifact++){
			curFactor = bigInt.from(n_factors[ifact] || 1);
			if(factor.neq(curFactor)){
				if(ifact!==0){result = result.multiply((factor.pow(exp)).subtract(factor.pow(exp.prev())));}
				exp = bigInt(1);
				factor = curFactor;
			}
			else if(factor.eq(curFactor)){
				exp = exp.next();
				continue;
			}
		}
		console.log('Done! Result', result.toString());
		return result;
		
	/*
		//Also, by this way:
		//phi(n) = phi(p1^a) * phi(p2^b) * phi(p3^c) * ... * phi(pN^n) =
		//(p1^a - p1^(a-1)) * (p2^b - p2^(b-1)) * ... * (pN^n - pN^(n-1)) = 
		//n * (1 - 1/p1) * (1 - 1/p2) * ... * (1 - 1/pN) = 
		//(((n - n/p1) - (n - n/p1) / p2) - .../pN ); 
		//phin = n; phin = phin - phin/p1; phin = phin - phin/p2; ... phin = phin - phin/pN;
		var n_copy = n;
		var result2 = n;
		//var factors = n.Factorize();		//factors
		var factor = bigInt(1);
		var curFactor = bigInt(1);
		for(var ifact = 0; ifact<n_factors.length; ifact++){
			curFactor = bigInt.from(n_factors[ifact]);
			if(factor.neq(curFactor)){
				factor = curFactor;
			}
			else if(factor.eq(curFactor)){
				continue;
			}
			while(n.mod(curFactor).eq(0)){
				n = n.divide(curFactor);
			}
			result2 = result2.subtract(result2.divide(curFactor));
		}

		if(n.gt(1)){
			result2 = result2.subtract(result2.divide(n));
		}
		
		console.log('BigInteger.EulerPhi(', n_copy.valueOf(), '): ', result.toString(), ', (result.eq(result2))', (result.eq(result2)));
		return result2;
	*/
	}

	BigInteger.prototype.isPrimitiveRoot = function (	//check is this primitive root by modulo p, or not? (true/false)
		p												//p - modulo,			(g = this)
	,	MRrounds										//rounds of MillerRabin
	,	is_p_prime										//to do not compute it again and again
	,	phi_p											//to do not compute it again and again
	,	phi_pFactors									//to do not compute it again and again
	){
		MRrounds = MRrounds || getSetMRrounds();				//default MillerRabin rounds
		var is_p_prime = is_p_prime || p.MillerRabin(MRrounds);	//is p prime - true/false
		var g = this;											//g = this
		phi_p = (
						phi_p										//use phi_p, if defined
					||												//or compute it
						(
								(	p instanceof bigInt			)	//if p is BigInteger
									?	EulerPhi(p)						//compute phi(p)
									:	undefined						//or undefined
						)
				)
		;
		phi_pFactors = phi_pFactors || phi_p.Factorize();			//use phi_pFactors or compute it by factorize phi_p;
		
		var isPrimitiveRoot = false;								//false on start
		if(															//g is a primitive root by modulo p, when:
					!g.eq(1)												//g!==1, because if g === 1, g^x mod p = 1 mod p for any x;
				&&	!g.mod(phi_p).isZero()									//g can be only from (1 up to phi(p)-1), not 0 or phi_p: (0 mod phi_p) === (phi_p mod phi_p)
				&& (												//and
						is_p_prime											//when p is prime, any number in range [1, phi(p)] is co-prime;
					||	(	!is_p_prime && p.checkCoPrime(g)			)	//or when p is not a prime, g must to be a number co-prime with p
				)
		){
			var done = true;	//then, g is a maybe primitive root by modulo p.

			//Now, to verify is g primitive root or not, need to verify:
			//g^(phi(p)/pf) mod p !== 1 mod p; where pf - this prime factors of phi(p) as result of factorization this: (pf1, pf2, ..., pfn),
			//Since phi(p) is always even number for each p>2, phi(p) always have divisor 2 (prime number),
			//so g^(phi(p)/2) mod p !== 1 mod p, for primitive root by modulo p;
			for(var factor = 0; factor<phi_pFactors.length; factor++){						//now, for each prime factor "pf", from result of factorization phi_p
				if(	g.modPow(phi_p.divide(bigInt.from(phi_pFactors[factor])), p).eq(1) )	//check g^(phi(p)/pf) mod p === 1 mod p
				{
					done = false;	//and if this true for some prime factor, then g is not a primitive root.
					break;			//and break from this cycle;
				}
			}
			if(done === true){		//if still true, after check all prime factors
				isPrimitiveRoot = true;				//g is a primitive root
			}//else - false;
		}
		return	isPrimitiveRoot;	//and return true/false.
	};
	SmallInteger.prototype.isPrimitiveRoot = BigInteger.prototype.isPrimitiveRoot;

	//g is a primitive root by modulo m, and g is exists only by modulus: m = 2(1*2^1), 4(2*2^1), p^a (1*p^a), 2*p^a (2*p^a); where p - prime, a>=1;
    BigInteger.prototype.GetPrimitiveRoot = function (	//return primitive root, for prime or SafePrime, or any number
		g_mode		//start number to generate g;
	,	MRrounds
	,	prev		//true if need 'previous' or false, or undefined if need 'next'
	,	Exp			//a=Exp, if number = p^a or number = 2*p^a;
	)
	{
		//	Get first or random primitive root, by module of prime p.
	
		//This function fast finding a primitive root g, by module of prime p,
		//For the numbers:
		//	p is prime,
		//	or p = p^Exp,
		//	or p = 2*p^Exp,
		//	or sfp = (sp-1)/2 is a prime too (sfp - Sophie-Germain prime, sp - SafePrime).
		//	phi(sp) = (sp-1); phi(sp) / 2 = (sp-1)/2 = sgp; factors(phi(sp)) = [2, sgp]; phi(phi(sp)) = phi(sgp) = (sgp-1); - easy to compute this all;
	
		var p = this;
		MRrounds = MRrounds || getSetMRrounds();			//default MillerRabin rounds
		prev = ( ( (typeof prev === 'undefined') || (prev === false) ) ? false : true );
		var exp = (typeof Exp !== 'undefined');				//if exponent defined, that means n = n^exp;
		
		var is_p_prime = p.MillerRabin(MRrounds);			//is p prime? if p = p^a or p = 2p^a, this can be not a prime.
		var phi_p = EulerPhi(p, MRrounds, Exp); 			//if p is prime, phi(p) = p-1, phi(p^a) = phi(2p^a) = p^a - p^(a-1); without factorization of p.
		
		var phi_p_factors = phi_p.Factorize();				//factorize phi_p into array of prime-factors. phi(m) - always even, for any m > 2; so at least 2 is a prime factor for this;
		//console.log('phi_p_factors', phi_p_factors);		//show this factors

		var phi_phi_p = EulerPhi(phi_p, MRrounds);			//phi(phi(m)) - number of primitive roots, by modulo m;
		//for Safe-Prime p = sgp * 2 + 1; phi(p) = p-1 = 2sgp; phi(phi(p)) = phi(2sgp) = phi(2) * phi(sgp) = 1 * (sgp-1) = (sgp-1);

		if		(typeof g_mode === 'undefined'){	g_mode = bigInt('1');	}	//use 1 if undefined;
		else if	(
					(	g_mode === 'random'			)
				||	(	g_mode === '0'				)
				||	(	g_mode === 0				)
				||	(	bigInt.from(g_mode).eq(0)	)
		)
		{
			g_mode = ( ( bigInt.randBetween(bigInt('0'), p) ).mod( phi_p ) );	//or generate randomly
		}
		else{
			g_mode = bigInt.from(g_mode);	//or use specified number
		}

		//Now, just return first finded primitive root
		var last_g = g_mode.prev( ( ( prev ) ? -1 : 1 ) ).mod(p);	//save previous or next g
		for(
			var g = g_mode;					//from g_mode
			true;							//while g not found		
			g = (							//rolling g from g_mode, by modulo p
				g.next(
					( ( prev ) ? -1 : 1 )	//by increment or decrement g
				)
			).mod(p)						//in circle, by modulo p
		){
			if(	g.eq(last_g)	){break;}	//if all cycle was been checked - break;
			if(	g.isPrimitiveRoot(p, MRrounds, is_p_prime, phi_p,	phi_p_factors)){	//if current g is a valid primitive root
				return g;																//stop finding and return it
			}
		}
	};
    SmallInteger.prototype.GetPrimitiveRoot = BigInteger.prototype.GetPrimitiveRoot;
	
	//Blum-Blum Shub (BBS) PRNG, allow to get n-th number, without rotate PRNG, and generate all previous numbers, to skip it.
	//seed is (x0, M, lambdaM), n - N-th value from PRNG, bits need to specify number of bits, to generate seed, if this was been undefined.
	function BBSBigInteger(
		bits,		//(string, number, or BigInteger) 	-	If need to generate random p, and q with specified bitlength
		n,			//(string, number, or BigInteger)	-	N-th number
		seed		//JSON-object with PRNG-seed:		-	{'x0': x0, 'M': M, 'lambdaM': lambdaM}
	)
	{	//n-th number from BBS PRNG, without calculating previous.
		seed = (
					(typeof seed !== 'undefined')
						?(typeof seed === 'string')
							?	(typeof JSON.parse(seed) === 'object')
									? JSON.parse(seed)
									: undefined
							:	(typeof seed === 'object')
									? seed
									: undefined
						: undefined
				)
		;
		
		var x0;
		if(
				(typeof seed					!==	'undefined')
			&&(
				(
						(
								(seed.x0		instanceof	bigInt	)
							&&	(seed.M			instanceof	bigInt	)
							&&	(seed.lambdaM	instanceof	bigInt	)
						)
					&&	(
							(typeof seed.x0			!==	'undefined')
						&&	(typeof seed.M			!==	'undefined')
						&&	(typeof seed.lambdaM	!==	'undefined')
					)
				)
				||
				(
						(typeof seed.x0			===	'string')
					&&	(typeof seed.M			===	'string')
					&&	(typeof seed.lambdaM	===	'string')
				)
			)
			&&		(new bigInt().from(seed.x0)).checkCoPrime(new bigInt().from(seed.M))
		){
			x0			=	new bigInt().from(seed.x0);
			M			=	new bigInt().from(seed.M);
			lambdaM		=	new bigInt().from(seed.lambdaM);
		}
		else{	//generate new p, q, M, lambdaM and x0, with bitlength of bits.
			bits =	(
						bits
						||	(
								(typeof bits === 'string')
							&&	(/^\d+$/.test(bits) === true)
							)
							? parseInt(bits, 10)
							: 256		//256 bits, by default.
					)
			;
			
			var p = get_random_k_bits(bits).nextprime();				//	p
			console.log('p', p.toString(), p.isPrime());
		
			var q = get_random_k_bits(bits).nextprime();				//	q
			console.log('q', q.toString(), q.isPrime());
		
			var M = p.multiply(q);										//	M = p * q
			console.log('M = p*q = ', M.toString());

			//compute lambdaM
			var BigPrevP = p.subtract(bigInt('1'));						//(p-1)
			var BigPrevQ = q.subtract(bigInt('1'));						//(q-1)
			var lambdaM = lcm(BigPrevP, BigPrevQ);						//lambdaM = lcm((p-1), (q-1))

			//generate x0
			var coPrime = M.genCoPrime(bits);
			console.log('coPrime = ', coPrime.toString(), 'is CoPrime: ', coPrime.checkCoPrime(M));

			if(coPrime.checkCoPrime(M) === true){
				x0 = coPrime;
				console.log('x0 is coPrime with M: ', x0.toString(), x0.checkCoPrime(M));
			}
			
			//combine this all to seed
			seed = {'M': M.toString(), 'lambdaM': lambdaM.toString(), 'x0': x0.toString()};
			console.log('new seed was been generated!');
			console.log(
				'JSON.stringify(seed)\n'+
				'\''+JSON.stringify(seed)+'\''
			);
		}
	
		if(typeof n === 'undefined' || !(n instanceof bigInt)){
			n = new bigInt().from(n);	//0 index, by default, if undefined, or return bigInt as is or from (hexa)decimal-string
		}
		//now, compute N-th value, from PRNG;
		
		//prepare computing 2^n mod lambdaM
		var twoBig 		=	Integer[2];							//2
		var nBig 		=	n;									//n
		//do it
		var expBig = twoBig.modPow(nBig, lambdaM);				//2^n mod lambdaM
		//compute pseudorand result Nth-value
		var result = x0.modPow(expBig, M);						//and finaly:	result = x0 ^ (2 ^ n mod lambdaM ) mod M;
		
		//and return this all.
		return {'n': n.toString(), 'NthValue': result.toString(), 'seed': JSON.stringify(seed)};
	}
	//	Usage:
	//	First run:
	//		var bits = 128; BigInteger.BBSBigInteger(bits); //-> return JSON-string with seed.
	//	Random Access PRNG, with seed:
	//		BigInteger.BBSBigInteger(
	//			undefined,														//number, bigInt, or (hexa)decimal-string	(bitlength for p and q, but optional, and default 256)
	//			n,																//number, bigInt, or (hexa)decimal-string	(optional, for generation)
	//			'{"M":"M_value","lambdaM":"lamdaM_value","x0":"x0_value"}'		//(optional) - seed, returned as string, after generation of this
	//		);	//return object {"n":"n","NthValue":"pseudo-rand","seed":{seedObjectString}}
	//		//.NthValue.toString()	//N-th value as string

	/*
		BRAPRNG - Bijective Random Access Pseudo-Random Number Generator (Bijective Random Access PRNG, BRAPRNG).
		
		The main formula of this generator, is a simply formula, from Diffie-Helman Key-Exchange Protocol:
			pubKey = g ^ privKey mod p
		which allow to generate pseudorand-values,
		when result - prand, privKey - Index, p - safe prime (prime for which ((p/2)-1) is Sophie-Germain prime):
			prand = g ^ Index mod p;		where p is Safe-Prime (for which (p/2)-1 is prime too), g is primitive root by modulo p,
											Index - some index in range (1, ... phi(p)), prand - pseudorand-value in the same range.

		Because g is a primitive root by modulo p,
		the main property of ransfrom "Index" to "prand" - this is a bijective-transform.
		This means, for each unique "Index", in range (1, ... phi(p)), corresponding one, and only one "prand"-value, in the same range,
		where phi(p) = (p-1), when p is prime nubmer.
		For each unique "index" in this range, only one "prand" is corresponding, and this is unique too, wihtout any repeations of "prand", in this range.
		
		This transfrom is not reversible, because to "Index", by known "prand", and moreover "g", "p", need to resolve "discrette-logarithm"-problem.
		Because of this, this transorm seems, like a hash, but this is not a hash, because bitlength of data is not changing,
		and, as result - no any collisions, so, this is just - a bijective transform "Index" into "prand".
				
		Random-Access PRNG, means, any "prand", can be extracted directly by "Index", and "Index", can be a random-values for each "prand".
		No need to compute N values, ans skip it then, to extract N-th value.
		So, this PRNG, seems like Blum-Blum-Shub Algorithm too, but there need to specify N, and the seed with three numbers: x0, M, and lamdaM.
		Here, "Index", and seed (g, p, shift_value)
		
		In Diffie-Hellman Key-Exchange protocol, g and p - this is a public values.
		Here, this can be customized, and this can be a private.
		p, can be selected, as any safe-prime, from the some start_number:
			p = BigInteger.GenSafePrime(new BigInteger().from('some seed, with a hexa(decimal)-value to compute this p'));

		g - this is primitive root, by modulo p.
		The number of primitive roots by modulo p, is phi(phi(p)),
		and when p is a safe-prime, then phi(phi(p)) = ( ( p-1 )/2 ) - 1 -> big number of primitive roots.
		So, there is possible to use any primitive root, by modulo p.
		For example, this can be depended from Index:
			g = p.GetPrimitiveRoot(Index);
		
		Index, can be a private value too.
		This can have unique values in range (1, ... phi(p)), where 0 = phi(p) (mod phi(p)),
		and by modulo p, we have a circle, and finite field, with (p-1) elements (excluding 0-th element).
		
		Also, a big table of unique values can be generated, when:
			Index = (i * floor(sqrt(p)) + j), where i and j, the number of i-th row, and j-th column in this table.
			This i and j numbers can have value from 0 up to floor(sqrt(p)).
			
		After all, all this circle, can be rotated on "shift_value" indexes (shift_value mod phi(p) indexes):
			Index = (i * floor(sqrt(p)) + j)
		or	Index = (i * floor(sqrt(p)) + j) mod phi(p)
		or	Index = (i * floor(sqrt(p)) + j + 0) mod phi(p)
		or	Index = (i * floor(sqrt(p)) + j + 0) mod (p-1)
		or	Index = (i * floor(sqrt(p)) + j + shift_value) mod (p-1)				-> where shift_value = 0
		or	Index = (i * floor(sqrt(p)) + j + shift_value) mod (p-1)				-> where shift_value = any
		or	Index = (i * floor(sqrt(p)) + j + (shift_value mod phi(p)) ) mod (p-1)	-> this is the same, by modulo phi(p) = (p-1), when p is prime.
			
			And shift_value can be private value too, which can be used to generate "Index", locally.

			All, this, allow to extract an unique pseudo-rand values,
			from large table floor(sqrt(p)) * floor(sqrt(p)),
			and extract it, just by indexes (i and j),
			and extract this directly, like in Blum-Blum-Shub algorithm, by index, after compute that "Index".
			
				Any "prand", contains in range (1, (p-1)),
				and can have bitlength up to (p.prev()).bitLength;
				or bytelength up to ( ( (p.prev()).bitLength - (p.prev()).bitLength % 8 ) / 8 + (((p.prev()).bitLength%8 > 0) ? 1 : 0) );
				So, any "prand", can have a static bitlength, or bytelength of specified bits,
				when p is a SafePrime, lesser than ((new BigInteger('2').pow(new BigInteger(bits))).subtract(1));
		
					Seed values, can be specified on start, with index 'seed',
					then, any "prand"-value can be extracted by index or [i, j], as BigIntegers, or as (hexa)decimals-strings.
	*/
	
	//define this valuest to cache it, after seed, and do not re-compute this again and again, on each iteration.
	var BRAPRNG_p				=	undefined;
	var BRAPRNG_phi_p			=	undefined;
	var BRAPRNG_FloorSqrtP		=	undefined;
	var BRAPRNG_bits			=	undefined;
	var BRAPRNG_g				=	undefined;
	var BRAPRNG_shift_value		=	undefined;
	
	function BRAPRNG(
			IndexOrObject_ij		//Index (need to specify it)	-	string, or BigInteger, or array with strings ['0', '1'], or object with i and j: {'i':'1', 'j':'3'}, or 'seed' if seed specified on first start.
		,	set_p					//(optional, seed or 'hex')		-	string or BigInteger with P, or start value of p, or number with bits, or 'hex', if need to return hex;
		,	set_g					//(optional, seed)				-	string or BigInteger with g, or start number to generate g, or 'dynamic', to get g from Index.
		,	set_shiftValue			//(optional, seed)				-	set shift-value, to generate Index from (i,j)-values.
	)
	{
		//console.log('start Bijective PRNG...');
		
		if(
				typeof BRAPRNG_p === 'undefined'
			||	(
					(typeof set_p !== 'undefined')
				&&	(set_p !== 'hex')
			)
		){
			console.log('BRAPRNG_p - is undefined or must to be changed. Try to set it...');
			var gen_p =	(
								(
									(set_p !== 'hex')
									?	set_p
									: undefined
								)
							||	prompt(
										'Enter the (hexa)decimal-string with safe-prime p\n'
									+	'or with number from which previous safe-prime will be generated\n'
									+	'or type nothing and cancel this prompt, to set default bitlength 256 bits.'
								)
							||	256
						)
			;
			
			if(
					(typeof gen_p === 'number')
				&&	(gen_p === 256)
			){
				gen_p = new bigInt('115792089237316195423570985008687907853269984665640564039457584007913129603823');		//first safe prime before 2^256 (to do not recalculate it for bitlength of 256 bits of input value "Index", and output value "prand")
			}
			else{
				gen_p = new bigInt().from(gen_p);
			}
			
			BRAPRNG_p = bigInt.GenSafePrime(gen_p);
			console.log('now BRAPRNG_p = ', BRAPRNG_p.toString());
			
			BRAPRNG_phi_p = BRAPRNG_p.prev();							//phi(p) = (p-1), when p is prime, and moreover safe-prime. 	Save this value, to do not recalculate this.
			
			BRAPRNG_FloorSqrtP = BRAPRNG_p.sqrt('floor')[0];			//save this value to do not recalculate this.
			
			BRAPRNG_bits = BRAPRNG_p.bitLength().value;					//save this value to get formatted hex-values, with fixed bitlength, in future;
		}
		if(
				(typeof BRAPRNG_g	===	'undefined')
			||	(typeof set_g !== 'undefined')
		){
			var gen_g = 	set_g
						||	prompt(
									'Enter (hexa)decimal-string to specify g\n'
								+	'or the first number from which g will be generated, (default = 1, means first primitive root, from \'1\')\n'
								+	'or type nothing and cancel prompt, to set default value of g as \'dynamic\', and depended from \'Index\'', '1'
							)
						||	'dynamic'
			;
			if(gen_g === 'dynamic'){
				BRAPRNG_g = gen_g;
			}else{
				BRAPRNG_g = (BRAPRNG_p).GetPrimitiveRoot(new bigInt().from(gen_g));
			}
			console.log('BRAPRNG_g', BRAPRNG_g.toString());
			
		}
		if(
				(typeof BRAPRNG_shift_value === 'undefined')
			||	(typeof set_shiftValue !== 'undefined')
		){
			console.log('Set \'shift_value\' to rotate circle.');
			var use_shift_value = 		set_shiftValue
									||	prompt(
												'To rotate cicle on some number of indexes, specify the \'shift_value\'\n'
											+	'as a (hexa)decimal-string (default = 0)\n'
											+	'or type nothing and cancel prompt, to set default value as 0', '0'
										)
									||	'0'
			;
			
			BRAPRNG_shift_value = bigInt().from(use_shift_value);
			console.log('BRAPRNG_shift_value', BRAPRNG_shift_value.toString());
		}
		if(IndexOrObject_ij === 'seed'){console.log("seed accepted"); return;}

		if(
					(typeof IndexOrObject_ij === 'object')
			&&	(
					(typeof IndexOrObject_ij.i !== 'undefined')
				||	(typeof IndexOrObject_ij[0] !== 'undefined')
			)
			&&
			(
					(typeof IndexOrObject_ij.j !== 'undefined')
				||	(typeof IndexOrObject_ij[1] !== 'undefined')
			)
		){
			var i = IndexOrObject_ij.i || IndexOrObject_ij[0];
			var j = IndexOrObject_ij.j || IndexOrObject_ij[1];
			
			//console.log('i', i, 'j', j);
			
			var Index = (
							(												//	(
								(
									(
										(
											new BigInteger().from(i)		//		i
										)
										.multiply(							//		*
											BRAPRNG_FloorSqrtP				//		floor(sqrt(p))
										)
									)
									.add(
											new BigInteger().from(j)		//		+j
									)
								)
								.add(
											new BigInteger().from(
												BRAPRNG_shift_value			//		+shift_value
											).mod(							//		mod
												BRAPRNG_phi_p				//		phi(p)
											)
								)											//	)
							)
							.mod(											//	mod
											BRAPRNG_phi_p					//	phi(p)
							)
						)
			;
		}
		else{
		//	console.log('this...')
			var Index = bigInt().from(IndexOrObject_ij)
									.add(
										BRAPRNG_shift_value
											.mod(							//	mod
											BRAPRNG_phi_p					//	phi(p)
										)
									)
			;
		}
		
	//	console.log(
	//		'\n'	+	'BRAPRNG_p', BRAPRNG_p.toString(),
	//		'\n'	+	'BRAPRNG_phi_p', BRAPRNG_phi_p.toString(),
	//		'\n'	+	'BRAPRNG_FloorSqrtP', BRAPRNG_FloorSqrtP.toString(),
	//		'\n'	+	'BRAPRNG_bits', BRAPRNG_bits.toString(),
	//		'\n'	+	'BRAPRNG_g', BRAPRNG_g.toString()
	//	);
		

		//console.log('Index', Index.toString());

		var use_g = (
						(BRAPRNG_g === 'dynamic')
						? (BRAPRNG_p).GetPrimitiveRoot(Index)
						: BRAPRNG_g
					)
		;

		var prand = use_g.modPow(Index, BRAPRNG_p);		//prand = g^Index mod p
		prand =
					(set_p !== 'hex')
					?	prand
					:	prand
						.toString(16)
						.padStart(
									(
											( ( BRAPRNG_p.bitLength().value - BRAPRNG_p.bitLength().value % 8 ) / 8 )
										+	( ( BRAPRNG_p.bitLength().value % 8 > 0 ) ? 1 : 0 )
									)
									*2
								,	'0'
						)
		;
		return prand;	//as BigInteger
	}
	//Usage:
	//	BigInteger.BRAPRNG(
	//			Index			//Index, as string or BigInteger, or array with indexes, with string or with bigIntegers [i, j], or object {'i': i, 'j', j}
	//		,	p				//(optional)	string or BigInteger - p, or the number from which need to find previous safe prime p, or string 'hex', if need to return hex with bytelength of p
	//		,	g				//(optional)	string or Biginteger - g, or first value from which need to find g. Or string 'dynamic', to compute g from Index
	//		,	shift_value		//(optional)	string or BigInteger - shift_value to rotate circle on shift_value mod phi(p) indexes.
	//	).toString()
	
	//	optional parameters, can be specified at first start of generator,
	//	then just Index, as string with Index, or array/object with i, j + 'hex', as second parameter 'p'
	//		Example:
	//		console.log(
	//				BigInteger.BRAPRNG('seed',256,'1','0')		//set seed for generator (any value can bee undefined, to set it, using prompt)
	//			,	BigInteger.BRAPRNG('1')						//generate without seet
	//			,	BigInteger.BRAPRNG('2')
	//			,	BigInteger.BRAPRNG(['1', '1'])
	//			,	BigInteger.BRAPRNG(['1', '2'], 'hex')		//b4870a125e963a78979dcd0222fb973c12e6f1adcdd7167fb511cfd4ee8f5315
	//		);
	
	
	//When p, g, and shift_value already defined, after set the BRAPRNG-seed
	//there is possible to find unknown indexes (i, j) by hexadecimal value, with this function,
	//by searching this, in growing square of the table:
	function BRAPRNG_FindIJ(value){
	
		//	i	1 2 1 2 3 1 3 2 3 4 1 4 2 ...
		//	j	1 1 2 2 1 3 2 3 3 1 4 2 4 ...
		//		1     2         3
		//		1*1   2*2       3*3
		//		Square side is growing...
		if(typeof BRAPRNG_FloorSqrtP === 'undefined'){console.log('set seed, at first'); return false;}
		for (var i = new BigInteger('1'); i.leq(BRAPRNG_FloorSqrtP); i = i.next()){
			for (var j = new BigInteger('1'); j.leq(i); j = j.next()){
			//	console.log('i', i.toString(), 'j', j.toString(), BRAPRNG([j, i], 'hex'));
				if(BRAPRNG([i.toString(), j.toString()], 'hex') === value){	//	compare (i, j) too
					break;
				}
				else if(i.neq(j)){	//if i not equal of j,								compare (j, i) too
			//		console.log('i', j.toString(), 'j', i.toString(), BRAPRNG([j, i], 'hex'));
					if(BRAPRNG([j.toString(), i.toString()], 'hex') === value){
						var temp = i;												//	and change indexes
						i = j;														//	i to j
						j = temp;													//	j to i
						break;
					}
				}
			}
			if(BRAPRNG([i.toString(), j.toString()], 'hex') === value){
				break;
			}
		}
		return { 'i': (i.toString()), 'j': (j.toString()) };
		//BRAPRNG([i, j], 'hex') - element, after set seed.
	}
	//For example, indexes i, j, is not known, but seed (p, g, and shift_value) is known:
	//and also, known some value: b4870a125e963a78979dcd0222fb973c12e6f1adcdd7167fb511cfd4ee8f5315
	//let's find this indexes:
	//	BigInteger.BRAPRNG('seed',256,'1','0') 	//seed generator (any value can bee undefined, to set it, using prompt)
	//	console.log(
	//			BigInteger.BRAPRNG_FindIJ('b4870a125e963a78979dcd0222fb973c12e6f1adcdd7167fb511cfd4ee8f5315')	//{i: "1", j: "2"}
	//		,	BigInteger.BRAPRNG(['1', '2'], 'hex')			//b4870a125e963a78979dcd0222fb973c12e6f1adcdd7167fb511cfd4ee8f5315
	//	)


	
	
	
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
    Integer.randBetween						=	randBetween;					//randBetween(a, b, rng)
    Integer.randbits						=	get_random_k_bits;
    Integer.getSetMRrounds					=	getSetMRrounds;					//getSetMRrounds() or getSetMRrounds(rounds) - get or set the value of rounds MillerRabin, to check primality for prime numbers.
    Integer.from							=	from;							//from(value), value - (hexa)decimal string, number, or bigInteger;
    Integer.BBSBigInteger 					=	BBSBigInteger;
    Integer.GenSafePrime 					=	generateSafePrime;				//generateSafePrime(bitlength)
    Integer.genStrongPrime 					=	genStrongPrime;					//genStrongPrime(bits, maxIter, strings)
    Integer.isStrongPrime 					=	isStrongPrime;					//isStrongPrime(p, s, r, t)
    Integer.EulerPhi 						=	EulerPhi;						//EulerPhi(n)
    Integer.Factorize 						=	Factorize;						//factorize number, using Pollard-rho algorithm, with Richard Brent optimization.
    Integer.BRAPRNG 						=	BRAPRNG;						//Bijective PRNG.
    Integer.BRAPRNG_FindIJ 					=	BRAPRNG_FindIJ;					//Find (i and j), by value, in the square table, by grow the sqaure in this table.
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

//RSABigInteger object with functions:
var RSABigInteger = (function (undefined) {
    "use strict";
	
	/*
		This code allow to RSA-encrypt/RSA-decrypt, and RSA-sign/RSA-verify of bytearrays, with arbitrary bytelengths, using BigIntegers.
		
		Describe an RSA-operations:
		m - message, c - encrypted message (cipher), e - public exponent, d - secret exponent, n - modulus,
		(e, n) - public key, (d, n) - private key, m_ - decrypted message,	s - signature;
			
		RSA Encrypt-decrypt:
			(e, n) -> from owner for someone
			c	=	m ^ e % n;	-	RSA-encrypt by owner's public key (someone)
			c -> to owner of privkey
			m_	=	c ^ d % n;	-	RSA-decrypt by owner's private key (owner)
			m_ === m			-	true, the main property.
			
		RSA Sign-Verify:
			s	=	m ^ d % n;	-	RSA-sign by private key (owner)
			(m, s, (e, n)) -> to someone;
			m_	=	s ^ e % n;	-	RSA-decrypt by public key (someone)
			m_ === m			-	true, the main property.
			
			All this is working, using bigInt.modPow()
			when m, e, d, n - is bigInegers,
			and when m have value from 0 up to n-1,
			then c and s have value from 0 up to n-1 too;
			
			For data with arbitrary bytelengths,
			data can be readed by blocks,
			blocks -> to hex,
			hex -> to bigIntegers,
			bigIntegers -> to cipher, and back.
			
			(e, n) - pubkey, (d, n) - privkey.

			c = m^e % n		- encrypt	by pub;
			m_ = m^d % n	- decrypt	by priv;

			s = m^d % n		- sign		by priv;
			m_ = m^e % n	- extract	by pub;

			When "m" is BigInteger in (0, ..., (n-1)), "c" and "s" is BigIntegers in (0, ..., (n-1)) too.
			And m.modPow(exp, modulus), can be used.

			When "m" have arbitrary length, it must to be splitted by blocks with values in (0, ..., (n-1));
			When "m_block" have bitlength (n.bitLength()-1), or bytelength ( ( n.bitLength() - ( n.bitLength()%8 ) / 8 ) - ( ( n.bitLength()%8 > 0 ) ? 1 : 0 ) ),
				any block can be encoded in bigitnegers with value in range (0, ..., (n-1)), and return cipher in the same range, with value up to (n-1)
				with bitlength (n.bitLength()) and bytelength (n.bitLength() - (n.bitLength() % 8) / 8);
			Different block-lengths make encryption/decrypion and sign/verify the different-function, dispite one function (modPow), to do this - RSA-operations.
			
			The following functions allow to do this:
				RSABigInteger.EncryptBytes(key, src, byPriv)		// Encrypt bytearray with arbitrary length by Pub (default), or byPriv (sign it).
				RSABigInteger.DecryptBytes(key, src, byPub)			// Decrypt bytearray with arbitrary length by Priv (default), or byPub (extract it from signature).
	*/
	
	//			Additional functions.
	function hexToBase64(hstr)										// Hex to Base64
	{
		hstr = ((hstr.length%2 == 1)? '0'+hstr : hstr);	//add one null, at beginning, if string length is odd.
		return btoa(
			String.fromCharCode.apply(null,
				hstr.replace(/\r|\n/g, "").replace(/([\da-fA-F]{2}) ?/g, "0x$1 ").replace(/ +$/, "").split(" ")
			)
		);
	}
	RSABigInteger.hexToBase64				=	hexToBase64;			//hexToBase64(hstr)						// Hex to Base64

	function base64ToHex(b64str)									// Base64 to Hex
	{
		for (var i = 0, bin = atob(b64str.replace(/[ \r\n]+$/, "")), hex = []; i < bin.length; ++i) {
			var tmp = bin.charCodeAt(i).toString(16);
			if (tmp.length === 1) tmp = "0" + tmp;
			hex[hex.length] = tmp;
		}
		return hex.join("");
	}
	RSABigInteger.base64ToHex				=	base64ToHex;			//base64ToHex(b64str)					// Base64 to Hex

	function	B64ToBi		( 	b64	)								// Base64-string -> to BigInteger.
	{
		return new BigInteger(base64ToHex(b64), 16);
	}
	RSABigInteger.B64ToBi					=	B64ToBi;				//B64ToBi	( 	b64	)					// Base64-string -> to BigInteger.

	function	Bi2Base64	(	bi	)								// BigInteger -> to Base64-string.
	{
		return hexToBase64(bi.toString(16));
	}
	RSABigInteger.Bi2Base64					=	Bi2Base64;				//Bi2Base64	(	bi	)					// BigInteger -> to Base64-string.

	function	Combine		(first, second)							// Combine, and concatenate two arrays.
	{
		return first.concat(second);
	}
	RSABigInteger.Combine					=	Combine;				//Combine(first, second)				// Combine, and concatenate two arrays.

	//	Methods to work with with ByteArrays.
	function	CombineUint8(first, second)							// Combine, and concatenate two bytearrays(Uint8Arrays).
	{
	//		1.
		var combined;
		if(first.length === 0 || second.length === 0){
			combined = ((first.length > 0) ? first : second);
		}else{
			combined = new Uint8Array(first.length + second.length);
			combined.set(first, 0);
			combined.set(second, first.length);
		}

	//		or 2.
	//	var first_str = first.join(','); var second_str = second.join(',');
	//	var combined_str = first_str + (((second_str !== '') && (first_str !== '')) ? ',' : '') + second_str;
	//	//console.log('first_str', first_str, 'second_str', second_str, 'combined_str', combined_str);
	//	var combined = new Uint8Array(combined_str.split(','));												//or by this way
		
	//		or 3.
	//	var combined = new Uint8Array(	(Array.from(	first	)).concat(Array.from(	second	)));		//or by this way

		return combined;
	}
	RSABigInteger.CombineUint8				=	CombineUint8;			//CombineUint8(first, second)			// Combine, and concatenate two bytearrays.

	function CompareBytes(one, two) 								// Compare two bytearrays (Uint8Arrays)
	{
		return (one.toString() === two.toString());
	}
	RSABigInteger.CompareBytes				=	CompareBytes;			//CompareBytes(one, two) 				// Compare two bytearrays

	function diffarrays(arr1, arr2){								// Show differences between two arrays.
		var maxlength = ( (arr1.length>arr2.length) ? arr1.length : arr2.length);
		var res = '';
		for(var i = 0; i<maxlength; i++){
			if(arr1[i] !== arr2[i]){
				res += ('i: '+i+', arr1[i]: '+arr1[i]+', arr2[i]'+arr2[i]+'\n');
			}
		}
		return (res === '');
	}
	RSABigInteger.diffarrays				=	diffarrays;				//diffarrays(arr1, arr2) 				// Show differences between two arrays.
	//console.log('diffarrays(src2, dec2)', diffarrays(src2, dec2));



	//		Generated key, or loaded key...
	var RSA_key = {
		//	main rsa-keys components:
			'e'				:	new BigInteger()	//public exponent
		,	'd'				:	new BigInteger()	//secret exponent
		,	'n'				:	new BigInteger()	//modulus
		//	another values to save from rsa-key (for privkey only):
		,	'p'				:	new BigInteger()	//privKey's "p"
		,	'q'				:	new BigInteger()	//privKey's "q"
		//	need to acellerate encryption/decryption with privKey using chinese-remainder-theorem:
		,	'dp'			:	new BigInteger()	//dp
		,	'dq'			:	new BigInteger()	//dq
		,	'InverseQ'		:	new BigInteger()	//IneverseQ
		//	xml-keys, as strings:
		,	'xml_privKey'	:	''					//xml_privKey (if loaded)
		,	'xml_pubKey'	:	''					//xml_pubKey from privKey, or just pub.
	};
	RSABigInteger.RSA_key					=	RSA_key;				//RSA_key								// Object with key, after generating and import of this. Available just for test, but commented.
	//console.log(RSABigInteger.RSA_key) 						//show it:
	//console.log(JSON.stringify(RSABigInteger.RSA_key));		//Object with bigInts -> to JSON-string.

	var ready = false;	//need to stop script, when keys loading or save. Default - false; true, when ready.
	
	//Generate RSA-key, and save in RSA_key-variable.
	function GenerateRSAKeys(	//Generate, and save RSA-keys
		bitlength				//bitlength can be specified, default value = 512, just for test (this is faster)
	)
	{
		ready = false;
		bitlength = bitlength || 512;						//default value = 512 bits, if undefined.
		bitlength = (bitlength < 128 ? 128 : bitlength);	//minimum is 128 bits, else, sometimes errors, in RSABigInteger.TEST()...

		/*
					Crypto Strength of p and q.

			The values p and q must be a safe-primes, or strong primes,
			and (p-1) with (q-1) must to have no common divisors (composition of common factors of this),
			becides at least one common divisor beetween this - number 2,
			just because since p and q is prime, this is odd, so (p-1) and (q-1) is even numbers, and 2 is a common divisor for this even numbers.
	
			Since n = pq, (n-1) = (pq-1) = (p−1)(q−1)+(p−1)+(q−1),
			so any common divisors, and a greatest common divisor (as composition of all commmon factors) of secret values (p-1), (q-1),
			contains in factorization order of public value (n-1), since n is public.
			Moreover, g = gcd((p-1), (q-1)) is a divisor for secret value phi(n):
			φ(n) / g = λ(n) - Carmichael's totient function.
	
			Proof:
				Since n = pq, λ(n) = lcm(λ(p),λ(q)), and since p and q - primes, λ(p) = φ(p) = (p − 1), and λ(q) = φ(p) = (q − 1),
				therefore, λ(n) = lcm((p − 1), (q − 1)), and since lcm(a,b) = |ab|/gcd(a,b),
				then λ(n) = lcm((p-1), (q-1)) = |(p-1)(q-1)|/gcd((p-1), (q-1)).
				What is "(p-1)(q-1)" ? this is φ(n), since p and q - is a primes. Moreover, this is natural number, and |φ(n)| = φ(n).
				So: λ(n) = φ(n) / gcd((p-1), (q-1)), where gcd((p-1), (q-1)) = g,
				This means:	λ(n) = φ(n) / g, or φ(n) / g = λ(n)
	
			Also, this means g * λ(n) = φ(n), where g - this is a number privkeys, which are cryptoeqivalent privkeys for secret key d.
			Because φ(n) always divisible on λ(n), and φ(n) / λ(n) = g, when e*d = 1 mod φ(n) is true, then e*d = 1 mod λ(n) is true too.
			And for each d, can be finded some privkey d', which is cryptoequivalently for that secret privkey d:
			(d' = d mod λ(n) === d' mod λ(n)), but look: (d' mod φ(n) !== d mod phi(n));
			For this conditions, is corresponding all keys, in this row: (d', d'+λ(n), d'+2λ(n), d'+3λ(n), ..., d'+(g-1)λ(n)),
			and all this keys are privkeys, which are cryptoequivalently for privkey d.
	
			The number of this cryptoequivalently keys is growing, when g is growing, and since g = gcd((p-1), (q-1)),
			this value is growing, when (p-1) and (q-1), have large greatest common divisors,
			or many common-factors, as result of factorization private values (p-1), (q-1),
			or just a public value (n-1), since n is public value. When g is large number,
			then any d'+x*λ(n) is more easy to brute and force, just in range [0, ..., λ(n)];
			__________________
			1. But, when p and q is a safe-prime numbers, then p' = (p-1)/2, q' = (p-1)/2 - Sophie-Germen prime-numbers,
			and (p-1) = 2p', (q-1) = 2q', this numbers have only one common divisor - number 2, and another divisors are not common, this is a primes.
	
			2. Also, when p and q is a strong-prime numbers, then (p-1) and (q-1) have large prime divisors and some another divisors,
			which can be not a common divisors for both this numbers, together.
		*/

				//use Safe-Primes for p and q:
				var bi_p		=	BigInteger.GenSafePrime(BigInteger.randbits(bitlength/2), 'previous');		//generate p as random safe-prime, with half-bitlength of n.
				var bi_q 		=	bi_p;																		//q is p, on start.
				while(bi_q.eq(bi_p)){																			//while q == p
					bi_q		=	BigInteger.GenSafePrime(BigInteger.randbits(bitlength/2), 'previous');		//generate safe prime q != p, with half-bitlength of n.
				}
				
				//			Also, can be used a strong-primes for p and q, but need to fix bitlength there, on genertion of this...
				//	var SP = BigInteger.genStrongPrime(20);
				//	console.log(
				//		'StongPrime object: ', SP,
				//		'Strong Prime value:', SP.p.toString(),
				//		'isStrongPrime: ', BigInteger.isStrongPrime(SP.p, SP.s, SP.r, SP.t),
				//		'bitlength: ', SP.p.bitLength().value
				//	);

				var bi_n		=	bi_p.multiply(bi_q);									//n = p*q
				var lambdaN = BigInteger.lcm(bi_p.prev(), bi_q.prev());
				var bi_e = lambdaN.genCoPrime(lambdaN.bitLength().value);					//lambdaN
				
				//continue generate values...
				var bi_d		=	bi_e.modInv(lambdaN);									//lambdaN - d			=	( e^(−1) mod phi_n ) - is working, because (phi_n % λ(n) === 0), and for when (d*e ≡ 1 (mod λ(n))), (d*e ≡ 1 (mod λ(n))) too. But (d > λ(n)) can be true.
				
			//	if(bi_e.geq(bi_d)){					//if e lesser or equals d
			//		var temp = bi_d; bi_d = bi_e; bi_e = temp;	//swap bi_e <-> bi_d
			//	}												//to return e, lesser than d, to keep secret a longer d.
				
				var bi_dp		=	bi_d.mod(bi_p.prev());									//dp		=	( d mod (p−1) )
				var bi_dq		=	bi_d.mod(bi_q.prev());									//dq		=	( d mod (q−1) )
				
				var bi_InverseQ	=	bi_q.modInv(bi_p);										//inverseQ	=	( q^(−1) mod p )
				
						//save pub (e,n) and priv (d, n);
						RSA_key.e = bi_e;
						RSA_key.d = bi_d;
						RSA_key.n = bi_n;

						//save another values.
						RSA_key.p			=	bi_p;
						RSA_key.q			=	bi_q;
						//additional values for accelleration
						RSA_key.dp			=	bi_dp;
						RSA_key.dq			=	bi_dq;
						RSA_key.InverseQ	=	bi_InverseQ;
				
				//Try to save this generated values into xml-string.
				//
				//	XML RSA-keys format (like in C# RSA.ToXmlString(Boolean), RSA.FromXmlString(Boolean)): 
				//	<RSAKeyValue>
				//		<Modulus>	Base64-encoded-number	</Modulus>
				//		<Exponent>	Base64-encoded-number	</Exponent>
				//		<P>			Base64-encoded-number	</P>
				//		<Q>			Base64-encoded-number	</Q>
				//		<DP>		Base64-encoded-number	</DP>
				//		<DQ>		Base64-encoded-number	</DQ>
				//		<InverseQ>	Base64-encoded-number	</InverseQ>
				//		<D>			Base64-encoded-number	</D>
				//	</RSAKeyValue>
				//
				//	n	-	Modulus
				//	e	-	Exponent
				//	p	-	P
				//	q	-	Q
				//	d	-	D
				//
				//	dp	-	DP, this is ( d mod (p−1) ), 
				//	dq	-	DQ, this is ( d mod (q−1) ),
				//	InverseQ - this is ( q^(−1) mod p ).
				//
				//	These are used in applying the Chinese Remainder Theorem to RSA decryption, which is an optimization technique.
				//

					//Generate xml-string with RSA-privKey
					RSA_key.xml_privKey =	""
									//	+	"<RSAKeyValue>"
										+	"<RSAKeyValueBigInteger>"
										+		"<Modulus>"		+	( Bi2Base64(	bi_n		) )	+	"</Modulus>"
										+		"<Exponent>"	+	( Bi2Base64(	bi_e		) )	+	"</Exponent>"
										+		"<P>"			+	( Bi2Base64(	bi_p		) )	+	"</P>"
										+		"<Q>"			+	( Bi2Base64(	bi_q		) )	+	"</Q>"
										+		"<DP>"			+	( Bi2Base64(	bi_dp		) )	+	"</DP>"
										+		"<DQ>"			+	( Bi2Base64(	bi_dq		) )	+	"</DQ>"
										+		"<InverseQ>"	+	( Bi2Base64(	bi_InverseQ	) )	+	"</InverseQ>"
										+		"<D>"			+	( Bi2Base64(	bi_d		) )	+	"</D>"
									//	+	"</RSAKeyValue>"
										+	"</RSAKeyValueBigInteger>"
					;
					//Format this as a multistring.
					RSA_key.xml_privKey = 	RSA_key.xml_privKey
									.replace(/</g, "\n\t<")
									.replace(/>/g,">\n\t\t")
									.replace(/\t\t\n/g,"")
								//	.replace(/\t<\/RSAKeyValue>\n\t\t/g,"</RSAKeyValue>")
									.replace(/\t<\/RSAKeyValueBigInteger>\n\t\t/g,"</RSAKeyValueBigInteger>")
									.replace(/\n\t<R/g,"<R")
					;
					
					
					RSA_key.xml_pubKey = ""
									//	+	"<RSAKeyValue>"
										+	"<RSAKeyValueBigInteger>"
										+		"<Modulus>"		+	( Bi2Base64(	bi_n		) )	+	"</Modulus>"
										+		"<Exponent>"	+	( Bi2Base64(	bi_e		) )	+	"</Exponent>"
									//	+	"</RSAKeyValue>"
										+	"</RSAKeyValueBigInteger>"
					;

					RSA_key.xml_pubKey = 	RSA_key.xml_pubKey
									.replace(/</g, "\n\t<")
									.replace(/>/g,">\n\t\t")
									.replace(/\t\t\n/g,"")
								//	.replace(/\t<\/RSAKeyValue>\n\t\t/g,"</RSAKeyValue>")
									.replace(/\t<\/RSAKeyValueBigInteger>\n\t\t/g,"</RSAKeyValueBigInteger>")
									.replace(/\n\t<R/g,"<R")
					;
					
					ready = true;
	}
	RSABigInteger.GenerateRSAKeys			=	GenerateRSAKeys;		//GenerateRSAKeys(bitlength)			// Generate RSA-keys with specified bitlength.
	//Usage:
	//RSABigInteger.GenerateRSAKeys();	//generate keys with default bitlength 512 bits
	//RSABigInteger.GenerateRSAKeys(256); //generate keys with specified bitlength 256 bits

	function lsTest(){		//check is LocalStorage available (true/false)
		var test = 'test';
		try {
			if(localStorage.getItem(test) === null){
				localStorage.setItem(test, test);
				localStorage.removeItem(test);
			}
			return true;	//or/and return true
		} catch(e) {
			return false;	//false
		}
	}
	var IsLocalStorageAvailable = lsTest();		//test is LocalStorage available? true/false
	//Usage:
	//if(IsLocalStorageAvailable===true){} //work with LocalStorage.
	
	function LocalStorageSaveKeys(){	// Store keys in LocalStorage
		if(!IsLocalStorageAvailable) return false;
		//maybe need to check before, is LocalStorage available or not.
		localStorage.setItem("xml_privKey", RSA_key.xml_privKey		);
		localStorage.setItem("xml_pubKey",	RSA_key.xml_pubKey		);
		ready = true;
	}
	RSABigInteger.LocalStorageSaveKeys		=	LocalStorageSaveKeys;	//LocalStorageSaveKeys()				// Save RSA-keys, in localStorage, after generating or importing it. 
	//Usage:
	//RSABigInteger.LocalStorageSaveKeys();	//just save keys in LS.

	//Generate RSA_keys and save
	function GenerateRSAKeysAndSave(	// Generate RSA-keys and save this as XML-keys, into the files
		bitlength						//bitlength can be specified, default value = 512, just for test (this is faster)
	)
	{
		ready = false;
		bitlength = bitlength || 512;
		//Generate RSA-keys, and save this in (rsa, pa_Priv, pa_Pub)-values, or into BigIntegers.
		GenerateRSAKeys(
			bitlength					//bitlength, default value = 512, just for test (this is faster)
		);
		LocalStorageSaveKeys();
	}
	RSABigInteger.GenerateRSAKeysAndSave	=	GenerateRSAKeysAndSave;	//GenerateRSAKeysAndSave(bitlength);	// Generate keys and save in localStorage.
	//Usage:
	//RSABigInteger.GenerateRSAKeysAndSave(128); //Generate keys with bitLength 128, and save in LocalStorage.

	//Load RSA_keys from xml-string in LocalStorage
	function LocalStorageLoadKeys(){	// Retrieve keys from LocalStorage
		if(!IsLocalStorageAvailable) return false;
		ready = false;
		//maybe need to check before, is LocalStorage available or not.
		RSA_key.xml_privKey		=	localStorage.getItem("xml_privKey");
		RSA_key.xml_pubKey		=	localStorage.getItem("xml_pubKey");
		console.log('xml_privKey', RSA_key.xml_privKey, 'xml_pubKey', RSA_key.xml_pubKey);
		if(RSA_key.xml_privKey === null && RSA_key.xml_pubKey === null){
			console.log('Keys not found, and will be generated. Default bitlength === 512 bits. Run "GenerateRSAKeysAndSave(bits);" to change bitlength.');
			GenerateRSAKeysAndSave();
			setTimeout(
				function(){
					LocalStorageLoadKeys();
					console.log('xml_privKey', RSA_key.xml_privKey, 'xml_pubKey', RSA_key.xml_pubKey);
				},
				500
			);
		}
	}
	RSABigInteger.LocalStorageLoadKeys		=	LocalStorageLoadKeys;	//LocalStorageLoadKeys();				// Retrieve keys from LocalStorage.
	//Usage:
	//RSABigInteger.LocalStorageLoadKeys(); //Load keys from LocalStorage.

	//Load Keys from XML-string
	function LoadXMLKey(			// Load keys (priv+pub) or pub only if pubKey
		xmlKey 						//	and load it string with XML-pubKey or XML-privKey, or from LocalStorage, if this was undefined.
	)
	{
		ready = false;
		if(typeof xmlKey === 'undefined'){LocalStorageLoadKeys(); return;}	//Load Keys from LocalStorage, or generate it, if this does not exists, there.
		var xmlString = xmlKey;
		xmlString = xmlString.replace(/\t/g, '').replace(/\n/g, '');
		
		var parser = new DOMParser();
		var xmlDoc = parser.parseFromString(xmlString,"text/xml");
			//Then, load this key, into BigInteger-values:

			//Load values from xml-string
			if(xmlString.indexOf("<D>") !== -1){											//if this was been a privKey, and this contains <D>-value
				//decode values from base64 fields of XML - and import this into BigIntegers
				RSA_key.n			=	B64ToBi(xmlDoc.getElementsByTagName		("Modulus")		[0].childNodes[0].nodeValue);			//	n
				RSA_key.e			=	B64ToBi(xmlDoc.getElementsByTagName		("Exponent")	[0].childNodes[0].nodeValue);			//	e
				RSA_key.p			=	B64ToBi(xmlDoc.getElementsByTagName		("P")			[0].childNodes[0].nodeValue);			//	p
				RSA_key.q			=	B64ToBi(xmlDoc.getElementsByTagName		("Q")			[0].childNodes[0].nodeValue);			//	q
				RSA_key.dp			=	B64ToBi(xmlDoc.getElementsByTagName		("DP")			[0].childNodes[0].nodeValue);			//	dp
				RSA_key.dq			=	B64ToBi(xmlDoc.getElementsByTagName		("DQ")			[0].childNodes[0].nodeValue);			//	dq
				RSA_key.InverseQ	=	B64ToBi(xmlDoc.getElementsByTagName		("InverseQ")	[0].childNodes[0].nodeValue);			//	InverseQ
				RSA_key.d			=	B64ToBi(xmlDoc.getElementsByTagName		("D")			[0].childNodes[0].nodeValue);			//	d
				
				RSA_key.xml_privKey =	""
								//	+	"<RSAKeyValue>"
									+	"<RSAKeyValueBigInteger>"
									+		"<Modulus>"		+	( Bi2Base64(	RSA_key.n			) )	+	"</Modulus>"
									+		"<Exponent>"	+	( Bi2Base64(	RSA_key.e			) )	+	"</Exponent>"
									+		"<P>"			+	( Bi2Base64(	RSA_key.p			) )	+	"</P>"
									+		"<Q>"			+	( Bi2Base64(	RSA_key.q			) )	+	"</Q>"
									+		"<DP>"			+	( Bi2Base64(	RSA_key.dp			) )	+	"</DP>"
									+		"<DQ>"			+	( Bi2Base64(	RSA_key.dq			) )	+	"</DQ>"
									+		"<InverseQ>"	+	( Bi2Base64(	RSA_key.InverseQ	) )	+	"</InverseQ>"
									+		"<D>"			+	( Bi2Base64(	RSA_key.d			) )	+	"</D>"
								//	+	"</RSAKeyValue>"
									+	"</RSAKeyValueBigInteger>"
				;
				//Format this as a multistring.
				RSA_key.xml_privKey = 	RSA_key.xml_privKey
								.replace(/</g, "\n\t<")
								.replace(/>/g,">\n\t\t")
								.replace(/\t\t\n/g,"")
							//	.replace(/\t<\/RSAKeyValue>\n\t\t/g,"</RSAKeyValue>")
								.replace(/\t<\/RSAKeyValueBigInteger>\n\t\t/g,"</RSAKeyValueBigInteger>")
								.replace(/\n\t<R/g,"<R")
				;
			}
			else{																		//else if this was been pubKey
				RSA_key.e			=	B64ToBi(xmlDoc.getElementsByTagName		("Exponent")	[0].childNodes[0].nodeValue);			//	e
				RSA_key.n			=	B64ToBi(xmlDoc.getElementsByTagName		("Modulus")		[0].childNodes[0].nodeValue);			//	n
				RSA_key.p			=	new BigInteger();										//	and leave
				RSA_key.q			=	new BigInteger();										//	this values
				RSA_key.dp			=	new BigInteger();										//	all
				RSA_key.dq			=	new BigInteger();										//	as
				RSA_key.InverseQ	=	new BigInteger();										//	an empty
				RSA_key.d			=	new BigInteger();										//	values
				
				//RSA_key.xml_privKey		=	'';			//commented to leave old xml_privKey. Use pubkey, only, if you have only pubkey.
			}
			
			//or/and save pubkey.
			RSA_key.xml_pubKey = ""
							//	+	"<RSAKeyValue>"
								+	"<RSAKeyValueBigInteger>"
								+		"<Modulus>"		+	( Bi2Base64(	RSA_key.n		) )	+	"</Modulus>"
								+		"<Exponent>"	+	( Bi2Base64(	RSA_key.e		) )	+	"</Exponent>"
							//	+	"</RSAKeyValue>"
								+	"</RSAKeyValueBigInteger>"
			;

			RSA_key.xml_pubKey = 	RSA_key.xml_pubKey
							.replace(/</g, "\n\t<")
							.replace(/>/g,">\n\t\t")
							.replace(/\t\t\n/g,"")
						//	.replace(/\t<\/RSAKeyValue>\n\t\t/g,"</RSAKeyValue>")
							.replace(/\t<\/RSAKeyValueBigInteger>\n\t\t/g,"</RSAKeyValueBigInteger>")
							.replace(/\n\t<R/g,"<R")
			;

		//After all, key from keyFile, or from xmlString, is loaded into (rsa, pa_Priv, pa_Pub)-values, or into BigIntegers.
		ready = true;
	}
	RSABigInteger.LoadXMLKey				=	LoadXMLKey;			//LoadXMLKey(xmlKey);					// Load keys (priv+pub) or pub only if pubKey
	//Usage:
	//RSABigInteger.LoadXMLKey(xmlKeyString)

	//Load Key from string, and save in LocalStorage.
	function LoadXMLKeyAndSave(			// Load keys (priv+pub) or pub only if pubKey
		xmlKey 									//from KeyFile or string with XML-pubKey or XML-privKey.
	)
	{
		ready = false;
		console.log('xmlKey', xmlKey);
		LoadXMLKey(						//Load keys (priv+pub) or pub only if pubKey
			xmlKey 								//from KeyFile or string with XML-pubKey or XML-privKey.
		);
		LocalStorageSaveKeys();
	}
	RSABigInteger.LoadXMLKeyAndSave		=	LoadXMLKeyAndSave;		//LoadXMLKeyAndSave(xmlKey);			// Load keys (priv+pub) or pub only if pubKey, and save in LocalStorage.
	//Usage:
	//RSABigInteger.LoadXMLKeyAndSave(xmlKeyString); //Load key from xml-string, and save in LocalStorage.
	
	
	
//	Now, will be implemented the following RSA operations, for bytearrays with arbitrary bytelength, using BigInteger:
//		(d, n) - privkey, (e, n) - pubkey; e - public exponent, d - private exponent, n - modulus, c - ciphertext, 
//		c	= m ^ (e or d) mod n;		- encryption by pubkey or privkey (sign),
//		m'	= c ^ (d or e) mod n;		- decryption by privkey or pubkey (extract message from signature to verify it),
//	EncryptBytes, will encrypt (by pubKey) or sign (by privKey), the bytearray [src], into bytearray [dest], and return [dest],
//	DecryptBytes, will decrypt (by privKey) or extract from sinature (by pubKey), the bytearray [src], into bytearray [dest], and return [dest],
//	key - this is an xml-string, with pubKey or privKey (pubKey will be extracted from this, if need to use pubKey only).
//	
//	Data Lengths:
//	BlockSizeToWrite = ( ( ( n_bitlength - ( n_bitlength % 8 ) ) / 8 ) + ((( n_bitlength % 8 ) > 0)?1:0) );
//	ByteArray with source data, will be splitted by blocks with (BlockSiseToRead = ( BlockSizeToWrite - SubtractBytes )) bytes.
//	This blocks will be encrypted by pubkey from "key", or pubkey which is extracted from prikey "key" (if no need to sign by privKey).
//	Pubkey - is (e, n), where n, this is a modulus - a big number with specified "n_bitlength".
//	The result ciphertext have "n_bitlength" bits, or "BlockSizeToWrite" bytes, and will be writted by blocks in encrypted bytearray.
//
//	Last block will be encrypted as is, but after encrypting this block will be added a ulong-value (8 bytes) with "LastBlockLength".
//

	//Save length for blocks, to read-write data with arbitrary bytelenths.
	
	// Define this variables, to save the values of blocks to read openedText and cipher data.
	var 	SubtractBytes,	//how many bytes need to subtract from "result-block-length", to read "src-data", by blocks with "BlockSizeToWrite"
			BlockSizeToWrite,		//bytesize of block to write "dest-data".
			BlockSiseToRead;	//bytesize of block to read "src-data"
	
	//Set this values, by value of bitlength of modulus n.
	function set_lengths(				// Set lengths of blocks to read-write
		n_bitlength						//bitlength of modulus n from KeyFile
	)
	{
			//set this values:
			SubtractBytes = 1;											//select how many bytes need to subtract from each block. Default - 1 byte.

			BlockSizeToWrite          =         (							//BlockSizeToWrite for destination cipherData = n_bytelength (+ 1, when n_bitlength%8 > 0).
													(									//n_bytelength
														(								//=
															n_bitlength					//n_bitlength
															-							//-
															( n_bitlength % 8 )			//rest by modulo 8 (8 bits in byte)
														)
														/								//and divide
														8								//to 8
													)
													+									//block-size will be
													(
														(
															( ( n_bitlength % 8 ) > 0 ) //if rest is over null
														)
														? 1								//is larger
														: 0								//or the same
													)
												)
			;

			BlockSiseToRead         =         BlockSizeToWrite - SubtractBytes;	//block length to read source openText data
	//		console.log('n_bitlength', n_bitlength, 'SubtractBytes', SubtractBytes, 'BlockSiseToRead', BlockSiseToRead);
			return;	//and return, then.
	}
	RSABigInteger.set_lengths				=	set_lengths;			//set_lengths(n_bitlength)				// Set lengths of blocks to read-write
	//Usage:
	//RSABigInteger.set_lengths(n_bitlength);		//set length for read-write blocks, by n_bitlength, before read-write the data with arbitrary length.

	//		Additional functions (need to encode-decode bytes):
	function buf2hex(buffer) 	// ArrayBuffer to hex. buffer is an ArrayBuffer (Uint8Array.buffer)
	{
		return Array.prototype.map.call( new Uint8Array(buffer), function(x){ return (('00' + x.toString(16)).slice(-2));} ).join('');
	}
	RSABigInteger.buf2hex					=	buf2hex;				//buf2hex(buffer)						// ArrayBuffer to hex. buffer is an ArrayBuffer (Uint8Array.buffer)
	
	function hex2buf(hex)		// Hex to ArrayBuffer
	{
		hex = hex.padStart(2, '0');
		var typedArray = new Uint8Array(
			hex.match(/[\da-fA-F]{2}/gi)
			.map(
				function (h) {
					return parseInt(h, 16)
				}
			)
		);
		return typedArray.buffer;
	}
	RSABigInteger.hex2buf					=	hex2buf;				//hex2buf(hex)							// Hex to ArrayBuffer
	
	function hexToUint8(						// Hex to Uint8Array
		hexString
	,	padZeroBytes			//null padding on start
	){
		hexString = hexString
			.padStart(
				(
					(typeof padZeroBytes !== 'undefined')
						? padZeroBytes*2									//number of hexadecimal characters if double bytes
						: ( hexString.length + (hexString.length % 2) )		//or if hex string-length is odd, add 1 null at beginning.
				),
				'0'
			)
		;
	
		return (new Uint8Array(hex2buf(hexString)));
	}
	RSABigInteger.hexToUint8				=	hexToUint8;				//hexToUint8(hexString, padZeroBytes)	// Hex to Uint8Array + padding on start
	
	function Uint8ToHex(byteArray, padZeroBytes)		// Uint8Array to Hex
	{
		return Array.prototype.map
			.call(
				byteArray,
				function(byte) {
					return ('0' + (byte & 0xFF).toString(16)).slice(-2);
				}
			)
			.join('')
			.padStart( ( ( typeof padZeroBytes !== 'undefined' ) ? ( padZeroBytes*2 ) : 0 ), '0' )
		;
	}
	RSABigInteger.Uint8ToHex				=	Uint8ToHex;				//Uint8ToHex(byteArray, padZeroBytes)	// Uint8Array to Hex + padding on start
	//End additional functions.

	//function to write data in specified offset of block.
	function WriteBlock(								// Write src in the end of dest.
		dest	//here, in empty block, with fixed length
	,	src		//write this data
	)
	{
		for(
			var o = dest.length - src.length,	j=0;	//from offset "o", of dest array, and from offset "j" of src array
			o<dest.length;								//up to the end of dest
			o++, j++									//write each byte
		){
			dest[o] = src[j];							//as src bytes
		}
		return dest;									//and return rewrited dest
	}
	RSABigInteger.WriteBlock				=	WriteBlock;				//WriteBlock(dest,src)					// Write src in the end of dest.
	
	//			Accelerating, RSA-computing, using the chinese remainder theorem (used for decrypt by priv, or sign by priv only, not by pub):
	function CRTAcceleration(						// Decrypt encrypted block of ciphertext by priv, or sign block of openedText, by priv, using acceleration with chinese-remainder-theorem.
		value	//ciphertext BigInteger, with value from 0 up to (n-1), encrypted by pub, which need to decrypt faster by priv,
				//or message to sign by priv, which need to encrypt faster by priv.
	)
	{
		//		By definition of this method of accelleration, propose the following thing:
		//			2 modPow with exp 512 bits, by modulus 512 bits + 1 adding + 1 mulmod,
		//			all this is faster then 1 modPow with exponent 1024 bits, and faster in 2-3 times, for many values.
		//		This accelleration working only for encrypt by privKey (signing the data), or decrypt by privKey (decrypt encrypted data), not by a pubKey.
	
		//		Description:
		//		//	additional key values:
		//		d_P = d mod (p-1);
		//		d_Q = d mod (q-1);
		//		InverseQ = q^(-1) mod (p) = q.modInv(p);
		//		____________________________________________________________________________________________
		//		//	where this is defined:
		//		d_P			-	RSA_key.dp
		//		d_Q			-	RSA_key.dq
		//		InverseQ	-	RSA_key.InverseQ
		//			This values, defined, after load key.
		//		____________________________________________________________________________________________
		//		Steps:
		//		//faster decrypt (by priv), or sign-encrypt (when sign message by priv):
		//		m_p = C^(d_P) mod p
		//		m_q = C^(d_Q) mod q
		//		h = (InverseQ * (m_p + ( ( m_p < m_q ) ? [q/p]*p : 0 ) - m_q)) mod p
		//		m = (m_q + hq) mod (p*q) = (m_q + hq) mod n;
		//			where, C - ciphertext (encrypted by pubKey, and which is try to decrypt by privKey), or message (which is try to be signed by privKey);
		//			d_P, d_Q, InverseQ - additional key values; p, q - prime numbers as components of privKey; m - decrypted message, or signature. 

		var m_p = value.modPow(RSA_key.dp, RSA_key.p);				//		m_p = C^(d_P) mod p
		var m_q = value.modPow(RSA_key.dq, RSA_key.q);				//		m_q = C^(d_Q) mod q
		var h = (													//		h = (InverseQ * (m_p + ( ( m_p < m_q ) ? [q/p]*p : 0 ) - m_q)) mod p
					RSA_key.InverseQ
					.multiply(
						(
							m_p
							.add(
								(
									(m_p.leq(m_q))
										?	(
												(
													((RSA_key.q).divide(RSA_key.p))
													.add(BigInteger.one)
												)
												.multiply(RSA_key.p)
											)
										:	new BigInteger('0')
								)
							)
							.subtract(m_q)
						)
					)
				)
				.mod(RSA_key.p)
		;
		var decr = (m_q.add(h.multiply(RSA_key.q))).mod(RSA_key.n);		//		m = (m_q + hq) mod (p*q);
		return decr;	//return BigInteger, with value from 0 up to (n-1);
	}
	RSABigInteger.CRTAcceleration			=	CRTAcceleration;		//CRTAcceleration(value)				// Decrypt encrypted block of ciphertext by priv, or sign block of openedText, by priv, using acceleration with chinese-remainder-theorem.

	//
	//	Encrypt one block of "buffer", with "BlockSiseToRead", in each iteration of read "src-data",
	//	or encrypt last block in "buffer" with length "c",
	//	and return encrypted ciphertext as "encbuffer" with "BlockSizeToWrite".
	//	Encrypt this by pubkey, which is contains in "RSA_key",
	//	or encrypt it with privKey (if need to sign "src-data").
	//	
	//	This method will be called on each iteration of reading blocks of "source data"
	//

	//Encrypt one block of readed data.
	function	EncryptFullBlockOrLastBlock(	//encrypt full block or last block inside the cycles.
		buffer					//readed bytearray "buffer", with "BlockSiseToRead", from the source data, which can be converted to BigInteger with value from 0 up to (n-1)
	,	BlockSizeToWrite		//already defined by "set_lengths"-function, the "BlockSizeToWrite"
	,	BlockSiseToRead			//length of blocks for readed "src-data"
	,	c						//number of readed bytes of the current block
	,	ed						//ed - e or d. e (public exponent), if encrypt by pubkey (e, n); or d (secret exponent), if encrypt by privkey (d, n) to sign the message.
	,	n						//n - modulus
	)
	{
		var encbuffer = new Uint8Array(BlockSizeToWrite);		//create new encbuffer with "BlockSizeToWrite".
		if (c == BlockSiseToRead)								//if this was been readed a full block, and not a last block - just encrypt it.
		{
			var encryptedBuffer;													//define new bytearray for encryptedBuffer (this can have a different bytelength)
					encryptedBuffer = hexToUint8(									//and encrypt there
						(
							(ed === 'chinese-remainder-theorem')					//if priv used, and if need to accellerate singing of data (encrypt by priv)
							? CRTAcceleration(new BigInteger	(Uint8ToHex(buffer), 16)) //use this function
							:	(													//or
									(new BigInteger	(Uint8ToHex(buffer), 16))		//encrypt the buffer -> to Hex -> to BigInteger
									.modPow	(										//by using modPow
										ed,											//to encrypt this buffer, into BigInteger, by e or d
										n											//and modulus n
									)
								)
						)
						.toString(16)												//convert BigInteger -> to Hex
						, BlockSizeToWrite											//and add Padding
					)
			;
			encbuffer = WriteBlock(encbuffer, encryptedBuffer);						//Write block in the end of encbuffer.
		}
		else //else if last block, and readed bytes not equals of BlockSiseToRead.
		{
			var buffer2 = new Uint8Array(c);
			
			for (var i = 0; i < c; i++){
				buffer2[i] = buffer[i];
			}
			var encryptedBuffer;										//define new encrypted buffer for result, this can have different length
				encryptedBuffer = hexToUint8(							//and encrypt
						(
							(ed === 'chinese-remainder-theorem')
							? CRTAcceleration(
									new BigInteger	(
										( (buffer.length === 0) ? '00' : Uint8ToHex(buffer2) )
										, 16
									)
								)
							:	(
									(
										new BigInteger	(
											( (buffer.length === 0) ? '00' : Uint8ToHex(buffer2) )
											, 16
										)
									)
									.modPow	(ed, n)						//by using BigInteger modPow method
								)
						)
						.toString(16)
					,
					BlockSizeToWrite
				)
			;
			encbuffer = WriteBlock(encbuffer, encryptedBuffer);
			var LastBlockLength = new Uint8Array(8);
			LastBlockLength = hexToUint8(c.toString(16), 8);
			encbuffer = CombineUint8(encbuffer, LastBlockLength);
		}
		
		return encbuffer;
	}

	//encrypt "src"-bytes with arbitrary bytelength.
	function	EncryptBytes(				//Encrypt bytearray from src to dest, by using pubkey in key;
		key									//key - pub, for encrypt, or priv, to get pub from it, and encrypt then, if byPriv == false. This can be xml-string with key too.
	,	src									//reference to bytearray with source data	
	,	byPriv								//encrypt by privKey to sing the message, and decrypt by pubKey, then.
	,	disableCRT
	)
	{
		byPriv = ( ( ( typeof byPriv === 'undefined' ) || (byPriv === false ) ) ? false : true );			//false, by default, or true;
		disableCRT = ((typeof disableCRT === 'undefined') || (disableCRT === false)) ? false : true;
		LoadXMLKey(key);							//extract public key from "key"-file with xml.
		var n_bitlength = 0;
			n_bitlength = (RSA_key.n).bitLength().value;
		set_lengths(n_bitlength);
			
		var buffer = new Uint8Array( BlockSiseToRead );
		var encbuffer = new Uint8Array ( BlockSizeToWrite );
		var c = 0;

		var ed = null;
		var n = null;
		ed = ed || (
			(byPriv === true)					//if byPriv == true
			?	
				(disableCRT === false)
					?	'chinese-remainder-theorem'		//then, use accelleration with chinese-remainder-theorem
					:	RSA_key.d						//or use, d -> to BigInteger
			:	RSA_key.e						//else, e -> to BigInteger
		);
		n = RSA_key.n;							//n -> to BigInteger

		var dest = new Uint8Array(0);
		var i = 0;
		while(i<=src.length){
			buffer = src.subarray(i, (i+=BlockSiseToRead));
			c = buffer.length;
			encbuffer = EncryptFullBlockOrLastBlock(buffer, BlockSizeToWrite, BlockSiseToRead, c, ed, n);
			dest = CombineUint8(dest, encbuffer);
		}
		return dest;
	}
	
	//Decrypt one block of readed cipher.
	//RSA decrypt
	function	DecryptFullBlockOrLastBlock(	//Decrypt full block or last block inside the cycle.
		buffer									//readed buffer from the source file
	,	BlockSizeToWrite						//already defined BlockSizeToWrite, as reference
	,	c										//number of readed bytes, as reference
	,	isNextUlong								//is next value ulong or not? true/false
	,	dataLength								//Length of data
	,	de										//de - d or e. d (secret exponent) - if decrypt by priv (d, n), (by default); or e (pubic exponent) - if decrypt by pub (verify signature)
	,	n										//n - modulus
	,	current_block							//number of the current block
	,	max_blocks								//number of the max block to decrypt
	,	length__								//length of last block
	)
	{
		dataLength		=	dataLength		||	0		;
		de				=	de				||	null	;
		n				=	n				||	null	;
		current_block	=	current_block	||	0		;
		max_blocks		=	max_blocks		||	0		;
		length__		=	length__		||	0		;

		var BufferLength = ( ( current_block == max_blocks-1 ) ? length__ : ( BlockSizeToWrite - SubtractBytes ) );		//length__ !

		var decryptedBuffer = new Uint8Array( BlockSizeToWrite );
		var decbuffer = new Uint8Array( (((isNextUlong === true)) ? length__ : BlockSiseToRead ) );

		decryptedBuffer = hexToUint8(															//and encrypt
							(
								(de === 'chinese-remainder-theorem')
								?	CRTAcceleration(new BigInteger	(Uint8ToHex(buffer), 16))
								:	(
										(new BigInteger	(Uint8ToHex(buffer), 16))				//buffer2
											.modPow	(de, n)										//by using BigInteger modPow method
									)
							)
							.toString(16)
				,
				BufferLength
			)
		;

		decbuffer = WriteBlock(decbuffer, decryptedBuffer);
		return decbuffer;
	}

	
	//
	//	Decrypt encrypted bytearray with cipher, by priv.
	//	(d, n) - privkey, where n have n_bitlength size, and n_bytelength.
	//	encrypted file readed by blocks with n_bytelength,
	//	this block will be decrypted, then result will writted to blocks with bytelength (n_bytelenght - 1).
	//	Last 8 bytes of encrypted file, this is ulong value with bytelength of last block.
	//	This value will be readed at beginning, and then this value need to skip, and slice the bytes of last block, then.
	//
	
	//Decrypt cipher with arbitrary bytelength.
	function	DecryptBytes(
		key								//file with priv or pub
	,	src								//reference on src-bytes
	,	byPub							//default - false (decrypt by Priv);
	,	disableCRT
	)
	{
		byPub = ( ( ( typeof byPub === 'undefined' ) || (byPub === false) ) ? false : true );
		disableCRT = ((typeof disableCRT === 'undefined') || (disableCRT === false)) ? false : true;

		var length__ = 0;
		var LastBlockLength = src.subarray(src.length-8, src.length);	//read last 8 bytes with LastBlockLength
		length__ = parseInt((new BigInteger	(Uint8ToHex(LastBlockLength), 16)).toString(), 10);

		var dataLength = src.length;								//get length of src.

		LoadXMLKey(key);			//extract public key from "key"-file with xml.

		var n_bitlength = 0;
			n_bitlength = (RSA_key.n).bitLength().value;
			set_lengths(n_bitlength);

			var buffer 		= new Uint8Array(BlockSizeToWrite);
			var decbuffer 	= new Uint8Array(BlockSiseToRead);

			var de	=	null;
			var n	=	null;
				de	=	de	||	(
									(byPub === true)
									? RSA_key.e
									: 	
										(disableCRT === false)
										?	'chinese-remainder-theorem'	//then, use accelleration with chinese-remainder-theorem
										:	RSA_key.d					//or use privKey to decrypt, by default
								)
				;
				n	=	RSA_key.n;

			var max_blocks = Math.floor(src.length / BlockSizeToWrite);
			var current_block = 0;

			var c = 0;

			var	isNextUlong = false;

			var dest = new Uint8Array(0);
			var i = 0;
			while(i<src.length){
				buffer = src.subarray(i, (i+=(BlockSiseToRead+1)));
				c = buffer.length;
				if (c != BlockSizeToWrite)
				{
					var buffer2 = new Uint8Array(c);
					for (var i = 0; i < c; i++){
						buffer2[i] = buffer[i];
					}
					buffer = buffer2;
				}
				var rest = dataLength - ( current_block * BlockSizeToWrite );
				if		( rest <= 0 ){
					var NewBuffer = new Uint8Array(buffer.Length-8);
					buffer = NewBuffer;
				}
				else if	( rest < 8 ){
					var PartOfLenHere = 8 - rest;	//number of bytes in this block
					var NewBuffer = new Uint8Array(buffer.Length-PartOfLenHere);
						buffer = NewBuffer;
						isNextUlong = true;
				}
				else if	( rest == 8 ){
					break;
				}
				if( current_block >= (max_blocks-1) ){
					isNextUlong = true;
				}
				decbuffer = DecryptFullBlockOrLastBlock(
							buffer
						,	BlockSizeToWrite
						,	c
						,	isNextUlong
						,	dataLength
						,	de
						,	n
						,	current_block
						,	max_blocks
						,	length__
					)
				;
				dest = CombineUint8(dest, decbuffer);
				current_block += 1;
			}
		return dest;
	}

	RSABigInteger.EncryptBytes				=	EncryptBytes;			//EncryptBytes(key, src, byPriv)		// Encrypt bytearray with arbitrary length by Pub (default), or byPriv (sign it).
	RSABigInteger.DecryptBytes				=	DecryptBytes;			//DecryptBytes(key, src, byPub)			// Decrypt bytearray with arbitrary length by Priv (default), or byPub (extract it from signature).
	//RSABigInteger.EncryptBytes(key, src, byPriv)
	//RSABigInteger.DecryptBytes(key, src, byPub)
	
	//This functions can be used for encrypt-decrypt or sign-verify, with different keys.
	//		c	= m^e mod n		- encrypt by pub
	//		m_	= m^d mod n		- decrypt by priv
	//		s	= m^d mod n		- sing by priv
	//		e	= s^e mod n		- extract message from signature, to verify it.

	function TEST(){
		// TEST:
		var rand_byte = (window.crypto.getRandomValues(new Uint8Array(1))[0]) + 8;
		console.log('rand_byte', rand_byte);
		
		RSABigInteger.GenerateRSAKeys(rand_byte);	//generate keys
		//console.log('RSABigInteger.RSA_key', RSABigInteger.RSA_key);
		
		var rand_message = window.crypto.getRandomValues(new Uint8Array(window.crypto.getRandomValues(new Uint8Array(1))[0]));
		//console.log('rand_message', rand_message.toString());

		var readyInterval = setInterval(			//wait some time to write key.
			function(){
				if(ready===false){return;} 			//if not ready, return and repeat, by interval
				else{clearInterval(readyInterval)}; //else clearInterval, and continue with this code.
				
				var encdec = false;				//test encrypt-decrypt
				console.log(
					'RSA encrypt by pub, decrypt by priv:\t',
					(
						encdec =
						RSABigInteger.CompareBytes(
							rand_message,
							RSABigInteger.DecryptBytes(
								RSABigInteger.RSA_key.xml_privKey,
								RSABigInteger.EncryptBytes(
									RSABigInteger.RSA_key.xml_pubKey,
									rand_message,
									false
								),
								false
							)
						)
						, encdec		//and return it
					)
				);

				var signverify = false;			//test encrypt-decrypt
				console.log(
					'sign by priv, verify signature by pub:\t',
					(
						signverify = 
							RSABigInteger.CompareBytes(
								rand_message,
								RSABigInteger.DecryptBytes(
									RSABigInteger.RSA_key.xml_pubKey,
									RSABigInteger.EncryptBytes(
										RSABigInteger.RSA_key.xml_privKey,
										rand_message,
										true
									),
									true
								)
							)
						, signverify	//and return it
					)
				);

				if(encdec === false || signverify === false){
					if(encdec === false){console.log('encdec === false');}
					else if(signverify === false){console.log('signverify === false');}
					//	and show two variables for static-test
					console.log(
						'//multistring variable with privkey to load it;\n'+
						'var rsaprivkey = (function () {/*'+RSABigInteger.RSA_key.xml_privKey+
						'\n*/}).toString().match(/[^]*\\\/\\*([^]*)\\*\\\/\\}$\/)[1];'	+	'\n' +
						'//bytearray with generated message\n'+
						'var rand_message = new Uint8Array(['+rand_message.toString()+']);'
					);
				}
			},
			1	//wait to generate or load keys, and write it.
		);
	}
	
	function STATIC_TEST(){	//test with static values to debug it.

//		copy and paste two generated variables, on fail, to debug that fail.
//____________________

//multistring variable with privkey to load it;
var rsaprivkey = (function () {/*<RSAKeyValueBigInteger>
	<Modulus>
		VpqsJoYYQ9k=
	</Modulus>
	<Exponent>
		PUFutJpgMDM=
	</Exponent>
	<P>
		qbYkLw==
	</P>
	<Q>
		gqMudw==
	</Q>
	<DP>
		TnHzZQ==
	</DP>
	<DQ>
		Gb718w==
	</DQ>
	<InverseQ>
		FoEoVQ==
	</InverseQ>
	<D>
		FcEhbznTNec=
	</D>
</RSAKeyValueBigInteger>
*/}).toString().match(/[^]*\/\*([^]*)\*\/\}$/)[1];
//bytearray with generated message
var rand_message = new Uint8Array([14,86,57,157,225,178,156,2,205,1,232,157,227,157,237,204,76,102,30,102,251,244,217,41,141,226,15,183,154,59,179,97,115,184,236,70,170,97,240,235,192,205,223,192,33,139,232,133,45,131,222,20,205,152,119,211,249,45,56,240,131,205,254,88,4,246,21,159,79,229,187,194,123,0,46,194,11,97,211,167,92,34,109,7,96,119,240,71,71,14,117,139,22,6,204,209,101,177,163,244,148,111,235,195,160,55,31,77,83,10,139,65,30,170,196,209,237,222,184,2,25,184,78,214,15,134,221,182,84,17,96,190,86,28,217,12,169,0,32,163,132,5,140,18,94,115,33,208,54,18,116,123,86,164,140,29,245,96,48,255,135,44,166,49,198,71,188,126,200,165,7,117,30,215,182,68,58,169,204,186,119,216,143,20,41,218,50,214,176,186,59,170,204,189,96,63,11,161,165,21,205,227,239,114,224,127,120,149,197,220,32,98,63,241,43,127,196,232,175,132,211,242,112,234,214,6,78,239,144,13,251,45,102,237,175,225,86,25,185]);

//____________________

		//and continue test it...
		RSABigInteger.LoadXMLKey(rsaprivkey);	//load key from multistring variable.
		
		//test encrypt-decrypt:
		//console.log('rand_message', 'var rand_message = new Uint8Array(['+rand_message.toString()+']);');
		//console.log('xml_privKey', RSABigInteger.RSA_key.xml_privKey, '\nxml_pubKey', RSABigInteger.RSA_key.xml_pubKey);
		
	var readyInterval = setInterval( function(){
				if(ready===false){return;} 			//if not ready, return and repeat, by interval
				else{clearInterval(readyInterval)}; //else clearInterval, and continue with this code.
		
		var encrypted, decrypted;
		console.log(
			'RSA encrypt by pub, decrypt by priv:\t',
			RSABigInteger.CompareBytes(
				rand_message,
				(
					decrypted = 
						RSABigInteger.DecryptBytes(
							RSABigInteger.RSA_key.xml_privKey,
							(
								encrypted = 
									RSABigInteger.EncryptBytes(
									RSABigInteger.RSA_key.xml_pubKey,
									rand_message,
									false
								)
								, encrypted //and return it
							),
							false
						)
					,	decrypted //and return it
				)
			)
		);
		console.log('encrypted.toString()', encrypted.toString());
		console.log('decrypted.toString()', decrypted.toString());

		//test sign-verify
		var signed, verified;
		console.log(
			'sign by priv, verify signature by pub:\t',
			RSABigInteger.CompareBytes(
				rand_message,
				(
					verified = 
						RSABigInteger.DecryptBytes(
							RSABigInteger.RSA_key.xml_pubKey,
							(
								signed = 
									RSABigInteger.EncryptBytes(
										RSABigInteger.RSA_key.xml_privKey,
										rand_message,
										true
									)
								, signed	//and return it
							),
							true
						)
					, verified //and return it
				)
			)
		);
		console.log('signed.toString()', signed.toString());
		console.log('verified.toString()', verified.toString());
		}
		,
		1
	);
		
	
	}

    function RSABigInteger(){}	//empty constructor for this object.
	
	//Add functions to RSABigInteger-object. All this available by call RSABigInteger.function(params);
	RSABigInteger.TEST						=	TEST;					//TEST()								// Test RSA encryption-decryption.
	RSABigInteger.STATIC_TEST				=	STATIC_TEST;			//STATIC_TEST()							// STATIC_TEST RSA encryption-decryption, and debug it, after copy-and-paste the values from test.

	return RSABigInteger;			//return RSABigInteger-object, with functions inside.

})();

//	Now, add few polyfills (if this still not supported in old browsers):

//String.repeat - polyfill (using in String.padStart)
if (!String.prototype.repeat) {
  String.prototype.repeat = function(count) {
    'use strict';
    if (this == null) {
      throw new TypeError('can\'t convert ' + this + ' to object');
    }
    var str = '' + this;
    count = +count;
    if (count != count) {
      count = 0;
    }
    if (count < 0) {
      throw new RangeError('repeat count must be non-negative');
    }
    if (count == Infinity) {
      throw new RangeError('repeat count must be less than infinity');
    }
    count = Math.floor(count);
    if (str.length == 0 || count == 0) {
      return '';
    }
    // Обеспечение того, что count является 31-битным целым числом, позволяет нам значительно
    // соптимизировать главную часть функции. Впрочем, большинство современных (на август
    // 2014 года) браузеров не обрабатывают строки, длиннее 1 << 28 символов, так что:
    if (str.length * count >= 1 << 28) {
      throw new RangeError('repeat count must not overflow maximum string size');
    }
    var rpt = '';
    for (var i = 0; i < count; i++) {
      rpt += str;
    }
    return rpt;
  }
}

//	String.padStart - polyfill (using in some functions - keyword "padStart")
// https://github.com/uxitten/polyfill/blob/master/string.polyfill.js
// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/String/padStart
if (!String.prototype.padStart) {
    String.prototype.padStart = function padStart(targetLength,padString) {
        targetLength = targetLength>>0; //floor if number or convert non-number to 0;
        padString = String(padString || ' ');
        if (this.length > targetLength) {
            return String(this);
        }
        else {
            targetLength = targetLength-this.length;
            if (targetLength > padString.length) {
                padString += padString.repeat(targetLength/padString.length); //append to original to ensure we are longer than needed
            }
            return padString.slice(0,targetLength) + String(this);
        }
    };
}

//Additional functions:
function B64ToHex(b64) {
	var bin = atob(b64);
	var hex = [];

	bin.split('')
//	.forEach
	.map
	(function (ch) {
		var h = ch.charCodeAt(0).toString(16);
		if (h.length % 2) { h = '0' + h; }
		hex.push(h);
	});

	return hex.join('');
}
//console.log(B64ToHex('AQAB'));	//010001

function HexToB64(hex) {
	if (hex.length % 2) { hex = '0' + hex; }

	var bin = [], i = 0, d, b;
	while (i < hex.length) {
		d = parseInt(hex.slice(i, i + 2), 16);
		b = String.fromCharCode(d);
		bin.push(b);
		i += 2;
	}

	return btoa(bin.join(''));
}
//console.log(HexToB64('10001'));	//AQAB
