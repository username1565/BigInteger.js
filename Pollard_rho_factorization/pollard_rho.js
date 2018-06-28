/* More algorithm information here:     
 *https://en.wikipedia.org/wiki/Pollard%27s_rho_algorithm
*** This tool only guarantees accurate factorization up to 15 digits as JavaScript considers Integers accurate to 15 digits.
That being said sometimes it does correctly factor some larger Integers whereas some fail.
For an input with more than 15 digits, compare your input to the product
to evaulate whether an approximation was made in the calculation.

Still trying to identify why some are approximated and some work out.
Preliminary tests indicate that large integers with a lot of small factors fail whereas
large integers with fewer small factors succeed.
*/

var primeFactors;
var product;

function getPrimeFactorization() {
  var input = document.getElementById("input").value;
  var algo = document.getElementById("algo").value;
  clearResults();
  
  primeFactors = [];
  if(input===''){primeFactors.push("Empty string is not a number");}

  factorNumber(input, algo);
  primeFactors.sort(function(a, b) {
    return a - b;
  });
  if(shouldShowLargeIntegerInfo(input)){
    showWarning();
    showProduct();
  }
  document.getElementById("result").innerHTML = "Result factors: "+primeFactors;
}

// Results clearing + setting
function clearResults() {
  document.getElementById("result").innerHTML = "";
  document.getElementById("product").innerHTML = "";
  document.getElementById("warning").style.display = "none";
}
  
function shouldShowLargeIntegerInfo(input) {
  if(input.toString().length > 15) {
    return true;
  }
}

function showWarning() {
  document.getElementById("warning").style.display = "inline";
}

function showProduct() {
  product = getProduct();
  document.getElementById("product").innerHTML = "The product is: " + product;
}

function getProduct() {
  var product = bigInt('1');
  for(i = 0; i < primeFactors.length; i++) {
	product = product.multiply(bigInt(primeFactors[i].replace(/\s+/g, ""))); //remove whitespaces recursive from array element
  }
  return product.toString();
}

/*
//this functions rewrited inside in standart rho script
function f(x) {
  return x.multiply(x).subtract(bigInt('1'));
}

function g(x) {
  return x.multiply(x).add(bigInt('1'));
}
*/

// The algorithm
function factorNumber(input, algo) {
  var input = bigInt(input);
  
  if(input.eq(bigInt('1'))) {
    return;
  }
  if(input.eq(bigInt('0'))) {
    primeFactors.push(" Cann't find concrete prime factors for zero. [all primes * 0 = 0] ");
	return;
  }
  if(input.MillerRabin(20)) {
	console.log(
		'function factorNumber('+input+', '+algo+'):'
		, '\nFound prime factor - ', input.toString(), '\n'
	);
	
	primeFactors.push(" " + input.toString() + " ");
    return;
  }
  else{
    var divisor = rho(input, algo, 'f');
    factorNumber(divisor, algo);
    factorNumber(input.divide(divisor), algo);
  }
}

/*
//this function already know in bigInteger, as bigInt.MillerRabin(k);
function isPrime(input) {
  for(i = 2; i <= Math.sqrt(input); i++) {
    if (input % i == 0) {
      return false;
    }
  }
  return true;
}
*/

function rho(input, algo, func) {
  var num1 = bigInt('2'), num2 = bigInt('2'), divisor;
  if(input.mod(bigInt('2')).eq(bigInt('0'))) {
    return bigInt('2');
  }
  
  //select variation of rho-algorithm
  if(algo==='Pollard-rho'){ 											//using standart ρ-method
	//standart algo or Pollard ρ-method
	do {
		if(func==='f'){ //function as letter
		
			//f function
			//return x.multiply(x).subtract(bigInt('1'));
			
			//previous script
			//num1 = func(num1).mod(input);
			//num2 = func(func(num2)).mod(input);
			
			//rewrited
			num1 = num1
					.multiply(num1)
					.subtract(bigInt('1'))
					.mod(input);
			
			num2 = (num2
					.multiply(num2)
					.subtract(bigInt('1'))
					)
						.multiply(
							(num2
								.multiply(num2)
								.subtract(bigInt('1'))
							)
						)
					.subtract(bigInt('1'))
					.mod(input);
		}else if(func==='g'){ //function as letter
		
			//g function
			//return x.multiply(x).add(bigInt('1'));
		
			//prev script
			//num1 = func(num1).mod(input);
			//num2 = func(func(num2)).mod(input);
			
			//rewrited
			num1 = num1
					.multiply(num1)
					.add(bigInt('1'))
					.mod(input);
			
			num2 = (num2
					.multiply(num2)
					.add(bigInt('1'))
					)
						.multiply(
							(num2
								.multiply(num2)
								.add(bigInt('1'))
							)
						)
					.add(bigInt('1'))
					.mod(input);
		}
	

/*
	//previous script
//select variation of rho-algorithm
  if(algo==='Pollard-rho'){ 											//using standart ρ-method
	//standart algo or Pollard ρ-method
	do {
		if(func==='f'){
			num1 = func(num1).mod(input);
			num2 = func(func(num2)).mod(input);
		}else if(func==='g'){
			num1 = func(num1).mod(input);
			num2 = func(func(num2)).mod(input);
		}
	
	
	
		num1 = func(num1).mod(input);
		num2 = func(func(num2)).mod(input);
		
		and called as rho(input, f); rho(input, g), with f(x) and g(x) functions...
		After "algo" parameter was been added - this give an error.
*/	


	divisor = bigInt.gcd(num1.subtract(num2).abs(), input);
	} while (divisor.eq(bigInt('1')));

	if(divisor.eq(input)) {
		return rho(input, algo, 'g');
	}
	return divisor;
  }
  
  else if(algo==='Pollard-rho+random'){									//using ρ-method with random int in each iteration
	//Pollard ρ-method from here: http://rextester.com/TIJY97700
	//Here using random numbers in each iteration
  
	var sqrt = input.sqrt();
	if(typeof sqrt[1] !== 'undefined'){sqrt = sqrt[0];}
  
	var x = bigInt.randBetween('1', sqrt).mod(input).add(bigInt(1));
	var c = bigInt.randBetween('1', sqrt).mod(input).add(bigInt(1));
	var y = x;
	var g = bigInt(1);
  
	//fn is f(x) = x*x + c
    while(g.eq(bigInt(1)))
    {
        x = x.modPow(bigInt(2), input).add(c).mod(input);
        y = y.modPow(bigInt(2), input).add(c).mod(input);
        y = y.modPow(bigInt(2), input).add(c).mod(input);
        g = bigInt.gcd(x.subtract(y).abs(), input);
    }
    return g;
  }
  else if(algo==='Pollard-rho+Brent'){ 									//using Richard Brent optimization
	//Pollard-rho Brent
	//Source code from py-script, here: https://github.com/joxeankoret/diaphora/blob/master/jkutils/factor.py
	/*
	This is JS implementation of optimization from Richard Brent
	for John's Pollard ρ-method
	+ Using BigInteger
	
	This method give a faster factorization for number
	539665377349940636086669695451569769025523026168820293846695597848211:

	123457 , 1234577 , 12345701 , 123456791 , 1234567907 , 12345678923 , 123456789133 , 1234567891253
	The product is: 539665377349940636086669695451569769025523026168820293846695597848211
	*/
		var y = bigInt.randBetween('1', input.subtract(bigInt(1)));
        var c = bigInt.randBetween('1', input.subtract(bigInt(1)));
		var m = bigInt.randBetween('1', input.subtract(bigInt(1)));
		
		var g = bigInt(1);
		var r = bigInt(1);
		var q = bigInt(1);
		
		var x, k, ys;
		while(g.eq(bigInt(1))){             
                x = y;
                for(i=bigInt(0); i.leq(r); i = i.next()){
                        y = y.modPow(bigInt(2), input).add(c).mod(input);
				}
                k = bigInt(0);
                while( k.lt(r) && g.eq(bigInt(1)) ){
                        ys = y
                        for(i=bigInt(0); i.leq(bigInt.min(m, r.subtract(k))); i = i.next()){
								y = y.modPow(bigInt(2), input).add(c).mod(input);
                                q = q.multiply(x.subtract(y).abs()).mod(input);
                        }
						g = bigInt.gcd(q, input);
                        k = k.add(m);
				}
                r = r.multiply(bigInt(2));
		}
        if(g.eq(input)){
                while(true){
                        ys = ys.modPow(bigInt(2), input).add(c).mod(input);
						ys = ys.modPow(bigInt(2), input).add(c).mod(input);
						g = bigInt.gcd(x.subtract(ys).abs(), input);
                        if(g.greater(bigInt(1))){
                                break;
						}
				}
		}
        return g;
	}
}

/*
//this function already exists in BigInteger.

function gcd(x, y) {
  if (x % y == 0) {
    return y
  } else {
    return gcd(y, x % y);
  }
}


*/