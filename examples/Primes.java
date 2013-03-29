class Primes {
  static int isPrime(int x) {
    for(int d = 2; d < x; d++) {
      if(x % d == 0) {
        return 0;
      }
    }
    return 1;
  }
  
  static int nthPrime(int n) {
    int x = 2;
    int i = 0;
    while(i < n + 1) 
    {
      if(isPrime(x) != 0) {
        i++;
      }
      x++;
    }
    return x - 1;
  }
  
  static int main() {
    int res;
    res = isPrime(10);
    BuiltIn.assertEq(res, 0);
    res = isPrime(50);
    BuiltIn.assertEq(res, 0);
    res = isPrime(97);
    BuiltIn.assertEq(res, 1);
    res = nthPrime(0);
    BuiltIn.assertEq(res, 2);
    res = nthPrime(1);
    BuiltIn.assertEq(res, 3);
    res = nthPrime(2);
    BuiltIn.assertEq(res, 5);
    res = nthPrime(3);
    BuiltIn.assertEq(res, 7);
    res = nthPrime(4);
    BuiltIn.assertEq(res, 11);
    res = nthPrime(5);
    BuiltIn.assertEq(res, 13);
    return 0;
  }
}
