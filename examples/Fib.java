class Fib {
  static int fib(int n) {
    if(n == 0) {
      return 0;
    } else if(n == 1) {
      return 1;
    } else {
      return fib(n - 1) + fib(n - 2);
    }
  }
  
  static int main() {
    int res;
    res = fib(0);
    BuiltIn.assertEq(res, 0);
    res = fib(1);
    BuiltIn.assertEq(res, 1);
    res = fib(2);
    BuiltIn.assertEq(res, 1);
    res = fib(3);
    BuiltIn.assertEq(res, 2);
    res = fib(4);
    BuiltIn.assertEq(res, 3);
    res = fib(20);
    BuiltIn.assertEq(res, 6765);
    res = fib(30);
    BuiltIn.assertEq(res, 832040);
    res = fib(34);
    BuiltIn.assertEq(res, 5702887);
    return 0;
  }
}
