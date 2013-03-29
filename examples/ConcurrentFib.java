class ConcurrentFib {
  static int fib(int n) {
    if(n == 0) {
      return 0;
    } else if(n == 1) {
      return 1;
    } else {
      return fib(n - 1) + fib(n - 2);
    }
  }
  
  static int async_fib(int n) {
    return fib(n);
  }
  
  static int cfib(int n) {
    if(n == 0) {
      return 0;
    } else if(n == 1) {
      return 1;
    } else {
      int a = async_fib(n - 1);
      int b = fib(n - 2);
      return a + b;
    }
  }
  
  static int main() {
    int res;
    res = cfib(0);
    BuiltIn.assertEq(res, 0);
    res = cfib(1);
    BuiltIn.assertEq(res, 1);
    res = cfib(2);
    BuiltIn.assertEq(res, 1);
    res = cfib(3);
    BuiltIn.assertEq(res, 2);
    res = cfib(4);
    BuiltIn.assertEq(res, 3);
    res = cfib(20);
    BuiltIn.assertEq(res, 6765);
    res = cfib(30);
    BuiltIn.assertEq(res, 832040);
    res = cfib(34);
    BuiltIn.assertEq(res, 5702887);
    return 0;
  }
}
