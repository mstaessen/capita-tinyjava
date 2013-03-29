class Factorial {

  static int fac(int n) {
    if(n == 1) {
      return 1;
    } else {
      return n * fac(n -1);
    }
  }

  static int main() {
    int x = fac(5);
    BuiltIn.assertEq(x, 120);
    int y = fac(3);
    BuiltIn.assertEq(y, 6);
    return 0;
  }
}
