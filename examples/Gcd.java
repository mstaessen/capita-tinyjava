class Gcd {
  static int gcd(int a, int b) {
    if (a == 0)
       return b;
    while (b != 0) {
      if (a > b)
        a = a - b;
      else
        b = b - a;
    }
    return a;
  }
  
  static int main() {
    int x = gcd(33, 24);
    BuiltIn.assertEq(x, 3);
    int y = gcd(300, 150);
    BuiltIn.assertEq(y, 150);
    return 0;
  }
}
