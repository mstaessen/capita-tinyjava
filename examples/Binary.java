class Binary {
  static int div(int x, int y)
  {
    int n = 0;
    while(x >= y) {
      x = x - y;
      n++;
    }
    return n;
  }
  
  static int rem(int x, int y)
  {
    int n = 0;
    while(x >= y) {
      x = x - y;
      n++;
    }
    return x;
  }
  
  static int printBinary(int x)
  {
    if(x > 0) {
      printBinary(div(x, 2));
      if(rem(x, 2) == 0) {
        BuiltIn.printInt(0);
      } else {
        BuiltIn.printInt(1);
      }
    }
    return 0;
  }
  
  static int main() {
    int x = BuiltIn.readInt();
    printBinary(x);
    BuiltIn.newLine();
    return 0;
  }
}
