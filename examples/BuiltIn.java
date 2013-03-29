import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
 

class BuiltIn {
  public static void assertEq(int actual, int expected) {
    if (actual != expected)
      throw new Error("Assertion violation: expected " + expected + " but found " + actual);
  }

  public static void printInt(int x) {
    System.out.print(x);
  }
  
  public static void newLine() {
    System.out.println();
  }
  
  public static int readInt() {
    BufferedReader bufferRead = new BufferedReader(new InputStreamReader(System.in));
    try {
      while(true) {
        String s = bufferRead.readLine();
        try {
          int x = Integer.parseInt(s);
          return x;
        } catch(NumberFormatException e) {
          continue;
        }
      }
    } catch(IOException e) {
      System.exit(0);
    }
    return 0;
  }
}
